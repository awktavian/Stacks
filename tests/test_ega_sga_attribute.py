"""Native, core-only regression for EGA/SGA reference registration.

Run: python3 -m unittest discover -s tests -v
No Lake build or dependency download: only temporary compiler artifacts.
A missing pinned compiler is an error, never a skipped/pass result.
"""

import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "StacksCore/Tactic/EgaSgaAttribute.lean"

#: Wall-clock budget, in seconds, for EACH pinned-compiler leg of this check
#: (module compile, import fixture, probe).  Measured on this lane 2026-11-20:
#: the whole three-leg test runs in 25.4 s on the estate's Lean host when the
#: machine is not contended (commit b255dfed3, `python3 -m unittest discover
#: -s tests -p test_ega_sga_attribute.py`, rc 0).  The previous flat 60 s per
#: leg left a 2.4x margin on an idle host and false-failed on a contended one:
#: the first leg was measured exceeding 60 s on a saturated 10-core host while
#: `lean` was merely slow, not stuck.  A missing or broken compiler is still a
#: hard error at any budget, so raising the cap adds measurement and weakens
#: nothing.  Raise-only: the historic 60 s floor still applies to the
#: environment override.  Non-numeric override fails the test at import.
LEAN_TIMEOUT_S = max(60, int(os.environ.get("STACKS_TEST_LEAN_TIMEOUT_S", "600")))

IMPORTED = r'''
import ReferenceUnderTest
open Lean Elab Command Stacks.EgaSga
run_cmd liftCoreM do
  addRef ``Nat.add .ega "IV 5.8.6" "(i)"
'''

PROBE = r'''
import ImportedReferences
open Lean Elab Command Stacks.EgaSga
namespace ReferenceRegression
run_cmd liftCoreM do
  let imported := allRefs (← getEnv)
  unless imported.any (fun r => r.declName == ``Nat.add && r.comment == "(i)") do
    throwError "positive control: persisted imported reference missing"
  addRef ``Nat.add .ega "  IV  5.8.6 " "(ii)"
  unless allRefs (← getEnv) == imported do
    throwError "imported duplicate changed enumeration"
  let decl := `ReferenceRegression.subject
  addDecl <| .defnDecl {
    name := decl, levelParams := [], type := mkConst ``Nat, value := mkNatLit 0,
    hints := .opaque, safety := .safe
  }
  addDocStringCore decl "Original subject documentation."
  addRef decl .ega "IV 5.8.6" "(ii)"
  let before ← findDocString? (← getEnv) decl
  unless before.getD "" |>.endsWith "EGA IV₂, §5, (5.8.6) (ii)" do
    throwError "positive control: initial reference did not augment documentation"
  let refs := (allRefs (← getEnv)).filter (·.declName == decl)
  unless refs.size == 1 do throwError "expected one initial reference"
  addRef decl .ega "  IV   5.8.6  " "affine case"
  unless (← findDocString? (← getEnv) decl) == before do
    throwError "duplicate reference changed documentation"
  unless ((allRefs (← getEnv)).filter (·.declName == decl)) == refs do
    throwError "duplicate reference changed the original record"
  addRef decl .sga "4 IV 4.9.4" ""
  let distinct := (allRefs (← getEnv)).filter (·.declName == decl)
  unless distinct.size == 2 do throwError "distinct reference was lost"
  unless (← findDocString? (← getEnv) decl).getD "" |>.endsWith
      "SGA 4, Exp. IV, (4.9.4)" do
    throwError "distinct reference did not augment documentation"
  let mut rejected := false
  try
    addRef decl .ega "IV 5.8.6" "this comment is far longer than the permitted clause marker"
  catch _ => rejected := true
  unless rejected do throwError "invalid duplicate comment escaped validation"
  let env ← getEnv
  let enumeration := allRefs env
  unless enumeration == imported ++ distinct do
    throwError "imported/local enumeration order changed"
  for (name, work, ref) in [
      (decl, Work.ega, "IV 5.8.6"), (``Nat.add, Work.ega, "IV 5.8.6"),
      (decl, Work.sga, "4 IV 4.9.4"), (`missing, Work.ega, "IV 5.8.6"),
      (decl, Work.sga, "IV 5.8.6"), (decl, Work.ega, "IV 5.8.7")] do
    let oracle := enumeration.any fun r =>
      r.declName == name && r.work == work && r.ref == ref
    unless hasRef env name work ref == oracle do
      throwError "membership differs from enumeration oracle"
  logInfo "REGRESSION_OK: initial-doc normalized-duplicate original-record distinct-ref validation imported-local-membership ordering"

set_option maxRecDepth 100000 in
run_cmd liftCoreM do
  -- Synthetic extension state isolates lookup allocation/traversal, not parser or I/O cost.
  let rows := (List.range 20000).toArray.map fun n =>
    ({ declName := `benchmark, work := Work.ega, ref := toString n, comment := "" } : Ref)
  let localRef : Ref := { declName := `localHit, work := .ega, ref := "local", comment := "" }
  let env := PersistentEnvExtension.setState refExt (← getEnv) ([localRef], #[rows])
  for trial in [0:3] do
    for (name, key) in [(`localHit, "local"), (`benchmark, "0"),
        (`benchmark, "19999"), (`benchmark, "absent")] do
      let start ← IO.monoNanosNow
      let mut oldHits : Nat := 0
      for _ in [0:20] do
        if (allRefs env).any (fun r =>
            r.declName == name && r.work == .ega && r.ref == key) then
          oldHits := oldHits + 1
      let middle ← IO.monoNanosNow
      let mut newHits : Nat := 0
      for _ in [0:20] do
        if hasRef env name .ega key then newHits := newHits + 1
      let finish ← IO.monoNanosNow
      let expected := if key == "absent" then 0 else 20
      unless oldHits == expected && newHits == expected do
        throwError "benchmark result control failed"
      logInfo m!"LOOKUP_BENCH trial={trial} key={key} rows=20000 repetitions=20 old_ns={middle-start} new_ns={finish-middle} hits={newHits}"
end ReferenceRegression
'''


class ReferenceRegistrationTest(unittest.TestCase):
    def test_native_registration(self):
        pin = (ROOT / "lean-toolchain").read_text().strip()
        elan_home = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
        compiler = elan_home / "toolchains" / pin.replace("/", "--").replace(":", "---") / "bin/lean"
        self.assertTrue(compiler.is_file(), f"Pinned compiler unavailable: {compiler}")
        with tempfile.TemporaryDirectory(prefix="stacks-reference-test-") as directory:
            temporary = Path(directory)
            module = temporary / "ReferenceUnderTest.lean"
            source_bytes = SOURCE.read_bytes()
            module.write_bytes(source_bytes)
            env = dict(os.environ)
            env["LEAN_PATH"] = str(temporary)
            build = subprocess.run(
                [str(compiler), "-o", "ReferenceUnderTest.olean", module.name],
                cwd=temporary, env=env, capture_output=True, text=True, timeout=LEAN_TIMEOUT_S,
            )
            self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
            fixture = temporary / "ImportedReferences.lean"
            fixture.write_text(IMPORTED)
            imported_build = subprocess.run(
                [str(compiler), "-o", "ImportedReferences.olean", fixture.name],
                cwd=temporary, env=env, capture_output=True, text=True, timeout=LEAN_TIMEOUT_S,
            )
            self.assertEqual(imported_build.returncode, 0, imported_build.stdout + imported_build.stderr)
            result = subprocess.run(
                [str(compiler), "--stdin"], input=PROBE,
                cwd=temporary, env=env, capture_output=True, text=True, timeout=LEAN_TIMEOUT_S,
            )
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, output)
            self.assertIn("already carries this reference; skipping duplicate.", output)
            self.assertIn("REGRESSION_OK:", output)
            self.assertEqual(output.count("LOOKUP_BENCH"), 12)
            self.assertEqual(SOURCE.read_bytes(), source_bytes, "Source changed during the check")
            artifact_bytes = sum(p.stat().st_size for p in temporary.rglob("*") if p.is_file())
            print(
                f"source_sha256={hashlib.sha256(source_bytes).hexdigest()} "
                f"compile_rc={build.returncode} probe_rc={result.returncode} "
                f"temporary_bytes={artifact_bytes}\n{output}", end="",
            )


if __name__ == "__main__":
    unittest.main()
