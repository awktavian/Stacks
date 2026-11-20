"""Pure-Python regression for root-list coverage of the library's own modules.

Run: python3 -m unittest discover -s tests -p "test_root_module_coverage.py" -v
No Lake build, no compiler, no dependency download: one `git ls-files`
listing and three root files.

Why this exists: `lake build` and the estate proof-report producer see a
module only if the import closure from the root files reaches it. The two
tier roots `StacksCore.lean` and `StacksFrontier.lean` re-export every
tracked module of their tier directly, and `Stacks.lean` imports both roots;
that flat coverage is the contract this test pins. A module that is tracked
but not re-exported by its tier root is invisible to every downstream
compiler adjudication -- it is never built, never axiom-checked, and its
proof status reads UNKNOWN forever. A root import that names no tracked file
breaks `lake build` outright. Both cases were unguarded before this test.
"""

import re
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

IMPORT = re.compile(
    r"^[ \t]*(?:(?:public|private)[ \t]+)?(?:meta[ \t]+)?import[ \t]+(\S+)",
    re.MULTILINE,
)

TIER_ROOTS = ("StacksCore.lean", "StacksFrontier.lean")
MAIN_ROOT = "Stacks.lean"


def tracked_lean_files():
    listing = subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "--", "*.lean"],
        capture_output=True, text=True, check=True,
    ).stdout.splitlines()
    return [f for f in listing if f]


def root_import_names(root_file):
    text = (ROOT / root_file).read_text(encoding="utf-8", errors="replace")
    return IMPORT.findall(text)


class RootCoverageTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.files = tracked_lean_files()
        cls.modules = {f[:-5].replace("/", "."): f for f in cls.files}

    def test_main_root_reexports_both_tiers(self):
        """`import Stacks` must pull in both tier roots; otherwise the
        consumer-facing entry module hides a whole tier."""
        names = set(root_import_names(MAIN_ROOT))
        for tier in ("StacksCore", "StacksFrontier"):
            self.assertIn(tier, names, f"{MAIN_ROOT} does not import the {tier} root")

    def test_own_module_root_imports_resolve(self):
        """Every own-module import in a tier root names a tracked file;
        a dangling name fails `lake build` of that root."""
        for root_file in (MAIN_ROOT,) + TIER_ROOTS:
            for name in root_import_names(root_file):
                if not (name == "StacksCore" or name == "StacksFrontier"
                        or name.startswith("StacksCore.")
                        or name.startswith("StacksFrontier.")):
                    continue  # external package (Mathlib, batteries, ...)
                self.assertIn(
                    name, self.modules,
                    f"{root_file} imports {name}, which has no tracked .lean file",
                )

    def test_no_duplicate_reexports(self):
        """Each tier root lists each of its modules exactly once."""
        for root_file in TIER_ROOTS:
            names = root_import_names(root_file)
            seen = set()
            for name in names:
                self.assertNotIn(name, seen, f"{root_file} re-exports {name} twice")
                seen.add(name)

    def test_every_tracked_tier_module_is_reexported(self):
        """Every tracked module under a tier directory is re-exported by
        that tier's root; an unlisted module is never compiled."""
        listed = {root_file: set(root_import_names(root_file)) for root_file in TIER_ROOTS}
        for module, path in sorted(self.modules.items()):
            for tier in ("StacksCore", "StacksFrontier"):
                if not path.startswith(tier + "/"):
                    continue
                self.assertIn(
                    module, listed[tier + ".lean"],
                    f"{path} is tracked but not re-exported by {tier}.lean "
                    f"-- invisible to lake build and every proof-report producer",
                )


if __name__ == "__main__":
    unittest.main()
