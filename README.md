[![](logo.svg)](https://axiommath.ai/)

# The Stacks Project in Lean

* [Website](https://stacks.axiommath.ai/)

A Lean 4 formalization of [the Stacks Project](https://stacks.math.columbia.edu/), the open-source reference work on algebraic geometry, built on [Mathlib](https://github.com/leanprover-community/mathlib4). The compiler version is pinned in [lean-toolchain](lean-toolchain).

Coverage includes every Stacks tag with formalizable content. A tag may be partially formalized: inspect the declaration's statement and the tag comment to see what part it covers. Declarations also carry references to Grothendieck's *Éléments de géométrie algébrique* (EGA) and *Séminaire de géométrie algébrique* (SGA).

**Start here:** [find a tag](#finding-a-tag) · [choose an import](#structure) · [check a result](#checking-a-result) · [contribute](#contributing)

Coverage, human review, and proof status are independent. The trust boundary for a declaration is Lean's kernel: its proof must use only the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`, and no `native_decide`. This is a verification requirement, not a claim about the mathematical statement; see [Checking a result](#checking-a-result).

## Structure

`import Stacks` brings in both tiers; `import StacksCore` restricts imports to the human-reviewed tier. For a focused dependency, import the individual module containing the declaration instead of either umbrella. The tiers describe review provenance, not different proof-checking standards.

* [StacksCore](StacksCore/): human-reviewed formalizations, checked against the Stacks Project and brought to Mathlib standards of naming, generality and style.
* [StacksFrontier](StacksFrontier/): formalizations written by AI agents. This is where coverage grows fastest, and where review is most needed before code moves into StacksCore.

## Finding a tag

A declaration carrying `@[stacks TAG]` formalizes all or part of that Stacks tag. A tag claimed by Mathlib carries `add_to_stacks TAG` instead. A single tag may appear on multiple declarations; when a declaration covers only part of the tag, the attribute's comment explains which part. Example: `@[stacks 00DS "part (1)"]` or `@[stacks 00DS "affine case"]`. After `import Stacks`, the command `#stacks_tags` lists all tagged declarations with their tags, and `#stacks_tags!` adds the statement text. The [website](https://stacks.axiommath.ai/) links each tag to its Lean code, dependencies, and the Stacks Project text.

## EGA and SGA references

Declarations proving content from Grothendieck's works carry `@[ega "IV 7.8.3"]` or `@[sga "4 IV 4.9.4"]` (or `add_to_ega` / `add_to_sga` for Mathlib declarations). A reference means the declaration proves exactly one of:

* the whole numbered item (no comment);
* a more general result (comment: `"more general"`);
* specific clauses of a multi-part item (comment: `"(ii)"` or `"(ii), (iii)"`);
* a special case (comment: `"affine case"` or similar).

Declarations only tangentially related to an item are not tagged with it. Theorem numbers use the original publication: Publ. Math. IHÉS for EGA, standard Springer Lecture Notes for SGA.

## Checking a result

Use the version in `lean-toolchain` and the dependencies in `lake-manifest.json`. Check the current source of the module you intend to consume, then use a small probe importing that module:

```lean
import StacksCore.Order.DirectedInverseSystem

set_option pp.fullNames true
#check DirectedSystem
```

Run a probe with `lake env lean path/to/Probe.lean` once its dependencies are built. `#check` confirms the imported declaration's type, not its proof dependencies. For a theorem, add `#print axioms Fully.Qualified.theoremName`, replacing the name with the exact theorem being reused, and retain the raw output together with the compiler exit status, source revision and any local modifications.

### Axioms

The axiom receipt is the output of `#print axioms DeclarationName` for each declaration you reuse. A proof is clean when its axiom set is exactly a subset of `{propext, Classical.choice, Quot.sound}`. An empty set is valid; sorries, sorryAx, custom axioms, and native-decision trust are not. A successful compile does not establish this by itself: Lean can compile `sorry` with a warning, and a precompiled file does not certify its source.

The receipt is specific: it covers the named declaration, not a tag, module, or tier. It does not establish that the statement formalizes the mathematical claim: you must verify the hypotheses, conclusion, the objects it operates on, and any partial-coverage note separately. Explicit hypotheses in a theorem statement are assumptions regardless of axiom status.

The EGA/SGA registration utilities have a bounded native regression test, requiring only the pinned compiler (no Mathlib download or full library build):

```sh
python3 -m unittest discover -s tests -v
```

This checks reference metadata and documentation behavior, not the mathematical library's proof certification.

## Building

```
lake exe cache get
lake build
```

`lake exe cache get` downloads Mathlib's compiled files. The library itself has about 63,000 modules, so a full build takes a long time and a lot of memory; a cache service for the compiled Stacks modules is planned, so that `lake build` will not have to compile them locally.

## Contributing

Contributions are welcome: formalizing the remaining examples, exercises and remarks, reviewing StacksFrontier code and moving it into StacksCore, formalizing directly for StacksCore, or improving existing proofs.

New formalizations and reviews are claimed before they start, so that efforts do not collide:

1. Find a task on the [task board](https://stacks.axiommath.ai/contributing) and check the [open claims](https://github.com/AxiomMath/Stacks/issues?q=is%3Aissue+label%3Aclaim).
2. Open a [claim](https://github.com/AxiomMath/Stacks/issues/new?template=claim.yml) with a blueprint: the exact statement, the Lean statement you intend to prove, the declarations in this library or in Mathlib that you will use or extend, and a proof outline. The task board pre-fills it for you.
3. A maintainer reviews the blueprint. When it is approved, the issue is labelled `blueprint-approved` and assigned to you; that is your claim.
4. Formalize it and open a pull request that closes the issue. The maintainers review every pull request, to either tier.

Improvements to existing proofs and small fixes (typos, broken proofs, documentation) need no claim; open a pull request directly. [CONTRIBUTING.md](CONTRIBUTING.md) has the conventions.

## License

[Apache 2.0](LICENSE). The Stacks Project itself is licensed under the GNU Free Documentation License.
