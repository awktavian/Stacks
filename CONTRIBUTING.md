# Contributing

Contributions are welcome from anyone interested in formalizing the Stacks Project: new formalizations, reviews of existing ones, and better proofs.

## Claim before you start

New formalizations and reviews are claimed before they start, so that efforts do not collide.

1. Find a task on the [task board](https://stacks.axiommath.ai/contributing), or a Stacks tag in the [library](https://stacks.axiommath.ai/library), and check the [open claims](https://github.com/AxiomMath/Stacks/issues?q=is%3Aissue+label%3Aclaim).
2. Open a [claim](https://github.com/AxiomMath/Stacks/issues/new?template=claim.yml) with a blueprint: the exact statement, the Lean statement you intend to prove, the declarations in this library or in Mathlib that you will use or extend, and a proof outline. The task board pre-fills this for you.
3. A maintainer reviews the blueprint in the issue. When it is approved, the issue is labelled `blueprint-approved` and assigned to you. That is your claim.
4. Formalize it and open a pull request that closes the issue.

Improvements to existing proofs and small fixes (typos, broken proofs, documentation) do not need a claim; open a pull request directly.

## The two tiers

* **StacksCore**: formalizations checked against the Stacks Project and brought to Mathlib standards of naming, generality and style.
* **StacksFrontier**: everything else, including AI-assisted formalizations. Moving code from StacksFrontier into StacksCore, after checking that its statements faithfully capture the source, is one of the most useful contributions.

Every pull request, to either tier, is reviewed by the maintainers: Kenny Lau, Brian Nugent, Ashvin A. Swaminathan and Yunzhou Xie.

## Conventions

* Attach `@[stacks TAG]` to the declaration that formalizes a tag, adding a comment if it covers only part, for example `@[stacks 00DS "part (1)"]`. Use `add_to_stacks TAG` for a Mathlib declaration.
* State the result as the Stacks Project states it, in its full generality. Do not weaken a statement to make it provable. If the statement is wrong or incomplete, note that in your claim.
* Place each file in the module matching its topic. Reuse existing definitions rather than introducing parallel ones.
* No `sorry`, `admit`, `native_decide`, or new `axiom`. Running `#print axioms DeclarationName` must list only `propext`, `Classical.choice`, and `Quot.sound`.
* Follow Mathlib's naming and style conventions.
