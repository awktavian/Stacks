module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Subobject.MonoOver
import StacksCore.Tactic.StacksAttribute

/-! ## `MonoOver.exists` along monomorphisms and composites.

## Relation to mathlib

The three declarations this file ported — `full_exists`,
`factorThruImage_comp_existsPullbackAdj_counit_app_hom_left` and `existsComp`, the `MonoOver`
half of mathlib#42757 (`feat(CategoryTheory/Subobject): extend exists and pullback API`, merged
2026-09-07, after our previous pinned revision of 2026-09-01) — have landed upstream in
`Mathlib.CategoryTheory.Subobject.MonoOver` with the same names and statements. The estate rc4
pin (`leanprover/lean4:v4.35.0-rc4`) has moved past that commit, so the local copies are deleted
as this port's header planned ("delete when the pin moves past it"): keeping them would now
collide as duplicate declarations against the upstream import below.

This module is retained only as a public re-export shim, so that
`import StacksCore.CategoryTheory.Subobject.MonoOver` keeps resolving those names; it declares
nothing of its own.
-/
