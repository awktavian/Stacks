module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
import StacksCore.Tactic.StacksAttribute

/-! # The Milnor triangle of a tower at an object which is its derived limit

Let `T : ℕᵒᵖ ⥤ D` be a tower in a pretriangulated category with a product of its terms, and let
`X` be an object equipped with maps `cₙ : X ⟶ Tₙ` compatible with the transition maps. If the
canonical comparison from `X` to *every* derived limit of `T` is an isomorphism, then `X` itself
sits in the Milnor triangle of the tower:

`X ⟶ ∏ Tₙ ⟶ ∏ Tₙ ⟶ X⟦1⟧`,

with first map `(cₙ)` and middle map `(tₙ) ↦ (tₙ - tₙ₊₁)`.

This is the step that turns a convergence criterion -- a statement of the form "the canonical map
`X ⟶ R lim Tₙ` is an isomorphism", which is how Tags 0D6M and 0D6P are stated -- into a
distinguished triangle based at `X`, which is the form the Milnor sequence of Tag 0D6K consumes.
Without it the two cannot be composed: a derived limit is only determined up to isomorphism, and
the convergence criterion is phrased for an arbitrary presentation of one.

## Main results

* `Stacks.InverseSystem.comp_map_of_comp_map_succ`: a family of maps into a tower which is
  compatible with the successive transition maps is compatible with every transition map, i.e. it
  is a cone.
* `Stacks.InverseSystem.exists_distTriang_milnor_of_isIso`: the Milnor triangle based at `X`.

## Implementation notes

The hypothesis is the convergence criterion in exactly the shape
`Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic` has it: for every
object, every presentation of it as a derived limit of the tower, and every comparison map whose
composites with the product projections are the given cone, that comparison is an isomorphism.

A derived limit of the tower is produced by
`CategoryTheory.Pretriangulated.exists_isDerivedLimit`, the comparison map out of `X` by exactness
of the triangle against `X`, and the triangle is then transported along that comparison.

## References

* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.InverseSystem

universe v u

section Cone

variable {D : Type u} [Category.{v} D]

/-- **A family of maps compatible with the successive transitions of a tower is a cone.** If
`cₙ : X ⟶ Tₙ` satisfies `cₙ₊₁ ≫ (Tₙ₊₁ ⟶ Tₙ) = cₙ` for every `n`, then it is compatible with every
transition map of the tower. -/
theorem comp_map_of_comp_map_succ {T : ℕᵒᵖ ⥤ D} {X : D} (c : ∀ n : ℕ, X ⟶ T.obj ⟨n⟩)
    (hc : ∀ n : ℕ, c (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op = c n)
    {j k : ℕᵒᵖ} (φ : j ⟶ k) : c j.unop ≫ T.map φ = c k.unop := by
  let α : (Functor.const ℕᵒᵖ).obj X ⟶ T :=
    NatTrans.ofOpSequence c (fun n ↦ by simpa using (hc n).symm)
  simpa [α] using (α.naturality φ).symm

end Cone

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **The Milnor triangle of a tower, based at an object which is its derived limit.** Let `cₙ`
be a cone from `X` over the tower `T`, and suppose that every comparison map from `X` to a derived
limit of `T` inducing that cone is an isomorphism. Then `X`, the map `(cₙ)` and the difference map
of the tower form a distinguished triangle. -/
theorem exists_distTriang_milnor_of_isIso (T : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ ↦ T.obj ⟨n⟩] {X : D} (c : ∀ n : ℕ, X ⟶ T.obj ⟨n⟩)
    (hc : ∀ n : ℕ, c (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op = c n)
    (hconv : ∀ (L : D) (f : X ⟶ L) (p : L ⟶ ∏ᶜ fun n : ℕ ↦ T.obj ⟨n⟩)
      (δ : (∏ᶜ fun n : ℕ ↦ T.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧),
      Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang D →
        (∀ n : ℕ, f ≫ p ≫ Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) n = c n) → IsIso f) :
    ∃ δ, Triangle.mk (Pi.lift c) (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang D := by
  obtain ⟨L, p, δ, hδ⟩ := exists_isDerivedLimit T
  set d : (∏ᶜ fun n : ℕ ↦ T.obj ⟨n⟩) ⟶ ∏ᶜ fun n : ℕ ↦ T.obj ⟨n⟩ :=
    Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op with hd_def
  have hw : (Pi.lift c) ≫ d = 0 := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, hd_def, Pi.lift_comp_π, Preadditive.comp_sub, Pi.lift_comp_π, ← Category.assoc,
      Pi.lift_comp_π, hc n, sub_self, zero_comp]
  obtain ⟨f, hf⟩ := (Triangle.mk p d δ).coyoneda_exact₂ hδ (Pi.lift c) hw
  have hf' : Pi.lift c = f ≫ p := hf
  have hiso : IsIso f := by
    refine hconv L f p δ hδ fun n ↦ ?_
    have h := congrArg (fun g : X ⟶ ∏ᶜ fun n : ℕ ↦ T.obj ⟨n⟩ ↦
      g ≫ Pi.π (fun n : ℕ ↦ T.obj ⟨n⟩) n) hf'
    simpa [Category.assoc] using h.symm
  have := hiso
  refine ⟨δ ≫ (shiftFunctor D (1 : ℤ)).map (inv f), ?_⟩
  have hd : Triangle.mk (f ≫ p) d (δ ≫ (shiftFunctor D (1 : ℤ)).map (inv f)) ∈
      distTriang D :=
    isomorphic_distinguished _ hδ _
      (Triangle.isoMk _ _ (asIso f) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp))
  rwa [← hf'] at hd

end Stacks.InverseSystem

end
