module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# Left Kan extension along a flat functor is left exact

For a representably flat functor `F : A ⥤ D`, the left Kan extension along `F.op` of
set-valued presheaves preserves finite limits. Unlike Mathlib's
`CategoryTheory.lan_preservesFiniteLimits_of_flat`, the categories and the coefficients may live
in independent universes; instead the categories of costructured arrows are assumed small.

## Main definitions

* `CategoryTheory.lanEvaluationIsoColimit`: evaluation of a left Kan extension as a colimit
  over costructured arrows.

## Main results

* `CategoryTheory.lan_preservesFiniteLimits_of_representablyFlat`: left Kan extension along a
  representably flat functor preserves finite limits.
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory

/-- Evaluating a left Kan extension at an object is the colimit over the costructured arrows
above that object. -/
public noncomputable def lanEvaluationIsoColimit.{s₁, s₂, s₃, x₁, x₂, x₃}
    {A : Type x₁} [Category.{s₁} A] {D : Type x₂} [Category.{s₂} D]
    (E : Type x₃) [Category.{s₃} E] (F : A ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents
    (fun G => F.leftKanExtensionObjIsoColimit G X)
    (fun {G₁ G₂} φ => by
      apply (F.isPointwiseLeftKanExtensionLeftKanExtensionUnit G₁ X).hom_ext
      intro T
      simp [Functor.lan])

/-- Left Kan extension of set-valued presheaves along a representably flat functor preserves
finite limits. -/
public theorem lan_preservesFiniteLimits_of_representablyFlat.{s₁, s₂, w, x₁, x₂}
    {A : Type x₁} [Category.{s₁} A] {D : Type x₂} [Category.{s₂} D]
    (F : A ⥤ D) [RepresentablyFlat F]
    [∀ Y : Dᵒᵖ, Small.{w} (CostructuredArrow F.op Y)]
    [∀ Y : Dᵒᵖ, Small.{w + 1} (CostructuredArrow F.op Y)] :
    PreservesFiniteLimits (F.op.lan : (Aᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{w}
  intro I _ _
  apply preservesLimitsOfShape_of_evaluation _ I
  intro Y
  haveI : IsFiltered (CostructuredArrow F.op Y) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F Y.unop)
  exact preservesLimitsOfShape_of_natIso
    (lanEvaluationIsoColimit (Type w) F.op Y).symm

end CategoryTheory
