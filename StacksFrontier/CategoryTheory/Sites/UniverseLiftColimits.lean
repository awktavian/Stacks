module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The universe lift of abelian sheaves preserves colimits

Raising the universe of the sections of a sheaf of abelian groups is
`CategoryTheory.sheafCompose J AddCommGrpCat.uliftFunctor`.  This file shows that it preserves
colimits, and that the universe lift of abelian groups preserves sheafification
(`CategoryTheory.GrothendieckTopology.PreservesSheafification`).

## Main results

* `Stacks.Sheaves.UniverseLift.isLocallyInjective_uliftFunctor` and
  `Stacks.Sheaves.UniverseLift.isLocallySurjective_uliftFunctor`: the universe lift preserves
  local injectivity and local surjectivity of a morphism of abelian presheaves.
* `Stacks.Sheaves.UniverseLift.preservesSheafification_uliftFunctor`: the universe lift of
  abelian groups preserves sheafification.
* `Stacks.Sheaves.UniverseLift.sheafCompose_uliftFunctor_preservesColimits`: composing an
  abelian sheaf with the universe lift preserves colimits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace Stacks.Sheaves.UniverseLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The universe lift of abelian groups preserves local injectivity of a morphism of abelian
presheaves. -/
theorem isLocallyInjective_uliftFunctor {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J f] :
    Presheaf.IsLocallyInjective J (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{t, w}) where
  equalizerSieve_mem x y h := by
    have he : Presheaf.equalizerSieve (F := P ⋙ AddCommGrpCat.uliftFunctor.{t, w}) x y =
        Presheaf.equalizerSieve x.down y.down := by
      ext V i
      simp only [Presheaf.equalizerSieve_apply]
      exact ⟨fun h ↦ congrArg ULift.down h, fun h ↦ ULift.ext h⟩
    rw [he]
    exact Presheaf.equalizerSieve_mem J f x.down y.down (congrArg ULift.down h)

/-- The universe lift of abelian groups preserves local surjectivity of a morphism of abelian
presheaves. -/
theorem isLocallySurjective_uliftFunctor {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{t, w}) where
  imageSieve_mem {X} s := by
    have he : Presheaf.imageSieve (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{t, w}) s =
        Presheaf.imageSieve f s.down := by
      ext V i
      simp only [Presheaf.imageSieve_apply]
      exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.down, congrArg ULift.down hx⟩,
        fun ⟨x, hx⟩ ↦ ⟨ULift.up x, ULift.ext hx⟩⟩
    rw [he]
    exact Presheaf.imageSieve_mem J f (U := op X) s.down

/-- The universe lift of abelian groups preserves sheafification. -/
theorem preservesSheafification_uliftFunctor
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max t w}] :
    J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, w} where
  le P Q f hf := by
    obtain ⟨hinj, hsurj⟩ := (J.W_iff_isLocallyBijective f).1 hf
    have : Presheaf.IsLocallyInjective J f := hinj
    have : Presheaf.IsLocallySurjective J f := hsurj
    change J.W (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{t, w})
    rw [J.W_iff_isLocallyBijective]
    exact ⟨isLocallyInjective_uliftFunctor f, isLocallySurjective_uliftFunctor f⟩

section

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{max t w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t w}]

/-- Sheafification of abelian presheaves followed by the universe lift preserves the colimit of
a diagram. -/
private theorem sheafifyCompose_uliftFunctor_preservesColimit {K : Type w} [Category.{w} K]
    (P : K ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w})) :
    PreservesColimit P (presheafToSheaf J AddCommGrpCat.{w} ⋙
      sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}) := by
  have := preservesSheafification_uliftFunctor.{u, v, w, t} (J := J)
  exact (preservesColimit_iff_of_natIso P
    (sheafComposeNatIso J AddCommGrpCat.uliftFunctor.{t, w}
      (sheafificationAdjunction J AddCommGrpCat.{w})
      (sheafificationAdjunction J AddCommGrpCat.{max t w}))).mp inferInstance

/-- Composing an abelian sheaf with the universe lift preserves the colimit of a single
diagram. -/
private theorem sheafCompose_uliftFunctor_preservesColimit {K : Type w} [Category.{w} K]
    (F : K ⥤ Sheaf J AddCommGrpCat.{w}) :
    PreservesColimit F (sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}) := by
  let T := sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}
  let G := sheafToPresheaf J AddCommGrpCat.{w}
  let S := presheafToSheaf J AddCommGrpCat.{w}
  let P := F ⋙ G
  let cP := colimit.cocone P
  let hP := colimit.isColimit P
  have hS : IsColimit (S.mapCocone cP) := isColimitOfPreserves S hP
  let e : F ≅ P ⋙ S :=
    Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction J AddCommGrpCat.{w}).counit).symm
  let cF := (Cocone.precompose e.hom).obj (S.mapCocone cP)
  have hF : IsColimit cF := (IsColimit.precomposeHomEquiv e _).symm hS
  let e' := Functor.isoWhiskerRight e T
  let : PreservesColimit P (S ⋙ T) :=
    sheafifyCompose_uliftFunctor_preservesColimit.{u, v, w, t} P
  have hT' : IsColimit ((Cocone.precompose e'.hom).obj ((S ⋙ T).mapCocone cP)) :=
    (IsColimit.precomposeHomEquiv e' _).symm (isColimitOfPreserves (S ⋙ T) hP)
  have hMapF : IsColimit (T.mapCocone cF) :=
    IsColimit.ofIsoColimit hT' (Cocone.ext (Iso.refl _) (fun j ↦ by simp [cF, e']))
  exact preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    (IsColimit.ofIsoColimit hMapF (Functor.mapIso (Cocone.functoriality F T)
      (IsColimit.uniqueUpToIso hF (colimit.isColimit F))))

/-- Composing an abelian sheaf with the universe lift preserves colimits. -/
theorem sheafCompose_uliftFunctor_preservesColimits :
    PreservesColimitsOfSize.{w, w} (sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}) where
  preservesColimitsOfShape := ⟨fun {F} ↦ sheafCompose_uliftFunctor_preservesColimit.{u, v, w, t} F⟩

end

end Stacks.Sheaves.UniverseLift

end
