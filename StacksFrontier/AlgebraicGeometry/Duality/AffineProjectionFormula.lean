module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace

/-!
# The projection formula for an affine morphism

Let `h : T ⟶ S` be a morphism of schemes, `G` a sheaf of `𝒪_T`-modules and `H` a sheaf of
`𝒪_S`-modules.  Adjunction produces a canonical comparison morphism

`h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)`,

namely the adjoint transpose of the composite of the pullback-tensor comparison of Stacks
01CD with the counit of `h^* ⊣ h_*` in the first tensor factor.  Stacks Tag 0FZE asserts that
this morphism is invertible when `h` is affine and `G` and `H` are quasi-coherent.

This file constructs that morphism, `projectionFormulaMap`, and proves everything about it
that does not use affineness: it is natural in both module arguments, and its composite with
the tensorized unit of the adjunction is again computed by adjunction.  Invertibility itself
is not proved in this file: it is proved in the repository as `isIso_projectionFormulaMap`
(`@[stacks 0FZE]`, `Duality/ProjectionFormulaLocal.lean`), whose import cone reaches this
file, so it cannot be cited here; see the implementation notes.

## Main definitions

* `CategoryTheory.adjunctionTensorMap`: the comparison morphism in
  the abstract setting of an adjunction `L ⊣ R` together with binary functors `A`, `B` on the
  two categories and a morphism `A ⋙ L ⟶ (L × L) ⋙ B`.  This is where all the formal content
  of the projection-formula map lives.
* `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap`: the projection-formula
  morphism `h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)` for a morphism of schemes.
* `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIso`: the projection-formula
  morphism packaged as an isomorphism, under the hypothesis that it is one.

## Main results

* `CategoryTheory.adjunctionTensorMap_natural` and
  `CategoryTheory.adjunctionTensorMap_unit`: naturality of the
  abstract comparison morphism in both arguments, and the identification of its composite
  with the tensorized unit; `adjunctionTensorMap_unit_comp` is the latter after a further
  morphism out of the tensor product on the source.
* `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_natural`,
  `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_natural_unit` and
  `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_natural_unit_eval`: the
  geometric instances of those two statements.

## Implementation notes

Tensor products of sheaves of modules use the native
`Stacks.SheafOfModules.Tensor.sheafTensor`, the sheafification of the objectwise tensor product.
Fixing the right factor `H` uses its `.flip.obj H` directly, while paired morphisms use
`Functor.uncurry.obj`. Pullback, pushforward and the adjunction between them are
`RingedSpaceModuleAdjunction.modulePullback`, `modulePushforward` and
`modulePullbackPushforwardAdjunction`.  The pullback-tensor comparison is
`Stacks.RingedSpace.comparisonNatTrans`, the canonical morphism of bifunctors
`h^*(A ⊗ B) ⟶ h^*A ⊗ h^*B` of Stacks 01CD; `Stacks.RingedSpace.comparison_unique` pins it
down, so no other candidate enters the definition of `projectionFormulaMap`.

### How Tag 0FZE is proved, and what this file contributes

Invertibility of `projectionFormulaMap` for an affine morphism and quasi-coherent modules is the
content of Stacks 0FZE; it is proved in `…Duality.ProjectionFormulaLocal` as
`…ProjectionFormula.isIso_projectionFormulaMap`, with no hypothesis on the base, and the list of
outstanding steps below is **withdrawn**.  The Stacks proof is "this follows
immediately on translating into algebra": over an affine open `V ⊆ S` with `h⁻¹V` affine the
two sides become `M ⊗_R N` and `M ⊗_A (A ⊗_R N)` for a ring map `R ⟶ A`, an `A`-module `M`
and an `R`-module `N`, and the comparison becomes the standard base-change isomorphism,
`TensorProduct.AlgebraTensorModule.cancelBaseChange` read backwards.  Each step of that
translation is missing:

* Invertibility of `Stacks.RingedSpace.comparisonNatTrans`, i.e. Stacks 01CD. **This is
  available: `IsIso (Stacks.RingedSpace.comparisonNatTrans f)` is a global `instance`
  (`Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparisonIso.lean:492`), so it is free to
  any consumer, and the free case of the induction has what it needs.**  Note that the
  declaration is *not* a tag site: the two `@[stacks 01CD]` attributes sit two declarations
  below it, on `Stacks.RingedSpace.comparisonBifunctorIso` (`:500`) and its canonicality clause
  (`:512`), which are the tag's two covering members.  A third declaration carries the same
  mathematics by the stalk formula (`StacksFrontier/AlgebraicGeometry/PullbackTensor/StalkFormula.lean:103`) — a parallel
  development, not a third member.
* Locality of the statement on `S`: compatibility of `modulePullback`, `modulePushforward` and
  the tensor bifunctor with restriction to an open of `S`, together with the resulting
  compatibility of `projectionFormulaMap`.  Of these only the pushforward half exists, as
  `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`.
* The comparison of the two functors `H ↦ h_*G ⊗ H` and `H ↦ h_*(G ⊗ h^*H)` with colimits,
  which is what reduces the claim to a presentation of `H` by free modules.  The left-hand
  functor preserves colimits for formal reasons; the right-hand one does so because `h_*`
  preserves cokernels of morphisms of quasi-coherent modules when `h` is affine.  **This part
  is proved**, as
    `Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_walkingParallelPair`
  (`Duality/AffinePushforwardQcohExact.lean:181`), with the dévissage built on it in
  `Duality/ProjectionFormulaAffineCokernel.lean` — in particular `:150` and `:175`.

  **Two remarks.** First, this exactness is *not* the
  first assertion of Stacks 01SB: that tag asserts the equivalence `QCoh(𝒪_X) ≃ QCoh(f_*𝒪_X)`
  and that an `f_*𝒪_X`-module is quasi-coherent over `𝒪_S` exactly when it is over `f_*𝒪_X`.
  Exactness on quasi-coherent modules is a *consequence* of that equivalence, not a clause of
  it — and routing 0FZE through the equivalence would be circular, since the equivalence is not
  cheaper than 0FZE.  Second, the statement must be about *quasi-coherent* modules: right
  exactness of `modulePushforward` on **all** sheaves of modules is **false** for a general
  affine morphism, with a counterexample recorded in the implementation notes of
  `Duality/ProjectionFormulaCokernel.lean`.
* The algebra at the end: that `~` carries tensor products of modules to tensor products of
  sheaves and base change to `modulePullback`, neither of which is available for the tensor
  product used here.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.SheafOfModules.Tensor (sheafTensor)

namespace Stacks.AlgebraicGeometry.ProjectionFormula

open RingedSpaceModuleAdjunction

/-! ### The abstract comparison morphism

All of the formal content of the projection-formula map is already present for an adjunction
`L ⊣ R` equipped with binary functors `A` on the source and `B` on the target and a morphism
of bifunctors `α : A ⋙ L ⟶ (L × L) ⋙ B`.  The geometric statements below are instances. -/

section Abstract

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- `adjunctionTensorMap_unit` after any further morphism out of the tensor product on the
source: the composite is still the adjoint transpose of `α` followed by that morphism. -/
lemma adjunctionTensorMap_unit_comp (F H : C) {K : D} (e : B.obj (L.obj F, L.obj H) ⟶ K) :
    A.map (adj.unit.app F ×ₘ 𝟙 H) ≫ adjunctionTensorMap adj A B α (L.obj F) H ≫ R.map e =
      adj.homEquiv _ _ (α.app (F, H) ≫ e) := by
  rw [← Category.assoc, adjunctionTensorMap_unit, Adjunction.homEquiv_naturality_right]

end Abstract

/-! ### The projection-formula map for a morphism of schemes -/

universe u

/-- The tensor bifunctor on sheaves of modules on a ringed space, applied to a pair of
morphisms, is the canonical induced morphism of tensor products of Tag 01CB. -/
lemma tensorSheaf_map (X : RingedSpace.{u, u})
    {F F' G G' : SheafOfModules.{u} (structureSheafRing X)} (f : F ⟶ F') (g : G ⟶ G') :
    ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩))).map (f ×ₘ g) =
      ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩)).map ((f, g) : (_, _) ⟶ (_, _))) :=
  rfl

/-- The canonical projection-formula morphism `h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)`: the
adjoint transpose of the pullback-tensor comparison of Stacks 01CD followed by the counit of
`h^* ⊣ h_*` in the first tensor factor. -/
def projectionFormulaMap {T S : Scheme.{u}} (h : T ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    ((sheafTensor.{u, u, u, u, u}
      ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩).obj
        ((modulePushforward h.toLRSHom.toShHom).obj G)).obj H ⟶
      (modulePushforward h.toLRSHom.toShHom).obj
        (((sheafTensor.{u, u, u, u, u}
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).obj G).obj
            ((modulePullback h.toLRSHom.toShHom).obj H)) :=
  (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).homEquiv _ _
    ((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
        ((modulePushforward h.toLRSHom.toShHom).obj G, H) ≫
      ((sheafTensor.{u, u, u, u, u}
        ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).flip.obj
          ((modulePullback h.toLRSHom.toShHom).obj H)).map
        ((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).counit.app G))

/-- `projectionFormulaMap` is the abstract comparison morphism of `adjunctionTensorMap` for
the adjunction `h^* ⊣ h_*` and the pullback-tensor comparison of Stacks 01CD. -/
lemma projectionFormulaMap_eq {T S : Scheme.{u}} (h : T ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    projectionFormulaMap h G H =
      adjunctionTensorMap (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom)
        ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u}
      ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)))
        ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u}
      ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)))
        (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom) G H := by
  unfold projectionFormulaMap adjunctionTensorMap
  apply congrArg ((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).homEquiv _ _)
  apply congrArg ((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
    ((modulePushforward h.toLRSHom.toShHom).obj G, H) ≫ ·)
  exact (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩
    ((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).counit.app G)
    (𝟙 ((modulePullback h.toLRSHom.toShHom).obj H))).symm

/-- The projection-formula morphism is natural in both module arguments. -/
@[reassoc]
lemma projectionFormulaMap_natural {T S : Scheme.{u}} (h : T ⟶ S)
    {G G' : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)}
    {H H' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)}
    (g : G ⟶ G') (k : H ⟶ H') :
    ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u}
      ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)).map
        (X := ((modulePushforward h.toLRSHom.toShHom).obj G, H))
        (Y := ((modulePushforward h.toLRSHom.toShHom).obj G', H'))
        ((modulePushforward h.toLRSHom.toShHom).map g, k)) ≫
      projectionFormulaMap h G' H' =
    projectionFormulaMap h G H ≫
      (modulePushforward h.toLRSHom.toShHom).map
        ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u}
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).map
            (X := (G, (modulePullback h.toLRSHom.toShHom).obj H))
            (Y := (G', (modulePullback h.toLRSHom.toShHom).obj H'))
            (g, (modulePullback h.toLRSHom.toShHom).map k)) := by
  rw [projectionFormulaMap_eq, projectionFormulaMap_eq]
  exact adjunctionTensorMap_natural _ _ _ _ g k

/-- Tensoring the unit of `h^* ⊣ h_*` into the first factor and then applying the
projection-formula morphism gives the adjoint transpose of the pullback-tensor comparison. -/
lemma projectionFormulaMap_natural_unit {T S : Scheme.{u}} (h : T ⟶ S)
    (F H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u}
      ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)).map
          ((((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).unit.app F), (𝟙 H)) : (_, _) ⟶
          (_, _))) ≫
      projectionFormulaMap h ((modulePullback h.toLRSHom.toShHom).obj F) H =
    (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).homEquiv _ _
      ((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app (F, H)) := by
  rw [← tensorSheaf_map S.toRingedSpace, projectionFormulaMap_eq]
  exact adjunctionTensorMap_unit _ _ _ _ F H

/-- After any morphism out of the tensor product on the source, the composite of the
tensorized unit with the projection-formula morphism is still computed by adjunction.  This
applies in particular to the evaluation morphism of an invertible module. -/
lemma projectionFormulaMap_natural_unit_eval {T S : Scheme.{u}} (h : T ⟶ S)
    (F H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    {K : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)}
    (e : (((sheafTensor.{u, u, u, u, u}
      ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).obj (((modulePullback
          h.toLRSHom.toShHom).obj F))).obj (((modulePullback h.toLRSHom.toShHom).obj H))) ⟶ K) :
    ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u}
      ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)).map
          ((((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).unit.app F), (𝟙 H)) : (_, _) ⟶
          (_, _))) ≫
      projectionFormulaMap h ((modulePullback h.toLRSHom.toShHom).obj F) H ≫
        (modulePushforward h.toLRSHom.toShHom).map e =
    (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).homEquiv _ _
      ((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app (F, H) ≫ e) := by
  rw [← tensorSheaf_map S.toRingedSpace, projectionFormulaMap_eq]
  exact adjunctionTensorMap_unit_comp
    (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom) _ _
    (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom) F H e

/-! ### The projection formula as an isomorphism

Stacks 0FZE says that `projectionFormulaMap h G H` is invertible when `h` is affine and `G`
and `H` are quasi-coherent.  That is proved in the repository, as `isIso_projectionFormulaMap`
(`@[stacks 0FZE]`, `Duality/ProjectionFormulaLocal.lean`).  That file lies downstream of this
one, so the proof cannot be cited here, and the declarations below keep invertibility as an
instance hypothesis: `ProjectionFormulaLocal` wires the theorem into them with
`haveI := isIso_projectionFormulaMap h G H hG hH` in `projectionFormulaIsoOfQuasicoherent`. -/

/-- The projection-formula morphism, packaged as an isomorphism
`h_*G ⊗_{𝒪_S} H ≅ h_*(G ⊗_{𝒪_T} h^*H)` under the hypothesis that it is invertible.  Stacks
0FZE — proved in the repository as `isIso_projectionFormulaMap` (`@[stacks 0FZE]`,
`Duality/ProjectionFormulaLocal.lean`) — supplies that hypothesis for an affine morphism and
quasi-coherent modules; `projectionFormulaIsoOfQuasicoherent` there is this `def` with it
discharged. -/
def projectionFormulaIso {T S : Scheme.{u}} (h : T ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    [IsIso (projectionFormulaMap h G H)] :
    ((sheafTensor.{u, u, u, u, u}
      ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩).obj
        ((modulePushforward h.toLRSHom.toShHom).obj G)).obj H ≅
      (modulePushforward h.toLRSHom.toShHom).obj
        (((sheafTensor.{u, u, u, u, u}
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).obj G).obj
            ((modulePullback h.toLRSHom.toShHom).obj H)) :=
  asIso (projectionFormulaMap h G H)

/-- The forward morphism of `projectionFormulaIso` is the canonical adjoint transpose, rather
than an unspecified isomorphism of objects. -/
@[simp]
lemma projectionFormulaIso_hom {T S : Scheme.{u}} (h : T ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    [IsIso (projectionFormulaMap h G H)] :
    (projectionFormulaIso h G H).hom = projectionFormulaMap h G H :=
  rfl

/-- Naturality of `projectionFormulaIso` in both module arguments. -/
@[reassoc]
lemma projectionFormulaIso_hom_natural {T S : Scheme.{u}} (h : T ⟶ S)
    {G G' : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)}
    {H H' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)}
    [IsIso (projectionFormulaMap h G H)] [IsIso (projectionFormulaMap h G' H')]
    (g : G ⟶ G') (k : H ⟶ H') :
    ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u}
      ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)).map
        (X := ((modulePushforward h.toLRSHom.toShHom).obj G, H))
        (Y := ((modulePushforward h.toLRSHom.toShHom).obj G', H'))
        ((modulePushforward h.toLRSHom.toShHom).map g, k)) ≫
      (projectionFormulaIso h G' H').hom =
    (projectionFormulaIso h G H).hom ≫
      (modulePushforward h.toLRSHom.toShHom).map
        ((Functor.uncurry.obj (sheafTensor.{u, u, u, u, u}
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).map
            (X := (G, (modulePullback h.toLRSHom.toShHom).obj H))
            (Y := (G', (modulePullback h.toLRSHom.toShHom).obj H'))
            (g, (modulePullback h.toLRSHom.toShHom).map k)) :=
  projectionFormulaMap_natural h g k

end Stacks.AlgebraicGeometry.ProjectionFormula
