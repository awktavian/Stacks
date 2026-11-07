module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change and inverse image for the small étale site

A morphism of schemes `f : X ⟶ Y` does not usually induce a functor on small étale sites in the
naive direction: an étale `X`-scheme is not an étale `Y`-scheme. What it does induce is base
change, `smallEtaleBaseChange f : Y.Etale ⥤ X.Etale`, sending an étale `Y`-scheme `W` to
`W ×_Y X`; this is the underlying site functor of the geometric morphism
`f_small : X_étale ⟶ Y_étale`, and it runs opposite to the morphism of topoi. The inverse-image
functor `smallEtaleInverseImage f` on sheaves of types is then the left Kan extension along the
opposite of base change, followed by sheafification — the standard presentation of `f^{-1}` as a
left adjoint built from a site functor.

Base change preserves the final object: `W = Y` pulls back to `Y ×_Y X ≅ X`. This is recorded
here as `isTerminalSmallEtaleBaseChangeObj`, because it is what makes the comparison map on
global sections canonical: the morphism in `X.Etale` from the final object to the base change of
the final object of `Y.Etale` exists and is unique, so there is no choice to be made.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleBaseChange` — base change between small étale sites, the
  functor `V/Y ↦ X ×_Y V/X` of Tag 04I1.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeObjIso` — the base change of `V` is `X ×_Y V`.
* `Stacks.EtaleCohomology.smallEtaleInverseImage` — the inverse-image functor on sheaves of
  types, as a left Kan extension followed by sheafification.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChangeObjIso_hom_fst` — the object formula: under that
  isomorphism the structure morphism of the base change of `V` is the first projection
  `X ×_Y V ⟶ X`.
* `Stacks.EtaleCohomology.isTerminalOfIsIsoHom` — an étale scheme over `X` whose structure
  morphism is an isomorphism is a final object of the small étale site.
* `Stacks.EtaleCohomology.isTerminalSmallEtaleBaseChangeObj` — base change preserves the final
  object of the small étale site.

## References

* [Stacks Project, Tag 0A0C](https://stacks.math.columbia.edu/tag/0A0C)
* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB)
* [Stacks Project, Tag 04I1](https://stacks.math.columbia.edu/tag/04I1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology

/-- Base change along `f : X ⟶ Y`, as a functor from the small étale site of `Y` to that of
`X`: an étale scheme `W` over `Y` is sent to the fibre product `W ×_Y X`, which is étale over
`X` because étale morphisms are stable under base change. This is the functor
`u : Y_étale → X_étale, V/Y ↦ X ×_Y V/X` of Tag 04I1, with the fibre product written in the
other order (see `smallEtaleBaseChangeObjIso`). -/
@[stacks 04I1]
public def smallEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  letI : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ f

/-- The base change of an étale `Y`-scheme `V` along `f : X ⟶ Y` is `X ×_Y V`: its underlying
scheme is by definition the fibre product `V ×_Y X`, and this is the canonical isomorphism with
`X ×_Y V`. -/
public def smallEtaleBaseChangeObjIso {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    ((smallEtaleBaseChange f).obj V).left ≅ pullback f V.hom :=
  pullbackSymmetry V.hom f

/-- The object formula `V/Y ↦ X ×_Y V/X` for the base-change functor `u : Y_étale → X_étale`:
under `smallEtaleBaseChangeObjIso`, the structure morphism of the base change of `V` to `X` is
the first projection `X ×_Y V ⟶ X`. -/
@[stacks 04I1 "object formula"]
public theorem smallEtaleBaseChangeObjIso_hom_fst {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    (smallEtaleBaseChangeObjIso f V).hom ≫ pullback.fst f V.hom =
      ((smallEtaleBaseChange f).obj V).hom :=
  pullbackSymmetry_hom_comp_fst V.hom f

/-- The inverse-image functor on sheaves of types for the small étale sites: left Kan extension
along the opposite of base change, followed by sheafification. -/
public def smallEtaleInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Scheme.smallEtaleTopology Y) (Type (max (u + 1) v)) ⥤
      Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)) :=
  sheafToPresheaf (Scheme.smallEtaleTopology Y) (Type (max (u + 1) v)) ⋙
    (smallEtaleBaseChange f).op.lan ⋙
      presheafToSheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))

/-- An étale scheme over `X` whose structure morphism is an isomorphism is a final object of the
small étale site of `X`: a morphism into it over `X` is forced to be the structure morphism of
the source composed with the inverse. -/
public def isTerminalOfIsIsoHom {X : Scheme.{u}} (A : X.Etale) [IsIso A.hom] :
    IsTerminal A := by
  refine IsTerminal.ofUniqueHom
    (fun B ↦ MorphismProperty.Over.homMk (B.hom ≫ inv A.hom) (by simp) trivial) ?_
  intro B m
  apply MorphismProperty.Over.Hom.ext
  have hw : m.left ≫ A.hom = B.hom := MorphismProperty.Over.w m
  -- NEVER name `MorphismProperty.Over.homMk` in a simp set: doing so minted
  -- `CategoryTheory.MorphismProperty.Over.homMk.eq_1` -- an equation lemma in MATHLIB's namespace,
  -- declared by THIS module. Two modules each minting it are mutually unimportable under the
  -- module system with no textual diff to point at, and a counting axiom census passes it; only
  -- the census NAME LIST sees it.
  -- On the rc4 pin the open-ended `simp [← hw]` no longer terminates: it fails with
  -- "maximum recursion depth has been reached" (build log stacks-pin-rc4-build-1106.log:4452).
  -- The uniqueness step is the underlying-morphism equality `m.left = B.hom ≫ inv A.hom`, so the
  -- proof now names no simp set at all: `change` reduces the homMk projection to that statement,
  -- and a directed rewrite chain closes it -- substitute `hw`, reassociate, cancel the inverse,
  -- compose with the identity.
  change m.left = B.hom ≫ inv A.hom
  rw [← hw, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Base change along `i : Z ⟶ X` carries a final object of the small étale site of `X` to a
final object of the small étale site of `Z`: the final object is `X` itself over `X`, and its
base change is `X ×_X Z`, whose structure morphism to `Z` is an isomorphism. -/
public def isTerminalSmallEtaleBaseChangeObj {X Z : Scheme.{u}} (i : Z ⟶ X) {A : X.Etale}
    (hA : IsTerminal A) : IsTerminal ((smallEtaleBaseChange i).obj A) := by
  have hX : IsIso (Scheme.Etale.mk (𝟙 X)).hom := inferInstanceAs (IsIso (𝟙 X))
  have hZ : IsIso ((smallEtaleBaseChange i).obj (Scheme.Etale.mk (𝟙 X))).hom :=
    pullback_snd_iso_of_left_iso (𝟙 X) i
  exact IsTerminal.ofIso
    (isTerminalOfIsIsoHom ((smallEtaleBaseChange i).obj (Scheme.Etale.mk (𝟙 X))))
    ((smallEtaleBaseChange i).mapIso
      (hA.uniqueUpToIso (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 X))))).symm

end Stacks.EtaleCohomology
