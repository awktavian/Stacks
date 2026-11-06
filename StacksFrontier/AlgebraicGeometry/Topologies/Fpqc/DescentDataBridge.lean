module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.CanonicalInvariantOpen
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphismAction
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentSizeBound

/-!
# The descent-data bridge for the middle paragraph of Stacks 0APL

The proof of Stacks 0APL reduces, in
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionMiddle`, to a bespoke hypothesis
`hAPK`: for the chart base change `V = U ×_{F, c} T'` of an algebraic space `F` along a section
`c` of `F` over `T'`, it asks for a scheme `W`, a morphism `w : W ⟶ T`, an isomorphism
`α : T' ×_T W ≅ V` over `T'`, and the invariance of `α ≫ q` for the two projections of the
self-fibre product of `T' ×_T W` over `W`. Stacks 0APK, which is what supplies that hypothesis,
is naturally stated at this repository's canonical notion of descent datum,
`AlgebraicGeometry.DescentDatum` (Stacks 023V, the one-member case of Stacks 023W) together
with `AlgebraicGeometry.DescentData.IsEffective` (Stacks 023Z part (3)). **This file is the
conversion between those two shapes, in both directions**, so that the final step of Stacks
0APL no longer depends on which of the two shapes a proof of Stacks 0APK delivers.

## Main results

* `AlgebraicGeometry.exists_gluingIso_of_pullbackIso`: **the dictionary between the two
  spellings of a gluing isomorphism.** An isomorphism `V ×_S X ≅ X ×_S V` of literal fibre
  products which respects the structure morphism to `X` on both sides is a candidate gluing
  isomorphism in the `Over S`-product shape in which a descent datum is stated, and its action
  on generalized points is the isomorphism itself. The cocycle condition is not among the
  conclusions and does not follow from the isomorphism alone.
* `AlgebraicGeometry.exists_transition_of_pullbackIso`: **the forward direction, as a statement
  about schemes.** An isomorphism `V ×_S X ≅ X ×_S V` of literal fibre products which respects
  the structure morphism to `X` on both sides and leaves a morphism `b : V ⟶ Y` invariant
  assembles into the gluing isomorphism of a descent datum, cocycle condition included, as soon
  as morphisms into `V` are determined by their composites with `V ⟶ X` and with `b`.
* `AlgebraicGeometry.DescentDatum.act_left_comp_of_transitionPullbackIso`: a morphism out of the
  scheme of a descent datum which is invariant for the gluing isomorphism read on the literal
  fibre products is invariant for the induced action on generalized points.
* `AlgebraicGeometry.DescentData.exists_iso_canonical_over`: **the projection to `W` is
  invariant for the action of the canonical descent datum of `W` on generalized points.** This
  is the only property of the canonical datum the backward direction needs. It is
  `AlgebraicGeometry.DescentData.canonical_transition_comp_canonicalProj` — the invariance read
  on the literal fibre products, proved in
  `StacksFrontier.AlgebraicGeometry.Descent.Scheme.CanonicalInvariantOpen` — transported to the
  generalized-point form by
  `AlgebraicGeometry.DescentDatum.act_left_comp_of_transitionPullbackIso`.
* `AlgebraicGeometry.DescentData.exists_descent_of_isEffective`: **the backward direction, for
  an arbitrary morphism of schemes.** If a descent datum relative to `g : X ⟶ S` is effective
  and a morphism `b` out of its scheme is invariant for its action, then there are `W₀`,
  `w₀ : W₀ ⟶ S` and an isomorphism `X ×_S W₀ ≅ V` over `X` for which `b` is invariant under the
  two projections of the self-fibre product of `X ×_S W₀` over `W₀`. This is exactly the shape
  the middle paragraph of Stacks 0APL consumes, and no such characterisation of effectivity
  existed before: `AlgebraicGeometry.DescentDatum.exists_openImmersionHom_isEffective_iff` is a
  different statement.
* `AlgebraicGeometry.BigFppfOver.hom_ext_of_isPullback`: **morphisms of schemes into the chart
  base change are determined by their two components.** The presheaf square makes
  `prod.lift p q : V ⟶ T' ⨯ U` a monomorphism of the site, and a monomorphism of the site is a
  monomorphism of schemes because the site has fibre products and the canonical functor to
  schemes preserves them.
* `AlgebraicGeometry.BigFppfOver.exists_gluingIso_of_isPullback`: **the geometric heart of the
  forward direction.** Both `V ×_T T'` and `T' ×_T V` represent the fibre product of the chart
  `u` with `T' ×_T T' ⟶ F`, the two maps to `F` agreeing by the compatibility of `c`; so they
  are isomorphic, compatibly with the projection to `T' ×_T T'` and with `q`.
* `AlgebraicGeometry.BigFppfOver.exists_gluing_of_isPullback`: the forward direction at the
  site: the chart base change carries a descent datum relative to `f`, for which `q` is
  invariant.
* `AlgebraicGeometry.BigFppfOver.exists_descent_scheme_of_isEffective_of_isPullback`: **the
  bridge.** The bespoke conclusion of `hAPK` follows from effectivity of descent data relative
  to `f` whose scheme is the chart base change.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffective_descentDatum`: **Stacks 0APL
  with Stacks 0APK as its only hypothesis, in canonical form.** The companion of
  `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffectiveFpqcDescent_scheme`, with the
  bespoke `hAPK` replaced by effectivity of descent data.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffective_affine_indQuasiAffine`:
  **Stacks 0APL from Stacks 0APK over an affine base**, the shape in which the reduction of
  `StacksFrontier.AlgebraicGeometry.Descent.DescentDatumResidue` delivers effectivity. Its
  hypothesis is stated for morphisms of schemes rather than for morphisms of the site, and
  places no condition on the datum beyond ind-quasi-affineness.
* `AlgebraicGeometry.exists_isAffine_descentDatum_isIndQuasiAffineHom`: the family that
  hypothesis quantifies over is inhabited, so the hypothesis is not vacuous.

## Implementation notes

**Why the generalized-point calculus.** The gluing isomorphism of
`AlgebraicGeometry.DescentData` lives in an `Over S` binary-product spelling and its cocycle
condition is a diagram on a left-associated triple product. Checking that diagram by hand is
heavy; `StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphismAction` already translates
it into the law `(v · x) · y = v · y` on generalized points, and in that form it follows from
two facts about the chart base change: the acting point of `X` is the new point's image in `X`,
and `q` is unchanged. So the whole cocycle condition reduces to
`AlgebraicGeometry.BigFppfOver.hom_ext_of_isPullback`.

**Why effectivity is taken as a hypothesis.** Stacks 0APK is proved in this repository, and this
file is the shape adapter through which its proof reaches the consumers of the bespoke
hypothesis `hAPK`. The tag is registered in
`StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcEffective` at
`AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isIndQuasiAffineHom_of_anyIndex`
(the family statement, over an arbitrary base) and at its affine-base special case
`AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isIndQuasiAffineHom`, and in
`StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteSchemeDescent` as the one-member
covering `AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom_of_quasiCompact` —
and this last is exactly the shape of every `hAPK` in this file: effectivity of a `DescentDatum`,
read as `AlgebraicGeometry.DescentData.IsEffective`. Nothing in this file proves effectivity of
any descent datum; effectivity remains a hypothesis of every statement here that uses it, and
what is proved is the equivalence of the two shapes in which that hypothesis can be met. This is
the reason no declaration here carries a Stacks tag: each either carries the hypothesis or is a
statement about shapes rather than about geometry. Stacks 0APL belongs on the unconditional
statement, and it now stands on one: `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc` of
`StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf`, whose proof reaches the
sheaf condition through the affine-base interface of this file.

**Why the affine-base shape is a third shape and not a special case.** The reduction of Stacks
0APK in `StacksFrontier.AlgebraicGeometry.Descent.DescentDatumResidue` needs `[IsAffine S]` and
`[IsAffine X]`, which is the case Stacks 02W3 reduces the tag to; so the hypothesis of
`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffective_indQuasiAffine`,
which quantifies over every surjective flat quasi-compact morphism of schemes, is not one that
reduction can meet. The affine-base shape below is the common interface: weak enough for the
reduction to produce and strong enough for this file's bridge to consume. One further detail:
the reduction takes its six conditions as instance binders while the hypothesis below
carries them as propositions, and no conversion is needed, because a local hypothesis whose
type is a class is found by instance search.

**What the backward direction uses about the canonical datum.** Only that the projection to `W`
is invariant, which is
`AlgebraicGeometry.DescentData.canonical_transition_comp_canonicalProj` of
`StacksFrontier.AlgebraicGeometry.Descent.Scheme.CanonicalInvariantOpen`; nothing about the
canonical datum is reproved here. The comparison isomorphism between the scheme of
`(canonicalFunctor g).obj W` and `(Over.pullback g).obj W` is
`AlgebraicGeometry.DescentData.canonicalOverIso`, the `objIso` field of
`AlgebraicGeometry.DescentData.pullbackFunctor` rather than a propositional identification of
the two objects, so no transport along an equality of objects appears anywhere.

## References

* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The action of a gluing map whose underlying morphism is `θ`, transported along
`CategoryTheory.Over.prodLeftIsoPullback`, is read off `θ` on the literal fibre products. -/
private theorem gluingAction_left_of_left_eq {T₀ X₀ : Scheme.{u}} (g : X₀ ⟶ T₀) (V : Over X₀)
    (φ : (Over.map g).obj V ⨯ Over.mk g ⟶ Over.mk g ⨯ (Over.map g).obj V)
    (θ : pullback (V.hom ≫ g) g ⟶ pullback g (V.hom ≫ g))
    (h : φ.left = (Over.prodLeftIsoPullback ((Over.map g).obj V) (Over.mk g)).hom ≫ θ ≫
      (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj V)).inv)
    {Z : Over T₀} (v : Z ⟶ (Over.map g).obj V) (x : Z ⟶ Over.mk g) :
    (gluingAction V φ v x).left = (prod.lift v x).left ≫
      (Over.prodLeftIsoPullback ((Over.map g).obj V) (Over.mk g)).hom ≫ θ ≫
        pullback.snd g (V.hom ≫ g) := by
  simp [gluingAction, h]

/-- **The gluing isomorphism of a descent datum, read off an isomorphism of fibre products.**
Let `g : X ⟶ S` be a morphism of schemes and let `pₛ : V ⟶ X` be a scheme over `X`. An
isomorphism `Θ : V ×_S X ≅ X ×_S V` of literal fibre products whose `X`-components are the
expected ones (`hΘ1` and `hΘ2`) is a candidate gluing isomorphism for `V` relative to `g`,
written in the shape `AlgebraicGeometry.DescentDatum.mk'` asks for, and its action on
generalized points is `Θ` itself: the point `v · x` is the image under `Θ` of the point
`(v, x)` of `V ×_S X`, read off by the projection to `V`.

The cocycle condition is *not* among the conclusions, and does not follow from `Θ` alone. What
this provides is the dictionary between the `Over S` binary products in which a gluing
isomorphism is stated and the literal fibre products, so that the cocycle condition may be
checked on the latter; the comparison in both directions is
`CategoryTheory.Over.prodLeftIsoPullback`. -/
theorem exists_gluingIso_of_pullbackIso {T₀ X₀ V₀ : Scheme.{u}} (g : X₀ ⟶ T₀) (pₛ : V₀ ⟶ X₀)
    (Θ : pullback (pₛ ≫ g) g ≅ pullback g (pₛ ≫ g))
    (hΘ1 : Θ.hom ≫ pullback.fst g (pₛ ≫ g) = pullback.fst (pₛ ≫ g) g ≫ pₛ)
    (hΘ2 : Θ.hom ≫ pullback.snd g (pₛ ≫ g) ≫ pₛ = pullback.snd (pₛ ≫ g) g) :
    ∃ φ : Over.mk (prod.map (structureMap g (Over.mk pₛ)) (𝟙 (Over.mk g))) ≅
        Over.mk (prod.map (𝟙 (Over.mk g)) (structureMap g (Over.mk pₛ))),
      φ.hom.left ≫ prod.fst = prod.fst ≫ structureMap g (Over.mk pₛ) ∧
      φ.hom.left ≫ prod.snd ≫ structureMap g (Over.mk pₛ) = prod.snd ∧
      ∀ {Z : Over T₀} (v : Z ⟶ (Over.map g).obj (Over.mk pₛ)) (x : Z ⟶ Over.mk g)
        (l : Z.left ⟶ pullback (pₛ ≫ g) g),
        l ≫ pullback.fst (pₛ ≫ g) g = v.left →
        l ≫ pullback.snd (pₛ ≫ g) g = x.left →
        (gluingAction (Over.mk pₛ) φ.hom.left v x).left =
          l ≫ Θ.hom ≫ pullback.snd g (pₛ ≫ g) := by
  have hA1 : (Over.prodLeftIsoPullback ((Over.map g).obj (Over.mk pₛ)) (Over.mk g)).hom ≫
      pullback.fst (pₛ ≫ g) g =
        (prod.fst : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_fst _ _
  have hA2 : (Over.prodLeftIsoPullback ((Over.map g).obj (Over.mk pₛ)) (Over.mk g)).hom ≫
      pullback.snd (pₛ ≫ g) g =
        (prod.snd : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_snd _ _
  have hB1 : (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj (Over.mk pₛ))).inv ≫
      (prod.fst : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left =
        pullback.fst g (pₛ ≫ g) :=
    Over.prodLeftIsoPullback_inv_fst _ _
  have hB2 : (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj (Over.mk pₛ))).inv ≫
      (prod.snd : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left =
        pullback.snd g (pₛ ≫ g) :=
    Over.prodLeftIsoPullback_inv_snd _ _
  have key1 : (Over.prodLeftIsoPullback ((Over.map g).obj (Over.mk pₛ)) (Over.mk g) ≪≫ Θ ≪≫
        (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj (Over.mk pₛ))).symm).hom ≫
        (prod.fst : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left =
      (prod.fst : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _).left ≫ pₛ := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hB1]
    rw [hΘ1, ← Category.assoc, hA1]
  have hB2p : (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj (Over.mk pₛ))).inv ≫
      (prod.snd : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left ≫ pₛ =
        pullback.snd g (pₛ ≫ g) ≫ pₛ := by rw [← Category.assoc, hB2]
  have key2 : (Over.prodLeftIsoPullback ((Over.map g).obj (Over.mk pₛ)) (Over.mk g) ≪≫ Θ ≪≫
        (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj (Over.mk pₛ))).symm).hom ≫
        (prod.snd : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ _).left ≫ pₛ =
      (prod.snd : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _).left := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hB2p]
    rw [hΘ2, hA2]
  set e : ((Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g).left ≅
      (Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ)).left :=
    Over.prodLeftIsoPullback ((Over.map g).obj (Over.mk pₛ)) (Over.mk g) ≪≫ Θ ≪≫
      (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj (Over.mk pₛ))).symm with he
  have hover : e.hom ≫ (Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ)).hom =
      ((Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g).hom := by
    rw [← Over.w (prod.fst : Over.mk g ⨯ (Over.map g).obj (Over.mk pₛ) ⟶ Over.mk g),
      ← Category.assoc, key1, Category.assoc]
    exact Over.w (prod.fst : (Over.map g).obj (Over.mk pₛ) ⨯ Over.mk g ⟶ _)
  have h1 : (Over.isoMk e hover).hom ≫ prod.fst = prod.fst ≫ structureMap g (Over.mk pₛ) := by
    refine Over.OverMorphism.ext ?_
    simpa using key1
  have h2 : (Over.isoMk e hover).hom ≫ prod.snd ≫ structureMap g (Over.mk pₛ) = prod.snd := by
    refine Over.OverMorphism.ext ?_
    simpa using key2
  have hw : (Over.isoMk e hover).hom ≫
      prod.map (𝟙 (Over.mk g)) (structureMap g (Over.mk pₛ)) =
      prod.map (structureMap g (Over.mk pₛ)) (𝟙 (Over.mk g)) := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.map_fst, Category.comp_id, prod.map_fst]
      exact h1
    · rw [Category.assoc, prod.map_snd, prod.map_snd, Category.comp_id]
      exact h2
  refine ⟨Over.isoMk (Over.isoMk e hover) hw, h1, h2, ?_⟩
  intro Z v x l hl1 hl2
  simp only [Over.isoMk_hom_left]
  have hl : (prod.lift v x).left ≫
      (Over.prodLeftIsoPullback ((Over.map g).obj (Over.mk pₛ)) (Over.mk g)).hom = l := by
    refine (IsPullback.of_hasPullback (pₛ ≫ g) g).hom_ext ?_ ?_
    · rw [Category.assoc, hA1, ← Over.comp_left, prod.lift_fst, hl1]
    · rw [Category.assoc, hA2, ← Over.comp_left, prod.lift_snd, hl2]
  rw [gluingAction_left_of_left_eq g (Over.mk pₛ) _ Θ.hom (by simp [he]) v x, ← Category.assoc, hl]
  rfl

/-- **The forward direction of the descent-data bridge, for schemes.** Let `g : X ⟶ S` be a
morphism of schemes, `pₛ : V ⟶ X` a scheme over `X` and `b : V ⟶ Y` a morphism. An isomorphism
`Θ : V ×_S X ≅ X ×_S V` of literal fibre products whose `X`-components are the expected ones
(`hΘ1` and `hΘ2`) and which leaves `b` invariant (`hΘ3`) is the gluing isomorphism of a descent
datum on `V` relative to `g`, for whose action `b` is invariant.

The isomorphism itself and its action are
`AlgebraicGeometry.exists_gluingIso_of_pullbackIso`, which needs neither `b` nor `hext`. The
cocycle condition is the only thing that needs an argument, and `hext` is what it needs:
two morphisms into `V` which agree after `pₛ` and after `b` are equal. Read on generalized
points the cocycle condition says `(v · x) · y = v · y`, and both sides have the same image
under `pₛ` — namely `y` — and the same image under `b` — namely that of `v`. -/
theorem exists_transition_of_pullbackIso {T₀ X₀ V₀ Y : Scheme.{u}} (g : X₀ ⟶ T₀) (pₛ : V₀ ⟶ X₀)
    (b : V₀ ⟶ Y) (Θ : pullback (pₛ ≫ g) g ≅ pullback g (pₛ ≫ g))
    (hΘ1 : Θ.hom ≫ pullback.fst g (pₛ ≫ g) = pullback.fst (pₛ ≫ g) g ≫ pₛ)
    (hΘ2 : Θ.hom ≫ pullback.snd g (pₛ ≫ g) ≫ pₛ = pullback.snd (pₛ ≫ g) g)
    (hΘ3 : Θ.hom ≫ pullback.snd g (pₛ ≫ g) ≫ b = pullback.fst (pₛ ≫ g) g ≫ b)
    (hext : ∀ {Z : Scheme.{u}} (a₁ a₂ : Z ⟶ V₀), a₁ ≫ b = a₂ ≫ b →
      a₁ ≫ pₛ = a₂ ≫ pₛ → a₁ = a₂) :
    ∃ φ : Over.mk (prod.map (structureMap g (Over.mk pₛ)) (𝟙 (Over.mk g))) ≅
        Over.mk (prod.map (𝟙 (Over.mk g)) (structureMap g (Over.mk pₛ))),
      (prod.map φ.hom.left (𝟙 (Over.mk g)) ≫ prodMapLastTwo φ.hom.left =
        prodMapFirstThird φ.hom.left) ∧
      ∀ {Z : Over T₀} (v : Z ⟶ (Over.map g).obj (Over.mk pₛ)) (x : Z ⟶ Over.mk g),
        (gluingAction (Over.mk pₛ) φ.hom.left v x).left ≫ b = v.left ≫ b := by
  obtain ⟨φ, h1, h2, hactl⟩ := exists_gluingIso_of_pullbackIso g pₛ Θ hΘ1 hΘ2
  have hinv : ∀ {Z : Over T₀} (v : Z ⟶ (Over.map g).obj (Over.mk pₛ)) (x : Z ⟶ Over.mk g),
      (gluingAction (Over.mk pₛ) φ.hom.left v x).left ≫ b = v.left ≫ b := by
    intro Z v x
    have hcond : v.left ≫ pₛ ≫ g = x.left ≫ g := by
      rw [← Category.assoc]
      exact (Over.w v).trans (Over.w x).symm
    rw [hactl v x (pullback.lift v.left x.left hcond) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)]
    simp only [Category.assoc]
    rw [hΘ3, ← Category.assoc, pullback.lift_fst]
  have hs : ∀ {Z : Over T₀} (v : Z ⟶ (Over.map g).obj (Over.mk pₛ)) (x : Z ⟶ Over.mk g),
      (gluingAction (Over.mk pₛ) φ.hom.left v x).left ≫ pₛ = x.left := fun v x => by
    simpa using congrArg (fun t => Over.Hom.left t)
      (gluingAction_comp_structureMap (Over.mk pₛ) φ.hom.left h2 v x)
  refine ⟨φ, (cocycle_iff_gluingAction_act_act (Over.mk pₛ) φ.hom.left h1 h2).mpr ?_, hinv⟩
  intro Z v x y
  refine Over.OverMorphism.ext (hext _ _ ?_ ?_)
  · simp only [hinv]
  · simp only [hs]

namespace DescentDatum

/-- A morphism `β` out of the scheme of a descent datum which is invariant for the gluing
isomorphism read on the literal fibre products is invariant for the action on generalized
points: `(v · x) ≫ β = v ≫ β`. The two forms differ only by the transport
`CategoryTheory.Over.prodLeftIsoPullback` between the `Over S` products in which the gluing
isomorphism is stated and the fibre products. -/
theorem act_left_comp_of_transitionPullbackIso {S X : Scheme.{u}} {g : X ⟶ S}
    (D : DescentDatum g) {Y : Scheme.{u}} (β : D.over.left ⟶ Y)
    (hβ : D.transitionPullbackIso.hom ≫ pullback.snd g (D.over.hom ≫ g) ≫ β =
      pullback.fst (D.over.hom ≫ g) g ≫ β)
    {Z : Over S} (v : Z ⟶ (Over.map g).obj D.over) (x : Z ⟶ Over.mk g) :
    (D.act v x).left ≫ β = v.left ≫ β := by
  have hΦ : D.transition.hom.left.left =
      (Over.prodLeftIsoPullback ((Over.map g).obj D.over) (Over.mk g)).hom ≫
        D.transitionPullbackIso.hom ≫
        (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj D.over)).inv := by
    have h : D.transitionPullbackIso.hom =
        (Over.prodLeftIsoPullback ((Over.map g).obj D.over) (Over.mk g)).inv ≫
          D.transition.hom.left.left ≫
          (Over.prodLeftIsoPullback (Over.mk g) ((Over.map g).obj D.over)).hom := rfl
    rw [h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [DescentDatum.act, gluingAction_left_of_left_eq g D.over _ _ hΦ v x]
  simp only [Category.assoc, hβ]
  erw [Over.prodLeftIsoPullback_hom_fst_assoc]
  rw [← Category.assoc, ← Over.comp_left, prod.lift_fst]

end DescentDatum

namespace DescentData

variable {S X : Scheme.{u}} (g : X ⟶ S) (W : Over S)

/-- The scheme of the canonical descent datum of `W` relative to `g`, identified with the base
change `W ×_S X` of `W`, together with the invariance of the projection to `W` for the action
of the canonical datum on generalized points.

The identification is `AlgebraicGeometry.DescentData.canonicalOverIso` and the composite
`ι.hom.left ≫ pullback.fst W.hom g` is, definitionally,
`AlgebraicGeometry.DescentData.canonicalProj`; the invariance is therefore exactly
`AlgebraicGeometry.DescentData.canonical_transition_comp_canonicalProj` read through
`AlgebraicGeometry.DescentDatum.act_left_comp_of_transitionPullbackIso`. -/
theorem exists_iso_canonical_over :
    ∃ ι : DescentDatum.over ((canonicalFunctor g).obj W) ≅ (Over.pullback g).obj W,
      ∀ {Z : Over S}
        (v : Z ⟶ (Over.map g).obj (DescentDatum.over ((canonicalFunctor g).obj W)))
        (x : Z ⟶ Over.mk g),
        (DescentDatum.act ((canonicalFunctor g).obj W) v x).left ≫ ι.hom.left ≫
            pullback.fst W.hom g =
          v.left ≫ ι.hom.left ≫ pullback.fst W.hom g :=
  ⟨canonicalOverIso g W,
    fun v x => DescentDatum.act_left_comp_of_transitionPullbackIso _ _
      (canonical_transition_comp_canonicalProj g W) v x⟩

/-- **The backward direction of the descent-data bridge.** Let `D` be a descent datum relative
to `g : X ⟶ S` and let `b` be a morphism out of its scheme which is invariant for its action on
generalized points. If `D` is effective then there are a scheme `W₀`, a morphism `w₀ : W₀ ⟶ S`
and an isomorphism `α₀ : X ×_S W₀ ≅ V` over `X` for which `b` is invariant under the two
projections of the self-fibre product of `X ×_S W₀` over `W₀`.

This is the shape in which the middle paragraph of Stacks 0APL consumes Stacks 0APK. Effectivity
is `AlgebraicGeometry.DescentData.IsEffective`, membership in the essential image of the
canonical-datum functor; the descended scheme is the one it supplies, `α₀` is its comparison
isomorphism composed with the symmetry of the fibre product, and the invariance of `b` comes
from the equivariance of that comparison together with
`AlgebraicGeometry.DescentData.exists_iso_canonical_over`. -/
theorem exists_descent_of_isEffective {S X : Scheme.{u}} {g : X ⟶ S} (D : DescentDatum g)
    {Y : Scheme.{u}} (b : D.over.left ⟶ Y)
    (hb : ∀ {Z : Over S} (v : Z ⟶ (Over.map g).obj D.over) (x : Z ⟶ Over.mk g),
      (D.act v x).left ≫ b = v.left ≫ b)
    (hEff : DescentData.IsEffective D) :
    ∃ (W₀ : Scheme.{u}) (w₀ : W₀ ⟶ S) (α₀ : pullback g w₀ ≅ D.over.left),
      α₀.hom ≫ D.over.hom = pullback.fst g w₀ ∧
      pullback.fst (pullback.snd g w₀) (pullback.snd g w₀) ≫ α₀.hom ≫ b =
        pullback.snd (pullback.snd g w₀) (pullback.snd g w₀) ≫ α₀.hom ≫ b := by
  obtain ⟨W, ⟨ε⟩⟩ := hEff
  obtain ⟨ι, hπ⟩ := exists_iso_canonical_over g W
  have hιw : ι.inv.left ≫ (DescentDatum.over ((canonicalFunctor g).obj W)).hom =
      pullback.snd W.hom g := Over.w ι.inv
  have hιw' : ι.hom.left ≫ pullback.snd W.hom g =
      (DescentDatum.over ((canonicalFunctor g).obj W)).hom := Over.w ι.hom
  have hsym1 : (pullbackSymmetry g W.hom).hom ≫ pullback.snd W.hom g = pullback.fst g W.hom :=
    pullbackSymmetry_hom_comp_snd g W.hom
  have hsym2 : (pullbackSymmetry g W.hom).hom ≫ pullback.fst W.hom g = pullback.snd g W.hom :=
    pullbackSymmetry_hom_comp_fst g W.hom
  have hεw : ((DescentDatum.forget g).map ε.hom).left ≫ D.over.hom =
      (DescentDatum.over ((canonicalFunctor g).obj W)).hom := Over.w _
  have hequiv : ∀ {Z : Over S}
      (v : Z ⟶ (Over.map g).obj (DescentDatum.over ((canonicalFunctor g).obj W)))
      (x : Z ⟶ Over.mk g),
      DescentDatum.act ((canonicalFunctor g).obj W) v x ≫
          (Over.map g).map ((DescentDatum.forget g).map ε.hom) =
        D.act (v ≫ (Over.map g).map ((DescentDatum.forget g).map ε.hom)) x :=
    (DescentDatum.hom_comm_iff ((canonicalFunctor g).obj W) D
      ((DescentDatum.forget g).map ε.hom)).mp (ε.hom.comm () ())
  have hpt : ∀ (Z : Over S) (k : Z.left ⟶ pullback g W.hom),
      k ≫ pullback.fst g W.hom ≫ g = Z.hom →
      ∃ (v : Z ⟶ (Over.map g).obj (DescentDatum.over ((canonicalFunctor g).obj W)))
        (x : Z ⟶ Over.mk g),
        v.left = k ≫ (pullbackSymmetry g W.hom).hom ≫ ι.inv.left ∧
        x.left = k ≫ pullback.fst g W.hom := by
    intro Z k hk
    refine ⟨Over.homMk (k ≫ (pullbackSymmetry g W.hom).hom ≫ ι.inv.left) ?_,
      Over.homMk (k ≫ pullback.fst g W.hom) ?_, rfl, rfl⟩
    · show (k ≫ (pullbackSymmetry g W.hom).hom ≫ ι.inv.left) ≫
        (DescentDatum.over ((canonicalFunctor g).obj W)).hom ≫ g = Z.hom
      rw [Category.assoc, Category.assoc, ← Category.assoc ι.inv.left, hιw,
        ← Category.assoc (pullbackSymmetry g W.hom).hom, hsym1]
      exact hk
    · rw [Category.assoc]
      exact hk
  refine ⟨W.left, W.hom, pullbackSymmetry g W.hom ≪≫ ((Over.forget X).mapIso ι).symm ≪≫
    (Over.forget X).mapIso ((DescentDatum.forget g).mapIso ε), ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Over.forget_map, Category.assoc]
    rw [hεw, hιw, hsym1]
  · have hcond : pullback.fst g W.hom ≫ g = pullback.snd g W.hom ≫ W.hom :=
      pullback.condition
    have hκ : pullback.fst (pullback.snd g W.hom) (pullback.snd g W.hom) ≫
        pullback.snd g W.hom =
        pullback.snd (pullback.snd g W.hom) (pullback.snd g W.hom) ≫ pullback.snd g W.hom :=
      pullback.condition
    have hcommon : pullback.snd (pullback.snd g W.hom) (pullback.snd g W.hom) ≫
        pullback.fst g W.hom ≫ g =
        (Over.mk (pullback.fst (pullback.snd g W.hom) (pullback.snd g W.hom) ≫
          pullback.fst g W.hom ≫ g)).hom := by
      show _ = pullback.fst (pullback.snd g W.hom) (pullback.snd g W.hom) ≫
        pullback.fst g W.hom ≫ g
      rw [hcond, ← Category.assoc, ← Category.assoc, hκ]
    obtain ⟨v₁, x₁, hv₁, hx₁⟩ := hpt (Over.mk (pullback.fst (pullback.snd g W.hom)
        (pullback.snd g W.hom) ≫ pullback.fst g W.hom ≫ g))
      (pullback.fst (pullback.snd g W.hom) (pullback.snd g W.hom)) rfl
    obtain ⟨v₂, x₂, hv₂, hx₂⟩ := hpt (Over.mk (pullback.fst (pullback.snd g W.hom)
        (pullback.snd g W.hom) ≫ pullback.fst g W.hom ≫ g))
      (pullback.snd (pullback.snd g W.hom) (pullback.snd g W.hom)) hcommon
    have hinvhom : ι.inv.left ≫ ι.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, ι.inv_hom_id]; rfl
    have hcancelf : ι.inv.left ≫ ι.hom.left ≫ pullback.fst W.hom g = pullback.fst W.hom g := by
      rw [← Category.assoc, hinvhom, Category.id_comp]
    have hact2 : (DescentDatum.act ((canonicalFunctor g).obj W) v₁ x₂).left ≫
        (DescentDatum.over ((canonicalFunctor g).obj W)).hom = x₂.left := by
      have h := congrArg (fun t => Over.Hom.left t)
        (DescentDatum.act_comp_structureMap ((canonicalFunctor g).obj W) v₁ x₂)
      simp only [Over.comp_left, Over.homMk_left] at h
      exact h
    have hCact : DescentDatum.act ((canonicalFunctor g).obj W) v₁ x₂ = v₂ := by
      refine Over.OverMorphism.ext ?_
      rw [← cancel_mono ι.hom.left]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hπ, hv₁, hv₂]
        simp only [Category.assoc, hcancelf, hsym2]
        exact hκ
      · rw [Category.assoc, Category.assoc, hιw', hact2, hv₂]
        simp only [Category.assoc, hιw, hsym1]
        exact hx₂
    have h1 : (DescentDatum.act ((canonicalFunctor g).obj W) v₁ x₂).left ≫
        ((DescentDatum.forget g).map ε.hom).left =
        (D.act (v₁ ≫ (Over.map g).map ((DescentDatum.forget g).map ε.hom)) x₂).left := by
      rw [← hequiv v₁ x₂, Over.comp_left, Over.map_map_left]
    have h3 := hb (v₁ ≫ (Over.map g).map ((DescentDatum.forget g).map ε.hom)) x₂
    simp only [Over.comp_left, Over.map_map_left, Category.assoc] at h3
    have h2 : (DescentDatum.act ((canonicalFunctor g).obj W) v₁ x₂).left ≫
        ((DescentDatum.forget g).map ε.hom).left ≫ b =
        v₁.left ≫ ((DescentDatum.forget g).map ε.hom).left ≫ b :=
      (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ b) h1).trans h3)
    have hfinal : v₁.left ≫ ((DescentDatum.forget g).map ε.hom).left ≫ b =
        v₂.left ≫ ((DescentDatum.forget g).map ε.hom).left ≫ b := by
      refine h2.symm.trans ?_
      rw [hCact]
    simp only [hv₁, hv₂] at hfinal
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Over.forget_map, Category.assoc]
    simpa only [Category.assoc] using hfinal

end DescentData

namespace BigFppfOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The two components of the chart base change are jointly monic in the site.** If
`yoneda.obj V` is the fibre product of a chart `u : yoneda.obj U ⟶ F` and a section
`c : yoneda.obj T' ⟶ F`, then `prod.lift p q : V ⟶ T' ⨯ U` is a monomorphism of the big fppf
category over `S`. -/
theorem mono_prodLift_of_isPullback {U T' V : BigFppfOver B S hS} {u : yoneda.obj U ⟶ F}
    {c : yoneda.obj T' ⟶ F} {q : V ⟶ U} {p : V ⟶ T'}
    (sq : IsPullback (yoneda.map q) (yoneda.map p) u c) : Mono (prod.lift p q) := by
  refine ⟨fun {Z} k₁ k₂ h => ?_⟩
  have hp : k₁ ≫ p = k₂ ≫ p := by
    have := congrArg (fun t => t ≫ (prod.fst : T' ⨯ U ⟶ T')) h
    simpa [Category.assoc] using this
  have hq : k₁ ≫ q = k₂ ≫ q := by
    have := congrArg (fun t => t ≫ (prod.snd : T' ⨯ U ⟶ U)) h
    simpa [Category.assoc] using this
  refine yoneda.map_injective (sq.hom_ext ?_ ?_)
  · rw [← Functor.map_comp, ← Functor.map_comp, hq]
  · rw [← Functor.map_comp, ← Functor.map_comp, hp]

/-- **Morphisms of schemes into the chart base change are determined by their two
components.** Two morphisms of schemes into the scheme underlying `V` which agree after `q` and
after `p` are equal.

The site statement is `AlgebraicGeometry.BigFppfOver.mono_prodLift_of_isPullback`, and it
transfers to schemes because a monomorphism is a pullback square and the canonical functor to
schemes preserves fibre products; joint monicity of the two projections of the product in the
site likewise transfers, the product of the slice being a fibre product over `S`. -/
theorem hom_ext_of_isPullback {U T' V : BigFppfOver B S hS} {u : yoneda.obj U ⟶ F}
    {c : yoneda.obj T' ⟶ F} {q : V ⟶ U} {p : V ⟶ T'}
    (sq : IsPullback (yoneda.map q) (yoneda.map p) u c)
    {Z : Scheme.{u}} (a b : Z ⟶ (toScheme B S hS).obj V)
    (hq : a ≫ (toScheme B S hS).map q = b ≫ (toScheme B S hS).map q)
    (hp : a ≫ (toScheme B S hS).map p = b ≫ (toScheme B S hS).map p) : a = b := by
  have hjs : Mono ((toScheme B S hS).map (prod.lift p q)) := by
    have := mono_prodLift_of_isPullback sq
    have h2 := (IsKernelPair.id_of_mono (f := prod.lift p q)).map (toScheme B S hS)
    rw [CategoryTheory.Functor.map_id] at h2
    exact IsKernelPair.mono_of_isIso_fst h2
  have hprod : IsPullback ((toScheme B S hS).map (prod.fst : T' ⨯ U ⟶ T'))
      ((toScheme B S hS).map (prod.snd : T' ⨯ U ⟶ U))
      (B.inclusion.map T'.hom) (B.inclusion.map U.hom) :=
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd T' U)).map B.inclusion
  rw [← cancel_mono ((toScheme B S hS).map (prod.lift p q))]
  refine hprod.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, ← Functor.map_comp, prod.lift_fst, hp]
  · rw [Category.assoc, Category.assoc, ← Functor.map_comp, prod.lift_snd, hq]

/-- **The geometric heart of the forward direction.** Let `f : T' ⟶ T` be a morphism of the
big fppf category over `S`, let `u : yoneda.obj U ⟶ F` be a chart of a presheaf `F`, let `c` be
a section of `F` over `T'` whose two restrictions to `T' ×_T T'` agree, and let `V` represent
the fibre product of `u` and `c`. Then `V ×_{T'} (T' ×_T T')` and `(T' ×_T T') ×_{T'} V` are
isomorphic over `T' ×_T T'`, compatibly with `q`.

Both represent the fibre product of `u` with the composite `T' ×_T T' ⟶ T' ⟶ F`, the first via
the first projection and the second via the second projection, and those two composites agree
by `hcc`. Full faithfulness of the Yoneda embedding of the site turns the isomorphism of
presheaves into an isomorphism of the site. -/
theorem exists_gluingIso_of_isPullback {T T' U V : BigFppfOver B S hS} {f : T' ⟶ T}
    {u : yoneda.obj U ⟶ F} {c : yoneda.obj T' ⟶ F} {q : V ⟶ U} {p : V ⟶ T'}
    (sq : IsPullback (yoneda.map q) (yoneda.map p) u c)
    (hcc : yoneda.map (pullback.fst f f) ≫ c = yoneda.map (pullback.snd f f) ≫ c) :
    ∃ θ : pullback p (pullback.fst f f) ≅ pullback (pullback.snd f f) p,
      θ.hom ≫ pullback.fst (pullback.snd f f) p = pullback.snd p (pullback.fst f f) ∧
      θ.hom ≫ pullback.snd (pullback.snd f f) p ≫ q =
        pullback.fst p (pullback.fst f f) ≫ q := by
  have sqQ : IsPullback (yoneda.map (pullback.fst p (pullback.fst f f)) ≫ yoneda.map q)
      (yoneda.map (pullback.snd p (pullback.fst f f))) u
      (yoneda.map (pullback.fst f f) ≫ c) :=
    ((IsPullback.of_hasPullback p (pullback.fst f f)).map yoneda).paste_horiz sq
  have sqQ' : IsPullback (yoneda.map (pullback.snd (pullback.snd f f) p) ≫ yoneda.map q)
      (yoneda.map (pullback.fst (pullback.snd f f) p)) u
      (yoneda.map (pullback.fst f f) ≫ c) := by
    rw [hcc]
    exact ((IsPullback.of_hasPullback (pullback.snd f f) p).flip.map yoneda).paste_horiz sq
  refine ⟨yoneda.preimageIso (sqQ.isoIsPullback _ _ sqQ'), ?_, ?_⟩
  · refine yoneda.map_injective ?_
    simp only [Functor.map_comp, Functor.preimageIso, Functor.map_preimage]
    exact sqQ.isoIsPullback_hom_snd _ _ sqQ'
  · refine yoneda.map_injective ?_
    simp only [Functor.map_comp, Functor.preimageIso, Functor.map_preimage]
    exact sqQ.isoIsPullback_hom_fst _ _ sqQ'

/-- **The forward direction of the descent-data bridge, at the site.** The chart base change
`V` of an algebraic space along a section `c` with `pr₀^* c = pr₁^* c` carries a descent datum
relative to `f`, whose scheme over `T'` is `p` itself and for whose action `q` is invariant.

The gluing isomorphism is `AlgebraicGeometry.BigFppfOver.exists_gluingIso_of_isPullback`
transported from the site to the literal fibre products of schemes — the canonical functor to
schemes preserves fibre products, and pasting the square of `p` against the square of `f`
identifies `V ×_{T'} (T' ×_T T')` with `V ×_T T'` — and then assembled by
`AlgebraicGeometry.exists_transition_of_pullbackIso`, whose extensionality hypothesis is
`AlgebraicGeometry.BigFppfOver.hom_ext_of_isPullback`. -/
theorem exists_gluing_of_isPullback {T T' U V : BigFppfOver B S hS} {f : T' ⟶ T}
    {u : yoneda.obj U ⟶ F} {c : yoneda.obj T' ⟶ F} {q : V ⟶ U} {p : V ⟶ T'}
    (sq : IsPullback (yoneda.map q) (yoneda.map p) u c)
    (hcc : yoneda.map (pullback.fst f f) ≫ c = yoneda.map (pullback.snd f f) ≫ c) :
    ∃ φ : Over.mk (prod.map (structureMap ((toScheme B S hS).map f)
          (Over.mk ((toScheme B S hS).map p))) (𝟙 (Over.mk ((toScheme B S hS).map f)))) ≅
        Over.mk (prod.map (𝟙 (Over.mk ((toScheme B S hS).map f)))
          (structureMap ((toScheme B S hS).map f) (Over.mk ((toScheme B S hS).map p)))),
      (prod.map φ.hom.left (𝟙 (Over.mk ((toScheme B S hS).map f))) ≫
          prodMapLastTwo φ.hom.left = prodMapFirstThird φ.hom.left) ∧
        ∀ {Z : Over ((toScheme B S hS).obj T)}
          (v : Z ⟶ (Over.map ((toScheme B S hS).map f)).obj
            (Over.mk ((toScheme B S hS).map p)))
          (x : Z ⟶ Over.mk ((toScheme B S hS).map f)),
          (gluingAction (Over.mk ((toScheme B S hS).map p)) φ.hom.left v x).left ≫
            (toScheme B S hS).map q = v.left ≫ (toScheme B S hS).map q := by
  obtain ⟨θ, hθfst, hθq⟩ := exists_gluingIso_of_isPullback sq hcc
  obtain ⟨Θ, hΘ1, hΘ2, hΘ3⟩ :
    ∃ Θ : pullback ((toScheme B S hS).map p ≫ (toScheme B S hS).map f)
          ((toScheme B S hS).map f) ≅
        pullback ((toScheme B S hS).map f)
          ((toScheme B S hS).map p ≫ (toScheme B S hS).map f),
      (Θ.hom ≫ pullback.fst ((toScheme B S hS).map f)
          ((toScheme B S hS).map p ≫ (toScheme B S hS).map f) =
        pullback.fst ((toScheme B S hS).map p ≫ (toScheme B S hS).map f)
          ((toScheme B S hS).map f) ≫ (toScheme B S hS).map p) ∧
      (Θ.hom ≫ pullback.snd ((toScheme B S hS).map f)
            ((toScheme B S hS).map p ≫ (toScheme B S hS).map f) ≫ (toScheme B S hS).map p =
        pullback.snd ((toScheme B S hS).map p ≫ (toScheme B S hS).map f)
          ((toScheme B S hS).map f)) ∧
      (Θ.hom ≫ pullback.snd ((toScheme B S hS).map f)
            ((toScheme B S hS).map p ≫ (toScheme B S hS).map f) ≫ (toScheme B S hS).map q =
        pullback.fst ((toScheme B S hS).map p ≫ (toScheme B S hS).map f)
          ((toScheme B S hS).map f) ≫ (toScheme B S hS).map q) := by
    have pbB : IsPullback ((toScheme B S hS).map (pullback.fst p (pullback.fst f f)))
        ((toScheme B S hS).map (pullback.snd p (pullback.fst f f)) ≫
          (toScheme B S hS).map (pullback.snd f f))
        ((toScheme B S hS).map p ≫ (toScheme B S hS).map f) ((toScheme B S hS).map f) :=
      ((IsPullback.of_hasPullback p (pullback.fst f f)).map (toScheme B S hS)).paste_vert
        ((IsPullback.of_hasPullback f f).map (toScheme B S hS))
    have pbB' : IsPullback
        ((toScheme B S hS).map (pullback.fst (pullback.snd f f) p) ≫
          (toScheme B S hS).map (pullback.fst f f))
        ((toScheme B S hS).map (pullback.snd (pullback.snd f f) p))
        ((toScheme B S hS).map f) ((toScheme B S hS).map p ≫ (toScheme B S hS).map f) :=
      ((((IsPullback.of_hasPullback (pullback.snd f f) p).map (toScheme B S hS)).flip).paste_vert
        (((IsPullback.of_hasPullback f f).map (toScheme B S hS)).flip)).flip
    have hsite1 : θ.hom ≫ pullback.fst (pullback.snd f f) p ≫ pullback.fst f f =
        pullback.fst p (pullback.fst f f) ≫ p := by
      rw [← Category.assoc, hθfst]
      exact pullback.condition.symm
    have hsite2 : θ.hom ≫ pullback.snd (pullback.snd f f) p ≫ p =
        pullback.snd p (pullback.fst f f) ≫ pullback.snd f f := by
      rw [← pullback.condition, ← Category.assoc, hθfst]
    have hsite2' : (θ.hom ≫ pullback.snd (pullback.snd f f) p) ≫ p =
        pullback.snd p (pullback.fst f f) ≫ pullback.snd f f := by
      rw [Category.assoc]; exact hsite2
    have hθq' : (θ.hom ≫ pullback.snd (pullback.snd f f) p) ≫ q =
        pullback.fst p (pullback.fst f f) ≫ q := by
      rw [Category.assoc]; exact hθq
    have hLf : (pbB.isoPullback.symm ≪≫ (toScheme B S hS).mapIso θ ≪≫ pbB'.isoPullback).hom ≫
        pullback.fst ((toScheme B S hS).map f)
          ((toScheme B S hS).map p ≫ (toScheme B S hS).map f) =
        pbB.isoPullback.inv ≫ (toScheme B S hS).map
          (θ.hom ≫ pullback.fst (pullback.snd f f) p ≫ pullback.fst f f) := by
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
        IsPullback.isoPullback_hom_fst, Functor.map_comp]
    have hLs : ∀ {Y₀ : Scheme.{u}} (β : (toScheme B S hS).obj V ⟶ Y₀),
        (pbB.isoPullback.symm ≪≫ (toScheme B S hS).mapIso θ ≪≫ pbB'.isoPullback).hom ≫
          pullback.snd ((toScheme B S hS).map f)
            ((toScheme B S hS).map p ≫ (toScheme B S hS).map f) ≫ β =
          pbB.isoPullback.inv ≫ (toScheme B S hS).map
            (θ.hom ≫ pullback.snd (pullback.snd f f) p) ≫ β := by
      intro Y₀ β
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
        IsPullback.isoPullback_hom_snd_assoc, Functor.map_comp]
    refine ⟨pbB.isoPullback.symm ≪≫ (toScheme B S hS).mapIso θ ≪≫ pbB'.isoPullback, ?_, ?_, ?_⟩
    · rw [hLf, hsite1, Functor.map_comp, ← Category.assoc pbB.isoPullback.inv,
        pbB.isoPullback_inv_fst]
    · rw [hLs, ← Functor.map_comp (toScheme B S hS)
        (θ.hom ≫ pullback.snd (pullback.snd f f) p) p, hsite2', Functor.map_comp,
        pbB.isoPullback_inv_snd]
    · rw [hLs, ← Functor.map_comp (toScheme B S hS)
        (θ.hom ≫ pullback.snd (pullback.snd f f) p) q, hθq', Functor.map_comp,
        ← Category.assoc pbB.isoPullback.inv, pbB.isoPullback_inv_fst]
  exact exists_transition_of_pullbackIso ((toScheme B S hS).map f)
    ((toScheme B S hS).map p) ((toScheme B S hS).map q) Θ hΘ1 hΘ2 hΘ3
    (fun a₁ a₂ h₁ h₂ => hom_ext_of_isPullback sq a₁ a₂ h₁ h₂)

/-- **The descent-data bridge.** The bespoke conclusion which the middle paragraph of Stacks
0APL asks of Stacks 0APK — a scheme `W₀`, a morphism `w₀ : W₀ ⟶ T`, an isomorphism
`α₀ : T' ×_T W₀ ≅ V` over `T'` and the invariance of `α₀ ≫ q` — follows from effectivity of
every descent datum relative to `f` whose scheme over `T'` is the chart base change `p`.

So a proof of Stacks 0APK stated at `AlgebraicGeometry.DescentDatum` and
`AlgebraicGeometry.DescentData.IsEffective` discharges `hAPK` of
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffectiveFpqcDescent_scheme`. Nothing
here proves effectivity of anything. -/
theorem exists_descent_scheme_of_isEffective_of_isPullback
    {T T' U V : BigFppfOver B S hS} {f : T' ⟶ T} {u : yoneda.obj U ⟶ F}
    {c : yoneda.obj T' ⟶ F} {q : V ⟶ U} {p : V ⟶ T'}
    (sq : IsPullback (yoneda.map q) (yoneda.map p) u c)
    (hcc : yoneda.map (pullback.fst f f) ≫ c = yoneda.map (pullback.snd f f) ≫ c)
    (hAPK : ∀ D : DescentDatum ((toScheme B S hS).map f),
      D.over = Over.mk ((toScheme B S hS).map p) → DescentData.IsEffective D) :
    ∃ (W₀ : Scheme.{u}) (w₀ : W₀ ⟶ (toScheme B S hS).obj T)
      (α₀ : pullback ((toScheme B S hS).map f) w₀ ≅ (toScheme B S hS).obj V),
      α₀.hom ≫ (toScheme B S hS).map p = pullback.fst ((toScheme B S hS).map f) w₀ ∧
      pullback.fst (pullback.snd ((toScheme B S hS).map f) w₀)
            (pullback.snd ((toScheme B S hS).map f) w₀) ≫
          α₀.hom ≫ (toScheme B S hS).map q =
        pullback.snd (pullback.snd ((toScheme B S hS).map f) w₀)
            (pullback.snd ((toScheme B S hS).map f) w₀) ≫
          α₀.hom ≫ (toScheme B S hS).map q := by
  obtain ⟨φ, hco, hinv⟩ := exists_gluing_of_isPullback sq hcc
  exact DescentData.exists_descent_of_isEffective
    (DescentDatum.mk' (Over.mk ((toScheme B S hS).map p)) φ hco)
    ((toScheme B S hS).map q) (fun v x => hinv v x) (hAPK _ rfl)

end BigFppfOver

/-- **The affine-base hypothesis below is not vacuous: its domain is inhabited.** There are
affine schemes `T`, `T'`, a surjective flat quasi-compact `g : T' ⟶ T` and a descent datum
relative to `g` whose scheme over `T'` is ind-quasi-affine.

The witness is `g = 𝟙 (Spec (ULift ℤ))` together with the canonical descent datum of
`Over.mk (𝟙 (Spec (ULift ℤ)))`; the ind-quasi-affineness of its scheme over `T'` is read off
`AlgebraicGeometry.DescentData.isPullback_canonicalProj`, which exhibits that scheme as the
base change of `U ⟶ T` along `g`, through
`AlgebraicGeometry.isIndQuasiAffineHom_of_isPullback`. The point of recording this is that a
statement whose only hypothesis quantifies over an empty family would be vacuous; nothing
else here depends on this declaration. -/
theorem exists_isAffine_descentDatum_isIndQuasiAffineHom :
    ∃ (T T' : Scheme.{u}) (g : T' ⟶ T), IsAffine T ∧ IsAffine T' ∧
      Surjective g ∧ Flat g ∧ QuasiCompact g ∧
      ∃ D : DescentDatum g, IsIndQuasiAffineHom D.over.hom := by
  refine ⟨Spec (CommRingCat.of (ULift.{u} ℤ)), Spec (CommRingCat.of (ULift.{u} ℤ)), 𝟙 _,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (DescentDatum.canonical (𝟙 _)).obj (Over.mk (𝟙 _)), ?_⟩
  have : IsIndQuasiAffineHom (Over.mk (𝟙 (Spec (CommRingCat.of (ULift.{u} ℤ))))).hom :=
    inferInstanceAs (IsIndQuasiAffineHom (𝟙 _))
  exact isIndQuasiAffineHom_of_isPullback
    ((DescentData.isPullback_canonicalProj (𝟙 _) (Over.mk (𝟙 _))).flip)

namespace IsAlgebraicSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}}
variable {hS : B.Contains S} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0APL with Stacks 0APK as its only hypothesis, stated at the canonical notion of
descent datum.** An algebraic space over `S` is a sheaf for the fpqc topology of the big fppf
category over `S` as soon as every descent datum of schemes relative to a surjective flat
quasi-compact morphism of the site between affine objects, whose scheme over the source is
surjective étale separated and ind-quasi-affine, is effective.

This is
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffectiveFpqcDescent_scheme` with its
bespoke hypothesis replaced, through
`AlgebraicGeometry.BigFppfOver.exists_descent_scheme_of_isEffective_of_isPullback`, by
effectivity in the vocabulary of `AlgebraicGeometry.DescentDatum` and
`AlgebraicGeometry.DescentData.IsEffective`. It proves no new mathematics; it records that
either shape of Stacks 0APK closes Stacks 0APL. -/
theorem isSheaf_fpqc_of_isEffective_descentDatum (hF : IsAlgebraicSpace B S hS F)
    (hAPK : ∀ (T T' : BigFppfOver B S hS) (f : T' ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
      Surjective ((BigFppfOver.toScheme B S hS).map f) →
      Flat ((BigFppfOver.toScheme B S hS).map f) →
      QuasiCompact ((BigFppfOver.toScheme B S hS).map f) →
      ∀ D : DescentDatum ((BigFppfOver.toScheme B S hS).map f),
        Surjective D.over.hom → Etale D.over.hom →
        _root_.AlgebraicGeometry.IsSeparated D.over.hom →
        IsIndQuasiAffineHom D.over.hom → DescentData.IsEffective D) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F := by
  refine hF.isSheaf_fpqc_of_isEffectiveFpqcDescent_scheme ?_
  intro T T' f hTaff hT'aff hfs hff hfqc U V u q p c sq hpsurj hpet hpsep hpiqa hcc
  refine BigFppfOver.exists_descent_scheme_of_isEffective_of_isPullback sq hcc ?_
  intro D hD
  refine hAPK T T' f hTaff hT'aff hfs hff hfqc D ?_ ?_ ?_ ?_
  · rw [hD]; exact hpsurj
  · rw [hD]; exact hpet
  · rw [hD]; exact hpsep
  · rw [hD]; exact hpiqa

/-- **Stacks 0APL from Stacks 0APK over an affine base.** An algebraic space over `S` is a
sheaf for the fpqc topology of the big fppf category over `S` as soon as every descent datum
of schemes relative to a surjective flat quasi-compact morphism `g : T' ⟶ T` of *affine*
schemes, whose scheme over `T'` is ind-quasi-affine, is effective.

This is the shape in which Stacks 0APK is approached in this development, and it is the only
reason for stating it: the hypothesis is the universally quantified form of the conclusion of
`AlgebraicGeometry.DescentDatum.isEffective_of_unitCoassoc_of_preimage_of_restrictOpen` of
`StacksFrontier.AlgebraicGeometry.Descent.DescentDatumResidue`, which reduces effectivity over an
affine base to four obligations and nothing else. So
`fun g _ _ _ _ _ D _ ↦ D.isEffective_of_unitCoassoc_of_preimage_of_restrictOpen hkey
hpreimage hrestrict hglueing` discharges it the moment those four are proved, with no
transport. Affineness of `T` and `T'` is precisely what the hypothesis of
`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffective_indQuasiAffine`
omits, and without it that reduction cannot be applied at all.

Compared with `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffective_descentDatum`,
the hypothesis here asks for effectivity from less information about the datum — only
ind-quasi-affineness of `D.over.hom`, not surjectivity, étaleness and separatedness as well —
so it is a stronger hypothesis and this statement is correspondingly weaker. Its domain is
inhabited, by `AlgebraicGeometry.exists_isAffine_descentDatum_isIndQuasiAffineHom`, so the
hypothesis is not vacuously true.

**This is not Stacks 0APL and carries no tag.** Nothing here proves effectivity of any descent
datum, but the hypothesis is no longer open in the repository: the one-member case of Stacks
0APK, `AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom_of_quasiCompact` of
`StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteSchemeDescent`, asserts effectivity
of every ind-quasi-affine descent datum along a surjective flat quasi-compact morphism — over an
arbitrary base, not only an affine one — and the last of the four obligations, Stacks 0AP4, is
proved here as `AlgebraicGeometry.DescentDatum.isEffective_of_forall_exists_restrictOpen` of
`StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme`, where it carries the tag. So
this interface waits on nothing: Stacks 0APL lands through it as
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc` of
`StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf`, via
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_legs_of_restrictOpen` of
`StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcLocalFromDescentData`, which is this theorem
fed with `AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen`; the landing file
discharges its three obligations `hlegs`, `hrestrict` and `hglueing` with
`AlgebraicGeometry.DescentDatum.preimage_specMap_legs_subsetΓSpecImage`,
`AlgebraicGeometry.DescentDatum.isEffective_restrictOpen_descentInvariants` and Stacks 0AP4
above. What remains of this statement's purpose is what it always was: to be the one interface
through which a proof of those obligations reaches both Stacks 0APL and, through
`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffective_affine_indQuasiAffine`,
Stacks 041Z. -/
theorem isSheaf_fpqc_of_isEffective_affine_indQuasiAffine (hF : IsAlgebraicSpace B S hS F)
    (hAPK : ∀ {T T' : Scheme.{u}} (g : T' ⟶ T), IsAffine T → IsAffine T' →
      Surjective g → Flat g → QuasiCompact g →
      ∀ D : DescentDatum g, IsIndQuasiAffineHom D.over.hom → DescentData.IsEffective D) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F :=
  hF.isSheaf_fpqc_of_isEffective_descentDatum fun _ _ f hT hT' hs hfl hqc D _ _ _ hiqa =>
    hAPK ((BigFppfOver.toScheme B S hS).map f) hT hT' hs hfl hqc D hiqa

end IsAlgebraicSpace

end AlgebraicGeometry

end
