module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ModelOverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationExtension
public import StacksFrontier.RingTheory.Flat.DevissageProjectiveStages
public import StacksFrontier.RingTheory.Flat.FlatAtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite presentation and flatness from a complete dévissage over a local base

Stacks 05I4 reads off three conclusions from an *algebraic* complete dévissage of `N/B/A` at a
prime `q` of `B` lying over the maximal ideal of a local ring `A`, when `N` is flat over `A` at
`q`: the module is of finite presentation over `B`, and it is free — hence flat — over `A`. A
*geometric* complete dévissage of a quasi-coherent module on a scheme over `Spec A` is turned
into an algebraic one by the dictionary of Stacks 05I0.

This file puts the two together on the geometric side: for an affine scheme `X` locally of
finite presentation over `Spec A` with `A` local, a finite type quasi-coherent `𝒪_X`-module
carrying a complete dévissage at a point over the closed point of `Spec A`, and flat over
`Spec A` there, is of finite presentation and flat over `Spec A` *everywhere*.

The dictionary of Stacks 05I0 is a proved fact of this repository, not an input carried from
the source. Its forward direction — a geometric complete dévissage at a point gives an
algebraic one, the only direction the source uses — is registered as
`Module.nonempty_completeDevissageAt_of_completeDevissageAt` (the `@[stacks 05I0]` theorem of
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/AlgebraTranslationAt.lean`), and
in the ring-map shape stated below it is proved outright as
`AlgebraicGeometry.geometricCompleteDevissageAtGivesAlgebraic` in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/SpecTranslation.lean`, which
identifies `Γ(Spec A, ⊤)`, `Γ(Spec B, ⊤)` and `Γ(Ñ, ⊤)` with `A`, `B` and `N` through
`Module.nonempty_completeDevissageAt_ofRingEquiv`. The results below nevertheless take the
forward direction as the single hypothesis
`AlgebraicGeometry.GeometricCompleteDevissageAtGivesAlgebraic`: the Stacks 05I5 proof in
`StacksFrontier/AlgebraicGeometry/Etale/ElementaryNeighborhoodFlatness.lean` applies
`AlgebraicGeometry.isFinitePresentation_isFlatOver_of_completeDevissageAt` with
`AlgebraicGeometry.geometricCompleteDevissageAtGivesAlgebraic` at the hypothesis position, so
the binder stays in the signature and the consumers discharge it from the repository rather
than from an assumed citation. The equivalence of the two existence statements is
`Module.nonempty_completeDevissageAt_iff` in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/SpecCompleteDevissageAt.lean`;
its converse half keeps the stage-by-stage fibre condition
`Module.CompleteDevissageAt.FibresHaveRelativeDimension` as a hypothesis, since the source's
unconditional converse needs the dimension of *every* fibre of a smooth morphism with
geometrically irreducible fibres.

## Main definitions

* `AlgebraicGeometry.GeometricCompleteDevissageAtGivesAlgebraic` is the forward implication of
  Stacks 05I0 (2), stated as a proposition so that the results depending on it take it as a
  single hypothesis; `AlgebraicGeometry.geometricCompleteDevissageAtGivesAlgebraic` in
  `SpecTranslation.lean` proves it from the registered `@[stacks 05I0]` theorem of
  `AlgebraTranslationAt.lean`.

## Main results

* `AlgebraicGeometry.isFinitePresentation_isFlatOver_of_completeDevissageAt` is the geometric
  reading of Stacks 05I4 described above.
* `AlgebraicGeometry.isFinitePresentation_isFlatOver_of_surjective_etale_pullback` descends
  finite presentation and flatness over the base along a surjective étale morphism, by Stacks
  05B0 and Stacks 02JZ.
* `AlgebraicGeometry.isAffine_source_of_devissageChain`: the source of a nonempty complete
  dévissage is affine.
* `AlgebraicGeometry.isFinitePresentation_of_isZero` and
  `AlgebraicGeometry.isFlatOver_of_isZero` record the two conclusions for a zero module, which
  is the case of the empty complete dévissage.
* `AlgebraicGeometry.isFlatOver_of_subsingleton_stalks`: a module on a ringed space whose
  stalks are all trivial is flat over the target of any morphism out of that space.

## Implementation notes

The passage from `X` to `Spec Γ(X, ⊤)` and from the module to a `Γ(X, ⊤)`-module is carried out
by `AlgebraicGeometry.CompleteDevissageAt.ofSourceIso` and
`AlgebraicGeometry.CompleteDevissageAt.ofModuleIso`, and the resulting statements are brought
back to `X` by the étale descent above rather than by transporting the conclusions along the
isomorphism.

## References

* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The zero module -/

/-- Every section of a zero module vanishes: the identity of the module is the zero morphism,
and its value on a section is that section. -/
lemma eq_zero_of_isZero_apply {X : Scheme.{u}} {F : X.Modules} (h : IsZero F)
    (W : Opens X) (w : F.val.presheaf.obj (op W)) : w = 0 :=
  congrArg (fun φ : F ⟶ F ↦ (ModuleCat.Hom.hom (φ.val.app (op W))) w) (h.eq_of_src (𝟙 F) 0)

/-- The stalks of a zero module are trivial: every germ comes from a section, and every section
of a zero module vanishes. -/
lemma subsingleton_moduleStalk_of_isZero {X : Scheme.{u}} {F : X.Modules} (h : IsZero F)
    (x : X) :
    Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) := by
  refine subsingleton_of_forall_eq 0 fun a ↦ ?_
  obtain ⟨U, hU, s, hs⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) F.val.presheaf a
  rw [← hs, eq_zero_of_isZero_apply h U s, map_zero]

/-- A zero module is of finite presentation. -/
theorem isFinitePresentation_of_isZero {X : Scheme.{u}} (F : X.Modules) (h : IsZero F) :
    F.IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso h.isoZero.symm
    (isFinitePresentation_zero X)

/-- A module with no nonzero elements is flat: it is free on the empty basis. The module
structure is an explicit argument so that the conclusion can be unified with a goal whose own
module structure is fixed. -/
private lemma flat_of_subsingleton (R M : Type u) [CommRing R] [AddCommGroup M]
    (inst : Module R M) (h : Subsingleton M) : @Module.Flat R M _ _ inst := by
  let := inst
  have := h
  have : Module.Free R M := Module.Free.of_subsingleton R M
  infer_instance

/-- A module with trivial stalks is flat over any base. -/
theorem isFlatOver_of_subsingleton_stalks {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    (h : ∀ x : X,
      Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)) :
    IsFlatOver g F := fun x ↦ flat_of_subsingleton _ _ _ (h x)

/-- A zero module is flat over any base. -/
theorem isFlatOver_of_isZero {X Y : Scheme.{u}} (g : X ⟶ Y) (F : X.Modules) (h : IsZero F) :
    IsFlatOver g.toLRSHom.toShHom F :=
  isFlatOver_of_subsingleton_stalks _ F fun x ↦ subsingleton_moduleStalk_of_isZero h x

/-! ### Affineness of the schemes of a dévissage -/

/-- The source of a complete dévissage is affine: every stage of the chain says so. -/
lemma isAffine_source_of_devissageChain {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
    {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType}
    (C : DevissageChain s X f F hl hq ht) : IsAffine X := by
  cases C with
  | last stage _ => exact stage.oneStep.affine_X
  | more stage _ _ _ _ => exact stage.oneStep.affine_X

/-! ### Descent along a surjective étale morphism -/

/-- Finite presentation of a quasi-coherent module, and its flatness over the base, descend
along a surjective étale morphism: the first by Stacks 05B0, since a surjective étale morphism
is a one-element fpqc cover, the second by Stacks 02JZ. -/
theorem isFinitePresentation_isFlatOver_of_surjective_etale_pullback
    {Y X S : Scheme.{u}} (e : Y ⟶ X) [Etale e] [Surjective e] (g : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent]
    (hfp : ((Scheme.Modules.pullback e).obj F).IsFinitePresentation)
    (hflat : IsFlatOver (e ≫ g).toLRSHom.toShHom ((Scheme.Modules.pullback e).obj F)) :
    F.IsFinitePresentation ∧ IsFlatOver g.toLRSHom.toShHom F := by
  refine ⟨?_, (isFlatOver_iff_modulePullback_isFlatOver e g F).mpr hflat⟩
  let C : X.Cover.{u} Scheme.fpqcPrecoverage :=
    Precoverage.ZeroHypercover.singleton e
      (Scheme.fppfPrecoverage_le_fpqcPrecoverage _ e.singleton_mem_fppfPrecoverage)
  exact isFinitePresentation_of_pullback_fpqcCover F C fun _ ↦ hfp

/-! ### Transporting a complete dévissage along an equality of structure morphisms -/

/-- A complete dévissage along `f` is one along any morphism equal to `f`. The statement is
needed because the three finiteness conditions are instance arguments of
`AlgebraicGeometry.CompleteDevissageAt`, so that `rw` cannot move across the equality. -/
lemma nonempty_completeDevissageAt_of_eq {X S : Scheme.{u}} {f f' : X ⟶ S} (hf : f = f')
    (F : X.Modules) (x : X) (hl : LocallyOfFiniteType f) (hl' : LocallyOfFiniteType f')
    (hq : F.IsQuasicoherent) (ht : F.IsFiniteType)
    (h : Nonempty (@CompleteDevissageAt X S f F x hl hq ht)) :
    Nonempty (@CompleteDevissageAt X S f' F x hl' hq ht) := by
  subst hf
  exact h

/-! ### The dictionary of Stacks 05I0, as a single hypothesis -/

/-- **Stacks Project, Tag 05I0**, the direction the source uses, as a proposition.

Let `A → B` be a ring map of finite type, let `N` be a finite `B`-module and let `q` be a prime
of `B`. Write `X = Spec B`, `S = Spec A` and `F = Ñ`, and let `x` be the point of `X`
corresponding to `q`. If `F/X/S` has a complete dévissage at `x` then `N/B/A` has a complete
dévissage at `q`.

Stacks 05I0 states the equivalence of the two existence statements and notes that only this
direction is ever used; this proposition is therefore the hypothesis the consumers below take.
It is no longer an assumption of the repository: it is proved as
`AlgebraicGeometry.geometricCompleteDevissageAtGivesAlgebraic` in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/SpecTranslation.lean`, which
wires the registered theorem `Module.nonempty_completeDevissageAt_of_completeDevissageAt`
(`@[stacks 05I0]`, `AlgebraTranslationAt.lean`) through the ring identifications of
`Module.nonempty_completeDevissageAt_ofRingEquiv`. The equivalence itself is
`Module.nonempty_completeDevissageAt_iff` in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/SpecCompleteDevissageAt.lean`. -/
def GeometricCompleteDevissageAtGivesAlgebraic : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (N : Type u) [AddCommGroup N] [Module B N] [Module.Finite B N] (q : PrimeSpectrum B),
    Nonempty (@CompleteDevissageAt (Spec (.of B)) (Spec (.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (tilde (R := .of B) (ModuleCat.of B N)) q
      (locallyOfFiniteType_specMap_algebraMap A B) inferInstance
      ((tilde_isFiniteType_iff (R := .of B) (ModuleCat.of B N)).2 inferInstance)) →
    Nonempty (@Module.CompleteDevissageAt A B N _ _ _ _ _ _ _ q.asIdeal q.isPrime)

/-! ### Flatness over the base of the module attached to a flat module -/

/-- If a module over the global sections of an affine scheme is flat over a base ring, then the
associated quasi-coherent module is flat over the spectrum of that base ring at every point:
every localization of a module flat over a base ring is again flat over it. -/
@[ega "IV 2.1.2" "Sufficiency"]
theorem isFlatOver_spec_tilde_of_flat {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (N : ModuleCat.{u} B) [Algebra (A : Type u) (B : Type u)]
    [Module (A : Type u) (N : Type u)] [IsScalarTower (A : Type u) (B : Type u) (N : Type u)]
    (hφ : φ.hom = algebraMap (A : Type u) (B : Type u)) (hN : Module.Flat (A : Type u) N) :
    IsFlatOver (Spec.map φ).toLRSHom.toShHom (tilde N) := fun q ↦
  (isFlatOverAt_spec_tilde_iff_flat_localizedModule φ N hφ q).mpr inferInstance

/-! ### Stacks 05I4, read geometrically -/

/-- Stacks 05I4 on the spectrum of an algebra over a local ring: if `Ñ/Spec B/Spec A` has a
complete dévissage at a point over the closed point where `Ñ` is flat, then `Ñ` is of finite
presentation and flat over `Spec A`. -/
theorem isFinitePresentation_isFlatOver_spec_tilde_of_completeDevissageAt
    (hdict : GeometricCompleteDevissageAtGivesAlgebraic.{u})
    {A : Type u} [CommRing A] [IsLocalRing A] {B : CommRingCat.{u}} (φ : CommRingCat.of A ⟶ B)
    [LocallyOfFinitePresentation (Spec.map φ)] (N : ModuleCat.{u} B) [(tilde N).IsFiniteType]
    (z : Spec B) (hz : Spec.map φ z = IsLocalRing.closedPoint A)
    (hD : Nonempty (CompleteDevissageAt (Spec.map φ) (tilde N) z))
    (hflat : IsFlatOverAt (Spec.map φ).toLRSHom.toShHom (tilde N) z) :
    (tilde N).IsFinitePresentation ∧ IsFlatOver (Spec.map φ).toLRSHom.toShHom (tilde N) := by
  have : Module.Finite (B : Type u) (N : Type u) := (tilde_isFiniteType_iff N).mp ‹_›
  let : Algebra A (B : Type u) := φ.hom.toAlgebra
  have hφ : φ.hom = algebraMap A (B : Type u) := rfl
  have : Algebra.FinitePresentation A (B : Type u) :=
    RingHom.finitePresentation_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp ‹_›)
  let : Module A (N : Type u) := Module.compHom (N : Type u) φ.hom
  let : IsScalarTower A (B : Type u) (N : Type u) :=
    IsScalarTower.of_compHom A (B : Type u) (N : Type u)
  have hqA : (z.asIdeal).under A = IsLocalRing.maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal hz
  have : z.asIdeal.IsPrime := z.isPrime
  have hflatLoc : Module.Flat A (LocalizedModule z.asIdeal.primeCompl (N : Type u)) :=
    (isFlatOverAt_spec_tilde_iff_flat_localizedModule φ N hφ z).mp hflat
  obtain ⟨D⟩ := hdict A (B : Type u) (N : Type u) z hD
  have : Module.FinitePresentation (B : Type u) (N : Type u) :=
    D.finitePresentation_of_flat hqA hflatLoc
  have : Module.Free A (N : Type u) := D.free_of_flat hqA hflatLoc
  exact ⟨(tilde_isFinitePresentation_iff N).mpr inferInstance,
    isFlatOver_spec_tilde_of_flat φ N hφ inferInstance⟩

/-- Let `g : Spec R ⟶ Spec A` be locally of finite presentation with `A` local, and let `F` be a
quasi-coherent `𝒪`-module of finite type on `Spec R`. If `F` admits a complete dévissage at a
point `z` lying over the closed point and `F` is flat over `Spec A` at `z`, then `F` is of finite
presentation and flat over `Spec A`. -/
theorem isFinitePresentation_isFlatOver_spec_of_completeDevissageAt
    (hdict : GeometricCompleteDevissageAtGivesAlgebraic.{u})
    {A : Type u} [CommRing A] [IsLocalRing A] {R : CommRingCat.{u}}
    (g : Spec R ⟶ Spec (.of A)) [LocallyOfFinitePresentation g]
    (F : (Spec R).Modules) [F.IsQuasicoherent] [F.IsFiniteType] (z : Spec R)
    (hz : g z = IsLocalRing.closedPoint A)
    (hD : Nonempty (CompleteDevissageAt g F z))
    (hflat : IsFlatOverAt g.toLRSHom.toShHom F z) :
    F.IsFinitePresentation ∧ IsFlatOver g.toLRSHom.toShHom F := by
  obtain ⟨N, ⟨eN⟩⟩ : (tilde.functor R).essImage F := by
    rw [essImage_tilde]
    exact inferInstanceAs F.IsQuasicoherent
  have : (tilde N).IsFiniteType := SheafOfModules.isFiniteType_of_iso eN.symm ‹_›
  let φ : CommRingCat.of A ⟶ R := Spec.preimage g
  have hφmap : Spec.map φ = g := Spec.map_preimage g
  have : LocallyOfFinitePresentation (Spec.map φ) := hφmap ▸ ‹_›
  have hD₁ : Nonempty (CompleteDevissageAt g (tilde N) z) := by
    obtain ⟨D⟩ := hD
    exact ⟨D.ofModuleIso eN⟩
  have hclosed : Spec.map φ z = IsLocalRing.closedPoint A := by rwa [hφmap]
  have hflat₁ : IsFlatOverAt (Spec.map φ).toLRSHom.toShHom (tilde N) z := by
    rw [hφmap]
    exact isFlatOverAt_of_moduleIso g.toLRSHom.toShHom eN.symm z hflat
  obtain ⟨hfpN, hflatN⟩ := isFinitePresentation_isFlatOver_spec_tilde_of_completeDevissageAt
    hdict φ N z hclosed (nonempty_completeDevissageAt_of_eq hφmap.symm (tilde N) z _ _ _ _ hD₁)
    hflat₁
  refine ⟨(SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso eN hfpN, ?_⟩
  refine isFlatOver_of_moduleIso g.toLRSHom.toShHom eN ?_
  rwa [← hφmap]

/-- **Stacks Project, Tag 05I4** on an affine scheme over the spectrum of a local ring. Let `A`
be a local ring, let `X` be an affine scheme locally of finite presentation over `Spec A`, and
let `F` be a finite type quasi-coherent `𝒪_X`-module which is flat over `Spec A` at a point `z`
lying over the closed point. If `F/X/Spec A` has a complete dévissage at `z`, then `F` is of
finite presentation and flat over `Spec A`.

The proof reads the data on `Spec Γ(X, ⊤)`, where the module becomes `Ñ` for a finite module
`N` over `Γ(X, ⊤)`, applies the dictionary of Stacks 05I0 to obtain an algebraic complete
dévissage of `N/Γ(X, ⊤)/A` at the prime of `z`, and feeds that to
`Module.CompleteDevissageAt.finitePresentation_of_flat` and
`Module.CompleteDevissageAt.free_of_flat`. -/
theorem isFinitePresentation_isFlatOver_of_completeDevissageAt
    (hdict : GeometricCompleteDevissageAtGivesAlgebraic.{u})
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} [IsAffine X]
    (g : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation g]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (z : X)
    (hz : g z = IsLocalRing.closedPoint A)
    (hD : Nonempty (CompleteDevissageAt g F z))
    (hflat : IsFlatOverAt g.toLRSHom.toShHom F z) :
    F.IsFinitePresentation ∧ IsFlatOver g.toLRSHom.toShHom F := by
  let e : (Spec Γ(X, ⊤) : Scheme.{u}) ≅ X := X.isoSpec.symm
  let z₁ : (Spec Γ(X, ⊤) : Scheme.{u}) := e.inv z
  have hez : e.hom z₁ = z := congrArg (fun k : X ⟶ X ↦ k z) e.inv_hom_id
  have : LocallyOfFinitePresentation (e.hom ≫ g) := inferInstance
  have : ((Scheme.Modules.pullback e.hom).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback e.hom F inferInstance
  have : ((Scheme.Modules.pullback e.hom).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType e.hom.toLRSHom.toShHom F
  have hz₁ : (e.hom ≫ g) z₁ = IsLocalRing.closedPoint A := by
    show g (e.hom z₁) = _
    rw [hez, hz]
  have hD₁ : Nonempty (CompleteDevissageAt (e.hom ≫ g) ((Scheme.Modules.pullback e.hom).obj F)
      z₁) := by
    obtain ⟨D⟩ := hD
    exact ⟨CompleteDevissageAt.ofSourceIso e rfl (Iso.refl _) hez D⟩
  have hflat₁ : IsFlatOverAt (e.hom ≫ g).toLRSHom.toShHom
      ((Scheme.Modules.pullback e.hom).obj F) z₁ := by
    refine (isFlatOverAt_iff_modulePullback_isFlatOverAt e.hom g F z₁ ?_).mp ?_
    · exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
        (Arrow.isoMk (Iso.refl _) (Iso.refl _))).mpr (RingHom.Flat.of_bijective
          (f := (e.hom.stalkMap z₁).hom) (ConcreteCategory.bijective_of_isIso _))
    · rwa [hez]
  -- Stacks 05I0 and then Stacks 05I4.
  obtain ⟨hfp, hflat'⟩ := isFinitePresentation_isFlatOver_spec_of_completeDevissageAt hdict
    (e.hom ≫ g) _ z₁ hz₁ hD₁ hflat₁
  exact isFinitePresentation_isFlatOver_of_surjective_etale_pullback e.hom g F hfp hflat'

end AlgebraicGeometry

end
