module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.Blowup.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Normalization.NormalizedBlowUpDescent
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChangePullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Models.Normalization
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpNormal
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Completed local rings on the blowup of a local ring in its maximal ideal

Let `A` be a Noetherian local ring and let `X ⟶ Spec A` be the blowup of `Spec A` in the maximal
ideal of `A`. If the blowup of `Spec A^` in the maximal ideal of the completion `A^` is a normal
scheme, then the completion of the local ring of `X` at every closed point of `X` is a normal
domain.

## Main definitions

* `AlgebraicGeometry.maximalIdealSheaf` is the ideal sheaf on `Spec A` cut out by the maximal
  ideal of a local ring `A`.

## Main results

* `AlgebraicGeometry.comap_maximalIdealSheaf_specMapAdicCompletion`: the inverse image of the
  maximal ideal sheaf along the completion morphism is the maximal ideal sheaf of the completion.
* `AlgebraicGeometry.isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal`: the completed local
  rings at the closed points of the blowup are normal domains.

## Implementation notes

The blowup of `Spec A^` in the maximal ideal of `A^` is the base change of the blowup of `Spec A`
in the maximal ideal of `A` along the flat morphism `Spec A^ ⟶ Spec A` ([Stacks, Tag 0805]), so
its local rings have the same completions as those of `X` at the closed points
([Stacks, Tag 0BG5]). Its base `A^` is a complete Noetherian local ring and therefore excellent,
so its local rings are excellent, and normality ascends from an excellent normal local ring to
its completion.

The hypothesis `hnormal` is [Stacks, Tag 0BG7]'s appeal to [Stacks, Tag 0B4Z] at the completion
`A^`; that tag is registered in this development as
`AlgebraicGeometry.isNormal_blowUp_maximalIdeal_rationalSingularitySituation`, whose hypotheses
are that the ring is a normal Nagata domain of dimension two defining a rational singularity.
The source's remaining hypotheses on `A` — normal, Nagata, of dimension two, defining a rational
singularity, with normal completion — are exactly what [Stacks, Tag 0B4Z] consumes at `A^` and
play no further role here, so they are not assumed and this general form carries the conclusion
of that tag as `hnormal`.

## References

* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
* [Stacks Project, Tag 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z)
* [Stacks Project, Tag 0BG5](https://stacks.math.columbia.edu/tag/0BG5)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The ideal sheaf on `Spec A` cut out by the maximal ideal of a local ring `A`. -/
public abbrev maximalIdealSheaf (A : Type u) [CommRing A] [IsLocalRing A] :
    (Spec (.of A)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (maximalIdeal A))

/-- The inverse image of the maximal ideal sheaf of `Spec A` along the completion morphism is the
maximal ideal sheaf of the spectrum of the completion. -/
public theorem comap_maximalIdealSheaf_specMapAdicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    (maximalIdealSheaf A).comap (specMapAdicCompletion A) =
      maximalIdealSheaf (AdicCompletion (maximalIdeal A) A) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Stacks.IdealSheaf.ideal_comap_top_of_isAffine]
  have hnat : ((specMapAdicCompletion A).appTop).hom.comp
      (Scheme.ΓSpecIso (.of A)).inv.hom =
      (Scheme.ΓSpecIso (.of (AdicCompletion (maximalIdeal A) A))).inv.hom.comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A)) :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))).symm
  simp only [maximalIdealSheaf, Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl,
    CategoryTheory.op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  rw [Ideal.map_map, hnat, ← Ideal.map_map, AdicCompletion.maximalIdeal_eq_map]

/-! ### Excellence and normality of completed local rings -/

/-- An algebra essentially of finite type over an excellent ring is excellent. -/
private theorem isExcellent_of_essFiniteType {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (hR : IsExcellent R) : IsExcellent S :=
  (isQuasiExcellent_and_isExcellent_of_essFiniteType.{u, u}).2 hR

/-- Excellence transports along a ring isomorphism: the target is generated, as an algebra over
the source, by the empty set. -/
private theorem isExcellent_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (hR : IsExcellent R) : IsExcellent S := by
  let : Algebra R S := e.toRingHom.toAlgebra
  have hsurj : Function.Surjective (Algebra.ofId R S) := fun b => ⟨e.symm b, e.apply_symm_apply b⟩
  have : Algebra.EssFiniteType R S := Algebra.EssFiniteType.of_surjective _ hsurj
  exact isExcellent_of_essFiniteType hR

/-- The local ring of the spectrum of an excellent ring at a point is excellent, being a
localization and hence essentially of finite type. -/
@[ega "IV 7.8.3" "(ii), special case"]
private theorem isExcellent_stalk_spec {R : Type u} [CommRing R] (hR : IsExcellent R)
    (q : PrimeSpectrum R) : IsExcellent ((Spec (.of R)).presheaf.stalk q) := by
  let : q.asIdeal.IsPrime := q.isPrime
  have hloc : IsExcellent (Localization.AtPrime q.asIdeal) := by
    let : Algebra.EssFiniteType R (Localization.AtPrime q.asIdeal) :=
      Algebra.EssFiniteType.of_isLocalization _ q.asIdeal.primeCompl
    exact isExcellent_of_essFiniteType hR
  exact isExcellent_of_ringEquiv
    (Spec.stalkIso (.of R) q).commRingCatIsoToRingEquiv.symm hloc

/-- The local rings of a scheme locally of finite type over an affine base are essentially of
finite type over the local rings of the base, so they are excellent as soon as the latter are. -/
@[ega "IV 7.8.3" "(ii)"]
private theorem isExcellent_stalk_of_locallyOfFiniteType {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of R)) [LocallyOfFiniteType f] (z : Z)
    (hS : IsExcellent ((Spec (.of R)).presheaf.stalk (f.base z))) :
    IsExcellent (Z.presheaf.stalk z) := by
  algebraize [(f.stalkMap z).hom]
  have hess : Algebra.EssFiniteType ((Spec (.of R)).presheaf.stalk (f.base z))
      (Z.presheaf.stalk z) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f z
  exact isExcellent_of_essFiniteType hS

/-- The completion of an excellent normal Noetherian local ring is normal: an excellent ring is a
G-ring, so the map to the completion is regular, and normality ascends along a regular map. -/
@[ega "IV 7.8.3" "(v), special case"]
private theorem isNormalRing_adicCompletion_of_isExcellent (R : Type u) [CommRing R]
    [IsLocalRing R] (hR : IsNormalRing R) (hExcellent : IsExcellent R) :
    IsNormalRing (AdicCompletion (maximalIdeal R) R) := by
  let : IsNoetherianRing R := hExcellent.1.1
  have hreg : IsRegularRingHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
    isRegularRingHom_algebraMap_adicCompletion hExcellent.1.2.1 (maximalIdeal R)
  rw [isRegularRingHom_iff_of_eq_algebraMap _ rfl] at hreg
  exact isNormalRing_of_flat_of_isGeometricallyRegular_fiber R
    (AdicCompletion (maximalIdeal R) R) hR fun q _ => (hreg.2 q).2

/-! ### Tag 0BG7, clause (2) -/

/-- **Stacks Project, Tag 0BG7, clause (2).** For a Noetherian local ring `A` whose blowup of
`Spec A^` in the maximal ideal of the completion `A^` is normal, the completion of the local ring
of the blowup of `Spec A` in the maximal ideal of `A` is a normal domain at every closed point.

The hypothesis `hnormal` is [Stacks, Tag 0B4Z] for `A^`, registered in this development as
`isNormal_blowUp_maximalIdeal_rationalSingularitySituation`; in the source it is supplied by the
hypotheses that `A` is a normal Nagata domain of dimension two defining a rational singularity
whose completion is normal, and since this theorem assumes none of those it carries the tag's
conclusion as `hnormal`. -/
@[stacks 0BG7 "clause (2): the completion of the local ring at every closed point of the blowup \
of Spec(A) in the maximal ideal is a normal domain. Tag 0B4Z at the completion — normality of \
the blowup of Spec(A^) in the maximal ideal of A^ — is registered in this development as \
isNormal_blowUp_maximalIdeal_rationalSingularitySituation and carried here as the hypothesis \
`hnormal`, the source's hypotheses on A (normal Nagata domain of dimension two defining a \
rational singularity with normal completion) being exactly what that theorem consumes"]
public theorem isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hnormal : IsNormal (blowUp (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A))))
    (x : blowUp (maximalIdealSheaf A))
    (hx : IsClosed ({x} : Set (blowUp (maximalIdealSheaf A)))) :
    IsNormalDomain (AdicCompletion
      (maximalIdeal ((blowUp (maximalIdealSheaf A)).presheaf.stalk x))
      ((blowUp (maximalIdealSheaf A)).presheaf.stalk x)) := by
  classical
  let : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  let : IsLocallyNoetherian (Spec (.of (AdicCompletion (maximalIdeal A) A))) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  let : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _
      (by rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
  let : Flat (specMapAdicCompletion A) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  -- the blowup upstairs is the base change of the blowup downstairs
  obtain ⟨p, hsq⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap
    (specMapAdicCompletion A) (maximalIdealSheaf A)
  have hYnormal :
      IsNormal (blowUp ((maximalIdealSheaf A).comap (specMapAdicCompletion A))) := by
    rw [comap_maximalIdealSheaf_specMapAdicCompletion]
    exact hnormal
  -- a closed point of the blowup lies over the closed point of `Spec A`
  have hxclosed : (blowUpToBase (maximalIdealSheaf A)).base x =
      (⟨maximalIdeal A, inferInstance⟩ : PrimeSpectrum A) := by
    have himage : IsClosed ((blowUpToBase (maximalIdealSheaf A)).base ''
        ({x} : Set (blowUp (maximalIdealSheaf A)))) :=
      Scheme.Hom.isClosedMap (blowUpToBase (maximalIdealSheaf A)) _ hx
    have hsingleton : IsClosed
        ({(blowUpToBase (maximalIdealSheaf A)).base x} : Set (Spec (.of A))) := by
      simpa using himage
    exact PrimeSpectrum.ext (eq_maximalIdeal
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hsingleton))
  -- lift `x` to the blowup upstairs
  obtain ⟨z, hz⟩ := (PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := A) (B := AdicCompletion (maximalIdeal A) A))
    ((blowUpToBase (maximalIdealSheaf A)).base x)
  obtain ⟨y, -, hyx⟩ := Scheme.exists_preimage_of_isPullback hsq z x hz
  -- the completed local ring upstairs is normal
  have hexc : IsExcellent (AdicCompletion (maximalIdeal A) A) :=
    let : IsPrecomplete (maximalIdeal (AdicCompletion (maximalIdeal A) A))
        (AdicCompletion (maximalIdeal A) A) := inferInstance
    (isExcellent_of_standard_classes_and_finiteType.{u, u}).2.1 _
  have hupstairs : IsNormalRing (AdicCompletion
      (maximalIdeal ((blowUp ((maximalIdealSheaf A).comap
          (specMapAdicCompletion A))).presheaf.stalk y))
      ((blowUp ((maximalIdealSheaf A).comap
        (specMapAdicCompletion A))).presheaf.stalk y)) :=
    isNormalRing_adicCompletion_of_isExcellent _
      (Stacks.Models.isNormalRing_stalk hYnormal y)
      (isExcellent_stalk_of_locallyOfFiniteType
        (blowUpToBase ((maximalIdealSheaf A).comap (specMapAdicCompletion A))) y
        (isExcellent_stalk_spec hexc _))
  -- transport along the isomorphism of completions supplied by Tag 0BG5
  obtain ⟨e, -⟩ := exists_adicCompletion_ringEquiv_stalkMap_of_isPullback A
    (maximalIdeal A).fg_of_isNoetherianRing (blowUpToBase (maximalIdealSheaf A)) p
    (blowUpToBase ((maximalIdealSheaf A).comap (specMapAdicCompletion A)))
    hsq.flip y x hyx hxclosed
  let : IsLocallyNoetherian (blowUp (maximalIdealSheaf A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (maximalIdealSheaf A))
  obtain ⟨hdomain, hclosed⟩ := (IsNormalRing.congr e.symm hupstairs).of_isLocalRing
  exact ⟨hdomain, hclosed⟩

end AlgebraicGeometry

end
