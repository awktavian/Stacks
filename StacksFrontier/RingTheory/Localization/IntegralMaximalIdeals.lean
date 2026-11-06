module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Integral

/-!
# Maximal ideals of a localization of an integral extension

Let `R → T` be an integral ring map, let `p` be a prime of `R` and let `L` be a localization of
`T` at the image of the complement of `p`. The primes of `L` are the primes of `T` disjoint from
that image, and among those the *maximal* ideals of `L` are exactly the ones coming from primes
of `T` lying over `p`.

## Main results

* `IsLocalization.disjoint_algebraMapSubmonoid_of_under_eq`: a prime of `T` lying over `p` is
  disjoint from the image of the complement of `p`.
* `IsLocalization.isMaximal_map_of_under_eq`: the ideal generated in `L` by a prime of `T` lying
  over `p` is maximal.
* `IsLocalization.under_under_eq_of_isMaximal`: a maximal ideal of `L` contracts to a prime of
  `T` lying over `p`.

## Implementation notes

The localization of `R` at `p` is not part of the data of the statements; each proof introduces
`Localization.AtPrime p` and makes `L` an algebra over it by `localizationAlgebra`, with
`isScalarTower_localizationAlgebra` for the commutativity of the resulting square and
`isIntegral_localization` for the integrality of `Localization.AtPrime p → L`. The two statements
are then the two halves of the correspondence, along an integral extension, between the maximal
ideals and the ideals contracting to the maximal ideal of a local ring.

Both conclusions are phrased with `Ideal.under`, so they compose along the tower `R → T → L`
without a `comap` of a composite appearing in the statement.
-/

@[expose] public section

namespace IsLocalization

variable {R T L : Type*} [CommRing R] [CommRing T] [CommRing L]
  [Algebra R T] [Algebra T L] [Algebra R L] [IsScalarTower R T L]
  (p : Ideal R) [p.IsPrime]
  [IsLocalization (Algebra.algebraMapSubmonoid T p.primeCompl) L]

/-- A prime of `T` lying over `p` is disjoint from the image in `T` of the complement of `p`. -/
public theorem disjoint_algebraMapSubmonoid_of_under_eq {q : Ideal T} (hq : q.under R = p) :
    Disjoint (Algebra.algebraMapSubmonoid T p.primeCompl : Set T) (q : Set T) := by
  rw [Set.disjoint_left]
  rintro - ⟨r, hr, rfl⟩ hmem
  exact hr (hq ▸ hmem)

variable [Algebra.IsIntegral R T]

/-- The localization `L` of `T` over the localization of `R` at `p` is a scalar tower over `R` and
is integral. -/
private theorem isScalarTower_isIntegral_localizationAlgebra :
    letI : Algebra (Localization.AtPrime p) L := localizationAlgebra p.primeCompl T
    IsScalarTower R (Localization.AtPrime p) L ∧ Algebra.IsIntegral (Localization.AtPrime p) L := by
  let : Algebra (Localization.AtPrime p) L := localizationAlgebra p.primeCompl T
  exact ⟨isScalarTower_localizationAlgebra p.primeCompl T, ⟨fun z => isIntegral_localization z⟩⟩

/-- **The maximal ideals of a localization of an integral extension.** If `q` is a prime of `T`
lying over `p`, the ideal it generates in the localization `L` of `T` at the image of the
complement of `p` is maximal. -/
public theorem isMaximal_map_of_under_eq {q : Ideal T} [q.IsPrime] (hq : q.under R = p) :
    (q.map (algebraMap T L)).IsMaximal := by
  let A := Localization.AtPrime p
  let : Algebra A L := localizationAlgebra p.primeCompl T
  obtain ⟨_, hi⟩ := isScalarTower_isIntegral_localizationAlgebra (R := R) (T := T) (L := L) p
  have : (q.map (algebraMap T L)).IsPrime :=
    isPrime_of_isPrime_disjoint _ _ q ‹q.IsPrime›
      (disjoint_algebraMapSubmonoid_of_under_eq p hq)
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap A L)
    (fun x => hi.isIntegral x) (q.map (algebraMap T L)) ?_
  have hle : p.map (algebraMap R A) ≤ (q.map (algebraMap T L)).under A := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change algebraMap A L (algebraMap R A r) ∈ q.map (algebraMap T L)
    rw [← IsScalarTower.algebraMap_apply R A L, IsScalarTower.algebraMap_apply R T L]
    have hrq : r ∈ q.under R := by rwa [hq]
    exact Ideal.mem_map_of_mem _ hrq
  rw [AtPrime.map_eq_maximalIdeal p A] at hle
  have heq : (q.map (algebraMap T L)).under A = IsLocalRing.maximalIdeal A :=
    le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) hle
  rw [show (q.map (algebraMap T L)).comap (algebraMap A L) =
    (q.map (algebraMap T L)).under A from rfl, heq]
  exact IsLocalRing.maximalIdeal.isMaximal A

/-- **The maximal ideals of a localization of an integral extension.** A maximal ideal of the
localization `L` of `T` at the image of the complement of `p` contracts to a prime of `T` lying
over `p`. -/
public theorem under_under_eq_of_isMaximal (Q : Ideal L) [Q.IsMaximal] :
    (Q.under T).under R = p := by
  let A := Localization.AtPrime p
  let : Algebra A L := localizationAlgebra p.primeCompl T
  obtain ⟨_, hi⟩ := isScalarTower_isIntegral_localizationAlgebra (R := R) (T := T) (L := L) p
  have : (Q.under A).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A L) (fun x => hi.isIntegral x) Q
  have hA : Q.under A = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal inferInstance
  rw [Ideal.under_under, ← Ideal.under_under (B := A), hA]
  exact AtPrime.under_maximalIdeal A p

end IsLocalization

end
