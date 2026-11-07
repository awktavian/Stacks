module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.PrincipalIdealDomain
public import StacksCore.Tactic.StacksAttribute

/-!
# Algebras integral over a field with no nontrivial idempotents

Let `K` be a field and let `A` be a `K`-algebra which is integral over `K`. Then `A` has Krull
dimension at most `0`, i.e. every prime of `A` is maximal. If moreover `A` is nontrivial and its
only idempotents are `0` and `1`, then `A` is a local ring, so that `Spec A` is a single point.

## Main results

* `Stacks.RingTheory.IntegralOverField.krullDimLE_zero`: an algebra integral over a field has
  Krull dimension at most `0`.
* `Stacks.RingTheory.IntegralOverField.isUnit_or_isNilpotent`: if the only idempotents of `A` are
  `0` and `1`, every element of `A` is a unit or nilpotent.
* `Stacks.RingTheory.IntegralOverField.isLocalRing_and_krullDimLE_zero`: such an `A`, if
  nontrivial, is local of dimension `0`, hence has a one-point spectrum.

## References

* [Stacks Project, Tag 0FD1](https://stacks.math.columbia.edu/tag/0FD1)
* [Stacks Project, Tag 00KH](https://stacks.math.columbia.edu/tag/00KH)
-/

@[expose] public section

open Polynomial

universe u v

namespace Stacks.RingTheory.IntegralOverField

section

variable {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]

/-- An algebra integral over a field has Krull dimension at most `0`: every prime is maximal. -/
theorem krullDimLE_zero [Algebra.IsIntegral K A] : Ring.KrullDimLE 0 A := by
  rw [Ring.krullDimLE_zero_iff]
  intro I hI
  refine Ideal.IsIntegral.isMaximal_of_isMaximal_under (R := K) I ?_
  have hp : (I.under K).IsPrime := Ideal.comap_isPrime _ _
  obtain h | h := (I.under K).eq_bot_or_top
  · rw [h]; exact Ideal.bot_isMaximal
  · exact absurd h hp.ne_top

/-- If `x` satisfies a polynomial over `K` whose constant coefficient is nonzero, then `x` is a
unit. -/
theorem isUnit_of_coeff_zero_ne_zero {x : A} {p : K[X]} (hpx : aeval x p = 0)
    (h0 : p.coeff 0 ≠ 0) : IsUnit x := by
  have key : x * aeval x p.divX = -algebraMap K A (p.coeff 0) := by
    have h : aeval x (X * p.divX + C (p.coeff 0)) = 0 := by rw [X_mul_divX_add]; exact hpx
    simp only [map_add, map_mul, aeval_X, aeval_C] at h
    linear_combination h
  refine isUnit_of_mul_isUnit_left (y := aeval x p.divX) ?_
  rw [key]
  exact ((isUnit_iff_ne_zero.mpr h0).map (algebraMap K A)).neg

/-- If the only idempotents of `A` are `0` and `1`, then every element of `A` integral over the
field `K` is either a unit or nilpotent. -/
theorem isUnit_or_isNilpotent (hidem : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) {x : A}
    (hx : IsIntegral K x) : IsUnit x ∨ IsNilpotent x := by
  obtain ⟨p, hpm, hpx⟩ := hx
  have hp : p ≠ 0 := hpm.ne_zero
  by_cases h0 : p.coeff 0 = 0
  · have hmpos : 0 < p.rootMultiplicity 0 := (rootMultiplicity_pos hp).mpr (by
      simpa [IsRoot, ← coeff_zero_eq_eval_zero] using h0)
    obtain ⟨m, q, hmpos, hpq, hq0⟩ :
        ∃ (m : ℕ) (q : K[X]), 0 < m ∧ X ^ m * q = p ∧ q.eval 0 ≠ 0 := by
      refine ⟨p.rootMultiplicity 0, p /ₘ (X - C (0 : K)) ^ p.rootMultiplicity 0, hmpos, ?_,
        eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hp⟩
      simpa using p.pow_mul_divByMonic_rootMultiplicity_eq 0
    have hXq : ¬ (X : K[X]) ∣ q := by
      rw [Polynomial.X_dvd_iff]
      simpa [coeff_zero_eq_eval_zero] using hq0
    have hcop : IsCoprime ((X : K[X]) ^ m) q :=
      (Polynomial.prime_X.coprime_iff_not_dvd.mpr hXq).pow_left
    obtain ⟨u, v, huv⟩ := hcop
    have key : x ^ m * aeval x q = 0 := by
      have h : aeval x (X ^ m * q) = 0 := by rw [hpq]; exact hpx
      simpa using h
    have hed : aeval x u * x ^ m + aeval x v * aeval x q = 1 := by
      have h : aeval x (u * X ^ m + v * q) = 1 := by rw [huv]; simp
      simpa using h
    have hmul : (aeval x u * x ^ m) * (aeval x v * aeval x q) = 0 := by
      have h : (aeval x u * x ^ m) * (aeval x v * aeval x q)
          = (aeval x u * aeval x v) * (x ^ m * aeval x q) := by ring
      rw [h, key, mul_zero]
    have hidem_e : IsIdempotentElem (aeval x u * x ^ m) := by
      have h := congrArg (fun z ↦ (aeval x u * x ^ m) * z) hed
      simp only [mul_add, mul_one] at h
      rw [hmul, add_zero] at h
      exact h
    obtain he | he := hidem (aeval x u * x ^ m) hidem_e
    · right
      obtain ⟨w, hw⟩ : ∃ w, aeval x q * w = 1 := by
        rw [he, zero_add] at hed
        exact ⟨aeval x v, by rw [mul_comm]; exact hed⟩
      refine ⟨m, ?_⟩
      have h2 : x ^ m * aeval x q * w = 0 := by rw [key, zero_mul]
      rwa [mul_assoc, hw, mul_one] at h2
    · left
      have hu : IsUnit (x ^ m) := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact he)
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      rw [pow_succ, mul_comm] at hu
      exact isUnit_of_mul_isUnit_left hu
  · exact Or.inl (isUnit_of_coeff_zero_ne_zero hpx (by simpa using h0))

/-- A nontrivial algebra integral over a field whose only idempotents are `0` and `1` is a local
ring of Krull dimension `0`;  equivalently, its spectrum is a single point. -/
theorem isLocalRing_and_krullDimLE_zero [Nontrivial A] [Algebra.IsIntegral K A]
    (hidem : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Ring.KrullDimLE 0 A ∧ IsLocalRing A := by
  refine ((Ring.krullDimLE_zero_and_isLocalRing_tfae A).out 3 1 rfl rfl).mp fun x ↦ ?_
  refine ⟨fun hnil hunit ↦ ?_, fun hunit ↦ ?_⟩
  · obtain ⟨n, hn⟩ := hnil
    have h1 : IsUnit (x ^ n) := hunit.pow n
    rw [hn, isUnit_zero_iff] at h1
    exact zero_ne_one h1
  · exact (isUnit_or_isNilpotent hidem
      (Algebra.IsIntegral.isIntegral (R := K) x)).resolve_left hunit

/-- The spectrum of a nontrivial algebra integral over a field whose only idempotents are `0`
and `1` is a subsingleton. -/
theorem subsingleton_primeSpectrum [Nontrivial A] [Algebra.IsIntegral K A]
    (hidem : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) : Subsingleton (PrimeSpectrum A) :=
  have h := isLocalRing_and_krullDimLE_zero (K := K) hidem
  have := h.1
  have := h.2
  Ring.KrullDimLE.subsingleton_primeSpectrum A

end

/-- If `φ : F →+* B` is an integral ring homomorphism out of a field, then `B` has Krull dimension
at most `0`. -/
theorem krullDimLE_zero_of_isIntegral {F B : Type*} [Field F] [CommRing B] (φ : F →+* B)
    (hφ : φ.IsIntegral) : Ring.KrullDimLE 0 B := by
  let := φ.toAlgebra
  have : Algebra.IsIntegral F B := algebraMap_isIntegral_iff.mp hφ
  exact krullDimLE_zero (K := F)

/-- If `φ : F →+* B` is an integral ring homomorphism out of a field and `B` is nontrivial with
no idempotents other than `0` and `1`, then the spectrum of `B` is a subsingleton. -/
theorem subsingleton_primeSpectrum_of_isIntegral {F B : Type*} [Field F] [CommRing B]
    [Nontrivial B] (φ : F →+* B) (hφ : φ.IsIntegral)
    (hidem : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : Subsingleton (PrimeSpectrum B) := by
  let := φ.toAlgebra
  have : Algebra.IsIntegral F B := algebraMap_isIntegral_iff.mp hφ
  exact subsingleton_primeSpectrum (K := F) hidem

end Stacks.RingTheory.IntegralOverField
