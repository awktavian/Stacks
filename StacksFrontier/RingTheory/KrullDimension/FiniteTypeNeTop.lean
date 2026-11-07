module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# A finite-type algebra over a field has finite Krull dimension

## Main results

* `ringKrullDim_ne_top_of_finiteType`: an algebra of finite type over a field has finite Krull
  dimension.
-/

@[expose] public section

/-- A finite-type algebra over a field has finite Krull dimension. -/
theorem ringKrullDim_ne_top_of_finiteType {κ A : Type*} [Field κ] [CommRing A]
    [Algebra κ A] [Algebra.FiniteType κ A] : ringKrullDim A ≠ ⊤ := by
  obtain ⟨ι, _, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  have h := ringKrullDim_le_of_surjective f.toRingHom hf
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add] at h
  refine ne_top_of_le_ne_top ?_ h
  exact fun he ↦ (ENat.card_lt_top_of_finite (α := ι)).ne (WithBot.coe_eq_coe.mp he)
