module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Generic linear forms are nonzerodivisors

Let `R` be a commutative ring and `a_1, …, a_n ∈ R` elements whose only common annihilator is
`0`, i.e. the map `R → R^{⊕n}`, `x ↦ (x a_1, …, x a_n)` is injective. Then the linear form
`∑ a_i t_i` is a nonzerodivisor in `R[t_1, …, t_n]`. This is a particular case of McCoy's theorem.

## Main definitions

* `Stacks.GenericLinearForm.phi`: The `R`-linear map `R → R^{⊕n}`, `x ↦ (x a_1, …, x a_n)`.
* `Stacks.GenericLinearForm.linearForm`: The linear form `∑ a_i t_i` in `R[t_1, …, t_n]`.

## Main results

* `Stacks.GenericLinearForm.mccoy_core`: If `(∑ a_i t_i) g = 0` for some nonzero `g`, then some
  nonzero `r ∈ R` annihilates every `a_i`.
* `Stacks.GenericLinearForm.linearForm_mem_nonZeroDivisors`: If the only common annihilator of the
  `a_i` is `0`, then `∑ a_i t_i` is a nonzerodivisor.

## Implementation notes

The leading monomial of a polynomial is Mathlib's `MonomialOrder.degree` for the lexicographic
monomial order `MonomialOrder.lex`, in which smaller indices are more significant.
-/

open MvPolynomial

open scoped nonZeroDivisors

namespace Stacks.GenericLinearForm

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The `R`-linear map `φ : R → R^{⊕n}`, `φ(x) = (x a_1, ..., x a_n)`. -/
def phi (a : Fin n → R) : R →ₗ[R] (Fin n → R) where
  toFun x := fun i => x * a i
  map_add' x y := by ext i; simp [add_mul]
  map_smul' c x := by ext i; simp [mul_assoc]

/-- The `i`-th component of `phi a x` is `x * a i`. -/
@[simp]
theorem phi_apply (a : Fin n → R) (x : R) (i : Fin n) : phi a x i = x * a i := rfl

/-- The map `phi a` is injective if and only if the only common annihilator of all `a i` is
`0`. -/
theorem phi_injective_iff (a : Fin n → R) :
    Function.Injective (phi a) ↔ ∀ x : R, (∀ i, x * a i = 0) → x = 0 := by
  rw [injective_iff_map_eq_zero]
  simp [funext_iff]

/-- The linear form `f = ∑_{i=1}^n a_i t_i ∈ R[t_1, ..., t_n]`. -/
noncomputable def linearForm (a : Fin n → R) : MvPolynomial (Fin n) R :=
  ∑ i, C (a i) * X i

/-- The coefficient of `m` in `linearForm a * g` is `∑ i, a i * coeff m (X i * g)`. -/
theorem coeff_linearForm_mul (a : Fin n → R) (g : MvPolynomial (Fin n) R) (m : Fin n →₀ ℕ) :
    (linearForm a * g).coeff m = ∑ i, a i * (X i * g).coeff m := by
  rw [linearForm, Finset.sum_mul, coeff_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, coeff_C_mul]

/-- Moving one unit of exponent from index `i` to a more significant index `k < i` increases a
monomial in the lexicographic order. -/
theorem toLex_lt_add_single_sub_single {σ : Type*} [LinearOrder σ] {μ : σ →₀ ℕ} {k i : σ}
    (hki : k < i) : toLex μ < toLex (μ + Finsupp.single k 1 - Finsupp.single i 1) := by
  rw [Finsupp.Lex.lt_iff]
  refine ⟨k, fun j hj => ?_, ?_⟩
  · simp [ofLex_toLex, Finsupp.tsub_apply, Finsupp.add_apply, hj.ne, (hj.trans hki).ne]
  · simp [ofLex_toLex, Finsupp.tsub_apply, Finsupp.add_apply, hki.ne]

/-- If `linearForm a * g = 0` and every `a i` with `i < k` annihilates `g`, then `a k` annihilates
the lex-leading coefficient of `g`. -/
theorem mul_leadingCoeff_eq_zero (a : Fin n → R) (g : MvPolynomial (Fin n) R)
    (hfg : linearForm a * g = 0) (k : Fin n) (hsmall : ∀ i, i < k → C (a i) * g = 0) :
    a k * MonomialOrder.lex.leadingCoeff g = 0 := by
  show a k * g.coeff (MonomialOrder.lex.degree g) = 0
  have hzero : (linearForm a * g).coeff (MonomialOrder.lex.degree g + Finsupp.single k 1) = 0 := by
    simp [hfg]
  rw [coeff_linearForm_mul, Finset.sum_eq_single k] at hzero
  · rwa [add_comm (MonomialOrder.lex.degree g), coeff_X_mul] at hzero
  · intro i _ hik
    rcases hik.lt_or_gt with hlt | hgt
    · rw [← coeff_C_mul, show C (a i) * (X i * g) = X i * (C (a i) * g) by ring,
        hsmall i hlt, mul_zero, coeff_zero, Finsupp.zero_apply]
    · rw [coeff_X_mul', MonomialOrder.coeff_eq_zero_of_lt
        (MonomialOrder.lex_lt_iff.mpr (toLex_lt_add_single_sub_single hgt))]
      simp
  · simp

/-- If `c` annihilates the lex-leading coefficient of a nonzero polynomial `g`, then `C c * g` has
strictly smaller support than `g`. -/
theorem card_support_C_mul_lt (g : MvPolynomial (Fin n) R) (hg : g ≠ 0) {c : R}
    (hc : c * MonomialOrder.lex.leadingCoeff g = 0) :
    (C c * g).support.card < g.support.card := by
  refine Finset.card_lt_card ⟨fun ν hν => ?_, fun hsub => ?_⟩
  · rw [mem_support_iff, coeff_C_mul] at hν
    exact mem_support_iff.mpr (right_ne_zero_of_mul hν)
  · have := hsub (MonomialOrder.degree_mem_support (m := MonomialOrder.lex) hg)
    rw [mem_support_iff, coeff_C_mul] at this
    exact this hc

/-- If `g ≠ 0` and `(∑ aᵢ Xᵢ) * g = 0`, then there is a nonzero `r ∈ R` annihilating every
`aᵢ`. -/
theorem mccoy_core (a : Fin n → R) (g : MvPolynomial (Fin n) R) (hfg : linearForm a * g = 0)
    (hg : g ≠ 0) : ∃ r : R, r ≠ 0 ∧ ∀ i, r * a i = 0 := by
  suffices H : ∀ N : ℕ, ∀ g : MvPolynomial (Fin n) R, g.support.card = N →
      linearForm a * g = 0 → g ≠ 0 → ∃ r : R, r ≠ 0 ∧ ∀ i, r * a i = 0 from
    H _ g rfl hfg hg
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro g hcard hfg hg
    by_cases hall : ∀ i, C (a i) * g = 0
    · obtain ⟨μ, hμ⟩ := MvPolynomial.support_nonempty.mpr hg
      refine ⟨g.coeff μ, mem_support_iff.mp hμ, fun i => ?_⟩
      rw [mul_comm, ← coeff_C_mul, hall i, coeff_zero, Finsupp.zero_apply]
    · push Not at hall
      obtain ⟨i0, hi0⟩ := hall
      obtain ⟨k, hkne, hmin⟩ :=
        (wellFounded_lt (α := Fin n)).has_min {i | C (a i) * g ≠ 0} ⟨i0, hi0⟩
      have hsmall : ∀ i, i < k → C (a i) * g = 0 :=
        fun i hik => not_not.mp fun hne => hmin i hne hik
      exact ih _ (hcard ▸ card_support_C_mul_lt g hg
        (mul_leadingCoeff_eq_zero a g hfg k hsmall)) _ rfl
        (by rw [mul_left_comm, hfg, mul_zero]) hkne

/-- If `phi a` is injective, i.e. the only `x ∈ R` with `x a_i = 0` for all `i` is `x = 0`, then
`f = ∑ a_i t_i` is a nonzerodivisor in `R[t_1, ..., t_n]`. -/
theorem linearForm_mem_nonZeroDivisors (a : Fin n → R) (hinj : Function.Injective (phi a)) :
    linearForm a ∈ (MvPolynomial (Fin n) R)⁰ :=
  mem_nonZeroDivisors_iff_left.mpr fun g hg => by
    by_contra hne
    obtain ⟨r, hr0, hra⟩ := mccoy_core a g hg hne
    exact hr0 ((phi_injective_iff a).mp hinj r hra)

/-- **Stacks 068P**.
If the only `x ∈ R` with `x a_i = 0` for all `i` is `x = 0`, then `f = ∑ a_i t_i` is a
nonzerodivisor in `R[t_1, ..., t_n]`: every `g` with `f * g = 0` is zero. -/
@[stacks 068P]
theorem linearForm_isNonZeroDivisor (a : Fin n → R)
    (hinj : ∀ x : R, (∀ i, x * a i = 0) → x = 0) :
    ∀ g : MvPolynomial (Fin n) R, linearForm a * g = 0 → g = 0 := fun g hg =>
  mem_nonZeroDivisors_iff_left.mp
    (linearForm_mem_nonZeroDivisors a ((phi_injective_iff a).mpr hinj)) g hg

end Stacks.GenericLinearForm
