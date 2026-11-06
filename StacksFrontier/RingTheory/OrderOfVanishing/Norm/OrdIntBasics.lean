module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Lattice.Defs

@[expose] public section


open Ring

/-! ## The order of vanishing (Stacks 02MD)

Let `R` be a Noetherian local domain of dimension `1` with fraction field `K`. The order of
vanishing `ord_R : K* → ℤ` is the group homomorphism taking a nonzero `r ∈ R` to
`length_R (R / (r))`, extended to `K*` by `ord_R(x/y) = ord_R(x) - ord_R(y)`.

In Mathlib this is `Ring.ordFrac R : K →*₀ WithZero (Multiplicative ℤ)`, a monoid-with-zero
homomorphism sending `0` to `0`. For nonzero `x ∈ K*` the value `Ring.ordFrac R x` is a nonzero
element of `WithZero (Multiplicative ℤ)`, and the integer `ord_R(x)` is recovered by
`Multiplicative.toAdd (WithZero.unzero ...)`. The definition below packages that extraction into
an integer-valued order function.
-/

/-! ### Correctness of `ordInt`

The two statements below characterize `ordInt` as the order of vanishing: it is a group
homomorphism `K* → ℤ`, and on a nonzero `r ∈ R` it equals `length_R (R / (r))`, a length that
is finite under the standing hypotheses.
-/

/-- `ordInt` is additive on `K^*`, i.e. it is a group homomorphism to `Z`. -/
theorem ordInt_mul (R : Type*) [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Nontrivial R]
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordInt R (x * y) (mul_ne_zero hx hy) = ordInt R x hx + ordInt R y hy := by
  unfold ordInt
  rw [← toAdd_mul]
  congr 1
  rw [← WithZero.coe_inj]
  rw [WithZero.coe_mul]
  rw [WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero]
  exact map_mul (Ring.ordFrac R) x y

/-- On a nonzero `r : R`, the order of vanishing equals the length `length_R (R / (r))`.
Here `Module.length` is valued in `ℕ∞`; under the dimension-`1` Noetherian hypotheses this
length is finite, and `.toNat` recovers the integer.

No locality is required: the proof below does not use `[IsLocalRing R]`. Requiring it would
exclude real cases — `A / 𝔮` is *not* local for a height-one prime of a two-dimensional ring,
so a consumer working with a height-one prime of a surface could not apply this lemma. -/
theorem ordInt_algebraMap (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (r : R) (hr : r ≠ 0) (hr' : algebraMap R K r ≠ 0) :
    ordInt R (algebraMap R K r) hr' =
      ((Module.length R (R ⧸ Ideal.span {r})).toNat : ℤ) := by
  have helper : ∀ {w : WithZero (Multiplicative ℤ)} (h : w ≠ 0) (k : ℤ),
      w = ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
      Multiplicative.toAdd (WithZero.unzero h) = k := by
    intro w h k hw
    have : WithZero.unzero h = (Multiplicative.ofAdd k : Multiplicative ℤ) := by
      rw [← WithZero.coe_inj, WithZero.coe_unzero, hw]
    rw [this]; simp
  set n := (Module.length R (R ⧸ Ideal.span {r})).toNat with hn
  unfold ordInt
  apply helper
  rw [Ring.ordFrac_eq_ord R (x := r) hr]
  have hr0 : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hr
  have hord : Ring.ord R r = Module.length R (R ⧸ Ideal.span {r}) := rfl
  -- key: evaluate the monoid hom on a nonzero divisor with a known finite order.
  have hval : ∀ m : ℕ, Ring.ord R r = (m : ℕ∞) →
      Ring.ordMonoidWithZeroHom R r
        = ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro m hm
    simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hr0, ite_true,
        hm]
    rfl
  have hne : Ring.ord R r ≠ ⊤ := by
    intro htop
    have h0 : Ring.ordMonoidWithZeroHom R r = 0 := by
      simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hr0, ite_true,
        htop]
      rfl
    have hu : Ring.ordFrac R (K := K) (algebraMap R K r) ≠ 0 :=
      (hr'.isUnit.map (Ring.ordFrac R)).ne_zero
    rw [Ring.ordFrac_eq_ord R (x := r) hr, h0] at hu
    exact hu rfl
  have hcoe : Ring.ord R r = (n : ℕ∞) := by
    rw [hn, hord]; rw [hord] at hne; exact (ENat.natCast_toNat (by rw [← hord]; exact hne)).symm
  exact hval n hcoe

