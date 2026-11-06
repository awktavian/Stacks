module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Lattice.Defs
import StacksFrontier.RingTheory.OrderOfVanishing.Norm.OrdIntBasics
import StacksFrontier.RingTheory.OrderOfVanishing.Norm.CokerLenDevissage
import StacksFrontier.RingTheory.OrderOfVanishing.Norm.BaseChangeDetNorm
import StacksFrontier.RingTheory.OrderOfVanishing.Norm.LocalizationLengthSum


@[expose] public section


open Ring

/-- If `B` is a module-finite extension of a one-dimensional local domain `A`, with `A → B`
injective, then the fraction field `L` of `B` is finite-dimensional over the fraction field `K`
of `A`. -/
theorem finiteDimensional_fractionRing_of_finite
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    (hAB : Function.Injective (algebraMap A B)) :
    Module.Finite K L := by
  -- B is integral (hence algebraic) over A since it is module-finite.
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  -- The image of `A \ {0}` lies in `B \ {0}` (injectivity + domain).
  have hMN : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
    rintro x ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    have : a ≠ 0 := nonZeroDivisors.ne_zero ha
    rw [ne_eq, ← (algebraMap A B).map_zero]
    exact fun h => this (hAB h)
  -- Every nonzero `n : B` divides a nonzero element of `A` (it is algebraic over `A`):
  -- by `exists_smul_eq_mul`, `d • 1 = n * c` with `d ≠ 0`, so `n ∣ algebraMap A B d`.
  have hdvd : ∀ n ∈ nonZeroDivisors B,
      ∃ m ∈ Algebra.algebraMapSubmonoid B (nonZeroDivisors A), n ∣ m := by
    intro n hn
    obtain ⟨c, d, hd, hdc⟩ :=
      Algebra.IsAlgebraic.exists_smul_eq_mul A (1 : B) (b := n) (nonZeroDivisors.ne_zero hn)
    refine ⟨algebraMap A B d, ?_, ?_⟩
    · rw [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
      exact ⟨d, mem_nonZeroDivisors_of_ne_zero hd, rfl⟩
    · rw [Algebra.smul_def, mul_one] at hdc
      exact ⟨c, hdc⟩
  -- Hence inverting `A \ {0}` in `B` already produces all of `L = Frac B`.
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      (nonZeroDivisors B) hMN hdvd).mpr inferInstance
  -- `Module.Finite A B` localizes to `Module.Finite K L`.
  exact Module.Finite.of_isLocalization A B (nonZeroDivisors A)

-- `Ideal.inertiaDeg'` has no semantics-preserving replacement here: `Ideal.inertiaDeg` is a
-- different definition (residue fields of localizations), equal only under `LiesOver` plus
-- maximality, so migrating would change this statement.
set_option linter.deprecated false in
/-- **Stacks 02MJ.** The order of vanishing of the norm of `b` is the sum, over the maximal
ideals `v` of `B`, of the inertia degree of `v` times the order of vanishing of `b` in `B_v`.

The localization data for each maximal ideal of `B` is supplied as instance hypotheses: for
each `v : MaximalSpectrum B` the localization `Localization.AtPrime v.asIdeal` is a Noetherian
ring of Krull dimension at most `1`, carries an algebra structure to `L` compatible with
`B → L`, the `IsScalarTower` hypothesis pinning it down as the canonical localization map, and
is a fraction ring of `L`. These say exactly that each `B_{mᵢ}` is a one-dimensional Noetherian
local domain with fraction field `L`. -/
@[stacks 02MJ]
theorem ord_norm_eq_sum_inertiaDeg_mul_ord
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Fintype (MaximalSpectrum B)]
    [∀ v : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime v.asIdeal)]
    [∀ v : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime v.asIdeal)]
    [∀ v : MaximalSpectrum B, Algebra (Localization.AtPrime v.asIdeal) L]
    [∀ v : MaximalSpectrum B, IsScalarTower B (Localization.AtPrime v.asIdeal) L]
    [∀ v : MaximalSpectrum B, IsFractionRing (Localization.AtPrime v.asIdeal) L]
    (hAB : Function.Injective (algebraMap A B))
    (y : L) (hy : y ≠ 0)
    (x : K) (hx : x = Algebra.norm K y)
    (hx0 : x ≠ 0) :
    ordInt A x hx0 =
      ∑ v : MaximalSpectrum B,
        (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℤ) *
          ordInt (Localization.AtPrime v.asIdeal) y hy := by
  -- PROOF (Stacks Tag 02MJ).  Define F y := ordInt A (Nm_{L/K} y) and
  -- G y := Σ_v [κ(m_v):κ(m_A)] · ordInt(B_v) y.  Both are additive in y; reduce y to a ratio
  -- b/b' of elements of B (`IsFractionRing.div_surjective`), then on each b∈B both F and G equal
  -- length_A(B/bB) (the two analytic kernels 02MI/02M0), hence F = G.
  -- L/K is finite (B finite over A; named side-lemma).
  have hKL : Module.Finite K L := finiteDimensional_fractionRing_of_finite A B K L hAB
  have : FiniteDimensional K L := hKL
  have hnorm_ne : ∀ z : L, z ≠ 0 → Algebra.norm K z ≠ 0 :=
    fun z hz => Algebra.norm_ne_zero_iff.mpr hz
  have ordA_congr : ∀ (a a' : K) (ha : a ≠ 0) (ha' : a' ≠ 0),
      a = a' → ordInt A a ha = ordInt A a' ha' := by
    intro a a' ha ha' h; subst h; rfl
  set F : (z : L) → z ≠ 0 → ℤ := fun z hz => ordInt A (Algebra.norm K z) (hnorm_ne z hz) with hF
  set G : (z : L) → z ≠ 0 → ℤ := fun z hz =>
    ∑ v : MaximalSpectrum B,
      (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℤ) *
        ordInt (Localization.AtPrime v.asIdeal) z hz with hG
  have hFcongr : ∀ (a a' : L) (ha : a ≠ 0) (ha' : a' ≠ 0), a = a' → F a ha = F a' ha' := by
    intro a a' ha ha' h; subst h; rfl
  have hGcongr : ∀ (a a' : L) (ha : a ≠ 0) (ha' : a' ≠ 0), a = a' → G a ha = G a' ha' := by
    intro a a' ha ha' h; subst h; rfl
  -- F additive (ordInt_mul on A + multiplicativity of the norm).
  have hFmul : ∀ (z w : L) (hz : z ≠ 0) (hw : w ≠ 0),
      F (z * w) (mul_ne_zero hz hw) = F z hz + F w hw := by
    intro z w hz hw
    simp only [hF]
    rw [ordA_congr (Algebra.norm K (z * w)) (Algebra.norm K z * Algebra.norm K w)
        (hnorm_ne _ (mul_ne_zero hz hw)) (mul_ne_zero (hnorm_ne z hz) (hnorm_ne w hw))
        (map_mul (Algebra.norm K) z w)]
    rw [ordInt_mul A (Algebra.norm K z) (Algebra.norm K w) (hnorm_ne z hz) (hnorm_ne w hw)]
  -- G additive (ordInt_mul on each B_v, summed).
  have hGmul : ∀ (z w : L) (hz : z ≠ 0) (hw : w ≠ 0),
      G (z * w) (mul_ne_zero hz hw) = G z hz + G w hw := by
    intro z w hz hw
    simp only [hG]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [ordInt_mul (Localization.AtPrime v.asIdeal) z w hz hw, mul_add]
  -- key (b ∈ B case): F (b) = G (b), both equal length_A (B / bB).
  have key : ∀ (c : B) (hc : c ≠ 0) (hcL : algebraMap B L c ≠ 0),
      F (algebraMap B L c) hcL = G (algebraMap B L c) hcL := by
    intro c hc hcL
    have hnc : Algebra.norm K (algebraMap B L c) ≠ 0 := hnorm_ne _ hcL
    have h1 : F (algebraMap B L c) hcL = ((Module.length A (B ⧸ Ideal.span {c})).toNat : ℤ) := by
      simp only [hF]
      exact ordInt_norm_eq_length_quotient A B K L hAB c hc hnc
    have h2 : G (algebraMap B L c) hcL = ((Module.length A (B ⧸ Ideal.span {c})).toNat : ℤ) := by
      simp only [hG]
      exact sum_inertiaDeg_ordInt_eq_length_quotient A B L c hc (fun _ => hcL)
    rw [h1, h2]
  -- ratio representation y = bL / b'L with b, b' ∈ B nonzero.
  obtain ⟨b, b', hb'mem, hyeq⟩ := IsFractionRing.div_surjective (A := B) (K := L) y
  have hb'ne : b' ≠ 0 := nonZeroDivisors.ne_zero hb'mem
  have hb'L : algebraMap B L b' ≠ 0 := by
    rw [ne_eq, ← (algebraMap B L).map_zero]
    exact fun h => hb'ne (IsFractionRing.injective B L h)
  have hbeq : algebraMap B L b = y * algebraMap B L b' := by
    field_simp at hyeq; rw [mul_comm]; exact hyeq
  have hbL : algebraMap B L b ≠ 0 := by rw [hbeq]; exact mul_ne_zero hy hb'L
  have hbne : b ≠ 0 := by intro h; apply hbL; rw [h, (algebraMap B L).map_zero]
  -- additivity gives F(bL) = F y + F(b'L), G(bL) = G y + G(b'L).
  have hFy : F (algebraMap B L b) hbL = F y hy + F (algebraMap B L b') hb'L := by
    have h := hFmul y (algebraMap B L b') hy hb'L
    rw [hFcongr (algebraMap B L b) (y * algebraMap B L b') hbL (mul_ne_zero hy hb'L) hbeq]
    exact h
  have hGy : G (algebraMap B L b) hbL = G y hy + G (algebraMap B L b') hb'L := by
    have h := hGmul y (algebraMap B L b') hy hb'L
    rw [hGcongr (algebraMap B L b) (y * algebraMap B L b') hbL (mul_ne_zero hy hb'L) hbeq]
    exact h
  -- combine with key at b and b' to get F y = G y.
  have hFG_y : F y hy = G y hy := by
    have e1 : F (algebraMap B L b) hbL = G (algebraMap B L b) hbL := key b hbne hbL
    have e2 : F (algebraMap B L b') hb'L = G (algebraMap B L b') hb'L := key b' hb'ne hb'L
    omega
  have hxF : ordInt A x hx0 = F y hy := by simp only [hF]; subst hx; rfl
  rw [hxF, hFG_y]
