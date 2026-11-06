module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.List.Indexes
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# A prime of a polynomial ring in standard form after a finite change of coordinates

Let `k` be a field, let `q ⊆ k[x_0, …, x_{n-1}]` be a prime ideal and let `r` be the
transcendence degree over `k` of the residue field `κ(q)`. Then there is a finite `k`-algebra
endomorphism `φ` of `k[x_0, …, x_{n-1}]` with `φ⁻¹(q) = (x_r, …, x_{n-1})`.

## Main results

* `Stacks.PolynomialRing.PrimeStandardForm.solution` and
  `MvPolynomial.exists_finite_comap_eq_span_X_image_of_trdeg_eq`: if
  `Algebra.trdeg k q.ResidueField = r`, there is a finite `φ` with
  `q.comap φ = Ideal.span (X '' {i | r ≤ (i : ℕ)})`.

## References

* [StacksProject 051P](https://stacks.math.columbia.edu/tag/051P)
-/

@[expose] public section

namespace Stacks.PolynomialRing.PrimeStandardForm



open Polynomial MvPolynomial Ideal RingHom List

/-- Pin-shim for the rc4 Mathlib polynomial API: the standalone exponent-first
`MvPolynomial.coeff s p` is gone (the coefficient is now the projection
`AddMonoidAlgebra.coeff p` of the polynomial), so re-export the old spelling
`coeff s p` locally. Statements in this file are unchanged by this alias. -/
private abbrev coeff {σ R : Type _} [CommSemiring R] (s : σ →₀ ℕ) (p : MvPolynomial σ R) : R :=
  AddMonoidAlgebra.coeff p s

section Tilt

open Nat

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

/-- A bound strictly larger than every exponent occurring in `f`. -/
local notation3 "up" => 2 + f.totalDegree

variable {f v} in
private lemma lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

/-- The exponents of Nagata's substitution: `i ↦ up ^ i`. -/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- Nagata's substitution `X i ↦ X i + c • X 0 ^ r i` for `i ≠ 0`, fixing `X 0`. -/
private noncomputable abbrev tilt1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

private lemma tilt1_comp_tilt1_neg (c : k) :
    (tilt1 f c).comp (tilt1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

/-- Nagata's substitution as an algebra automorphism. -/
private noncomputable abbrev tilt := AlgEquiv.ofAlgHom (tilt1 f 1) (tilt1 f (-1))
  (tilt1_comp_tilt1_neg f 1) (by simpa using tilt1_comp_tilt1_neg f (-1))

private lemma sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h

private lemma degreeOf_zero_tilt {a : k} (ha : a ≠ 0) : ((tilt f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, ite_eq_left,
    Fin.succ_ne_zero, ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ,
    algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

/-- The tilt sends distinct monomials of `f` to polynomials of distinct degrees in `X 0`. -/
private lemma degreeOf_tilt_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (tilt f <| monomial v <| coeff v f).degreeOf 0 ≠
    (tilt f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_tilt _ _ <| mem_support_iff.mp hv,
    degreeOf_zero_tilt _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

private lemma leadingCoeff_finSuccEquiv_tilt :
    (finSuccEquiv k n ((tilt f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((tilt1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, ite_eq_right h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

/-- Nagata's tilting lemma: after the substitution `tilt f`, the nonzero polynomial `f` has an
invertible leading coefficient as a polynomial in `X 0`. -/
private lemma isUnit_leadingCoeff_finSuccEquiv_tilt (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (tilt f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (tilt f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((tilt f) (h x))).degree <
      (finSuccEquiv k n ((tilt f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_tilt_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n ((tilt f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((tilt f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((tilt f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_tilt] at coeff
  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

end Tilt

section Finiteness

/-- An isomorphism is a finite ring map. -/
private lemma finite_of_algEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) : e.toAlgHom.toRingHom.Finite :=
  RingHom.Finite.of_surjective _ e.surjective

/-- Finiteness of algebra maps is stable under composition. -/
private lemma finite_comp {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] {f : A →ₐ[R] B} {g : B →ₐ[R] C}
    (hf : f.toRingHom.Finite) (hg : g.toRingHom.Finite) : (g.comp f).toRingHom.Finite :=
  hg.comp hf

/-- A ring map whose target is generated, as an algebra, by a single integral element is finite:
`x` is exhibited as a root of the monic `p`, and `hgen` says that every element of the target is
a polynomial in `x` with coefficients pulled back along `f`. -/
@[ega "0 1.0.5" "special case"]
private lemma finite_of_isIntegralElem {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {x : S} {p : R[X]} (hp : p.Monic) (hpx : Polynomial.eval₂ f x p = 0)
    (hgen : ∀ y : S, ∃ q : R[X], Polynomial.eval₂ f x q = y) : f.Finite := by
  algebraize [f]
  have hx : IsIntegral R x := ⟨p, hp, hpx⟩
  have htop : Algebra.adjoin R {x} = ⊤ := top_le_iff.mp fun y _ ↦ by
    obtain ⟨q, hq⟩ := hgen y
    rw [← hq]
    exact Polynomial.aeval_mem_adjoin_singleton R x (p := q)
  have hfg := hx.fg_adjoin_singleton
  rw [htop] at hfg
  exact Module.finite_def.2 (by simpa using hfg)

/-- Substituting a monic polynomial of positive degree for the variable is a finite ring
map. -/
private lemma finite_aeval_of_monic {A : Type*} [CommRing A] [Nontrivial A] {F : A[X]}
    (hF : F.Monic)
    (hd : 0 < F.natDegree) :
    (Polynomial.aeval F : A[X] →ₐ[A] A[X]).toRingHom.Finite := by
  have hfC : (Polynomial.aeval F : A[X] →ₐ[A] A[X]).toRingHom.comp
      (Polynomial.C : A →+* A[X]) = (Polynomial.C : A →+* A[X]) := by
    ext a; simp
  refine finite_of_isIntegralElem _ (x := (Polynomial.X : A[X]))
    (p := F.map (Polynomial.C : A →+* A[X]) - Polynomial.C (Polynomial.X : A[X])) ?_ ?_ ?_
  · refine (hF.map (Polynomial.C : A →+* A[X])).sub_of_left ?_
    refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    rw [hF.degree_map]
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hd
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_map, hfC, Polynomial.eval₂_C_X,
      Polynomial.eval₂_C, sub_eq_zero]
    simp
  · exact fun y ↦ ⟨y.map (Polynomial.C : A →+* A[X]), by
      rw [Polynomial.eval₂_map, hfC, Polynomial.eval₂_C_X]⟩

/-- Applying a finite ring map to the coefficients of a polynomial is again finite. -/
private lemma finite_mapAlgHom {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {χ : A →ₐ[R] B} (h : χ.toRingHom.Finite) :
    (Polynomial.mapAlgHom χ).toRingHom.Finite := by
  classical
  algebraize [χ.toRingHom, (Polynomial.mapAlgHom χ).toRingHom]
  obtain ⟨s, hs⟩ := Module.finite_def.1 (inferInstance : Module.Finite A B)
  set t : Set B[X] := ↑(s.image (Polynomial.C : B →+* B[X])) with ht
  have key : ∀ (n : ℕ) (b : B), (Polynomial.monomial n b : B[X]) ∈ Submodule.span A[X] t := by
    intro n b
    have hb : b ∈ Submodule.span A (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem c hc =>
        have : (Polynomial.X ^ n : A[X]) • (Polynomial.C c : B[X]) =
            Polynomial.monomial n c := by
          rw [Algebra.smul_def]
          change Polynomial.map (χ : A →+* B) (Polynomial.X ^ n) * Polynomial.C c = _
          rw [Polynomial.map_pow, Polynomial.map_X, mul_comm,
            Polynomial.C_mul_X_pow_eq_monomial]
        rw [← this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simpa [ht] using hc))
    | zero => simp
    | add u v _ _ hu hv =>
        rw [show (Polynomial.monomial n (u + v) : B[X]) =
          Polynomial.monomial n u + Polynomial.monomial n v from map_add _ _ _]
        exact Submodule.add_mem _ hu hv
    | smul a u _ hu =>
        have : (Polynomial.C a : A[X]) • (Polynomial.monomial n u : B[X]) =
            Polynomial.monomial n (a • u) := by
          rw [Algebra.smul_def]
          change Polynomial.map (χ : A →+* B) (Polynomial.C a) * Polynomial.monomial n u = _
          rw [Polynomial.map_C, Polynomial.C_mul_monomial, Algebra.smul_def]
          rfl
        rw [← this]
        exact Submodule.smul_mem _ _ hu
  exact Module.finite_def.2 ⟨s.image (Polynomial.C : B →+* B[X]), top_le_iff.mp fun y _ ↦
    Polynomial.induction_on' y (fun u v hu hv ↦ Submodule.add_mem _ hu hv) key⟩

end Finiteness

section Contraction

/-- Contracting along a composite of algebra maps is contracting one after the other. -/
private lemma comap_comp {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) (I : Ideal C) :
    I.comap (g.comp f) = (I.comap g).comap f := rfl

/-- For an ideal `Q` of `A[X]` containing `F`, the preimage of `Q` under `X ↦ F` consists of the
polynomials whose constant coefficient lies in `Q ∩ A`. -/
private lemma comap_aeval_of_mem {A : Type*} [CommRing A] {Q : Ideal A[X]} {F : A[X]}
    (hF : F ∈ Q) :
    Q.comap (Polynomial.aeval F : A[X] →ₐ[A] A[X]) =
      (Q.comap (Polynomial.C : A →+* A[X])).comap (Polynomial.constantCoeff) := by
  have key : (Ideal.Quotient.mkₐ A Q).comp (Polynomial.aeval F : A[X] →ₐ[A] A[X])
      = (Ideal.Quotient.mkₐ A Q).comp (Polynomial.aeval (0 : A[X])) :=
    Polynomial.algHom_ext (by simp [Ideal.Quotient.eq_zero_iff_mem.2 hF])
  ext y
  have h1 : Ideal.Quotient.mk Q ((Polynomial.aeval F : A[X] →ₐ[A] A[X]) y)
      = Ideal.Quotient.mk Q (Polynomial.C (Polynomial.constantCoeff y)) := by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.constantCoeff_apply]
      using AlgHom.congr_fun key y
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap,
    ← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem, h1]

/-- Coefficientwise application of `χ` commutes with taking the constant coefficient. -/
private lemma comap_mapAlgHom_comap_constantCoeff {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (χ : A →ₐ[R] B) (h : Ideal B) :
    (h.comap (Polynomial.constantCoeff)).comap (Polynomial.mapAlgHom χ) =
      (h.comap χ).comap (Polynomial.constantCoeff) := by
  ext p
  simp [Ideal.mem_comap, Polynomial.constantCoeff_apply, Polynomial.coeff_map]

/-- The ideal of polynomials whose constant coefficient lies in `h`. -/
private lemma comap_constantCoeff_eq {A : Type*} [CommRing A] (h : Ideal A) :
    h.comap (Polynomial.constantCoeff) =
      Ideal.map (Polynomial.C : A →+* A[X]) h ⊔ Ideal.span {(Polynomial.X : A[X])} := by
  refine le_antisymm (fun p hp ↦ ?_) (sup_le ?_ ?_)
  · rw [Ideal.mem_comap, Polynomial.constantCoeff_apply] at hp
    rw [← Polynomial.X_mul_divX_add p]
    exact Ideal.add_mem _
      (Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)))
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp [Ideal.mem_comap, ha]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simp

/-- The first `d + 1` variables of `k[x_0, …, x_m]` are `x_0` together with the images of the
first `d` variables of `k[x_0, …, x_{m-1}]` under `Fin.succ`. -/
private lemma setOf_lt_succ_eq_insert (m d : ℕ) :
    {i : Fin (m + 1) | (i : ℕ) < d + 1} = insert 0 (Fin.succ '' {i : Fin m | (i : ℕ) < d}) := by
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_image]
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨j, by simpa [Fin.val_succ] using h, rfl⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · simp
    · simpa [Fin.val_succ] using hj

/-- `MvPolynomial.finSuccEquiv` carries the ideal generated by the first `e + 1` variables of
`k[x_0, …, x_m]` to the ideal of polynomials over `k[x_0, …, x_{m - 1}]` whose constant
coefficient lies in the ideal generated by the first `e` variables. -/
private lemma map_finSuccEquiv_span_X_image {k : Type*} [CommRing k] {m e : ℕ} :
    Ideal.map ((finSuccEquiv k m).toAlgHom)
        (Ideal.span (X '' {i : Fin (m + 1) | (i : ℕ) < e + 1}))
      = Ideal.comap Polynomial.constantCoeff
          (Ideal.span (X '' {i : Fin m | (i : ℕ) < e})) := by
  rw [Ideal.map_span, comap_constantCoeff_eq, Ideal.map_span, setOf_lt_succ_eq_insert,
    Set.image_insert_eq, Set.image_insert_eq, Ideal.span_insert, sup_comm]
  congr 1
  · rw [← Set.image_comp, ← Set.image_comp, ← Set.image_comp]
    congr 1
    funext i
    simp [finSuccEquiv_X_succ]
  · rw [show ((finSuccEquiv k m).toAlgHom) (X 0) = (Polynomial.X : (MvPolynomial (Fin m) k)[X])
      from finSuccEquiv_X_zero]

/-- The form of `map_finSuccEquiv_span_X_image` used in the induction: pulling back along
`MvPolynomial.finSuccEquiv` the polynomials whose constant coefficient lies in the ideal
generated by the first `e` variables gives the ideal generated by the first `e + 1`. -/
private lemma comap_finSuccEquiv_comap_constantCoeff {k : Type*} [CommRing k] {m e : ℕ} :
    Ideal.comap ((finSuccEquiv k m).toAlgHom)
        (Ideal.comap Polynomial.constantCoeff
          (Ideal.span (X '' {i : Fin m | (i : ℕ) < e})))
      = Ideal.span (X '' {i : Fin (m + 1) | (i : ℕ) < e + 1}) := by
  rw [← map_finSuccEquiv_span_X_image]
  exact Ideal.comap_map_of_bijective _ (finSuccEquiv k m).bijective

/-- Reversing the coordinates turns the first `n - r` variables into the last `n - r`. -/
private lemma image_revPerm_setOf_lt {n r : ℕ} (h : r ≤ n) :
    (Fin.revPerm : Equiv.Perm (Fin n)) '' {i : Fin n | (i : ℕ) < n - r} =
      {i : Fin n | r ≤ (i : ℕ)} := by
  ext i
  simp only [Set.mem_image, Set.mem_ofPred_eq, Fin.revPerm_apply]
  refine ⟨?_, fun hi ↦ ⟨Fin.revPerm i, ?_, by simp⟩⟩
  · rintro ⟨j, hj, rfl⟩
    have := j.isLt
    simpa [Fin.val_rev] using by omega
  · have := i.isLt
    simpa [Fin.revPerm_apply, Fin.val_rev] using by omega

/-- Renaming the variables along a permutation `e` carries the ideal generated by the variables
indexed by `s` to the one generated by the variables indexed by `e '' s`. -/
private lemma map_renameEquiv_span_X_image {k : Type*} [CommRing k] {ι : Type*}
    (e : Equiv.Perm ι) (s : Set ι) :
    Ideal.map (renameEquiv k e).toAlgHom (Ideal.span (X '' s)) = Ideal.span (X '' (e '' s)) := by
  rw [Ideal.map_span, ← Set.image_comp, ← Set.image_comp]
  simp [Function.comp_def]

/-- The contracted form of `map_renameEquiv_span_X_image`. -/
private lemma comap_renameEquiv_span_X_image {k : Type*} [CommRing k] {ι : Type*}
    (e : Equiv.Perm ι) (s : Set ι) :
    Ideal.comap (renameEquiv k e).toAlgHom (Ideal.span (X '' s))
      = Ideal.span (X '' (e.symm '' s)) := by
  have h := map_renameEquiv_span_X_image (k := k) e (e.symm '' s)
  rw [Equiv.image_symm_image] at h
  rw [← h]
  exact Ideal.comap_map_of_bijective _ (renameEquiv k e).bijective

end Contraction

section Trdeg

/-- An injective algebraic extension `R → S` of a domain `R` over a field `k` does not change the
transcendence degree over `k`. -/
private lemma trdeg_eq_of_isAlgebraic {k R S : Type u} [Field k] [CommRing R]
    [CommRing S] [NoZeroDivisors S] [Nontrivial R] [Algebra k R] [Algebra k S] [Algebra R S]
    [IsScalarTower k R S] [Algebra.IsAlgebraic R S] (hinj : Function.Injective (algebraMap R S)) :
    Algebra.trdeg k S = Algebra.trdeg k R := by
  have : FaithfulSMul k R :=
    (faithfulSMul_iff_algebraMap_injective k R).2 (algebraMap k R).injective
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hinj
  rw [← trdeg_add_eq k R (A := S), trdeg_eq_zero_iff.2 ‹Algebra.IsAlgebraic R S›, add_zero]

/-- The residue field of a prime `q` has the same transcendence degree as the quotient domain
`A ⧸ q`. -/
private lemma trdeg_residueField {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    (q : Ideal A) [q.IsPrime] :
    Algebra.trdeg k q.ResidueField = Algebra.trdeg k (A ⧸ q) := by
  have : Algebra.IsAlgebraic (A ⧸ q) q.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ q))
  exact trdeg_eq_of_isAlgebraic q.injective_algebraMap_quotient_residueField

/-- The transcendence degree of the residue field of a prime of a polynomial ring in `n`
variables is at most `n`. -/
private lemma trdeg_residueField_le {k : Type u} [Field k] {n : ℕ}
    (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] :
    Algebra.trdeg k q.ResidueField ≤ (n : Cardinal.{u}) := by
  rw [trdeg_residueField]
  refine le_trans (trdeg_le_of_surjective (Ideal.Quotient.mkₐ k q)
    Ideal.Quotient.mk_surjective) ?_
  simp

/-- The residue field of `(0)` in `k[x_0, …, x_{n-1}]` has transcendence degree `n`. -/
private lemma trdeg_residueField_bot (k : Type u) [Field k] (n : ℕ) :
    Algebra.trdeg k (⊥ : Ideal (MvPolynomial (Fin n) k)).ResidueField = (n : Cardinal.{u}) := by
  have hn : Algebra.trdeg k (MvPolynomial (Fin n) k) = (n : Cardinal.{u}) := by simp
  have hb : Function.Bijective (Ideal.Quotient.mkₐ k (⊥ : Ideal (MvPolynomial (Fin n) k))) :=
    (Ideal.Quotient.mk_bijective_iff_eq_bot _).2 rfl
  rw [trdeg_residueField, ← hn]
  exact le_antisymm (trdeg_le_of_surjective _ hb.2) (trdeg_le_of_injective _ hb.1)

/-- Transcendence degrees of residue fields are transported by an algebra isomorphism. -/
private lemma trdeg_residueField_eq_of_comap {k : Type u} [Field k] {A B : Type u} [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (q₀ : Ideal A) [q₀.IsPrime]
    (q : Ideal B) [q.IsPrime] (hq : q₀ = q.comap e.toAlgHom) :
    Algebra.trdeg k q₀.ResidueField = Algebra.trdeg k q.ResidueField :=
  (Ideal.residueFieldAlgEquiv q₀ q e hq).trdeg_eq

/-- If `B ⧸ q` is a finite module over the image of `A ⧸ p`, then the two residue fields have the
same transcendence degree over `k`. -/
private lemma trdeg_residueField_eq_of_finite {k : Type u} [Field k] {A B : Type u} [CommRing A]
    [CommRing B] (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [Algebra k A] [Algebra k B]
    (ι : (A ⧸ p) →ₐ[k] (B ⧸ q)) (hinj : Function.Injective ι) (hfin : ι.toRingHom.Finite) :
    Algebra.trdeg k p.ResidueField = Algebra.trdeg k q.ResidueField := by
  rw [trdeg_residueField, trdeg_residueField]
  algebraize [ι.toRingHom]
  have : IsScalarTower k (A ⧸ p) (B ⧸ q) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  have : Algebra.IsAlgebraic (A ⧸ p) (B ⧸ q) := Algebra.IsIntegral.isAlgebraic
  exact (trdeg_eq_of_isAlgebraic hinj).symm

/-- If the prime `Q ⊆ A[X]` contains a monic polynomial, then its contraction `p = Q ∩ A` has a
residue field of the same transcendence degree over `k`. -/
private lemma trdeg_residueField_comap_C {k : Type u} [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (Q : Ideal A[X]) [Q.IsPrime] {F : A[X]} (hF : F.Monic) (hFQ : F ∈ Q) :
    Algebra.trdeg k (Q.comap (Polynomial.C : A →+* A[X])).ResidueField
      = Algebra.trdeg k Q.ResidueField := by
  have : Algebra.IsIntegral A (A[X] ⧸ Q) :=
    Algebra.isIntegral_def.2 fun x ↦ hF.quotient_isIntegral hFQ x
  have : Algebra.FiniteType A (A[X] ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A Q) Ideal.Quotient.mk_surjective
  have : Module.Finite A (A[X] ⧸ Q) := Algebra.IsIntegral.finite
  set ι : (A ⧸ Q.comap (Polynomial.C : A →+* A[X])) →ₐ[k] (A[X] ⧸ Q) :=
    Ideal.quotientMapₐ Q (Polynomial.CAlgHom : A →ₐ[k] A[X]) le_rfl
  have hιmk : ∀ a : A, ι (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk Q (Polynomial.C a) :=
    fun _ ↦ rfl
  refine trdeg_residueField_eq_of_finite _ Q ι ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hιmk, Ideal.Quotient.eq_zero_iff_mem] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_comap.2 ha)
  · algebraize [ι.toRingHom]
    have : IsScalarTower A (A ⧸ Q.comap (Polynomial.C : A →+* A[X])) (A[X] ⧸ Q) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ (hιmk x).symm
    exact Module.Finite.of_restrictScalars_finite A _ (A[X] ⧸ Q)

end Trdeg

section Induction

/-- A monic polynomial lying in a proper ideal is nonconstant. -/
private lemma natDegree_pos_of_monic_of_mem {A : Type*} [CommRing A] {Q : Ideal A[X]}
    (hQ : Q ≠ ⊤) {F : A[X]} (hF : F.Monic) (hFQ : F ∈ Q) : 0 < F.natDegree :=
  Nat.pos_of_ne_zero fun h0 ↦ hQ <| Ideal.eq_top_of_isUnit_mem Q hFQ <| by
    simp [eq_one_of_monic_natDegree_zero hF h0]

/-- A nonzero prime `q` of `k[x_0, …, x_m]` contains a polynomial monic of positive degree in
the distinguished variable, after a `k`-algebra isomorphism
`ε : k[x_1, …, x_m][X] ≃ k[x_0, …, x_m]`. -/
private lemma exists_monic_natDegree_pos_mem_comap {k : Type u} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin (m + 1)) k)) [q.IsPrime] (hq : q ≠ ⊥) :
    ∃ (ε : (MvPolynomial (Fin m) k)[X] ≃ₐ[k] MvPolynomial (Fin (m + 1)) k)
      (F : (MvPolynomial (Fin m) k)[X]),
      F.Monic ∧ 0 < F.natDegree ∧ F ∈ q.comap ε.toAlgHom := by
  obtain ⟨f, hfq, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
  have hu := isUnit_leadingCoeff_finSuccEquiv_tilt f hf0
  set A := MvPolynomial (Fin m) k
  set ε : A[X] ≃ₐ[k] MvPolynomial (Fin (m + 1)) k :=
    (finSuccEquiv k m).symm.trans (tilt f).symm
  set F : A[X] := (↑hu.unit⁻¹ : A) • finSuccEquiv k m (tilt f f) with hF
  have hFm : F.Monic := by
    simpa [hF, Units.smul_def] using monic_of_isUnit_leadingCoeff_inv_smul hu
  have hFQ : F ∈ q.comap ε.toAlgHom := by
    refine Submodule.smul_of_tower_mem _ _ ?_
    change (tilt f).symm ((finSuccEquiv k m).symm (finSuccEquiv k m (tilt f f))) ∈ q
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
    exact hfq
  have hQ : (q.comap ε.toAlgHom).IsPrime := Ideal.comap_isPrime _ _
  exact ⟨ε, F, hFm, natDegree_pos_of_monic_of_mem hQ.ne_top hFm hFQ, hFQ⟩

/-- Let `F` be monic of positive degree in the ideal `Q ⊆ A[X]`, and let `χ` be a finite
substitution of `A` contracting `p = Q ∩ A` to `J`. Then substituting `F` for the variable after
applying `χ` to the coefficients is finite and contracts `Q` to the ideal of polynomials whose
constant coefficient lies in `J`, that is to `J A[X] + (X)`. -/
private lemma exists_finite_comap_eq_comap_constantCoeff {k A : Type*} [Field k] [CommRing A]
    [Nontrivial A] [Algebra k A] {Q : Ideal A[X]} {F : A[X]} (hF : F.Monic) (hFQ : F ∈ Q)
    (hd : 0 < F.natDegree) {χ : A →ₐ[k] A} (hχ : χ.toRingHom.Finite) {J : Ideal A}
    (hJ : (Q.comap (Polynomial.C : A →+* A[X])).comap χ = J) :
    ∃ Θ : A[X] →ₐ[k] A[X], Θ.toRingHom.Finite ∧ Q.comap Θ = J.comap Polynomial.constantCoeff := by
  refine ⟨((Polynomial.aeval F : A[X] →ₐ[A] A[X]).restrictScalars k).comp
      (Polynomial.mapAlgHom χ),
    finite_comp (finite_mapAlgHom hχ) (finite_aeval_of_monic hF hd), ?_⟩
  have h : Q.comap ((Polynomial.aeval F : A[X] →ₐ[A] A[X]).restrictScalars k)
      = (Q.comap (Polynomial.C : A →+* A[X])).comap Polynomial.constantCoeff :=
    comap_aeval_of_mem hFQ
  rw [comap_comp, h, comap_mapAlgHom_comap_constantCoeff, hJ]

/-- If `d + r = n` and the residue field of `(0) ⊆ k[x_0, …, x_{n-1}]` has transcendence degree
`r`, then some finite `φ` contracts `(0)` to the ideal generated by the first `d` variables. -/
private lemma exists_finite_comap_bot {k : Type u} [Field k] {n d r : ℕ} (hdr : d + r = n)
    (hr : Algebra.trdeg k (⊥ : Ideal (MvPolynomial (Fin n) k)).ResidueField
      = (r : Cardinal.{u})) :
    ∃ φ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k, φ.toRingHom.Finite ∧
      (⊥ : Ideal (MvPolynomial (Fin n) k)).comap φ =
        Ideal.span (X '' {i : Fin n | (i : ℕ) < d}) := by
  obtain rfl : r = n := by
    exact_mod_cast hr.symm.trans (trdeg_residueField_bot k n)
  obtain rfl : d = 0 := by omega
  exact ⟨AlgHom.id k _, by simpa using RingHom.Finite.id _, by simp⟩

/-- A prime of a polynomial ring in no variables over a field is `(0)`. -/
private lemma eq_bot_of_isEmpty {k : Type u} [Field k] {σ : Type*} [IsEmpty σ]
    (q : Ideal (MvPolynomial σ k)) [q.IsPrime] : q = ⊥ := by
  have e := (MvPolynomial.isEmptyAlgEquiv k σ).toRingEquiv
  have : (q.map (e : MvPolynomial σ k →+* k)).IsPrime := Ideal.map_isPrime_of_equiv e
  rw [← Ideal.comap_map_of_bijective (I := q) (e : MvPolynomial σ k →+* k) e.bijective,
    Ideal.eq_bot_of_prime (q.map (e : MvPolynomial σ k →+* k))]
  exact Ideal.comap_bot_of_injective _ e.injective

/-- If every prime `p` of `k[x_1, …, x_m]` whose residue field has transcendence degree `r` is
contracted by some finite `χ` to the ideal generated by the first `d` variables whenever
`d + r = m`, then the same holds for every nonzero prime `q` of `k[x_0, …, x_m]` and
`d + r = m + 1`. -/
private theorem key_step {k : Type u} [Field k] (m : ℕ)
    (IH : ∀ (p : Ideal (MvPolynomial (Fin m) k)) [p.IsPrime] (d r : ℕ), d + r = m →
      Algebra.trdeg k p.ResidueField = (r : Cardinal.{u}) →
      ∃ χ : MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k,
        χ.toRingHom.Finite ∧ p.comap χ = Ideal.span (X '' {i : Fin m | (i : ℕ) < d}))
    (q : Ideal (MvPolynomial (Fin (m + 1)) k)) [q.IsPrime] (hq : q ≠ ⊥) (d r : ℕ)
    (hdr : d + r = m + 1) (hr : Algebra.trdeg k q.ResidueField = (r : Cardinal.{u})) :
    ∃ φ : MvPolynomial (Fin (m + 1)) k →ₐ[k] MvPolynomial (Fin (m + 1)) k,
      φ.toRingHom.Finite ∧
        q.comap φ = Ideal.span (X '' {i : Fin (m + 1) | (i : ℕ) < d}) := by
  obtain ⟨ε, F, hFm, hFd, hFQ⟩ := exists_monic_natDegree_pos_mem_comap q hq
  set A := MvPolynomial (Fin m) k
  set Q : Ideal A[X] := q.comap ε.toAlgHom with hQ
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have : (Q.comap (Polynomial.C : A →+* A[X])).IsPrime := Ideal.comap_isPrime _ _
  have htr : Algebra.trdeg k (Q.comap (Polynomial.C : A →+* A[X])).ResidueField
      = (r : Cardinal.{u}) := by
    rwa [trdeg_residueField_comap_C Q hFm hFQ, trdeg_residueField_eq_of_comap ε Q q hQ]
  have hrm : r ≤ m := by
    exact_mod_cast htr ▸ trdeg_residueField_le (Q.comap (Polynomial.C : A →+* A[X]))
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨χ, hχfin, hχ⟩ := IH (Q.comap (Polynomial.C : A →+* A[X])) e r (by omega) htr
  obtain ⟨Θ, hΘfin, hΘ⟩ :=
    exists_finite_comap_eq_comap_constantCoeff hFm hFQ hFd hχfin hχ
  refine ⟨ε.toAlgHom.comp (Θ.comp (finSuccEquiv k m).toAlgHom),
    finite_comp (finite_comp (finite_of_algEquiv (finSuccEquiv k m)) hΘfin)
      (finite_of_algEquiv ε), ?_⟩
  rw [comap_comp, comap_comp, ← hQ, hΘ]
  exact comap_finSuccEquiv_comap_constantCoeff

/-- Let `q` be a prime of `k[x_0, …, x_{n-1}]` whose residue field has transcendence degree `r`
over `k`, and let `d + r = n`. Then some finite `k`-algebra endomorphism `φ` contracts `q` to the
ideal generated by the first `d` variables. -/
private theorem key {k : Type u} [Field k] (n : ℕ) :
    ∀ (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] (d r : ℕ), d + r = n →
      Algebra.trdeg k q.ResidueField = (r : Cardinal.{u}) →
      ∃ φ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k,
        φ.toRingHom.Finite ∧ q.comap φ = Ideal.span (X '' {i : Fin n | (i : ℕ) < d}) := by
  induction n with
  | zero =>
    intro q _ d r hdr hr
    obtain rfl := eq_bot_of_isEmpty q
    exact exists_finite_comap_bot hdr hr
  | succ m IH =>
    intro q _ d r hdr hr
    rcases eq_or_ne q ⊥ with rfl | hq
    · exact exists_finite_comap_bot hdr hr
    · exact key_step m IH q hq d r hdr hr

end Induction

/-- Let `k` be a field, let `q ⊆ k[x_1, …, x_n]` be a prime ideal, and let `r` be the
transcendence degree of the residue field `κ(q)` over `k`. Then there is a finite `k`-algebra map
`φ : k[y_1, …, y_n] → k[x_1, …, x_n]` whose preimage of `q` is the ideal `(y_{r + 1}, …, y_n)`
generated by the last `n - r` variables. -/
public theorem solution {k : Type u} [Field k] {n : ℕ} (q : Ideal (MvPolynomial (Fin n) k))
    [q.IsPrime] {r : ℕ} (hr : Algebra.trdeg k q.ResidueField = r) :
    ∃ φ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k,
      φ.toRingHom.Finite ∧ q.comap φ = Ideal.span (X '' {i : Fin n | r ≤ (i : ℕ)}) := by
  have hrn : r ≤ n := by exact_mod_cast hr ▸ trdeg_residueField_le q
  set σ := renameEquiv k (Fin.revPerm : Equiv.Perm (Fin n)) with hσ
  have : (q.comap σ.toAlgHom).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨φ, hfin, hcomap⟩ := key n (q.comap σ.toAlgHom) (n - r) r (by omega)
    ((trdeg_residueField_eq_of_comap σ (q.comap σ.toAlgHom) q rfl).trans hr)
  refine ⟨σ.toAlgHom.comp (φ.comp σ.toAlgHom),
    finite_comp (finite_comp (finite_of_algEquiv σ) hfin) (finite_of_algEquiv σ), ?_⟩
  rw [comap_comp, comap_comp, hcomap, hσ, comap_renameEquiv_span_X_image,
    Fin.revPerm_symm, image_revPerm_setOf_lt hrn]

end Stacks.PolynomialRing.PrimeStandardForm

end

/-!
### The statement for `k[y_1, …, y_n] → k[x_1, …, x_n]`

Both polynomial rings are the one type `MvPolynomial (Fin n) k`, the variables `y_1, …, y_n`
being `X 0, …, X (n - 1)`, so `(y_{r + 1}, …, y_n)` is `Ideal.span (X '' {i | r ≤ (i : ℕ)})`.
The map `φ` is a `k`-algebra map, and `κ(q)` is the canonical `Ideal.ResidueField` of `q`.
-/

@[expose] public section

namespace MvPolynomial



/-- Let `k` be a field, let `q ⊆ k[x_1, …, x_n]` be a prime ideal, and let `r` be the
transcendence degree of the residue field `κ(q)` over `k`. Then there is a finite `k`-algebra map
`φ : k[y_1, …, y_n] → k[x_1, …, x_n]` whose preimage of `q` is the ideal `(y_{r + 1}, …, y_n)`
generated by the last `n - r` variables. -/
@[stacks 051P "The two polynomial rings are the one type `MvPolynomial (Fin n) k`, with
`(y_{r + 1}, …, y_n)` spelled `Ideal.span (X '' {i | r ≤ (i : ℕ)})`; `φ` is a `k`-algebra
map, as the source's construction gives, and `κ(q)` is the canonical
`Ideal.ResidueField`. See the module docstring."]
public theorem exists_finite_comap_eq_span_X_image_of_trdeg_eq {k : Type u} [Field k]
    {n : ℕ} (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] {r : ℕ}
    (hr : Algebra.trdeg k q.ResidueField = r) :
    ∃ φ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k,
      φ.toRingHom.Finite ∧ q.comap φ = Ideal.span (X '' {i : Fin n | r ≤ (i : ℕ)}) :=
  Stacks.PolynomialRing.PrimeStandardForm.solution q hr

end MvPolynomial

end
