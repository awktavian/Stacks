module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Presheaf
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Smoothness and differentials

Three theorems about the conormal modules attached to a smooth ring map.

Let `φ : R → S` be smooth, let `σ : S → R` be a left inverse of `φ`, and put `I = Ker(σ)`.
Stacks 05D5 says that the conormal module `I/I²` is finite locally free over `R`, and that when it
is free of rank `d` the `I`-adic completion of `S` is the formal power series algebra
`R[[t_1, …, t_d]]`.

Let `R → P → S` be ring maps with `P → S` surjective with kernel `J`. Stacks 00RU provides a
canonical exact sequence of `S`-modules
```
J/J² → S ⊗[P] Ω[P⁄R] → Ω[S⁄R] → 0 ,
```
whose left hand map takes the class of `f ∈ J` to `df ⊗ 1`. Stacks 06A8 says that if `R → S` is
smooth then this sequence is split short exact, so that in particular the left hand map is
injective and `S ⊗[P] Ω[P⁄R] ≅ J/J² × Ω[S⁄R]`. Formal smoothness of `S` over `R` is all that is
used, and it enters through the square-zero surjection `P ⧸ J² → S`: the identity of `S` lifts
along it to an `R`-algebra section, and such a section is the same datum as a retraction of the
left hand map (Stacks 031I, `retractionKerCotangentToTensorEquivSection`).

Let `A → B → C` be ring maps with `A → C` surjective, so that `B → C` is surjective too, and put
`I = Ker(A → C)` and `J = Ker(B → C)`. Stacks 065V provides a canonical exact sequence
```
I/I² → J/J² → Ω[B⁄A] ⊗[B] B/J → 0 ,
```
whose left hand map `ι` sends the class of `a ∈ I` to the class of its image in `J`, and whose
right hand map sends the class of `x ∈ J` to `1 ⊗ dx`. Stacks 06A9 says that if `A → B` is smooth
then `ι` is injective. What is proved is the source's own stronger assertion: `ι` has a retraction,
so that this sequence too is split short exact. Surjectivity of `A → C` identifies `C` with
`A ⧸ I`, so that `B → C` is an `A`-algebra map to `A ⧸ I`; formal smoothness of `A → B` lifts it
along the square-zero surjection `A ⧸ I² → A ⧸ I` to an `A`-algebra map `s : B → A ⧸ I²`, which
carries `J` into `I ⧸ I²` and `J²` into zero, hence induces `ρ : J/J² → I/I²`, and `ρ ∘ ι = id`
because `s` is a map of `A`-algebras.

## Main results

* `conormal_finite_projective` and `adicCompletion_algEquiv_mvPowerSeries`: the two parts of
  Stacks 05D5.
* `KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange`: Stacks 06A8.
* `Algebra.FormallySmooth.exists_leftInverse_mapCotangent`: Stacks 06A9.

## Implementation notes

For Stacks 05D5 a smooth ring map `φ : R → S` is rendered by endowing `S` with an `R`-algebra
structure and assuming `Algebra.Smooth R S`, and a ring map `σ : S → R` with `σ ∘ φ = id_R` by an
`R`-algebra homomorphism `σ : S →ₐ[R] R`, for which the left inverse condition holds automatically
and which is automatically surjective. The conormal module `I/I²` of `I = Ker(σ)` is
`(RingHom.ker σ).Cotangent`, an `S`-module, viewed as an `R`-module by restriction of scalars
along `φ`; along the identification `S/I ≅ R` induced by `σ` this is the `R`-module structure of
the source. "Finite locally free" is the conjunction of `Module.Finite` and `Module.Projective`,
"free of rank `d`" is `Module.Free` with `d := Module.finrank R (I/I²)`, and the `I`-adic
completion `S^∧` is `AdicCompletion (RingHom.ker σ) S`.

Stacks 06A8 and Stacks 06A9 are stated for a formally smooth ring map, which is the source's own
generalisation of each (Stacks 06A6 and Stacks 06A7): nothing in either conclusion sees the
`Algebra.FinitePresentation` that `Algebra.Smooth` carries in addition, and
`Algebra.Smooth.formallySmooth` is an instance, so the smooth case is recovered with no work.

Split exactness is recorded in each case as the datum the source's proof produces, rather than as
the conjunction "left hand map injective, sequence exact, right hand map surjective": for
Stacks 06A8 injectivity of `KaehlerDifferential.kerCotangentToTensor R P S` together with an
`S`-linear section of `KaehlerDifferential.mapBaseChange R P S`, for Stacks 06A9 a retraction of
`Ideal.mapCotangent` along `Algebra.ofId A B`. The remaining two thirds of exactness require no
smoothness and are the neighbouring tags: for the first sequence they are
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` and
`KaehlerDifferential.mapBaseChange_surjective` (Stacks 00RU), for the second Stacks 065V. Given
those, the datum recorded is equivalent to split short exactness and to the direct sum
decomposition, by `Function.Exact.split_tfae`.

Stacks 06A8 asks nothing of `P`, and that is where it differs from the two equivalences it sits
beside: Mathlib's `Algebra.FormallySmooth.iff_split_injection` and Stacks 031J both assume `P`
formally smooth over `R`, which their converse directions need. Only the direction "`S` formally
smooth implies split exact" is asserted, and for it an arbitrary `P` will do: with `R = ℚ`,
`P = ℚ[x, z]/(z²)` and `S = ℚ[x]` along `z ↦ 0`, where `Ω[P⁄ℚ]` is not projective, the sequence is
still the split exact `0 → S·z → S dx ⊕ S dz → S dx → 0`.

No hypothesis of either statement can be dropped. For `R = ℚ`, `P = ℚ[x]` and `S = P/(x²)` the
kernel is `J = (x²)`, `J/J² ≅ S` is free on `x²`, and the left hand map of Stacks 06A8 sends `x²`
to `2x · dx` and is not injective; there formal smoothness of `S` over `R` is what fails. For
`R = P = ℚ` and `S = ℚ[t]`, where `algebraMap P S` is not surjective, `S ⊗[ℚ] Ω[ℚ⁄ℚ] = 0` admits
no surjection onto `Ω[S⁄ℚ] ≅ S`. For Stacks 06A9, with `A = ℚ[t] → B = ℚ[x]` along `t ↦ x²` and
`C = ℚ`, the map `ι` sends the class of `t` to `x² ∈ J²` and so vanishes although `I/I² ≅ ℚ` does
not.

Where the source reads its sequences over `S`, resp. over `C`, two of the maps here are linear
over a smaller ring. `KaehlerDifferential.kerCotangentToTensor` is `P`-linear, but only its
injectivity is asserted, which does not see the scalars; the section of
`KaehlerDifferential.mapBaseChange` is over `S` as in the source. The retraction of Stacks 06A9 is
asserted `A`-linear, which for these modules is the same as `C`-linear, both being annihilated by
`I` while `A → C` is surjective with kernel `I` (`LinearMap.extendScalarsOfSurjectiveEquiv`);
`Ideal.Cotangent` carries the `A ⧸ I`-module structure rather than a `C`-module one. The side
condition `I ≤ Ideal.comap (Algebra.ofId A B) J` that `Ideal.mapCotangent` takes is not a
hypothesis but the identity `I = Ideal.comap (algebraMap A B) J`, supplied inline as in Mathlib's
`Ideal.mapCotangent_ker_of_surjective`; and `Ω[B⁄A] ⊗[B] B/J`, which does not occur below, is
spelled `C ⊗[B] Ω[B⁄A]` by Mathlib, the same module along `B/J ≅ C`.

## References

* [StacksProject 05D5](https://stacks.math.columbia.edu/tag/05D5)
* [StacksProject 06A6](https://stacks.math.columbia.edu/tag/06A6)
* [StacksProject 06A7](https://stacks.math.columbia.edu/tag/06A7)
* [StacksProject 06A8](https://stacks.math.columbia.edu/tag/06A8)
* [StacksProject 06A9](https://stacks.math.columbia.edu/tag/06A9)
* [StacksProject 00RU](https://stacks.math.columbia.edu/tag/00RU)
* [StacksProject 00TL](https://stacks.math.columbia.edu/tag/00TL)
* [StacksProject 031I](https://stacks.math.columbia.edu/tag/031I)
* [StacksProject 031J](https://stacks.math.columbia.edu/tag/031J)
* [StacksProject 065V](https://stacks.math.columbia.edu/tag/065V)

## Tags

smooth ring map, formally smooth, conormal module, cotangent module, Kaehler differentials,
split exact sequence, adic completion, power series
-/

@[expose] public section

section AdicCompletion

-- the graded quotient comparison maps must unfold past the default transparency
set_option backward.isDefEq.respectTransparency false

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (σ : S →ₐ[R] R)

/-- Part (1) of Stacks tag 05D5: the conormal module is finite locally free.
If `S` is a smooth `R`-algebra and `σ : S →ₐ[R] R`, then the conormal module `I/I²` of
`I = Ker(σ)` is a finitely generated projective `R`-module. -/
@[stacks 05D5 "(1)",
  ega "0 19.5.3" "(i), special case",
  ega "0 19.5.4.1" "a), special case",
  ega "0 19.5.7" "Clause (i), special case",
  ega "0 22.1.1" "(ii), condition α",
  ega "IV 17.10.4" "special case",
  sga "1 II 4.10" "(iv)",
  sga "3 III 4.25" "(ii), special case",
  sga "3 VIB 1.6" "special case",
  sga "6 VII 1.6" "special case",
  sga "6 VIII 2.4" "special case",
  sga "6 X 7.1" "special case"]
theorem conormal_finite_projective (h : Algebra.Smooth R S) :
    Module.Finite R (RingHom.ker σ).Cotangent ∧
      Module.Projective R (RingHom.ker σ).Cotangent := by
  let := σ.toAlgebra
  have : IsScalarTower R S R := inferInstance
  have : Algebra.FormallySmooth R S := h.formallySmooth
  have : Function.Surjective (algebraMap S R) := by
    intro r; exact ⟨algebraMap R S r, σ.commutes r⟩
  have : Module.Finite S (Ω[S⁄R]) := KaehlerDifferential.finite R S
  have : Module.Projective S (Ω[S⁄R]) :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
  have : Module.Finite R (TensorProduct S R (Ω[S⁄R])) :=
    Module.Finite.base_change S R (Ω[S⁄R])
  have : Module.Projective R (TensorProduct S R (Ω[S⁄R])) :=
    Module.Projective.tensorProduct
  obtain ⟨l, hl⟩ : ∃ l, l ∘ₗ KaehlerDifferential.kerCotangentToTensor R S R = LinearMap.id := by
    rw [← Algebra.FormallySmooth.iff_split_injection (R := R) (P := S) (A := R)
      ‹Function.Surjective (algebraMap S R)›]
    infer_instance
  set f := KaehlerDifferential.kerCotangentToTensor R S R
  have hl' : (l.restrictScalars R) ∘ₗ (f.restrictScalars R) = LinearMap.id := by
    ext x
    simpa using LinearMap.congr_fun hl x
  constructor
  · have hsurj : Function.Surjective (l.restrictScalars R) := by
      intro m
      refine ⟨f.restrictScalars R m, ?_⟩
      have := LinearMap.congr_fun hl' m
      simpa using this
    exact Module.Finite.of_surjective (l.restrictScalars R) hsurj
  · exact Module.Projective.of_split (f.restrictScalars R) (l.restrictScalars R) hl'

open MvPolynomial in
/-- When the conormal module `I/I²` of `I = RingHom.ker σ` is free, there is a tuple
`t : Fin d → S`, `d = Module.finrank R (I/I²)`, of elements of `I` whose classes form a basis. -/
private theorem exists_cotangentBasis_lift (h : Algebra.Smooth R S)
    (hfree : Module.Free R (RingHom.ker σ).Cotangent) :
    ∃ (b : Module.Basis (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
            (RingHom.ker σ).Cotangent)
      (t : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → S),
      ∀ i, ∃ hi : t i ∈ RingHom.ker σ,
        (RingHom.ker σ).toCotangent ⟨t i, hi⟩ = b i := by
  have : Module.Finite R (RingHom.ker σ).Cotangent := (conormal_finite_projective σ h).left
  obtain hR | hR := subsingleton_or_nontrivial R
  · have : Subsingleton (RingHom.ker σ).Cotangent := Module.subsingleton R _
    let b : Module.Basis (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
        (RingHom.ker σ).Cotangent :=
      ⟨{ toFun := 0, map_add' := fun _ _ => Subsingleton.elim _ _,
         map_smul' := fun _ _ => Subsingleton.elim _ _,
         invFun := 0, left_inv := fun _ => Subsingleton.elim _ _,
         right_inv := fun _ => Subsingleton.elim _ _ }⟩
    exact ⟨b, fun _ => 0, fun i => ⟨(RingHom.ker σ).zero_mem, Subsingleton.elim _ _⟩⟩
  · have : StrongRankCondition R := inferInstance
    let b := Module.finBasis R (RingHom.ker σ).Cotangent
    have hsurj : Function.Surjective (RingHom.ker σ).toCotangent := Ideal.toCotangent_surjective _
    choose u hu using fun i => hsurj (b i)
    refine ⟨b, fun i => (u i : S), fun i => ⟨(u i).property, ?_⟩⟩
    have : (⟨(u i : S), (u i).property⟩ : ↥(RingHom.ker σ)) = u i := Subtype.ext rfl
    rw [this]; exact hu i

open MvPolynomial in
/-- Evaluation `X i ↦ t i` at elements `t i` of `I = RingHom.ker σ` carries the `n`-th power of
the ideal of variables into `Iⁿ`. -/
private theorem comparisonMap_pow_le
    (d : ℕ) (t : Fin d → S) (htI : ∀ i, t i ∈ RingHom.ker σ) (n : ℕ) :
    (idealOfVars (Fin d) R) ^ n ≤
      Ideal.comap (MvPolynomial.aeval (R := R) (fun i => t i) : MvPolynomial (Fin d) R →ₐ[R] S)
        ((RingHom.ker σ) ^ n) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  apply Ideal.pow_right_mono
  rw [idealOfVars, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  simpa using htI i

open MvPolynomial in
/-- The comparison map `P ⧸ J⁰ → S ⧸ I⁰` is bijective, both quotients being the zero ring. -/
private theorem quotientComparison_bijective_zero
    (d : ℕ) (t : Fin d → S) (htI : ∀ i, t i ∈ RingHom.ker σ) :
    Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker σ) ^ 0)
        (MvPolynomial.aeval (R := R) (fun i => t i) :
          MvPolynomial (Fin d) R →ₐ[R] S)
        (comparisonMap_pow_le σ d t htI 0)) := by
  have hP : Subsingleton (MvPolynomial (Fin d) R ⧸ (idealOfVars (Fin d) R) ^ 0) := by
    rw [pow_zero, Ideal.Quotient.subsingleton_iff, Ideal.one_eq_top]
  have hS : Subsingleton (S ⧸ (RingHom.ker σ) ^ 0) := by
    rw [pow_zero, Ideal.Quotient.subsingleton_iff, Ideal.one_eq_top]
  exact ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- A polynomial whose evaluation at elements `t i` of `I = RingHom.ker σ` lies in `I` has
vanishing constant term. -/
private theorem constantCoeff_eq_zero_of_aeval_mem_ker
    {d : ℕ} (t : Fin d → S) (htI : ∀ i, t i ∈ RingHom.ker σ) {p : MvPolynomial (Fin d) R}
    (hp : MvPolynomial.aeval (R := R) (fun i => t i) p ∈ RingHom.ker σ) :
    MvPolynomial.constantCoeff p = 0 := by
  have hkey : σ.comp (MvPolynomial.aeval (R := R) (fun i => t i)) =
      MvPolynomial.aeval (R := R) (0 : Fin d → R) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa using htI i
  have hcomp := AlgHom.congr_fun hkey p
  rw [AlgHom.comp_apply, RingHom.mem_ker.mp hp, MvPolynomial.aeval_zero] at hcomp
  simpa using hcomp.symm

open MvPolynomial in
/-- The comparison map `P ⧸ J → S ⧸ I` is bijective: under the augmentation `P ⧸ J ≅ R` and the
identification `S ⧸ I ≅ R` induced by `σ` it is the identity of `R`. -/
private theorem quotientComparison_bijective_one
    (d : ℕ) (t : Fin d → S) (htI : ∀ i, t i ∈ RingHom.ker σ) :
    Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker σ) ^ 1)
        (MvPolynomial.aeval (R := R) (fun i => t i) :
          MvPolynomial (Fin d) R →ₐ[R] S)
        (comparisonMap_pow_le σ d t htI 1)) := by
  set Ψ : MvPolynomial (Fin d) R →ₐ[R] S := MvPolynomial.aeval (fun i => t i) with hΨ
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [show (Ideal.quotientMapₐ ((RingHom.ker σ) ^ 1) Ψ (comparisonMap_pow_le σ d t htI 1))
          (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (Ψ p) by
        simp [Ideal.quotientMapₐ, Ideal.quotientMap_mk]] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one] at hx
    have hc := constantCoeff_eq_zero_of_aeval_mem_ker σ t htI hx
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x hxdeg
    rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hxdeg
    rw [hxdeg]
    rwa [← MvPolynomial.constantCoeff_eq]
  · intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.C (σ s)), ?_⟩
    rw [show (Ideal.quotientMapₐ ((RingHom.ker σ) ^ 1) Ψ (comparisonMap_pow_le σ d t htI 1))
          (Ideal.Quotient.mk _ (MvPolynomial.C (σ s)))
          = Ideal.Quotient.mk _ (Ψ (MvPolynomial.C (σ s))) by
        simp [Ideal.quotientMapₐ, Ideal.quotientMap_mk]]
    rw [Ideal.Quotient.eq, pow_one, RingHom.mem_ker]
    have hΨC : Ψ (MvPolynomial.C (σ s)) = algebraMap R S (σ s) := by
      simp [hΨ]
    rw [hΨC, map_sub, σ.commutes]
    simp

open MvPolynomial in
/-- Elements `t i` of `I = RingHom.ker σ` whose classes form a basis of the conormal module
`I/I²` satisfy `I ≤ Ideal.span (Set.range t) + I²`. -/
private theorem ker_le_span_sup_sq
    (b : Module.Basis (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
            (RingHom.ker σ).Cotangent)
    (t : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → S)
    (htI : ∀ i, t i ∈ RingHom.ker σ)
    (ht : ∀ i, (RingHom.ker σ).toCotangent ⟨t i, htI i⟩ = b i) :
    (RingHom.ker σ) ≤ Ideal.span (Set.range t) ⊔ (RingHom.ker σ) ^ 2 := by
  classical
  intro x hx
  set c := b.repr ((RingHom.ker σ).toCotangent ⟨x, hx⟩) with hc
  set y : S := Finset.univ.sum fun i => algebraMap R S (c i) * t i with hy
  have hyI : y ∈ RingHom.ker σ := by
    rw [hy]; apply Ideal.sum_mem; intro i _
    exact Ideal.mul_mem_left _ _ (htI i)
  refine Submodule.mem_sup.mpr ⟨y, ?_, x - y, ?_, by ring⟩
  · rw [hy]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · have hxy : x - y ∈ RingHom.ker σ := (RingHom.ker σ).sub_mem hx hyI
    rw [← Ideal.toCotangent_eq_zero (RingHom.ker σ) ⟨x - y, hxy⟩]
    have hsub : (RingHom.ker σ).toCotangent ⟨x - y, hxy⟩
        = (RingHom.ker σ).toCotangent ⟨x, hx⟩ - (RingHom.ker σ).toCotangent ⟨y, hyI⟩ := by
      rw [← map_sub]; congr 1
    rw [hsub, sub_eq_zero]
    have hyc : (RingHom.ker σ).toCotangent ⟨y, hyI⟩ = Finset.univ.sum fun i => c i • b i := by
      have hyeq : (⟨y, hyI⟩ : ↥(RingHom.ker σ))
          = Finset.univ.sum fun i => c i • (⟨t i, htI i⟩ : ↥(RingHom.ker σ)) := by
        apply Subtype.ext
        rw [AddSubmonoid.coe_finsetSum]
        show y = Finset.univ.sum fun i =>
          ((c i • (⟨t i, htI i⟩ : ↥(RingHom.ker σ)) : ↥(RingHom.ker σ)) : S)
        rw [hy]
        apply Finset.sum_congr rfl
        intro i _
        show algebraMap R S (c i) * t i = c i • (t i)
        rw [Algebra.smul_def]
      rw [hyeq, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearMap.map_smul_of_tower, ht i]
    rw [hyc, hc]
    exact (b.sum_repr ((RingHom.ker σ).toCotangent ⟨x, hx⟩)).symm

/-- For ideals `K ≤ I` with `I ≤ K + I²`, one has `Iⁿ ≤ Kⁿ + Iⁿ⁺¹` for every `n`. -/
private theorem gen_fact_pow_abstract {S : Type*} [CommRing S] {I K : Ideal S} (hKI : K ≤ I)
    (hbase : I ≤ K ⊔ I ^ 2) (n : ℕ) :
    I ^ n ≤ K ^ n ⊔ I ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ I m]
    calc I ^ m * I ≤ (K ^ m ⊔ I ^ (m + 1)) * I := Ideal.mul_mono_left ih
      _ = K ^ m * I ⊔ I ^ (m + 1) * I := by rw [Ideal.sup_mul]
      _ ≤ K ^ m * (K ⊔ I ^ 2) ⊔ I ^ (m + 1) * I :=
            sup_le_sup_right (Ideal.mul_mono_right hbase) _
      _ = (K ^ m * K ⊔ K ^ m * I ^ 2) ⊔ I ^ (m + 1) * I := by rw [Ideal.mul_sup]
      _ ≤ K ^ (m + 1) ⊔ I ^ (m + 1 + 1) := by
            apply sup_le
            · apply sup_le
              · rw [← pow_succ]
                exact le_sup_left
              · refine le_trans ?_ le_sup_right
                calc K ^ m * I ^ 2 ≤ I ^ m * I ^ 2 :=
                     Ideal.mul_mono_left (Ideal.pow_right_mono hKI m)
                  _ = I ^ (m + 2) := by rw [← pow_add]
                  _ ≤ I ^ (m + 1 + 1) := le_of_eq (by ring_nf)
            · refine le_trans ?_ le_sup_right
              rw [← pow_succ]

open MvPolynomial in
/-- For `a` in the `n`-th power of `Ideal.span (Set.range t)`, the class of `a` in `S ⧸ Iⁿ⁺¹` lies
in the range of the comparison map `P ⧸ Jⁿ⁺¹ → S ⧸ Iⁿ⁺¹`. -/
private theorem quotientComparison_graded_range_mem
    (t : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → S)
    (htI : ∀ i, t i ∈ RingHom.ker σ) (n : ℕ)
    (a : S) (ha : a ∈ (Ideal.span (Set.range t)) ^ n) :
    ∃ q, (Ideal.quotientMapₐ ((RingHom.ker σ) ^ (n + 1))
            (MvPolynomial.aeval (R := R) (fun i => t i) :
              MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S)
            (comparisonMap_pow_le σ _ t htI (n + 1))) q
          = Ideal.Quotient.mk ((RingHom.ker σ) ^ (n + 1)) a := by
  classical
  let Ψ : MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S :=
    MvPolynomial.aeval (fun i => t i)
  let J : Ideal (MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) :=
    idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
  let qm := Ideal.quotientMapₐ ((RingHom.ker σ) ^ (n + 1)) Ψ
    (comparisonMap_pow_le σ _ t htI (n + 1))
  have hqmmk : ∀ p : MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R,
      qm (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk ((RingHom.ker σ) ^ (n + 1)) (Ψ p) := by
    intro p
    simp [qm, Ideal.quotientMapₐ, Ideal.quotientMap_mk]
  have hmapJ : Ideal.map Ψ J = Ideal.span (Set.range t) := by
    show Ideal.map Ψ (idealOfVars _ R) = Ideal.span (Set.range t)
    rw [idealOfVars, Ideal.map_span]
    congr 1
    rw [← Set.range_comp]
    congr 1
    ext i
    simp [Ψ]
  have hmapJn : Ideal.map Ψ (J ^ n) = (Ideal.span (Set.range t)) ^ n := by
    rw [Ideal.map_pow, hmapJ]
  have ha' : a ∈ Ideal.map Ψ (J ^ n) := by rw [hmapJn]; exact ha
  rw [Ideal.map] at ha'
  refine Submodule.span_induction
    (p := fun x _ => ∃ q, qm q = Ideal.Quotient.mk ((RingHom.ker σ) ^ (n + 1)) x)
    ?_ ?_ ?_ ?_ ha'
  · rintro x ⟨p, hp, rfl⟩
    exact ⟨Ideal.Quotient.mk _ p, hqmmk p⟩
  · exact ⟨0, by simp⟩
  · rintro x y _ _ ⟨qx, hqx⟩ ⟨qy, hqy⟩
    exact ⟨qx + qy, by rw [map_add, hqx, hqy, ← map_add]⟩
  · rintro s x hx ⟨qx, hqx⟩
    refine ⟨(σ s) • qx, ?_⟩
    have hxKn : x ∈ (Ideal.span (Set.range t)) ^ n := by
      rw [← hmapJn]; exact hx
    have hxIn : x ∈ (RingHom.ker σ) ^ n := by
      refine (Ideal.pow_right_mono ?_ n) hxKn
      apply Ideal.span_le.mpr; rintro _ ⟨i, rfl⟩; exact htI i
    have hsI : s - algebraMap R S (σ s) ∈ RingHom.ker σ := by
      rw [RingHom.mem_ker, map_sub, σ.commutes]
      simp
    have hterm1 : (s - algebraMap R S (σ s)) * x ∈ (RingHom.ker σ) ^ (n + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul hsI hxIn
    have hsmul_eq : (Ideal.Quotient.mk ((RingHom.ker σ) ^ (n + 1))) (s • x)
        = (σ s) • (Ideal.Quotient.mk ((RingHom.ker σ) ^ (n + 1))) x := by
      rw [smul_eq_mul]
      have hsplit : s * x = (s - algebraMap R S (σ s)) * x + algebraMap R S (σ s) * x := by ring
      rw [hsplit, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hterm1, zero_add]
      rw [Algebra.smul_def]
      rfl
    rw [map_smul, hqx, hsmul_eq]

open MvPolynomial in
/-- If the comparison map `P ⧸ Jⁿ → S ⧸ Iⁿ` is bijective, then `P ⧸ Jⁿ⁺¹ → S ⧸ Iⁿ⁺¹` is
surjective. -/
private theorem quotientComparison_step_surjective
    (b : Module.Basis (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
            (RingHom.ker σ).Cotangent)
    (t : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → S)
    (htI : ∀ i, t i ∈ RingHom.ker σ)
    (ht : ∀ i, (RingHom.ker σ).toCotangent ⟨t i, htI i⟩ = b i)
    (n : ℕ)
    (hind : Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker σ) ^ n)
        (MvPolynomial.aeval (R := R) (fun i => t i) :
          MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S)
        (comparisonMap_pow_le σ _ t htI n))) :
    Function.Surjective
      (Ideal.quotientMapₐ ((RingHom.ker σ) ^ (n + 1))
        (MvPolynomial.aeval (R := R) (fun i => t i) :
          MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S)
        (comparisonMap_pow_le σ _ t htI (n + 1))) := by
  classical
  set K : Ideal S := Ideal.span (Set.range t) with hKdef
  have hKI : K ≤ RingHom.ker σ := by
    rw [hKdef]; apply Ideal.span_le.mpr; rintro _ ⟨i, rfl⟩; exact htI i
  have hgen : (RingHom.ker σ) ^ n ≤ K ^ n ⊔ (RingHom.ker σ) ^ (n + 1) :=
    gen_fact_pow_abstract hKI (ker_le_span_sup_sq σ b t htI ht) n
  have hΨn1mk : ∀ p : MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R,
      (Ideal.quotientMapₐ ((RingHom.ker σ) ^ (n + 1))
          (MvPolynomial.aeval (R := R) (fun i => t i) :
            MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S)
          (comparisonMap_pow_le σ _ t htI (n + 1))) (Ideal.Quotient.mk _ p)
        = Ideal.Quotient.mk ((RingHom.ker σ) ^ (n + 1))
            (MvPolynomial.aeval (R := R) (fun i => t i) p) := by
    intro p; simp [Ideal.quotientMapₐ, Ideal.quotientMap_mk]
  intro y
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨xn, hxn⟩ := hind.right (Ideal.Quotient.mk ((RingHom.ker σ) ^ n) s)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective xn
  have hΨnmk : (Ideal.quotientMapₐ ((RingHom.ker σ) ^ n)
      (MvPolynomial.aeval (R := R) (fun i => t i) :
        MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S)
      (comparisonMap_pow_le σ _ t htI n))
      (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk ((RingHom.ker σ) ^ n)
        (MvPolynomial.aeval (R := R) (fun i => t i) p) := by
    simp [Ideal.quotientMapₐ, Ideal.quotientMap_mk]
  rw [hΨnmk] at hxn
  have hdiff : s - MvPolynomial.aeval (R := R) (fun i => t i) p ∈ (RingHom.ker σ) ^ n := by
    rw [show s - MvPolynomial.aeval (R := R) (fun i => t i) p
          = -(MvPolynomial.aeval (R := R) (fun i => t i) p - s) by ring]
    exact neg_mem (Ideal.Quotient.eq.mp hxn)
  obtain ⟨a, haK, r, hrI, hsum⟩ := Submodule.mem_sup.mp (hgen hdiff)
  obtain ⟨q, hq⟩ := quotientComparison_graded_range_mem σ t htI n a haK
  refine ⟨Ideal.Quotient.mk _ p + q, ?_⟩
  rw [map_add, hΨn1mk, hq, ← map_add]
  refine Ideal.Quotient.eq.mpr ?_
  rw [show MvPolynomial.aeval (R := R) (fun i => t i) p + a - s = -r by linear_combination hsum]
  exact neg_mem hrI

open MvPolynomial in
/-- The comparison map `P ⧸ J² → S ⧸ I²` is injective: a polynomial killed by it has vanishing
constant term, and the coefficients of its linear part are the coordinates of `0` in the basis `b`
of `I/I²`. -/
private theorem quotientComparison_two_injective
    (b : Module.Basis (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
            (RingHom.ker σ).Cotangent)
    (t : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → S)
    (htI : ∀ i, t i ∈ RingHom.ker σ)
    (ht : ∀ i, (RingHom.ker σ).toCotangent ⟨t i, htI i⟩ = b i) :
    Function.Injective
      (Ideal.quotientMapₐ ((RingHom.ker σ) ^ (1 + 1))
        (MvPolynomial.aeval (R := R) (fun i => t i) :
          MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S)
        (comparisonMap_pow_le σ _ t htI (1 + 1))) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [show (Ideal.quotientMapₐ ((RingHom.ker σ) ^ (1+1))
        (MvPolynomial.aeval (R := R) (fun i => t i)) (comparisonMap_pow_le σ _ t htI (1+1)))
        (Ideal.Quotient.mk _ p)
        = Ideal.Quotient.mk _ (MvPolynomial.aeval (R := R) (fun i => t i) p) by
      simp [Ideal.quotientMapₐ, Ideal.quotientMap_mk]] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem] at hx
  set a : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → R :=
    fun i => p.coeff (Finsupp.single i 1) with ha
  have hcc := constantCoeff_eq_zero_of_aeval_mem_ker σ _ htI ((Ideal.pow_le_self (by norm_num)) hx)
  set lin : MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R :=
    Finset.univ.sum fun i => a i • MvPolynomial.X i with hlin
  have hcoeff_lin : ∀ (y : Fin (Module.finrank R (RingHom.ker σ).Cotangent) →₀ ℕ),
      lin.coeff y
      = Finset.univ.sum fun i => a i * (if Finsupp.single i 1 = y then 1 else 0) := by
    intro y
    rw [hlin, MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_X, smul_eq_mul]
  have hqmem :
      p - lin ∈ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R)^(1+1) := by
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro y hy
    rw [MvPolynomial.coeff_sub, hcoeff_lin y]
    rcases (Nat.lt_succ_iff_lt_or_eq.mp hy) with hdeg | hdeg
    · rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hdeg
      subst hdeg
      have hsum0 : (Finset.univ.sum fun i =>
          a i * (if Finsupp.single i 1 = (0 : Fin (Module.finrank R (RingHom.ker σ).Cotangent) →₀ ℕ)
            then (1:R) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have : Finsupp.single i (1:ℕ) ≠ 0 := Finsupp.single_ne_zero.mpr (by norm_num)
        simp [this]
      rw [hsum0, sub_zero, ← MvPolynomial.constantCoeff_eq]; exact hcc
    · obtain ⟨j, rfl⟩ := (Finsupp.sum_eq_one_iff y).mp hdeg
      have hsumj : (Finset.univ.sum fun i =>
          a i * (if Finsupp.single i 1 = Finsupp.single j (1:ℕ) then (1:R) else 0)) = a j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij
          have : Finsupp.single i (1:ℕ) ≠ Finsupp.single j 1 := by
            intro h; apply hij; exact (Finsupp.single_left_injective (by norm_num)) h
          simp [this]
        · simp
      rw [hsumj]
      show p.coeff (Finsupp.single j 1) - a j = 0
      rw [ha]; simp
  have haeval_q : (MvPolynomial.aeval (fun i => t i)) (p - lin) ∈ (RingHom.ker σ)^(1+1) := by
    have := comparisonMap_pow_le σ _ t htI (1+1) hqmem
    rwa [Ideal.mem_comap] at this
  have haeval_lin : (MvPolynomial.aeval (fun i => t i)) lin ∈ (RingHom.ker σ)^(1+1) := by
    have hrw : (MvPolynomial.aeval (fun i => t i)) lin
        = (MvPolynomial.aeval (fun i => t i)) p
          - (MvPolynomial.aeval (fun i => t i)) (p - lin) := by
      rw [map_sub]; ring
    rw [hrw]
    exact Ideal.sub_mem _ hx haeval_q
  have hlinval : (MvPolynomial.aeval (fun i => t i)) lin
      = Finset.univ.sum fun i => algebraMap R S (a i) * t i := by
    rw [hlin, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, MvPolynomial.aeval_X, Algebra.smul_def]
  have hzero : (Ideal.Quotient.mk ((RingHom.ker σ)^2))
      (Finset.univ.sum fun i => algebraMap R S (a i) * t i) = 0 := by
    rw [← hlinval, Ideal.Quotient.eq_zero_iff_mem]
    exact haeval_lin
  have hbsum : (Finset.univ.sum fun i => a i • (b i)) = 0 := by
    apply (RingHom.ker σ).cotangentToQuotientSquare_injective
    rw [map_zero, map_sum, ← hzero, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.map_smul_of_tower, ← ht i]
    have hkey : (RingHom.ker σ).cotangentToQuotientSquare
          ((RingHom.ker σ).toCotangent ⟨t i, htI i⟩)
        = Ideal.Quotient.mk ((RingHom.ker σ)^2) (t i) := rfl
    rw [hkey, map_mul, Algebra.smul_def]
    congr 1
  have haz : ∀ i, a i = 0 := by
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    exact hli a hbsum
  rw [Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_pow_idealOfVars_iff']
  intro y hy
  rcases (Nat.lt_succ_iff_lt_or_eq.mp hy) with hdeg | hdeg
  · rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hdeg
    subst hdeg
    rw [← MvPolynomial.constantCoeff_eq]; exact hcc
  · obtain ⟨j, rfl⟩ := (Finsupp.sum_eq_one_iff y).mp hdeg
    have := haz j; rw [ha] at this; exact this

open MvPolynomial in
/-- Helper: a polynomial with zero constant term lies in the variable ideal. -/
private theorem mem_idealOfVars_of_aeval_zero {k : ℕ}
    (p : MvPolynomial (Fin k) R)
    (hp : (MvPolynomial.aeval (0 : Fin k → R)) p = 0) :
    p ∈ idealOfVars (Fin k) R := by
  rw [← pow_one (idealOfVars (Fin k) R), mem_pow_idealOfVars_iff' 1]
  intro y hy
  rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hy
  rw [hy, ← MvPolynomial.constantCoeff_eq]
  have : (MvPolynomial.aeval (0 : Fin k → R)) p = MvPolynomial.constantCoeff p := by
    simp [MvPolynomial.constantCoeff_eq]
  rw [← this]; exact hp

/-- A ring endomorphism congruent to the identity modulo `Jⁿ`, where `2 ≤ n` and `Jⁿ⁺¹ = 0`,
fixes `Jⁿ` pointwise. -/
private theorem RingHom.eq_self_of_sub_mem_pow {A F' : Type*} [CommRing A] [FunLike F' A A]
    [RingHomClass F' A A] (F : F') {J : Ideal A}
    {n : ℕ} (hn : 2 ≤ n) (hJ : J ^ (n + 1) = ⊥) (hF : ∀ z, F z - z ∈ J ^ n)
    {x : A} (hx : x ∈ J ^ n) : F x = x := by
  have hmul : ∀ {a b : ℕ} {u v : A}, u ∈ J ^ a → v ∈ J ^ b → n + 1 ≤ a + b → u * v = 0 := by
    intro a b u v hu hv hab
    have huv : u * v ∈ J ^ (a + b) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul hu hv
    have := Ideal.pow_le_pow_right hab huv
    rwa [hJ, Ideal.mem_bot] at this
  rw [show J ^ n = J * J ^ (n - 1) by rw [← pow_succ', show n - 1 + 1 = n by omega]] at hx
  refine Submodule.mul_induction_on hx (fun m hm c hc ↦ ?_) fun y z hy hz ↦ by
    rw [map_add, hy, hz]
  have h₁ := hmul (by rwa [pow_one] : m ∈ J ^ 1) (hF c) (by omega)
  have h₂ := hmul (hF m) hc (by omega)
  have h₃ := hmul (hF m) (hF c) (by omega)
  rw [map_mul]
  linear_combination h₁ + h₂ + h₃

set_option maxHeartbeats 1600000 in
-- The quotient and lifting calculation creates a large elaboration term.
open MvPolynomial in
/-- For `n ≥ 2`, if the comparison map `P ⧸ Jⁿ → S ⧸ Iⁿ` is bijective then `P ⧸ Jⁿ⁺¹ → S ⧸ Iⁿ⁺¹`
is injective. Formal smoothness of `S` over `R` lifts `S → S ⧸ Iⁿ ≅ P ⧸ Jⁿ` along the square-zero
surjection `q : P ⧸ Jⁿ⁺¹ → P ⧸ Jⁿ`, and the lift descends to `Θ : S ⧸ Iⁿ⁺¹ → P ⧸ Jⁿ⁺¹` because it
carries `I` into the ideal of variables. The composite of `Θ` with the comparison map differs from
the identity by an element of `Ker q`, so it fixes `Ker q` pointwise: `Ker q` is the `n`-th power
of an ideal whose `(n+1)`-st power vanishes, and `2n ≥ n + 1`. -/
private theorem quotientComparison_step_injective_ge_two (h : Algebra.Smooth R S)
    (t : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → S)
    (htI : ∀ i, t i ∈ RingHom.ker σ)
    (n : ℕ) (hn : 2 ≤ n)
    (hind : Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker σ) ^ n)
        (MvPolynomial.aeval (R := R) (fun i => t i) :
          MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S)
        (comparisonMap_pow_le σ _ t htI n))) :
    Function.Injective
      (Ideal.quotientMapₐ ((RingHom.ker σ) ^ (n + 1))
        (MvPolynomial.aeval (R := R) (fun i => t i) :
          MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S)
        (comparisonMap_pow_le σ _ t htI (n + 1))) := by
  classical
  have : Algebra.FormallySmooth R S := h.formallySmooth
  set Ψ : MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S :=
    MvPolynomial.aeval (fun i => t i) with hΨ
  set Ψn := Ideal.quotientMapₐ ((RingHom.ker σ) ^ n) Ψ (comparisonMap_pow_le σ _ t htI n) with hΨn
  set Ψn1 := Ideal.quotientMapₐ ((RingHom.ker σ) ^ (n + 1)) Ψ
    (comparisonMap_pow_le σ _ t htI (n + 1)) with hΨn1
  set q : MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
        ⧸ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ (n + 1)
      →ₐ[R] MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
        ⧸ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega : n ≤ n + 1)) with hq
  set π : S ⧸ (RingHom.ker σ) ^ (n + 1) →ₐ[R] S ⧸ (RingHom.ker σ) ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega : n ≤ n + 1)) with hπ
  have hsquare : π.comp Ψn1 = Ψn.comp q := by
    apply Ideal.Quotient.algHom_ext R
    apply MvPolynomial.algHom_ext
    intro i
    simp [hπ, hq, hΨn, hΨn1, Ideal.quotientMapₐ, Ideal.quotientMap_mk,
      Ideal.Quotient.factorₐ, Ideal.Quotient.factor_mk]
  set eₙ := AlgEquiv.ofBijective Ψn hind with heₙ
  set g : S →ₐ[R] MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
        ⧸ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ n :=
    eₙ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R ((RingHom.ker σ) ^ n)) with hg
  have hqsurj : Function.Surjective q := by
    rw [hq]
    show Function.Surjective (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : n ≤ n +
        1)))
    intro y; obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ z, Ideal.Quotient.factor_mk _ z⟩
  have hnil : IsNilpotent (RingHom.ker (q.toRingHom)) := by
    rw [hq]
    show IsNilpotent (RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : n ≤
        n + 1))))
    rw [Ideal.Quotient.factor_ker]
    refine ⟨2, ?_⟩
    rw [← Ideal.map_pow]
    have hle : ((idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ n) ^ 2
        ≤ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ (n + 1) := by
      rw [← pow_mul]; exact Ideal.pow_le_pow_right (by omega)
    show Ideal.map (Ideal.Quotient.mk _) (_ ^ 2) = ⊥
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hle
  set Θt : S →ₐ[R] MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
        ⧸ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ (n + 1) :=
    Algebra.FormallySmooth.liftOfSurjective g q hqsurj hnil with hΘt
  have hΘtq : q.comp Θt = g := Algebra.FormallySmooth.comp_liftOfSurjective g q hqsurj hnil
  have hσkill : ∀ (m : ℕ), 1 ≤ m → ∀ a ∈ (RingHom.ker σ) ^ m, σ a = 0 := fun m hm a ha ↦
    RingHom.mem_ker.mp (Ideal.pow_le_self (by omega) ha)
  set σbar : S ⧸ (RingHom.ker σ) ^ n →ₐ[R] R :=
    Ideal.Quotient.liftₐ ((RingHom.ker σ) ^ n) σ (hσkill n (by omega)) with hσbar
  have hσbar_mk : σbar.comp (Ideal.Quotient.mkₐ R ((RingHom.ker σ) ^ n)) = σ :=
    Ideal.Quotient.liftₐ_comp _ σ _
  have hε0 : ∀ (m : ℕ), 1 ≤ m → ∀ p ∈ (idealOfVars (Fin (Module.finrank R (RingHom.ker
      σ).Cotangent)) R) ^ m,
      (MvPolynomial.aeval (R := R) (0 : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → R)) p
        = 0 := by
    intro m hm p hp
    have hp1 : p ∈ idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R :=
      (Ideal.pow_le_self (by omega)) hp
    rw [← pow_one (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R),
      mem_pow_idealOfVars_iff'] at hp1
    have h0 := hp1 0 (by simp)
    have : (MvPolynomial.aeval (0 : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → R)) p
        = MvPolynomial.constantCoeff p := by simp [MvPolynomial.constantCoeff_eq]
    rw [this, ← MvPolynomial.constantCoeff_eq] at *
    simpa using h0
  set εn : MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
        ⧸ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ n →ₐ[R] R :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (0 : Fin (Module.finrank R (RingHom.ker
        σ).Cotangent) → R))
      (hε0 n (by omega)) with hεn
  set εn1 : MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
        ⧸ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ (n + 1) →ₐ[R] R :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (0 : Fin (Module.finrank R (RingHom.ker
        σ).Cotangent) → R))
      (hε0 (n + 1) (by omega)) with hεn1
  have hεcomp : εn.comp q = εn1 := by
    apply Ideal.Quotient.algHom_ext R
    apply MvPolynomial.algHom_ext
    intro i
    simp [hεn, hεn1, hq, Ideal.Quotient.factorₐ, Ideal.Quotient.factor_mk]
  have hinter : σbar.comp Ψn = εn := by
    apply Ideal.Quotient.algHom_ext R
    apply MvPolynomial.algHom_ext
    intro i
    simp [hσbar, hεn, hΨn, hΨ, Ideal.quotientMapₐ, Ideal.quotientMap_mk,
      RingHom.mem_ker.mp (htI i)]
  have hΘtI : Ideal.map Θt (RingHom.ker σ) ≤
      Ideal.map (Ideal.Quotient.mk ((idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent))
          R) ^ (n + 1)))
        (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    have hval : εn1 (Θt x) = 0 := by
      have h1 : εn1 (Θt x) = εn (q (Θt x)) := by rw [← hεcomp]; rfl
      rw [h1]
      have h2 : q (Θt x) = g x := by rw [← hΘtq]; rfl
      rw [h2, hg]
      have h3 : εn = σbar.comp Ψn := hinter.symm
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [h3]
      simp only [AlgHom.comp_apply]
      have h4 : ∀ z, Ψn ((eₙ.symm : _ →ₐ[R] _) z) = z := by
        intro z
        have : Ψn ((eₙ.symm : _ →ₐ[R] _) z) = eₙ (eₙ.symm z) := by
          rw [heₙ]; rfl
        rw [this, AlgEquiv.apply_symm_apply]
      rw [h4]
      have hσx : σbar (Ideal.Quotient.mk ((RingHom.ker σ)^n) x) = σ x := by
        simpa [Ideal.Quotient.mkₐ_eq_mk] using AlgHom.congr_fun hσbar_mk x
      rw [hσx]
      rwa [RingHom.mem_ker] at hx
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (Θt x)
    rw [← hp] at hval ⊢
    have hp0 :
        (MvPolynomial.aeval (0 : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → R)) p = 0 := by
      rwa [hεn1, Ideal.Quotient.liftₐ_apply] at hval
    exact Ideal.mem_map_of_mem _ (mem_idealOfVars_of_aeval_zero p hp0)
  set Jbar : Ideal (MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
        ⧸ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ (n + 1)) :=
    Ideal.map (Ideal.Quotient.mk _) (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent))
        R)
    with hJbar
  have hJbarpow : Jbar ^ (n + 1) = ⊥ := by
    rw [hJbar, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  have hΘtkill : ∀ a ∈ (RingHom.ker σ) ^ (n + 1), Θt a = 0 := by
    have hmap : Ideal.map Θt ((RingHom.ker σ) ^ (n + 1)) ≤ ⊥ := by
      rw [Ideal.map_pow]
      calc (Ideal.map Θt (RingHom.ker σ)) ^ (n + 1)
          ≤ Jbar ^ (n + 1) := Ideal.pow_right_mono hΘtI _
        _ = ⊥ := hJbarpow
    exact fun a ha ↦ by simpa using hmap (Ideal.mem_map_of_mem _ ha)
  set Θ : S ⧸ (RingHom.ker σ) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
        ⧸ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ (n + 1) :=
    Ideal.Quotient.liftₐ ((RingHom.ker σ) ^ (n + 1)) Θt hΘtkill with hΘ
  have hΘmk : Θ.comp (Ideal.Quotient.mkₐ R ((RingHom.ker σ) ^ (n + 1))) = Θt :=
    Ideal.Quotient.liftₐ_comp _ Θt hΘtkill
  set F := Θ.comp Ψn1 with hF
  have hqF : q.comp F = q := by
    apply Ideal.Quotient.algHom_ext R
    apply MvPolynomial.algHom_ext
    intro i
    have hΨn1X : Ψn1 (Ideal.Quotient.mk _ (MvPolynomial.X i))
        = Ideal.Quotient.mk ((RingHom.ker σ) ^ (n + 1)) (t i) := by
      have : Ψn1 (Ideal.Quotient.mk _ (MvPolynomial.X i))
          = Ideal.Quotient.mk _ (Ψ (MvPolynomial.X i)) := by
        simp [hΨn1, Ideal.quotientMapₐ, Ideal.quotientMap_mk]
      rw [this]; simp [hΨ]
    show q (F (Ideal.Quotient.mk _ (MvPolynomial.X i))) = q (Ideal.Quotient.mk _ (MvPolynomial.X
        i))
    rw [hF]
    simp only [AlgHom.comp_apply]
    rw [hΨn1X]
    have hΘti : Θ (Ideal.Quotient.mk ((RingHom.ker σ) ^ (n + 1)) (t i)) = Θt (t i) := by
      simpa [Ideal.Quotient.mkₐ_eq_mk] using AlgHom.congr_fun hΘmk (t i)
    rw [hΘti]
    have hgti : q (Θt (t i)) = g (t i) := by rw [← hΘtq]; rfl
    rw [hgti, hg]
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    have hqXi : q (Ideal.Quotient.mk _ (MvPolynomial.X i))
        = Ideal.Quotient.mk ((idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ n)
            (MvPolynomial.X i) := by
      rw [hq]; simp [Ideal.Quotient.factorₐ, Ideal.Quotient.factor_mk]
    rw [hqXi]
    apply eₙ.injective
    have hsa : eₙ ((eₙ.symm : _ →ₐ[R] _) (Ideal.Quotient.mk ((RingHom.ker σ) ^ n) (t i)))
        = Ideal.Quotient.mk ((RingHom.ker σ) ^ n) (t i) :=
      eₙ.apply_symm_apply _
    rw [hsa]
    have hb : eₙ (Ideal.Quotient.mk _ (MvPolynomial.X i))
        = Ψn (Ideal.Quotient.mk _ (MvPolynomial.X i)) := by
      rw [heₙ]; rfl
    rw [hb]
    have : Ψn (Ideal.Quotient.mk _ (MvPolynomial.X i))
        = Ideal.Quotient.mk ((RingHom.ker σ) ^ n) (Ψ (MvPolynomial.X i)) := by
      simp [hΨn, Ideal.quotientMapₐ, Ideal.quotientMap_mk]
    rw [this]; simp [hΨ]
  have hkerq : RingHom.ker q = Jbar ^ n := by
    rw [hq]
    show RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : n ≤ n + 1))) = _
    rw [Ideal.Quotient.factor_ker, hJbar, ← Ideal.map_pow]
  have hFsub : ∀ z, F z - z ∈ RingHom.ker q := by
    intro z
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact AlgHom.congr_fun hqF z
  have hFid : ∀ x ∈ RingHom.ker q, F x = x := fun x hx ↦
    RingHom.eq_self_of_sub_mem_pow F hn hJbarpow
      (fun z ↦ by rw [← hkerq]; exact hFsub z) (by rwa [hkerq] at hx)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hqx : q x = 0 := by
    have := AlgHom.congr_fun hsquare x
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hx, map_zero] at this
    apply hind.left
    rw [map_zero, ← this]
  calc x = F x := (hFid x (RingHom.mem_ker.mpr hqx)).symm
    _ = 0 := by rw [hF, AlgHom.comp_apply, hx, map_zero]

open MvPolynomial in
/-- For `n ≥ 1`, if the comparison map `P ⧸ Jⁿ → S ⧸ Iⁿ` is bijective then `P ⧸ Jⁿ⁺¹ → S ⧸ Iⁿ⁺¹`
is injective. -/
private theorem quotientComparison_step_injective (h : Algebra.Smooth R S)
    (b : Module.Basis (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
            (RingHom.ker σ).Cotangent)
    (t : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → S)
    (htI : ∀ i, t i ∈ RingHom.ker σ)
    (ht : ∀ i, (RingHom.ker σ).toCotangent ⟨t i, htI i⟩ = b i)
    (n : ℕ) (hn : 1 ≤ n)
    (hind : Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker σ) ^ n)
        (MvPolynomial.aeval (R := R) (fun i => t i) :
          MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S)
        (comparisonMap_pow_le σ _ t htI n))) :
    Function.Injective
      (Ideal.quotientMapₐ ((RingHom.ker σ) ^ (n + 1))
        (MvPolynomial.aeval (R := R) (fun i => t i) :
          MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S)
        (comparisonMap_pow_le σ _ t htI (n + 1))) := by
  obtain rfl | ⟨m, rfl⟩ : n = 1 ∨ ∃ m, n = m + 2 := by
    rcases n with _ | _ | m
    · exact absurd hn (by norm_num)
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  · exact quotientComparison_two_injective σ b t htI ht
  · exact quotientComparison_step_injective_ge_two σ h t htI (m + 2)
      (by omega) hind

open MvPolynomial in
/-- Every truncated comparison map `P ⧸ Jⁿ → S ⧸ Iⁿ` is bijective. -/
private theorem quotientComparison_bijective (h : Algebra.Smooth R S)
    (b : Module.Basis (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
            (RingHom.ker σ).Cotangent)
    (t : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → S)
    (htI : ∀ i, t i ∈ RingHom.ker σ)
    (ht : ∀ i, (RingHom.ker σ).toCotangent ⟨t i, htI i⟩ = b i)
    (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker σ) ^ n)
        (MvPolynomial.aeval (R := R) (fun i => t i) :
          MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S)
        (comparisonMap_pow_le σ _ t htI n)) := by
  rcases n with _ | n
  · exact quotientComparison_bijective_zero σ _ t htI
  · induction n with
    | zero => exact quotientComparison_bijective_one σ _ t htI
    | succ k ih =>
        exact ⟨quotientComparison_step_injective σ h b t htI ht (k + 1) (Nat.le_add_left 1 k) ih,
          quotientComparison_step_surjective σ b t htI ht (k + 1) ih⟩

open MvPolynomial in
/-- The truncated comparison maps are `R`-algebra isomorphisms `P ⧸ Jⁿ ≃ₐ[R] S ⧸ Iⁿ` compatible
with the transition maps of the two towers of quotients. -/
private theorem quotientPow_compatible_algEquiv (h : Algebra.Smooth R S)
    (b : Module.Basis (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
            (RingHom.ker σ).Cotangent)
    (t : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → S)
    (ht : ∀ i, ∃ hi : t i ∈ RingHom.ker σ,
        (RingHom.ker σ).toCotangent ⟨t i, hi⟩ = b i) :
    ∃ e : ∀ n, (MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
            ⧸ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ n)
            ≃ₐ[R] (S ⧸ (RingHom.ker σ) ^ n),
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (e n).toAlgHom
        = (e m).toAlgHom.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) := by
  have htI : ∀ i, t i ∈ RingHom.ker σ := fun i => (ht i).choose
  let Ψ : MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R →ₐ[R] S :=
    MvPolynomial.aeval (fun i => t i)
  let Ψn : ∀ n, (MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
      ⧸ (idealOfVars (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) ^ n)
      →ₐ[R] (S ⧸ (RingHom.ker σ) ^ n) :=
    fun n => Ideal.quotientMapₐ ((RingHom.ker σ) ^ n) Ψ (comparisonMap_pow_le σ _ t htI n)
  have hbij : ∀ n, Function.Bijective (Ψn n) :=
    fun n => quotientComparison_bijective σ h b t htI (fun i => (ht i).choose_spec) n
  refine ⟨fun n => AlgEquiv.ofBijective (Ψn n) (hbij n), ?_⟩
  intro m n hmn
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro i
  show (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
        ((AlgEquiv.ofBijective (Ψn n) (hbij n)) (Ideal.Quotient.mk _ (MvPolynomial.X i)))
      = (AlgEquiv.ofBijective (Ψn m) (hbij m))
          ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
            (Ideal.Quotient.mk _ (MvPolynomial.X i)))
  simp only [AlgEquiv.coe_ofBijective, Ψn, Ideal.quotientMapₐ, Ideal.Quotient.factorₐ,
    Ideal.quotientMap_mk, Ideal.Quotient.factor_mk, AlgHom.coe_mk]

/-- A family of `R`-algebra maps `P ⧸ Jⁿ → S ⧸ Iⁿ` compatible with the transition maps of the two
towers of quotients assembles into an `R`-algebra map of the `J`-adic and `I`-adic completions. -/
private theorem exists_adicCompletion_algHom_of_quotientPow
    {P S : Type*} [CommRing P] [CommRing S] [Algebra R P] [Algebra R S]
    (J : Ideal P) (I : Ideal S) (f : ∀ n, (P ⧸ J ^ n) →ₐ[R] (S ⧸ I ^ n))
    (hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (f n)
        = (f m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))) :
    ∃ F : AdicCompletion J P →ₐ[R] AdicCompletion I S,
      ∀ (n : ℕ) (x : AdicCompletion J P),
        AdicCompletion.evalₐ I n (F x) = f n (AdicCompletion.evalₐ J n x) := by
  have hev : ∀ {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion J P),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn : J ^ n ≤ J ^ m))
          ((AdicCompletion.evalₐ J n) x)
      = (AdicCompletion.evalₐ J m) x := by
    intro m n hmn x
    obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective J P x
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
    exact AdicCompletion.Ideal.mk_eq_mk J hmn a
  refine ⟨AdicCompletion.liftAlgHom I
    (fun n => (f n).comp ((AdicCompletion.evalₐ J n).restrictScalars R)) fun {m n} hmn => ?_,
    fun n x => AdicCompletion.evalₐ_liftAlgHom _ _ _ n x⟩
  ext x
  have h1 := AlgHom.congr_fun (hcompat hmn) ((AdicCompletion.evalₐ J n) x)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hev hmn x] at h1
  exact h1

/-- A family of `R`-algebra isomorphisms `P ⧸ Jⁿ ≃ₐ[R] S ⧸ Iⁿ` compatible with the transition
maps of the two towers of quotients assembles into an `R`-algebra isomorphism of the `J`-adic and
the `I`-adic completion. -/
private theorem adicCompletion_algEquiv_of_quotientPow
    {P S : Type*} [CommRing P] [CommRing S] [Algebra R P] [Algebra R S]
    (J : Ideal P) (I : Ideal S)
    (e : ∀ n, (P ⧸ J ^ n) ≃ₐ[R] (S ⧸ I ^ n))
    (hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (e n).toAlgHom
        = (e m).toAlgHom.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))) :
    Nonempty (AdicCompletion J P ≃ₐ[R] AdicCompletion I S) := by
  obtain ⟨F, hF⟩ :=
    exists_adicCompletion_algHom_of_quotientPow J I (fun n => (e n).toAlgHom) hcompat
  obtain ⟨G, hG⟩ := exists_adicCompletion_algHom_of_quotientPow I J
    (fun n => (e n).symm.toAlgHom) fun {m n} hmn ↦ AlgHom.ext fun x ↦ by
      apply (e m).injective
      simpa using (AlgHom.congr_fun (hcompat hmn) ((e n).symm x)).symm
  refine ⟨AlgEquiv.ofAlgHom F G (AlgHom.ext fun x ↦ ?_) (AlgHom.ext fun x ↦ ?_)⟩ <;>
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_ <;> simp [hF, hG]

open MvPolynomial in
/-- Evaluation `X i ↦ t i` at lifts `t` of an `R`-basis of `I/I²` induces an `R`-algebra
isomorphism from the completion of `MvPolynomial (Fin d) R` at the ideal of variables to the
`I`-adic completion of `S`. -/
private theorem adicCompletion_polynomial_algEquiv (h : Algebra.Smooth R S)
    (b : Module.Basis (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R
            (RingHom.ker σ).Cotangent)
    (t : Fin (Module.finrank R (RingHom.ker σ).Cotangent) → S)
    (ht : ∀ i, ∃ hi : t i ∈ RingHom.ker σ,
        (RingHom.ker σ).toCotangent ⟨t i, hi⟩ = b i) :
    Nonempty
      (AdicCompletion (MvPolynomial.idealOfVars
          (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R)
          (MvPolynomial (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R)
        ≃ₐ[R] AdicCompletion (RingHom.ker σ) S) := by
  obtain ⟨e, hcompat⟩ := quotientPow_compatible_algEquiv σ h b t ht
  exact adicCompletion_algEquiv_of_quotientPow _ _ e (fun {m n} hmn => hcompat hmn)

open MvPolynomial in
/-- Part (2) of Stacks tag 05D5: the completion is a power series ring when the conormal
module is free. If `S` is a smooth `R`-algebra, `σ : S →ₐ[R] R`, and the conormal module `I/I²` of
`I = Ker(σ)` is free (necessarily of finite rank `d := Module.finrank R (I/I²)` by (1)),
then the `I`-adic completion `S^∧` is isomorphic, as an `R`-algebra, to the formal power
series `R`-algebra in `d` variables `R[[t_1, …, t_d]]`. -/
@[stacks 05D5 "(2)",
  sga "1 II 4.17" "affine case, (i)⇒(iii)",
  ega "0 19.0.2" "special case",
  ega "0 19.5.4" "a) ⇒ c)",
  ega "0 19.5.4.4" "partial",
  ega "0 21.9.2" "special case",
  ega "IV 17.5.3" "partial",
  sga "1 III 1.5" "necessity, special case",
  sga "3 VIIB 5.5.2" "partial",
  sga "3 XI 1.2" "(ii), special case"]
theorem adicCompletion_algEquiv_mvPowerSeries (h : Algebra.Smooth R S)
    (hfree : Module.Free R (RingHom.ker σ).Cotangent) :
    Nonempty (AdicCompletion (RingHom.ker σ) S ≃ₐ[R]
      MvPowerSeries (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R) := by
  set d := Module.finrank R (RingHom.ker σ).Cotangent with hd
  obtain ⟨b, t, ht⟩ := exists_cotangentBasis_lift σ h hfree
  obtain ⟨e⟩ := adicCompletion_polynomial_algEquiv σ h b t ht
  let eMv : MvPowerSeries (Fin d) R ≃ₐ[R]
      AdicCompletion (idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) :=
    (MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) R).restrictScalars R
  exact ⟨(e.symm.trans eMv.symm)⟩

end AdicCompletion

section ConormalSequence

open scoped TensorProduct

/-- **Stacks 00TL, the direction that asks nothing of the cover** (equivalently, Stacks 031J
`1 → 2`): a formally smooth `R`-algebra `S` is a retract of every `R`-algebra covering it with
nilpotent kernel, that is, every surjection `g : B →ₐ[R] S` with `RingHom.ker g` nilpotent admits
an `R`-algebra section. Mathlib's `Algebra.FormallySmooth.iff_split_surjection` is the
corresponding equivalence, whose converse direction assumes `B` formally smooth over `R`. -/
private theorem Algebra.FormallySmooth.exists_section_of_isNilpotent_ker {R B S : Type*}
    [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]
    [Algebra.FormallySmooth R S] (g : B →ₐ[R] S) (hg : Function.Surjective g)
    (hg' : IsNilpotent (RingHom.ker g.toRingHom)) : ∃ s : S →ₐ[R] B, g.comp s = AlgHom.id R S :=
  ⟨Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) g hg hg',
    Algebra.FormallySmooth.comp_liftOfSurjective _ _ hg hg'⟩

/-- **Stacks 06A6.** If `S` is a formally smooth `R`-algebra and `P → S` is surjective with kernel
`J`, then the canonical map `J/J² → S ⊗[P] Ω[P⁄R]` of Stacks 00RU admits a retraction, so that the
sequence `0 → J/J² → S ⊗[P] Ω[P⁄R] → Ω[S⁄R] → 0` is split exact. Nothing is required of `P`. -/
@[stacks 06A6 "Split exactness, i.e. the two assertions of the tag that are not already in Mathlib
(exactness at `Ω_{B/A} ⊗_B C` is `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` and
surjectivity on the right is `KaehlerDifferential.mapBaseChange_surjective`), stated as the
existence of a retraction of the injection `J/J² → Ω_{B/A} ⊗_B C`: that single datum is at once its
injectivity and the splitting. See the module docstring.",
  ega "0 20.5.14" "injectivity, splitting",
  ega "IV 17.2.5" "injectivity, affine",
  ega "0 22.4.6" "(22.4.6.1)",
  sga "3 III 4.25" "(ii) inj. + splitting", ega "0 22.4.4.2" "partial"]
public theorem KaehlerDifferential.exists_retraction_kerCotangentToTensor (R P S : Type*)
    [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra P S] [Algebra R S]
    [IsScalarTower R P S] [Algebra.FormallySmooth R S]
    (hf : Function.Surjective (algebraMap P S)) :
    ∃ l : S ⊗[P] Ω[P⁄R] →ₗ[P] (RingHom.ker (algebraMap P S)).Cotangent,
      l ∘ₗ kerCotangentToTensor R P S = LinearMap.id := by
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_section_of_isNilpotent_ker
    (IsScalarTower.toAlgHom R P S).kerSquareLift
    (fun x ↦ by obtain ⟨y, rfl⟩ := hf x; exact ⟨Ideal.Quotient.mk _ y, rfl⟩)
    (by rw [AlgHom.ker_kerSquareLift]; exact ⟨2, Ideal.cotangentIdeal_square _⟩)
  exact ⟨_, ((retractionKerCotangentToTensorEquivSection hf).symm ⟨g, hg⟩).2⟩

/-- A retraction of the left hand map of the sequence `J/J² → S ⊗[P] Ω[P⁄R] → Ω[S⁄R] → 0` of
Stacks 00RU makes it split short exact: the left hand map is then injective and the right hand map
admits an `S`-linear section. This is the splitting lemma, so no smoothness is involved; the two
remaining thirds of exactness hold for every surjection `P → S`. The retraction is `P`-linear and
so is the section it produces, which is upgraded to an `S`-linear one along the surjection
`P → S`. -/
private theorem KaehlerDifferential.split_exact_of_retraction_kerCotangentToTensor (R P S : Type*)
    [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra P S] [Algebra R S]
    [IsScalarTower R P S] (hf : Function.Surjective (algebraMap P S))
    {l : S ⊗[P] Ω[P⁄R] →ₗ[P] (RingHom.ker (algebraMap P S)).Cotangent}
    (hl : l ∘ₗ kerCotangentToTensor R P S = LinearMap.id) :
    Function.Injective (kerCotangentToTensor R P S) ∧
      ∃ σ : Ω[S⁄R] →ₗ[S] S ⊗[P] Ω[P⁄R], mapBaseChange R P S ∘ₗ σ = LinearMap.id := by
  have hinj : Function.Injective (kerCotangentToTensor R P S) :=
    Function.LeftInverse.injective (g := l) (LinearMap.congr_fun hl)
  have hsplit := ((exact_kerCotangentToTensor_mapBaseChange R P S hf).split_tfae
    (g := (mapBaseChange R P S).restrictScalars P) hinj
    (mapBaseChange_surjective R P S hf)).out 2 1
  obtain ⟨σ, hσ⟩ := hsplit.mp ⟨l, hl⟩
  exact ⟨hinj, LinearMap.extendScalarsOfSurjective hf σ,
    LinearMap.ext fun x ↦ LinearMap.congr_fun hσ x⟩

/-- **Stacks 06A8.** Let `R → P → S` be ring maps with `R → S` smooth and `P → S` surjective with
kernel `J`. Then the exact sequence `0 → J/J² → S ⊗[P] Ω[P⁄R] → Ω[S⁄R] → 0` of Stacks 00RU is
split short exact: its left hand map `J/J² → S ⊗[P] Ω[P⁄R]` is injective and its right hand map
`S ⊗[P] Ω[P⁄R] → Ω[S⁄R]` admits an `S`-linear section. Only formal smoothness of `R → S` is used,
and nothing is required of `P`. -/
@[stacks 06A8 "Stated for a formally smooth `R → S`, which is the source's own generalisation
06A6, and with no hypothesis on `P`. Split exactness is recorded as injectivity of the left hand
map together with an `S`-linear section of the right hand map, the exactness of the sequence of
00RU in the middle and on the right being Mathlib's
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` and
`KaehlerDifferential.mapBaseChange_surjective`. See the module docstring.",
  ega "0 20.5.14"
  "injectivity, splitting",
  ega "IV 17.2.5" "affine case",
  sga "3 III 4.25" "(ii) inj. + splitting",
  ega "0 20.5.14" "injectivity, splitting", ega "0 20.6.22" "partial", ega "0 22.4.4.2" "partial"]
theorem KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange
    (R P S : Type*) [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra P S]
    [Algebra R S] [IsScalarTower R P S] [Algebra.FormallySmooth R S]
    (hf : Function.Surjective (algebraMap P S)) :
    Function.Injective (kerCotangentToTensor R P S) ∧
      ∃ σ : Ω[S⁄R] →ₗ[S] S ⊗[P] Ω[P⁄R], mapBaseChange R P S ∘ₗ σ = LinearMap.id :=
  (exists_retraction_kerCotangentToTensor R P S hf).elim fun _ hl ↦
    split_exact_of_retraction_kerCotangentToTensor R P S hf hl

/-- If `σ : B →ₐ[A] A ⧸ I ^ 2` carries the ideal `J ≤ B` into `I ⧸ I²`, then the map it induces on
conormal modules retracts `Ideal.mapCotangent I J (Algebra.ofId A B) : I/I² → J/J²`. No
compatibility between `σ` and `A → B` is assumed beyond `σ` being a map of `A`-algebras, which is
exactly what forces the composite to be the identity. -/
private theorem Ideal.exists_retraction_mapCotangent_of_algHom
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) (J : Ideal B)
    (hIJ : I ≤ J.comap (Algebra.ofId A B)) (σ : B →ₐ[A] A ⧸ I ^ 2)
    (hσ : J ≤ I.cotangentIdeal.comap σ) :
    ∃ ρ : J.Cotangent →ₗ[A] I.Cotangent,
      ρ ∘ₗ Ideal.mapCotangent I J (Algebra.ofId A B) hIJ = LinearMap.id := by
  have hmul : ∀ x y : I.cotangentIdeal, (x * y : I.cotangentIdeal) = 0 := fun x y ↦ by
    refine Subtype.ext ?_
    have hx : (x : A ⧸ I ^ 2) * (y : A ⧸ I ^ 2) ∈ I.cotangentIdeal * I.cotangentIdeal :=
      Ideal.mul_mem_mul x.2 y.2
    rw [← pow_two, I.cotangentIdeal_square] at hx
    simpa using hx
  refine ⟨Ideal.Cotangent.lift I.cotangentEquivIdeal.symm.toLinearMap
      (fun x y ↦ by rw [hmul, map_zero]) ∘ₗ
      Ideal.mapCotangent J I.cotangentIdeal σ hσ, LinearMap.ext fun x ↦ ?_⟩
  obtain ⟨a, rfl⟩ := I.toCotangent_surjective x
  simp only [LinearMap.coe_comp, Function.comp_apply, Ideal.mapCotangent_toCotangent,
    Ideal.Cotangent.lift_toCotangent, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq]
  rw [LinearEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  simp only [Ideal.cotangentEquivIdeal_apply, Ideal.toCotangent_to_quotient_square,
    Algebra.ofId_apply, AlgHom.commutes]
  rfl

/-- **The lifting step of Stacks 06A7.** If `A → B` is formally smooth and `A → C` is surjective
with kernel `I`, then the `A`-algebra map `B → C` lifts along the square-zero surjection
`A ⧸ I² → C` to an `A`-algebra map `B → A ⧸ I²`. -/
private theorem Algebra.FormallySmooth.exists_algHom_quotient_kerSq
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [Algebra.FormallySmooth A B]
    (h : Function.Surjective (algebraMap A C)) :
    ∃ σ : B →ₐ[A] A ⧸ RingHom.ker (algebraMap A C) ^ 2,
      ∀ x : B, algebraMap (A ⧸ RingHom.ker (algebraMap A C) ^ 2) C (σ x) = algebraMap B C x := by
  set I := RingHom.ker (algebraMap A C)
  have hsurj : Function.Surjective (algebraMap (A ⧸ I ^ 2) C) := fun x ↦ by
    obtain ⟨y, rfl⟩ := h x; exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hnil : IsNilpotent (RingHom.ker (algebraMap (A ⧸ I ^ 2) C)) :=
    AlgHom.ker_kerSquareLift (Algebra.ofId A C) ▸ ⟨2, I.cotangentIdeal_square⟩
  exact ⟨Algebra.FormallySmooth.liftOfSurjective (IsScalarTower.toAlgHom A B C)
    (IsScalarTower.toAlgHom A (A ⧸ I ^ 2) C) hsurj hnil,
    Algebra.FormallySmooth.liftOfSurjective_apply _ _ hsurj hnil⟩

/-- **Stacks 06A9.** Let `A → B → C` be ring maps with `A → C` surjective and `A → B` smooth, and
put `I = ker (A → C)` and `J = ker (B → C)`. Then the map `I/I² → J/J²` of Stacks 065V admits an
`A`-linear left inverse; in particular it is injective, so that the sequence
`0 → I/I² → J/J² → Ω[B⁄A] ⊗[B] B/J → 0` of Stacks 065V is exact, indeed split exact. Only formal
smoothness of `A → B` is used. -/
@[stacks 06A9 "Stated for a formally smooth `A → B`, which is the source's own generalisation
06A7, and with the retraction that generalisation asserts rather than bare injectivity, the latter
following by `Function.LeftInverse.injective`. Exactness at `J/J²` and surjectivity of
`KaehlerDifferential.kerCotangentToTensor A B C` are the neighbouring tag 065V and are not
restated. See the module docstring."]
theorem Algebra.FormallySmooth.exists_leftInverse_mapCotangent
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [Algebra.FormallySmooth A B]
    (h : Function.Surjective (algebraMap A C)) :
    ∃ ρ : (RingHom.ker (algebraMap B C)).Cotangent →ₗ[A]
        (RingHom.ker (algebraMap A C)).Cotangent,
      ρ ∘ₗ Ideal.mapCotangent (RingHom.ker (algebraMap A C))
        (RingHom.ker (algebraMap B C)) (Algebra.ofId A B)
        (((RingHom.comap_ker (algebraMap B C) (algebraMap A B)).trans
          (congrArg RingHom.ker (IsScalarTower.algebraMap_eq A B C).symm)).ge) =
        LinearMap.id := by
  obtain ⟨s, hs⟩ := Algebra.FormallySmooth.exists_algHom_quotient_kerSq A B C h
  have hker : RingHom.ker (algebraMap (A ⧸ RingHom.ker (algebraMap A C) ^ 2) C)
      = (RingHom.ker (algebraMap A C)).cotangentIdeal :=
    AlgHom.ker_kerSquareLift (Algebra.ofId A C)
  refine Ideal.exists_retraction_mapCotangent_of_algHom _ _ _ s fun x hx ↦ ?_
  rw [Ideal.mem_comap, ← hker, RingHom.mem_ker, hs x]
  exact hx

end ConormalSequence

end

/-!
# The conormal sequence of a formally smooth algebra is split exact

Proof of Stacks 06A6. Let `R → P → S` be ring maps with `S` formally smooth over `R` and `P → S`
surjective with kernel `J`. Then the exact sequence
```
0 → J/J² → S ⊗[P] Ω[P⁄R] → Ω[S⁄R] → 0
```
of Stacks 00RU is split exact: the left hand map
`KaehlerDifferential.kerCotangentToTensor R P S` admits a `P`-linear retraction. In the source's
letters the tower is `A → B → C`, and nothing is required of the middle ring.

## Implementation notes

The argument is the first paragraph of the source's proof of Lemma 031I, in two steps:

* formal smoothness of `S` over `R` lifts the identity of `S` along the square-zero surjection
  `P ⧸ J² → S`, giving an `R`-algebra section of it (Lemma 00TL, forward direction);
* such a section is the same datum as a retraction of `J/J² → S ⊗[P] Ω[P⁄R]` (Lemmas 02HQ and
  02HP, packaged by Mathlib as `retractionKerCotangentToTensorEquivSection`).

Neither step asks anything of `P`, which is what makes the conclusion available for an arbitrary
`P`: the first is the lifting property of a formally smooth algebra along a square-zero
surjection, and the second is a bijection between the two kinds of splitting, for any surjection
`P → S`. The route the source sketches for 06A6, through Proposition 031J and Lemma 00S2, goes by
a longer road, and not to a more general place: 031J assumes `P` formally smooth over `R`, so
reaching a general `P` along it would mean splitting the sequence of a formally smooth
presentation `P' → S` factoring through `P`, and comparing the two sequences by the
Jacobi-Zariski sequence of `R → P → S`. The implication `1 → 2` of 031J is the step used here,
and it is the one implication of that proposition needing no hypothesis on `P`.

The whole content of the statement is therefore the first step, isolated below as the `private` lemma
`Algebra.FormallySmooth.exists_kerSquareLift_comp_eq_id`. Both of Mathlib's forms of it,
`Algebra.FormallySmooth.iff_split_surjection` and `Algebra.FormallySmooth.iff_split_injection`,
are equivalences carrying `[Algebra.FormallySmooth R P]`, which only their converse directions
need: for `S = P` the sequence is `0 → 0 → 0 → Ω[P⁄R] → 0` and splits whatever `P` is, so no
converse can drop that hypothesis.

## References

* [StacksProject 06A6](https://stacks.math.columbia.edu/tag/06A6)
* [StacksProject 031I](https://stacks.math.columbia.edu/tag/031I)
* [StacksProject 031J](https://stacks.math.columbia.edu/tag/031J)
* [StacksProject 00TL](https://stacks.math.columbia.edu/tag/00TL)
* [StacksProject 02HP](https://stacks.math.columbia.edu/tag/02HP)
* [StacksProject 02HQ](https://stacks.math.columbia.edu/tag/02HQ)
* [StacksProject 00RU](https://stacks.math.columbia.edu/tag/00RU)
-/

@[expose] public section

open scoped TensorProduct

/-- **Stacks 00TL, forward direction, with no hypothesis on `P`** (equivalently, Stacks 031J
`1 → 2`). If `S` is a formally smooth `R`-algebra and `f : P →ₐ[R] S` is surjective with kernel
`J`, then the square-zero surjection `f.kerSquareLift : P ⧸ J² → S` admits an `R`-algebra section.

Only the lifting property of a formally smooth algebra along a surjection with nilpotent kernel is
used, so nothing is required of `P`: the surjection is `f` composed with `Ideal.Quotient.mk`, and
its kernel is `J.cotangentIdeal` (`AlgHom.ker_kerSquareLift`), which squares to zero
(`Ideal.cotangentIdeal_square`). Mathlib's `Algebra.FormallySmooth.iff_split_surjection` is the
corresponding equivalence, whose converse direction assumes `P` formally smooth over `R`. -/
@[ega "0 19.3.10.1" "special case", ega "0 22.2.1" "more general"]
private theorem Algebra.FormallySmooth.exists_kerSquareLift_comp_eq_id {R P S : Type*}
    [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra R S]
    [Algebra.FormallySmooth R S] (f : P →ₐ[R] S) (hf : Function.Surjective f) :
    ∃ g : S →ₐ[R] P ⧸ RingHom.ker f ^ 2, f.kerSquareLift.comp g = AlgHom.id R S :=
  ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id R S) f.kerSquareLift
    (Ideal.Quotient.lift_surjective_of_surjective _ _ hf)
    (f.ker_kerSquareLift ▸ ⟨2, Ideal.cotangentIdeal_square _⟩)⟩

end

/-!
# The conormal sequence of a formally smooth algebra is split exact

Let `R → P → S` be ring maps with `P → S` surjective with kernel `J`. Stacks 00RU produces a
canonical exact sequence of `S`-modules
```
J/J² → S ⊗[P] Ω[P⁄R] → Ω[S⁄R] → 0 ,
```
whose left hand map sends the class of `f ∈ J` to `df ⊗ 1`. Stacks 06A6 says that as soon as `S`
is formally smooth over `R` this sequence is *split* exact, so that in particular the left hand
map is injective and `S ⊗[P] Ω[P⁄R] ≅ J/J² × Ω[S⁄R]`.

Nothing is required of `P`. Formal smoothness of `S` over `R` enters through the square-zero
surjection `P ⧸ J² → S`: the identity of `S` lifts along it to an `R`-algebra section, and such a
section is the same datum as a retraction of the left hand map `J/J² → S ⊗[P] Ω[P⁄R]`
(Stacks 031I, `retractionKerCotangentToTensorEquivSection`).

## Main results

* `KaehlerDifferential.exists_retraction_kerCotangentToTensor`: if `S` is a formally smooth
  `R`-algebra and `P → S` is surjective with kernel `J`, then `J/J² → S ⊗[P] Ω[P⁄R]` admits a
  retraction, i.e. the sequence `0 → J/J² → S ⊗[P] Ω[P⁄R] → Ω[S⁄R] → 0` of Stacks 00RU is split
  short exact.

## Implementation notes

Split exactness is recorded as a single datum, a retraction of the left hand map, rather than as
the conjunction "left hand map injective, right hand map admits a section". The two are
equivalent, and equivalent to the direct sum decomposition, by `Function.Exact.split_tfae`,
because the other two thirds of exactness hold for every surjection `P → S`: exactness at
`S ⊗[P] Ω[P⁄R]` is `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` and
surjectivity of the right hand map is `KaehlerDifferential.mapBaseChange_surjective`. A retraction
is the shape Mathlib uses for this idea (`Algebra.FormallySmooth.iff_split_injection`,
`Algebra.Extension.formallySmooth_iff_split_injection`) and the shape the sibling Stacks 031K
takes here (`KaehlerDifferential.exists_retraction_mapBaseChange`).

Only the implication "`S` formally smooth implies split exact" is asserted, and that is what makes
the statement available for an arbitrary `P`. Mathlib's
`Algebra.FormallySmooth.iff_split_injection` is the same implication turned into an equivalence at
the price of assuming `P` formally smooth over `R`, which its converse direction needs: for `S = P`
the sequence is `0 → 0 → 0 → Ω[P⁄R] → 0` and splits whatever `P` is.

The smooth case of this lemma is Stacks 06A8, which needs no separate argument: `Algebra.Smooth`
extends `Algebra.FormallySmooth` by `Algebra.FinitePresentation`, which the conclusion does not
see, and `Algebra.Smooth.formallySmooth` is an instance. It is proved in this library as
`KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange`, stated as the above
conjunction; that declaration follows from this one by `Function.Exact.split_tfae`.

Faithfulness. (1) Both hypotheses are used by the conclusion. Dropping formal smoothness of `S`
breaks it already for `R = ℚ`, `P = ℚ[x]`, `S = P ⧸ (x²)`: there `J = (x²)`, `J/J²` is free of
rank one on the class of `x²`, and `x · x² = x³ ≠ 0` in `J/J²` is sent to `3x² dx = 0`, so the
left hand map is not even injective. Dropping surjectivity of `P → S` breaks it for `R = ℚ`,
`P = ℚ[x, y]` and `S = ℚ(x)` along `y ↦ 0`, where `S` is formally smooth over `ℚ` and `J = (y)`
with `J/J² ≅ ℚ[x]` free on the class of `y`: a retraction `l` is `P`-linear and `dy = x • (x⁻¹ dy)`
in the divisible `S`-module `S ⊗[P] Ω[P⁄R]`, so `l dy ∈ ⋂ n, xⁿ • (J/J²) = 0`, while a retraction
must send `dy` to the class of `y`. (2) The scalars and base are the source's: both are relative
to `R` (the source's `A`), the tensor product is over `P` (the source's `B`), and the retraction is
`P`-linear, which for these two modules is the source's `S`-linearity (the source's `C`) — `J`
annihilates both `J/J²` and `S ⊗[P] Ω[P⁄R]`, so restriction along the surjection `P → S` is a
bijection on linear maps between them, `LinearMap.extendScalarsOfSurjectiveEquiv`. (3) The
canonical map of the source is pinned rather than asserted to exist: it is
`KaehlerDifferential.kerCotangentToTensor R P S`, characterised by
`KaehlerDifferential.kerCotangentToTensor_toCotangent` as the source's `f ↦ df ⊗ 1`, and the
composite is fixed to be `LinearMap.id`, so the retraction is a genuine splitting and not an
arbitrary map. (4) The instantiation is not degenerate: for `R = ℚ`, `P = ℚ[x, y]` and `S = ℚ[x]`
along `y ↦ 0` the hypotheses hold, `J = (y)`, and the sequence is
`0 → S · y → S dx ⊕ S dy → S dx → 0` with all three terms nonzero, so the splitting asserted is
not a splitting of a sequence of zero modules.

## References

* [StacksProject 06A6](https://stacks.math.columbia.edu/tag/06A6)
* [StacksProject 00RU](https://stacks.math.columbia.edu/tag/00RU)
* [StacksProject 031I](https://stacks.math.columbia.edu/tag/031I)
* [StacksProject 031J](https://stacks.math.columbia.edu/tag/031J)
* [StacksProject 06A8](https://stacks.math.columbia.edu/tag/06A8)
-/

/-!
# The conormal sequence of a formally smooth ring map is split exact

Proof of Stacks 06A7. Let `A → B → C` be ring maps with `A → C` surjective — so that `B → C` is
surjective too — and put `I = ker (A → C)` and `J = ker (B → C)`. Stacks 065V provides the exact
sequence
```
I/I² → J/J² → Ω[B⁄A] ⊗[B] B/J → 0
```
whose left hand map `ι` is `Ideal.mapCotangent` along `Algebra.ofId A B`, the source's
`a mod I² ↦ a mod J²`. Stacks 06A7 says that if `A → B` is formally smooth then `ι` admits a
retraction, so that the sequence is split short exact.

The argument is the source's. Surjectivity of `A → C` makes `A ⧸ I² → C` a surjection of
`A`-algebras whose kernel `I ⧸ I²` squares to zero, so formal smoothness of `A → B` lifts the
`A`-algebra map `B → C` to an `A`-algebra map `σ : B → A ⧸ I²`. Such a `σ` carries `J` into
`I ⧸ I²` and hence induces `ρ : J/J² → I/I²`, and `ρ ∘ ι = id` because `σ`, being a map of
`A`-algebras, restricts on the image of `A` to the quotient map `A → A ⧸ I²`.

## Main results

* `Stacks.Smooth.ConormalRetraction.solution`: `Ideal.mapCotangent I J (Algebra.ofId A B)` admits
  an `A`-linear retraction when `A → B` is formally smooth and `algebraMap A C` is surjective.

## Implementation notes

The proof splits into the two steps of the source's argument, neither of which mentions both
hypotheses, and each of which is stated with the conclusion the other one consumes:

* `Algebra.FormallySmooth.exists_algHom_ker_le_comap_cotangentIdeal` is the lifting step. The
  square-zero surjection it lifts `B → C` along is `algebraMap (A ⧸ I ^ 2) C`, which is Mathlib's
  `Ideal.Algebra.kerSquareLift` instance, i.e. `AlgHom.kerSquareLift` of `Algebra.ofId A C`; its
  kernel is `I.cotangentIdeal` (`AlgHom.ker_kerSquareLift`), which squares to zero
  (`Ideal.cotangentIdeal_square`), so the lift is `Algebra.FormallySmooth.liftOfSurjective`. The
  conclusion records not the lifting property but its one consequence used below, that `σ` carries
  `J` into `I ⧸ I²`.
* `Ideal.exists_retraction_mapCotangent_of_algHom` turns such a `σ` into the retraction, and needs
  no hypothesis on `A → B` and no third ring at all: for ideals `I ≤ A` and `J ≤ B` with `I`
  mapping into `J`, any `A`-algebra map `σ : B → A ⧸ I²` carrying `J` into `I ⧸ I²` retracts
  `Ideal.mapCotangent I J (Algebra.ofId A B)`. That `σ` is `A`-linear is what makes the composite
  the identity, which is why no compatibility of `σ` with `A → B` appears among its hypotheses.

The induced map `ρ` is assembled from Mathlib's functoriality `Ideal.mapCotangent` of `I ⧸ I²`
applied to `σ`, followed by `Ideal.Cotangent.lift` of the inverse of `Ideal.cotangentEquivIdeal`.
Concretely, `σ` induces `J/J² → (I/I²)/(I/I²)²` and the target is `I/I²` because `I ⧸ I²`, as an
ideal of `A ⧸ I²`, squares to zero; taking that route rather than restricting `σ` to `J` by hand
reuses the `A`-linearity Mathlib established for `Ideal.mapCotangent`. The side condition
`Ideal.Cotangent.lift` asks for is the elementwise form of square-zeroness,
`Ideal.mul_eq_zero_of_sq_eq_bot`, which Mathlib states only at the level of ideals.

## References

* [StacksProject 06A7](https://stacks.math.columbia.edu/tag/06A7)
* [StacksProject 065V](https://stacks.math.columbia.edu/tag/065V)
* [StacksProject 00TN](https://stacks.math.columbia.edu/tag/00TN)
-/

@[expose] public section

/-- Two elements of a square-zero ideal annihilate each other: the elementwise form of
`K ^ 2 = ⊥`, which is what `Ideal.Cotangent.lift` asks of a map defined on `K`. -/
private theorem Ideal.mul_eq_zero_of_sq_eq_bot {R : Type*} [CommRing R] {K : Ideal R}
    (hK : K ^ 2 = ⊥) (x y : K) : (x * y : K) = 0 :=
  Subtype.ext <| by simpa [hK] using (pow_two K).ge (Ideal.mul_mem_mul x.2 y.2)

/-- **Stacks 06A7, the lifting step.** If `A → B` is formally smooth and `A → C` is surjective with
kernel `I`, then the `A`-algebra map `B → C` lifts along the square-zero surjection `A ⧸ I² → C` to
an `A`-algebra map `σ : B → A ⧸ I²`; such a lift carries `ker (B → C)` into `I ⧸ I²`, which is the
only property of it that Stacks 06A7 uses. -/
private theorem Algebra.FormallySmooth.exists_algHom_ker_le_comap_cotangentIdeal
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [Algebra.FormallySmooth A B]
    (h : Function.Surjective (algebraMap A C)) :
    ∃ σ : B →ₐ[A] A ⧸ RingHom.ker (algebraMap A C) ^ 2,
      RingHom.ker (algebraMap B C) ≤
        (RingHom.ker (algebraMap A C)).cotangentIdeal.comap σ := by
  obtain ⟨s, hs⟩ := Algebra.FormallySmooth.exists_algHom_quotient_kerSq A B C h
  have hker : RingHom.ker (algebraMap (A ⧸ RingHom.ker (algebraMap A C) ^ 2) C)
      = (RingHom.ker (algebraMap A C)).cotangentIdeal :=
    AlgHom.ker_kerSquareLift (Algebra.ofId A C)
  refine ⟨s, fun x hx ↦ ?_⟩
  rw [Ideal.mem_comap, ← hker, RingHom.mem_ker, hs x]
  exact hx

namespace Stacks.Smooth.ConormalRetraction

/-- If `A → B` is formally smooth and `A → C` is surjective, then the map of conormal modules
`I/I² → J/J²` induced by `A → B`, where `I = ker (A → C)` and `J = ker (B → C)`, has an
`A`-linear left inverse. -/
public theorem solution
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [Algebra.FormallySmooth A B]
    (h : Function.Surjective (algebraMap A C)) :
    ∃ ρ : (RingHom.ker (algebraMap B C)).Cotangent →ₗ[A]
        (RingHom.ker (algebraMap A C)).Cotangent,
      ρ ∘ₗ Ideal.mapCotangent (RingHom.ker (algebraMap A C))
        (RingHom.ker (algebraMap B C)) (Algebra.ofId A B)
        (((RingHom.comap_ker (algebraMap B C) (algebraMap A B)).trans
          (congrArg RingHom.ker (IsScalarTower.algebraMap_eq A B C).symm)).ge) =
        LinearMap.id := by
  obtain ⟨σ, hσ⟩ :=
    Algebra.FormallySmooth.exists_algHom_ker_le_comap_cotangentIdeal A B C h
  exact Ideal.exists_retraction_mapCotangent_of_algHom _ _ _ σ hσ

end Stacks.Smooth.ConormalRetraction

end

/-!
# Split exactness of the conormal sequence of a formally smooth ring map

Let `A → B → C` be ring maps with `A → C` surjective — so that `B → C` is surjective as well — and
put `I = ker (A → C)` and `J = ker (B → C)`. Stacks 065V provides a canonical exact sequence
```
I/I² → J/J² → Ω[B⁄A] ⊗[B] B/J → 0 ,
```
whose left hand map `ι` sends the class of `a ∈ I` to the class of its image in `J`, and whose
right hand map sends the class of `x ∈ J` to `1 ⊗ dx`. Stacks 06A7 says that as soon as `A → B` is
formally smooth this sequence is *split* exact: `ι` is a split injection, so that
`0 → I/I² → J/J² → Ω[B⁄A] ⊗[B] B/J → 0` is a split short exact sequence and `J/J²` decomposes as
`I/I² × Ω[B⁄A] ⊗[B] B/J`.

Formal smoothness enters as it does in the source. Surjectivity of `A → C` identifies `C` with
`A ⧸ I`, so that `B → C` is a map of `A`-algebras into `A ⧸ I`; formal smoothness of `A → B` lifts
that map along the square-zero surjection `A ⧸ I² → A ⧸ I` to an `A`-algebra map `σ : B → A ⧸ I²`.
Such a `σ` carries `J` into `I ⧸ I²` and `J²` to zero, hence induces `ρ : J/J² → I/I²`, and
`ρ ∘ ι = id` because `σ` is a map of `A`-algebras.

## Main results

* `Algebra.FormallySmooth.exists_retraction_mapCotangent`: for `A → B` formally smooth and `A → C`
  surjective, the map `ι : I/I² → J/J²` of Stacks 065V admits a retraction. In particular `ι` is
  injective, and the sequence of Stacks 065V is split short exact.

## Implementation notes

Split exactness is recorded as a single datum, a retraction of `ι`, rather than as the conjunction
"`ι` injective, sequence exact, right hand map surjective". Given the exactness supplied by
Stacks 065V the two are equivalent, and equivalent to the direct sum decomposition, by
`Function.Exact.split_tfae`; and the two thirds of exactness that Stacks 065V provides hold with no
hypothesis whatever on `A → B`, so restating them here would decorate a hypothesis-free statement
with formal smoothness. A retraction is also the shape Mathlib uses for this idea
(`Algebra.FormallySmooth.iff_split_injection`, and
`Algebra.Extension.formallySmooth_iff_split_injection`) and the shape the neighbouring tags take in
this tree (Stacks 06A6, Stacks 031K).

The conormal module `I/I²` is `Ideal.Cotangent`, and `ι` is its functoriality `Ideal.mapCotangent`
for the algebra map `Algebra.ofId A B`; the side condition `I ≤ Ideal.comap (Algebra.ofId A B) J`
that `Ideal.mapCotangent` takes is not a hypothesis but the identity
`I = Ideal.comap (algebraMap A B) J`, supplied inline as in Mathlib's
`Ideal.mapCotangent_ker_of_surjective`. The right hand term `Ω[B⁄A] ⊗[B] B/J` of the sequence is
spelled `C ⊗[B] Ω[B⁄A]` by Mathlib, the same module along `B/J ≅ C`; it does not occur below.

The retraction is asserted `A`-linear. Both `I/I²` and `J/J²` are killed by `I`
(`Ideal.isTorsionBySet_cotangent`, and the image of `I` lies in `J`) while `A → C` is surjective
with kernel `I`, so `A`-linear maps between them are the same thing as the source's `C`-linear ones
(`LinearMap.extendScalarsOfSurjectiveEquiv`); `Ideal.Cotangent` carries the `A ⧸ I`-module
structure rather than a `C`-module one, which is why the statement is phrased over `A`.

The smooth case is Stacks 06A9, which needs no separate argument: `Algebra.Smooth` extends
`Algebra.FormallySmooth` by `Algebra.FinitePresentation`, which the conclusion does not see, and
`Algebra.Smooth.formallySmooth` is an instance. That tag is proved in this library as
`Algebra.FormallySmooth.exists_leftInverse_mapCotangent`, already at the present generality, so the
statement below and that one are the same theorem seen from its two tags.

Faithfulness. (1) Both hypotheses are live: formal smoothness cannot be dropped, since for
`A = ℚ[t] → B = ℚ[x]`, `t ↦ x²`, and `C = ℚ` the map `A → C` is surjective with `I = (t)` and
`I/I² ≅ ℚ` nonzero, while `J = (x)` and `ι` sends the class of `t` to `x² ∈ J²`, so `ι = 0` has no
retraction; and surjectivity of `A → C` is what identifies `C` with `A ⧸ I`, supplies the
square-zero extension `A ⧸ I² → C` the lift is taken along, and makes `Ω[B⁄A] ⊗[B] B/J` the
cokernel of `ι`. (2) The scalars and base are the source's: the two conormal modules are those of
the kernels of the source's own two maps, differentials are relative to `A` and tensored over `B`,
and `A`-linearity of the retraction is the source's `C`-linearity as above. (3) The canonical map
of the source is pinned rather than asserted to exist: it is `Ideal.mapCotangent` along
`Algebra.ofId A B`, characterised by `Ideal.mapCotangent_toCotangent` as the source's
`a mod I² ↦ a mod J²`, and the composite is fixed to be `LinearMap.id`, so the retraction is a
genuine splitting and not an arbitrary map. (4) The instantiation is not degenerate: for
`A = ℚ[t]`, `B = ℚ[t, y]` and `C = ℚ` with `t ↦ 0` and `y ↦ 0` the hypotheses hold, `I = (t)`,
`J = (t, y)`, and the sequence reads `0 → ℚ·t → ℚ·t ⊕ ℚ·y → ℚ·dy → 0` with all three terms nonzero,
the retraction being the projection onto the first summand.

## References

* [StacksProject 06A7](https://stacks.math.columbia.edu/tag/06A7)
* [StacksProject 065V](https://stacks.math.columbia.edu/tag/065V)
* [StacksProject 06A9](https://stacks.math.columbia.edu/tag/06A9)

## Tags

formally smooth, conormal module, cotangent module, split exact sequence
-/

@[expose] public section

/-- **Stacks 06A7.** Let `A → B → C` be ring maps with `A → C` surjective and `A → B` formally
smooth, and put `I = ker (A → C)` and `J = ker (B → C)`. Then the map `ι : I/I² → J/J²` of
Stacks 065V admits a retraction; in particular `ι` is injective, so that the sequence
`0 → I/I² → J/J² → Ω[B⁄A] ⊗[B] B/J → 0` of Stacks 065V is split short exact. -/
@[stacks 06A7 "Split exactness, i.e. the part of the tag that is not already the neighbouring tag
065V, stated as the existence of a retraction of the injection `I/I² → J/J²`: given 065V's exactness
that single datum is at once its injectivity and the splitting. Exactness at `J/J²` and surjectivity
of `KaehlerDifferential.kerCotangentToTensor A B C` are 065V, hold with no hypothesis on `A → B`,
and are not restated. See the module docstring."]
public theorem Algebra.FormallySmooth.exists_retraction_mapCotangent
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [Algebra.FormallySmooth A B]
    (h : Function.Surjective (algebraMap A C)) :
    ∃ ρ : (RingHom.ker (algebraMap B C)).Cotangent →ₗ[A]
        (RingHom.ker (algebraMap A C)).Cotangent,
      ρ ∘ₗ Ideal.mapCotangent (RingHom.ker (algebraMap A C))
        (RingHom.ker (algebraMap B C)) (Algebra.ofId A B)
        (((RingHom.comap_ker (algebraMap B C) (algebraMap A B)).trans
          (congrArg RingHom.ker (IsScalarTower.algebraMap_eq A B C).symm)).ge) =
        LinearMap.id := by exact Stacks.Smooth.ConormalRetraction.solution A B C h

end
