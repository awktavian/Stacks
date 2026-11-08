module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Interchanging direct products with tensor: the finitely generated case

Let `R` be a commutative ring and `M` an `R`-module. For a family `(Q α)` of `R`-modules the
canonical map `TensorProduct.piRightHom R R M Q : M ⊗[R] (∀ α, Q α) →ₗ[R] ∀ α, M ⊗[R] Q α` is
surjective for every family exactly when `M` is finitely generated, and the successively weaker
conditions of Stacks 059J already force this.

The argument is the source's, in the following form. A finite generating family `x : ι → M` lets
every element of `M ⊗[R] Q` be written as `∑ i, x i ⊗ₜ q i` with the *same* `x`; collecting the
right-hand factors of a family of such expressions over `α` produces a preimage under
`piRightHom`, which is the source's diagram with a surjection `R^n → M`. Conversely a single
instance suffices: for a module `Q` carrying an evaluation `e : M ⊗[R] Q →ₗ[R] M` which maps
`y ⊗ₜ q` into `R ∙ y` and admits the section `y ↦ y ⊗ₜ q₀`, surjectivity of the comparison map for
the constant family `Q` indexed by `M` exhibits the identity of `M` as a finite sum of maps
`x ↦ e (y ⊗ₜ b x)`, and the finitely many `y` occurring generate `M`. Both converse implications of
the source are that one lemma, for `Q = R ∙ (1 : Module.End R M)` with the evaluation of
endomorphisms, and for `Q = R` with `TensorProduct.rid`.

## Main results

* `Stacks.Module.FinitenessViaProducts.solution`: the proof of Stacks 059J, as stated in
  `Module.Finite.tfae_piRightHom_surjective`.

## Implementation notes

The source deduces (1) from (2) by tensoring with a surjection `R^n → M`; the equivalent form used
here, `Stacks.Module.FinitenessViaProducts.exists_fun_eq_sum_tmul`, is that surjectivity of `R^n
⊗[R] Q → M ⊗[R] Q` written elementwise, which avoids transporting a diagram through the isomorphism
`(Fin n → R) ⊗[R] Q ≃ₗ[R] (Fin n → Q)`.

The map of item 4 is the comparison map for the constant family `R`, read through
`M ⊗[R] R ≃ₗ[R] M`, so its surjectivity is equivalent to the condition of item 3 for `Q = R`
(`Stacks.Module.FinitenessViaProducts.surjective_piScalarRightHom_iff`). Both implications for
item 4 are obtained from that equivalence, so neither argument is repeated for it; that `R` lies
in `Type u` rather than in `Type v` is no obstruction, the two lemmas it is fed to being universe
polymorphic.

The source's step (3) ⇒ (4) tests item 3 on `R` itself, which item 3 does not allow: it quantifies
over modules in `Type v` while `R` lives in `Type u`. Item 3 is instead tested here on
`R ∙ (1 : Module.End R M)`, the `R`-submodule of endomorphisms spanned by the identity — the
scalars as they act on `M`, a module in `Type v` whose evaluation map `M ⊗[R] (R ∙ 1) → M` sends
`y ⊗ₜ q` into `R ∙ y` and `y ⊗ₜ 1` to `y`. This is the reason no smallness hypothesis on `R` is
needed, in contrast with the finitely presented case, Stacks 059K. Correspondingly the
implications are arranged as 1 ⇒ 2 ⇒ 3 ⇒ 1 together with 1 ⇔ 4, rather than as the source's cycle.

## References

* [StacksProject 059J](https://stacks.math.columbia.edu/tag/059J)
-/

namespace Stacks.Module.FinitenessViaProducts

open Function LinearMap TensorProduct

section Forward

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- If the finite family `x : ι → M` generates `M`, then every element of `M ⊗[R] Q` is of the
form `∑ i, x i ⊗ₜ q i`: the elementwise form of the surjectivity of `(ι → R) ⊗[R] Q → M ⊗[R] Q`. -/
private lemma exists_fun_eq_sum_tmul {ι : Type*} [Fintype ι] {x : ι → M}
    (hx : Submodule.span R (Set.range x) = ⊤) (Q : Type*) [AddCommGroup Q] [Module R Q]
    (t : M ⊗[R] Q) : ∃ q : ι → Q, t = ∑ i, x i ⊗ₜ[R] q i := by
  induction t with
  | tmul y p =>
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp
        (hx.ge (Submodule.mem_top : y ∈ ⊤))
      refine ⟨fun i => c i • p, ?_⟩
      rw [← hc, sum_tmul]
      exact Finset.sum_congr rfl fun i _ => smul_tmul _ _ _
  | add t₁ t₂ h₁ h₂ =>
      obtain ⟨q₁, rfl⟩ := h₁
      obtain ⟨q₂, rfl⟩ := h₂
      exact ⟨q₁ + q₂, by simp [tmul_add, Finset.sum_add_distrib]⟩

/-- (1) ⇒ (2): for a finitely generated `M` the comparison map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is surjective. -/
private lemma surjective_piRightHom_of_finite [Module.Finite R M] {A : Type*} (Q : A → Type*)
    [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)] : Surjective (piRightHom R R M Q) := by
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := R) (M := M)
  intro g
  choose q hq using fun α => exists_fun_eq_sum_tmul hx (Q α) (g α)
  refine ⟨∑ i, x i ⊗ₜ[R] fun α => q α i, funext fun α => ?_⟩
  rw [map_sum, Finset.sum_apply]
  simpa using (hq α).symm

end Forward

section Scalar

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The map `M ⊗[R] R^A → M^A` of item 4 is the comparison map of items 2 and 3 for the constant
family `R`, read through `M ⊗[R] R ≃ₗ[R] M`. -/
private lemma piScalarRightHom_eq_comp_piRightHom (A : Type*) :
    piScalarRightHom R R M A =
      (LinearEquiv.piCongrRight fun _ : A ↦ TensorProduct.rid R M).toLinearMap ∘ₗ
        piRightHom R R M fun _ : A ↦ R :=
  TensorProduct.ext' fun y r => funext fun _ => by simp

/-- Item 4 of Stacks 059J is item 3 for the constant family `R`. -/
private lemma surjective_piScalarRightHom_iff (A : Type*) :
    Surjective (piScalarRightHom R R M A) ↔ Surjective (piRightHom R R M fun _ : A ↦ R) := by
  rw [piScalarRightHom_eq_comp_piRightHom]
  exact (LinearEquiv.piCongrRight fun _ : A ↦ TensorProduct.rid R M).toEquiv.comp_surjective _

end Scalar

section Eval

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

/-- Evaluation of the homomorphisms in a submodule `Q` of `M →ₗ[R] N`, as a linear map
`M ⊗[R] Q →ₗ[R] N`; on pure tensors it is `y ⊗ₜ q ↦ q y`. -/
@[sga "5 IIIB 5.0" "special case"]
private noncomputable def homEval (Q : Submodule R (M →ₗ[R] N)) : M ⊗[R] Q →ₗ[R] N :=
  TensorProduct.lift (LinearMap.applyₗ.compl₂ Q.subtype)

private lemma homEval_tmul (Q : Submodule R (M →ₗ[R] N)) (y : M) (q : Q) :
    homEval Q (y ⊗ₜ[R] q) = (q : M →ₗ[R] N) y := rfl

/-- An endomorphism in the span of the identity is a scalar, so it sends `y` into `R ∙ y`. -/
private lemma apply_mem_span_singleton_of_mem_span_one {f : Module.End R M}
    (hf : f ∈ (R ∙ (1 : Module.End R M))) (y : M) : f y ∈ (R ∙ y) := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hf
  exact Submodule.mem_span_singleton.mpr ⟨r, by rw [← hr]; simp⟩

end Eval

section Converse

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The finite generation criterion behind both converse implications: if the identity of `M` is a
value of a linear map `F : M ⊗[R] N →ₗ[R] (M → M)` whose value on a pure tensor `y ⊗ₜ b` is at
every point a multiple of `y`, then `M` is finitely generated, generated by the left-hand factors
of any representation of a preimage of the identity as a finite sum of pure tensors. -/
private lemma finite_of_apply_tmul_mem_span_singleton {N : Type*} [AddCommGroup N] [Module R N]
    (F : M ⊗[R] N →ₗ[R] (M → M)) (hF : ∀ (y : M) (b : N) (x : M), F (y ⊗ₜ[R] b) x ∈ (R ∙ y))
    (t : M ⊗[R] N) (ht : F t = id) : Module.Finite R M := by
  classical
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset t
  refine Module.finite_def.mpr ⟨s.image Prod.fst, eq_top_iff.mpr fun x _ => ?_⟩
  have hx : ∑ p ∈ s, F (p.1 ⊗ₜ[R] p.2) x = x := by
    rw [← Finset.sum_apply, ← map_sum, ← hs, ht, id_eq]
  refine hx ▸ Submodule.sum_mem _ fun p hp => Submodule.span_mono ?_ (hF p.1 p.2 x)
  exact Set.singleton_subset_iff.mpr (by simpa using Finset.mem_image_of_mem Prod.fst hp)

/-- Both converse implications of Stacks 059J: if `Q` carries a linear map `e : M ⊗[R] Q →ₗ[R] M`
sending `y ⊗ₜ q` into `R ∙ y` and having `y ↦ y ⊗ₜ q₀` as a section, then surjectivity of the
comparison map for the constant family `Q` indexed by `M` forces `M` to be finitely generated. -/
private lemma finite_of_surjective_piRightHom_const {Q : Type*} [AddCommGroup Q] [Module R Q]
    (e : M ⊗[R] Q →ₗ[R] M) (he : ∀ (y : M) (q : Q), e (y ⊗ₜ[R] q) ∈ (R ∙ y))
    (q₀ : Q) (hq₀ : ∀ y : M, e (y ⊗ₜ[R] q₀) = y)
    (h : Surjective (piRightHom R R M fun _ : M ↦ Q)) : Module.Finite R M := by
  obtain ⟨t, ht⟩ := h fun x => x ⊗ₜ[R] q₀
  refine finite_of_apply_tmul_mem_span_singleton (e.compLeft M ∘ₗ piRightHom R R M fun _ : M ↦ Q)
    (fun y b x => by simpa using he y (b x)) t (funext fun x => ?_)
  simpa [ht] using hq₀ x

/-- (3) ⇒ (1): item 3 tested on `R ∙ (1 : Module.End R M)`, the scalars as they act on `M`. Its
evaluation map sends `y ⊗ₜ q` into `R ∙ y` because an endomorphism in the span of the identity is
a scalar, and `y ⊗ₜ 1` to `y`. -/
private lemma finite_of_surjective_piRightHom_span_one
    (h : Surjective (piRightHom R R M fun _ : M ↦ (R ∙ (1 : Module.End R M)))) :
    Module.Finite R M :=
  finite_of_surjective_piRightHom_const (homEval _)
    (fun y q => by simpa [homEval_tmul] using apply_mem_span_singleton_of_mem_span_one q.2 y)
    ⟨1, Submodule.mem_span_singleton_self _⟩ (fun _ => by simp [homEval_tmul]) h

/-- (4) ⇒ (1): item 4 tested on `A = M`, through the identification of its map with the comparison
map for the constant family `R`, whose evaluation map `M ⊗[R] R → M` is `TensorProduct.rid`. -/
private lemma finite_of_surjective_piScalarRightHom
    (h : Surjective (piScalarRightHom R R M M)) : Module.Finite R M :=
  finite_of_surjective_piRightHom_const (TensorProduct.rid R M)
    (fun y r => Submodule.mem_span_singleton.mpr ⟨r, by simp⟩) 1 (fun _ => by simp)
    ((surjective_piScalarRightHom_iff M).mp h)

end Converse

-- The universe names are declared inside a section, so that they do not escape to importers.
section

/-- **Stacks 059J**, the four conditions in the source's order: `M` is finitely generated;
`TensorProduct.piRightHom` is surjective for every family of `R`-modules indexed by a type in
`Type v`; it is surjective for every constant family; and `TensorProduct.piScalarRightHom`, the map
`M ⊗[R] R^A → M^A`, is surjective for every `A : Type v`. -/
public theorem solution (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] :
    List.TFAE
      [Module.Finite R M,
        ∀ (A : Type v) (Q : A → Type v) [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)],
          Function.Surjective (TensorProduct.piRightHom R R M Q),
        ∀ (A : Type v) (Q : Type v) [AddCommGroup Q] [Module R Q],
          Function.Surjective (TensorProduct.piRightHom R R M fun _ : A ↦ Q),
        ∀ A : Type v, Function.Surjective (TensorProduct.piScalarRightHom R R M A)] := by
  tfae_have 1 → 2 := fun _ A Q _ _ => surjective_piRightHom_of_finite Q
  tfae_have 2 → 3 := fun h A Q _ _ => h A fun _ => Q
  tfae_have 3 → 1 := fun h =>
    finite_of_surjective_piRightHom_span_one (h M (R ∙ (1 : Module.End R M)))
  tfae_have 1 → 4 := fun _ A =>
    (surjective_piScalarRightHom_iff A).mpr (surjective_piRightHom_of_finite _)
  tfae_have 4 → 1 := fun h => finite_of_surjective_piScalarRightHom (h M)
  tfae_finish

end

end Stacks.Module.FinitenessViaProducts

/-!
# Interchanging direct products with tensor: the finitely generated case

Let `R` be a commutative ring, let `M` be an `R`-module and let `(Q α)` be a family of
`R`-modules indexed by a set `A`. There is a canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α`, given on pure tensors by `x ⊗ (q α) ↦ (x ⊗ q α)`;
it is an isomorphism when `A` is finite, and in general it is neither injective nor surjective,
as the source's Example 059I shows for `R = ℤ` and `M = ℚ`.

This file states that surjectivity of this map, for all families, characterizes finite generation
of `M`, and that three successively weaker conditions already do so: surjectivity for every
family, surjectivity for every constant family `Q^A`, and surjectivity of `M ⊗[R] R^A → M^A` for
every set `A`. Finite generation gives the first because a surjection `R^n → M` sits in a square
whose top map, the case of a finite index type, is an isomorphism and whose two vertical maps are
surjective. Conversely, a single instance suffices: if the family `(x)` indexed by `x ∈ M` lies in
the image of `M ⊗[R] R^M → M^M`, writing a preimage as `∑ i, x i ⊗ a i` and projecting to the
`x`-th factor gives `x = ∑ i, a i x • x i`, so that the finitely many `x i` generate `M`.

## Main results

* `Module.Finite.tfae_piRightHom_surjective`: for an `R`-module `M`, the following are equivalent:
  `M` is finitely generated; `TensorProduct.piRightHom` is surjective for every family of
  `R`-modules; it is surjective for every constant family; and `TensorProduct.piScalarRightHom`,
  the map `M ⊗[R] R^A → M^A`, is surjective for every set `A`.

## Implementation notes

The canonical maps the source names are pinned to Mathlib's, not merely asserted to exist. The
comparison map of the section is `TensorProduct.piRightHom R R M Q`, whose value on `x ⊗ q` is
`fun α ↦ x ⊗ q α`, and the source's `M ⊗_R Q^A → (M ⊗_R Q)^A` is that map for the constant family
`fun _ : A ↦ Q`. The source's `M ⊗_R R^A → M^A` is `TensorProduct.piScalarRightHom R R M A`, whose
value on `x ⊗ a` is `fun α ↦ a α • x`; this is the composite of `piRightHom` for the constant
family `R` with the identification `M ⊗[R] R = M`, so no identification is left implicit in the
statement.

The source quantifies over families of `R`-modules in every universe, which no single Lean
statement can do. The index types and the test modules here range over `Type v`, the universe of
`M`, and this is the sharp choice: the forward implications hold for families in any universe,
while the converse needs an index set of the cardinality of `M`, which `Type v` already provides,
so tying the test universe to `M` weakens neither direction of the equivalence, and no smallness
hypothesis on `R` is imposed. A family of modules in a larger universe is reached by applying the
statement to a `ULift` copy of `M`. The implication from the constant-family condition to the
condition on `R^A` is the one place where the test universe is felt, `R` itself living in
`Type u`; it is available all the same, since `R` may there be replaced by
`R ⧸ Module.annihilator R M`, which acts on `M` by scalars, satisfies `M ⊗[R] (R ⧸ Ann) ≃ₗ[R] M`
and is `Small.{v}`, acting faithfully on `M`.

The equivalence is stated as a `List.TFAE`, as the source states it: the four conditions are
listed in the source's order, so that `(Module.Finite.tfae_piRightHom_surjective R M).out 1 2` is
the source's `(1) ↔ (2)`, and each item is a `Prop` quantifying over its own test data.

Faithfulness. (1) There is no hypothesis to be dead: the data are a commutative ring `R` and an
`R`-module `M`, both used by every item, and nothing is assumed of either — no finiteness, no
Noetherian hypothesis, no smallness — the test data of items 2, 3 and 4 being quantified inside
those items. (2) The scalars and the base are the source's: every tensor product is over `R`,
every comparison map is `R`-linear, and item 1 is finite generation of `M` as an `R`-module; no
localization and no base change occurs. (3) The canonical maps are pinned, as described above, to
`TensorProduct.piRightHom R R M Q` and `TensorProduct.piScalarRightHom R R M A`; the assertion is
surjectivity of those maps, not the existence of some surjection. (4) The instantiation is not
degenerate and both directions have content: for `R = ℤ` and `M = ℤ ⧸ 2ℤ` all four conditions
hold, and for `R = ℤ` and `M = ℚ` all four fail, item 4 already at `A = ℕ`, where the image of
`ℚ ⊗[ℤ] ℤ^ℕ → ℚ^ℕ` consists of the sequences `(a n / m)` with `a n : ℤ` and `m` a fixed nonzero
integer — the source's Example 059I.

## References

* [StacksProject 059J](https://stacks.math.columbia.edu/tag/059J)
-/



@[expose] public section

/-- **Stacks 059J.** Let `R` be a commutative ring and `M` an `R`-module. The following are
equivalent: (1) `M` is finitely generated; (2) for every family `Q` of `R`-modules the canonical
map `M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is surjective; (3) for every `R`-module `Q` and every
set `A` the canonical map `M ⊗[R] Q^A → (M ⊗[R] Q)^A` is surjective; (4) for every set `A` the
canonical map `M ⊗[R] R^A → M^A` is surjective. -/
@[stacks 059J]
public theorem Module.Finite.tfae_piRightHom_surjective (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] :
    List.TFAE
      [Module.Finite R M,
        ∀ (A : Type v) (Q : A → Type v) [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)],
          Function.Surjective (TensorProduct.piRightHom R R M Q),
        ∀ (A : Type v) (Q : Type v) [AddCommGroup Q] [Module R Q],
          Function.Surjective (TensorProduct.piRightHom R R M fun _ : A ↦ Q),
        ∀ A : Type v, Function.Surjective (TensorProduct.piScalarRightHom R R M A)] :=
  Stacks.Module.FinitenessViaProducts.solution R M

end
