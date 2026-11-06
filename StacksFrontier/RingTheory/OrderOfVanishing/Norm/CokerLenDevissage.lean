module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Lattice.Defs
import StacksFrontier.RingTheory.OrderOfVanishing.Norm.OrdIntBasics


@[expose] public section


open Ring

/-! ### Norms, the local rings of `B`, and residue degrees

For the finite field extension `L/K` and `y ∈ L`, the norm `Nm_{L/K}(y) = det_K(mul_y)` is the
determinant of multiplication by `y` on the `K`-vector space `L`, which is `Algebra.norm K`.

Under the standing hypotheses `B` is semi-local, with finitely many maximal ideals, indexed here
by the finite type `MaximalSpectrum B`. For each `v`, the localization
`B_v = Localization.AtPrime v.asIdeal` is a Noetherian local domain of dimension `1` with
fraction field `L`, so `ord_{B_v}` is defined as above with `R = B_v` and `K = L`.

Let `m_A` be the maximal ideal of `A`. Each maximal ideal `mᵢ` of `B` lies over `m_A`, and the
residue degree `[κ(mᵢ) : κ(m_A)] = finrank_{A/m_A} (B/mᵢ)` is finite; it is
`Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) mᵢ`, which equals
`Module.finrank (A / m_A) (B / mᵢ)` when `mᵢ` lies over `m_A`.
-/

/-! ### The norm-length identity (Stacks 02MI)

For a nonzero `b : B`, the order of vanishing of its norm equals the `A`-length of the cyclic
quotient `B / bB`:

`ord_A (Nm_{L/K}(b)) = length_A (B / bB)`.

Let `μ_b : L → L` be multiplication by `y = algebraMap B L b`, a `K`-linear endomorphism of the
finite `K`-vector space `L`, so that `Nm_{L/K}(y) = det_K(μ_b)` by definition. Since `b` is a
nonzerodivisor of `B`, multiplication by `b` is an injective map `B → B` with cokernel `B/bB` of
finite `A`-length: `B/bB` is a finite `A`-module supported only at `m_A`, being killed by some
power of `m_A` because `dim A = 1` and `b ≠ 0`. The determinant `det_K(μ_b)` is, up to a unit, the
`A`-norm of `b`, an element of `A`, and `ord_A` of it is the length of `A / (Nm b)`.

Concretely, one pushes `Nm_{L/K}(y)` into `A`, as `algebraMap A K (Algebra.norm A b)` via
`Algebra.norm_localization`, applies `ordInt_algebraMap` to turn `ord_A` into
`length_A (A / (Nm b))`, and finally invokes the length identity
`length_A (A / (Nm b)·A) = length_A (B / bB)`.

The route through `Algebra.norm_localization` or `relNorm` is not available here: it needs
`[Module.Free A B]`, respectively `[IsIntegrallyClosed A]`, and `A` is only a one-dimensional
Noetherian local domain while `B` is finite and torsion-free but not free. An additivity-only
strategy is also genuinely insufficient: the discrepancy `D = length − ord ∘ Nm` is an additive
homomorphism vanishing on `A`, which does not force `D ≡ 0`. The decisive content is Stacks
02QH: for a finite `A`-module `M` and an `A`-linear endomorphism `φ` with `det_K(φ ⊗ K) ≠ 0`,
`ord_A(det_K(φ ⊗ K)) = length_A(coker φ)`. It is applied with `M = B` and `φ = lmul_A b`.

The identity is therefore assembled from `ordInt_baseChangeDet_eq_length_cokernel`, the 02QH
determinant-length kernel, and `baseChangeDet_lmul_eq_norm`, identifying the determinant of
`lmul_A b ⊗ K` with `Nm_{L/K}(b)` through the `K`-algebra isomorphism `B ⊗[A] K ≅ L`, together
with the inline identification `range (lmul_A b) = span {b}` making the cokernel `B/bB`.
-/

/-! ### Background on the matrix base case

For a square matrix `T` over a one-dimensional Noetherian local domain `A` with `det T ≠ 0`, the
`A`-length of the cokernel `Aᵐ ⧸ T·Aᵐ` equals `ord_A(det T) = length_A(A/(det T))`.

An additivity-only strategy cannot reach this. The two functions `L(T) = length_A(Aᵐ/T·Aᵐ)` and
`Δ(T) = ord_A(det T)` are both additive under matrix multiplication and agree on scalar matrices
`cI` and on `GLₘ(A)`, but that yields only the single relation `δ(T) + δ(adj T) = 0` for
`δ = L − Δ`, which does not force `δ ≡ 0`; and triangularizing to a pivot would require a
principal ideal domain, which `A` is not. The correct route is a filtration and dévissage
argument, or base change to the completion `Â`, where `ℓ_A(N) = ℓ_Â(N̂)` for finite-length `N`.

The reusable building blocks are: additivity of length along short exact sequences; the
isomorphism `Aᵐ/aAᵐ ≅ (A/aA)ᵐ`, giving `L(aI) = m·ord_A(a)`; multiplicativity
`L(T₁T₂) = L(T₁) + L(T₂)` via `0 → T₁Aᵐ/T₁T₂Aᵐ → Aᵐ/T₁T₂Aᵐ → Aᵐ/T₁Aᵐ → 0` together with the
isomorphism `Aᵐ/T₂Aᵐ ≅ T₁Aᵐ/T₁T₂Aᵐ` for injective `T₁`; and the chain
`(det T)Aᵐ ⊆ TAᵐ ⊆ Aᵐ` with `Matrix.adjugate_mul` and `Matrix.det_adjugate`, giving
`L(T) + L(adj T) = m·ord_A(det T)`.
-/

/-! ### Multiplicativity of the cokernel length under matrix product

For square matrices `T₁ T₂` over a one-dimensional Noetherian local domain `A`, with both
determinants nonzero, so that both `toLin'` are injective over the domain `A`,
`length_A(Aᵐ/range(toLin'(T₁*T₂)))`
`= length_A(Aᵐ/range(toLin' T₁)) + length_A(Aᵐ/range(toLin' T₂))`.
The route: `Matrix.toLin'_mul` turns `toLin'(T₁*T₂)` into the
composition `toLin' T₁ ∘ₗ toLin' T₂`; the nested-submodule SES
`0 → range φ ⧸ range(φ∘ψ) → Aᵐ ⧸ range(φ∘ψ) → Aᵐ ⧸ range φ → 0` (`Module.length_eq_add_of_exact`)
plus the iso `range φ ⧸ range(φ∘ψ) ≅ Aᵐ ⧸ range ψ` (from `LinearEquiv.ofInjective φ` and
`Submodule.Quotient.equiv`) give the additivity.
-/

open Submodule LinearMap in
/-- The abstract multiplicativity behind `matrix_cokerLen_mul`, for an arbitrary injective `φ`
and any `ψ` on a module `M`.

It comes from the short exact sequence
`0 → M ⧸ range ψ →[f] M ⧸ range (φ∘ψ) →[g] M ⧸ range φ → 0`, where `f : [x] ↦ [φ x]` is injective
because `φ` is injective and `comap φ (map φ (range ψ)) = range ψ`, and `g` is the natural
projection, surjective with `ker g = map (range (φ∘ψ)).mkQ (range φ) = range f`. -/
private theorem matrix_cokerLen_mul_helper (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    Module.length R (M ⧸ LinearMap.range (φ ∘ₗ ψ))
      = Module.length R (M ⧸ LinearMap.range ψ) + Module.length R (M ⧸ LinearMap.range φ) := by
  set S := LinearMap.range (φ ∘ₗ ψ) with hS
  set T := LinearMap.range φ with hT
  have hSmap : S = Submodule.map φ (LinearMap.range ψ) := by
    rw [hS, LinearMap.range_comp]
  have hST : S ≤ T := LinearMap.range_comp_le_range ψ φ
  have hf : LinearMap.range ψ ≤ Submodule.comap φ S := by
    rw [hSmap]
    exact fun _ hx => Submodule.mem_map_of_mem hx
  let f : (M ⧸ LinearMap.range ψ) →ₗ[R] (M ⧸ S) := Submodule.mapQ (LinearMap.range ψ) S φ hf
  have hg : S ≤ Submodule.comap LinearMap.id T := by
    rw [Submodule.comap_id]; exact hST
  let g : (M ⧸ S) →ₗ[R] (M ⧸ T) := Submodule.mapQ S T LinearMap.id hg
  have hcomap : Submodule.comap φ S = LinearMap.range ψ := by
    rw [hSmap, Submodule.comap_map_eq_of_injective hφ]
  have hfrange : f.range = Submodule.map S.mkQ T := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range ψ) z
      refine ⟨φ x, ?_, ?_⟩
      · rw [hT]; exact LinearMap.mem_range_self φ x
      · simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply]
    · rintro _ ⟨y, hy, rfl⟩
      rw [hT] at hy
      obtain ⟨x, rfl⟩ := hy
      refine ⟨Submodule.mkQ _ x, ?_⟩
      simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply]
  apply Module.length_eq_add_of_exact f g
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  · exact (Submodule.mkQ_surjective T).forall.2 fun x => ⟨Submodule.mkQ S x, rfl⟩
  · rw [LinearMap.exact_iff, Submodule.ker_mapQ, Submodule.comap_id, hfrange]

/-- Multiplicativity of the cokernel length: for square matrices over a one-dimensional
Noetherian local domain, with the first determinant nonzero, the cokernel length of a product
is the sum of the cokernel lengths. -/
theorem matrix_cokerLen_mul
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (m : ℕ) (T₁ T₂ : Matrix (Fin m) (Fin m) A) (h₁ : T₁.det ≠ 0) :
    Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' (T₁ * T₂)))
      = Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' T₁))
        + Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' T₂)) := by
  have hinj : Function.Injective (Matrix.toLin' T₁) :=
    (injective_iff_map_eq_zero _).2 fun x hx =>
      Matrix.eq_zero_of_mulVec_eq_zero h₁ (by rwa [Matrix.toLin'_apply] at hx)
  rw [Matrix.toLin'_mul, matrix_cokerLen_mul_helper A (Fin m → A) _ _ hinj, add_comm]

/-- SCALAR BASE CASE of the matrix base case.  For `a : A` (with `a ≠ 0`) the cokernel of the
scalar matrix `a • 1 : Matrix (Fin m) (Fin m) A` has `A`-length `m · length_A(A ⧸ span{a})`.
The map `Matrix.toLin' (a • 1)` is the diagonal map `x ↦ a • x` on `Fin m → A`, so the cokernel
is `(Fin m → A) ⧸ (a • ⊤) ≅ ∏ (A ⧸ span{a})`, whence `Module.length_pi`. -/
@[ega "IV 21.10.13" "special case"]
theorem matrix_cokerLen_scalar
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (m : ℕ) (a : A) :
    Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' (a • (1 : Matrix (Fin m) (Fin m)
        A))))
      = m * Module.length A (A ⧸ Ideal.span {a}) := by
  -- Submodule.quotientPi + Module.length_pi; even true without `a ≠ 0`).
  have hrange :
      LinearMap.range (Matrix.toLin' (a • (1 : Matrix (Fin m) (Fin m) A)))
        = Submodule.pi Set.univ (fun _ : Fin m => Ideal.span {a}) := by
    have hmul : ∀ x : Fin m → A,
        Matrix.toLin' (a • (1 : Matrix (Fin m) (Fin m) A)) x = a • x := by
      intro x; ext i; simp
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_true_left,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩ i
      rw [hmul]
      exact ⟨y i, by simp⟩
    · intro h
      choose c hc using h
      refine ⟨c, ?_⟩
      rw [hmul]
      ext i
      simp [hc i]
  rw [hrange, (Submodule.quotientPi (fun _ : Fin m => Ideal.span {a})).length_eq, Module.length_pi,
    ENat.card_eq_coe_fintype_card]
  simp

/-! ### The dévissage step

This is the conceptual crux of the matrix base case, for a block-triangular or, more generally,
`N`-preserving endomorphism.

For an `A`-linear endomorphism `φ` of `M` that maps a submodule `N` into itself (`hφN`), inducing
`φ̄ := N.mapQ N φ hφN` on the quotient `M ⧸ N`, IF `φ̄` is injective then the cokernel length is
additive along the flag `N ⊆ M`:
  `length(M ⧸ range φ) = length(N ⧸ range(φ|_N)) + length((M ⧸ N) ⧸ range φ̄)`.

This comes from the snake lemma applied to `0 → N → M → M ⧸ N → 0` with the `φ`-action: the
boundary map `ker φ̄ → coker(φ|_N)` vanishes because `φ̄` is injective (`ker φ̄ = 0`), leaving the
genuine short exact sequence of cokernels
  `0 → N ⧸ range(φ|_N) → M ⧸ range φ → (M ⧸ N) ⧸ range φ̄ → 0`,
whose additivity (`Module.length_eq_add_of_exact`, in `ℕ∞`, unconditional) gives the identity.
THIS is the piece that defeats the "additivity-only is insufficient" obstruction (it splits the
cokernel along a flag, not merely under a product).  No domain/local/finite-length hypothesis is
needed (the identity holds over any `CommRing`, in `ℕ∞`).
-/

open Submodule LinearMap in
/-- Dévissage for cokernel lengths along an invariant submodule: for `φ` preserving `N` with
injective induced map on `M ⧸ N`, the cokernel length of `φ` splits as the sum of the cokernel
lengths of `φ|_N` and of the induced map. -/
theorem matrix_cokerLen_devissage
    (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    (N : Submodule A M) (φ : M →ₗ[A] M) (hφN : N ≤ Submodule.comap φ N)
    (hbar_inj : Function.Injective (N.mapQ N φ hφN)) :
    Module.length A (M ⧸ LinearMap.range φ)
      = Module.length A (N ⧸ LinearMap.range (φ.restrict hφN))
        + Module.length A ((M ⧸ N) ⧸ LinearMap.range (N.mapQ N φ hφN)) := by
  -- hypotheses; the SES of cokernels 0→coker(φ|N)→coker φ→coker φ̄→0 via
  -- Module.length_eq_add_of_exact).
  set φbar := N.mapQ N φ hφN with hφbar
  set φN := φ.restrict hφN with hφN'
  -- f : N ⧸ range φN → M ⧸ range φ induced by N.subtype
  have hf : LinearMap.range φN ≤ Submodule.comap N.subtype (LinearMap.range φ) := by
    rintro _ ⟨z, rfl⟩
    rw [Submodule.mem_comap]
    refine ⟨(z : M), ?_⟩
    simp [hφN', LinearMap.coe_restrict_apply]
  let f : (N ⧸ LinearMap.range φN) →ₗ[A] (M ⧸ LinearMap.range φ) :=
    Submodule.mapQ (LinearMap.range φN) (LinearMap.range φ) N.subtype hf
  -- g : M ⧸ range φ → (M ⧸ N) ⧸ range φbar induced by N.mkQ
  have hg : LinearMap.range φ ≤ Submodule.comap N.mkQ (LinearMap.range φbar) := by
    rintro _ ⟨m, rfl⟩
    rw [Submodule.mem_comap]
    refine ⟨N.mkQ m, ?_⟩
    rw [hφbar, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  let g : (M ⧸ LinearMap.range φ) →ₗ[A] ((M ⧸ N) ⧸ LinearMap.range φbar) :=
    Submodule.mapQ (LinearMap.range φ) (LinearMap.range φbar) N.mkQ hg
  apply Module.length_eq_add_of_exact f g
  · -- f injective
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φN) z
    rw [LinearMap.mem_ker] at hz
    simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.subtype_apply] at hz
    rw [Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨m, hm⟩ := hz
    -- φ m = ↑x, so φbar [m] = [↑x] = 0, hence [m] = 0, m ∈ N
    have hbar0 : φbar (N.mkQ m) = 0 := by
      rw [hφbar, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero, hm]
      exact x.property
    have hmN : N.mkQ m = 0 := hbar_inj (by rw [hbar0, map_zero])
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmN
    -- x = φN ⟨m, hmN⟩ ∈ range φN
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨m, hmN⟩, ?_⟩
    apply Subtype.ext
    rwa [hφN', LinearMap.coe_restrict_apply]
  · -- g surjective
    intro w
    obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φbar) w
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective N q
    refine ⟨(LinearMap.range φ).mkQ m, ?_⟩
    simp only [g, Submodule.mkQ_apply, Submodule.mapQ_apply]
  · -- Function.Exact f g
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · -- ker g ≤ range f
      intro z hz
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φ) z
      rw [LinearMap.mem_ker] at hz
      simp only [g, Submodule.mkQ_apply, Submodule.mapQ_apply] at hz
      rw [Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨q, hq⟩ := hz
      obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective N q
      rw [hφbar, Submodule.mkQ_apply, Submodule.mapQ_apply] at hq
      -- hq : Quotient.mk (φ m') = Quotient.mk m, so m - φ m' ∈ N
      have hmem : m - φ m' ∈ N := (Submodule.Quotient.eq N).mp hq.symm
      -- m - φ m' ∈ N, call it x
      set x : M := m - φ m' with hx
      refine ⟨(LinearMap.range φN).mkQ ⟨x, hmem⟩, ?_⟩
      simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.subtype_apply]
      rw [Submodule.Quotient.eq]
      refine ⟨-m', ?_⟩
      rw [hx]
      simp
    · -- range f ≤ ker g
      rintro _ ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φN) z
      rw [LinearMap.mem_ker]
      simp only [f, g, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.subtype_apply]
      rw [Submodule.Quotient.mk_eq_zero]
      -- the element (↑x : M) is in N, hence its class in M ⧸ N is 0, so it lies in range φbar
      have : (Submodule.Quotient.mk (x : M) : M ⧸ N) = 0 :=
        (Submodule.Quotient.mk_eq_zero N).mpr x.property
      rw [this]
      exact zero_mem _

/-! ### Additivity of `length (A ⧸ span{·})` under multiplication

This is the span side of the determinant
relation).  Over a domain `A`, for nonzero `a b`, the SES
`0 → A/span{b} →(·a) A/span{a*b} → A/span{a} → 0` (`Module.length_eq_add_of_exact`) gives
`length (A/span{a*b}) = length (A/span{b}) + length (A/span{a})`.
-/
open Submodule LinearMap in
/-- Over a domain, for `a ≠ 0`, `length (A ⧸ span {a * b})` is the sum of
`length (A ⧸ span {b})` and `length (A ⧸ span {a})`. -/
@[sga "7 X 2.14" "partial"]
theorem length_span_mul
    (A : Type*) [CommRing A] [IsDomain A]
    (a b : A) (ha : a ≠ 0) :
    Module.length A (A ⧸ Ideal.span {a * b})
      = Module.length A (A ⧸ Ideal.span {b}) + Module.length A (A ⧸ Ideal.span {a}) := by
  set μ : A →ₗ[A] A := LinearMap.toSpanSingleton A A a with hμ
  have hμapp : ∀ x : A, μ x = a * x := by intro x; rw [hμ]; simp [mul_comm]
  have hf : (Ideal.span {b}).restrictScalars A ≤
      Submodule.comap μ ((Ideal.span {a*b}).restrictScalars A) := by
    intro x hx
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hx ⊢
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem, Ideal.mem_span_singleton, hμapp]
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by ring⟩
  let f : (A ⧸ (Ideal.span {b}).restrictScalars A) →ₗ[A]
      (A ⧸ (Ideal.span {a*b}).restrictScalars A) :=
    Submodule.mapQ _ _ μ hf
  have hg : (Ideal.span {a*b}).restrictScalars A ≤
      Submodule.comap LinearMap.id ((Ideal.span {a}).restrictScalars A) := by
    rw [Submodule.comap_id]
    intro x hx
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨b * c, by ring⟩
  let g : (A ⧸ (Ideal.span {a*b}).restrictScalars A) →ₗ[A]
      (A ⧸ (Ideal.span {a}).restrictScalars A) :=
    Submodule.mapQ _ _ LinearMap.id hg
  have hlen : Module.length A (A ⧸ (Ideal.span {a*b}).restrictScalars A)
      = Module.length A (A ⧸ (Ideal.span {b}).restrictScalars A)
        + Module.length A (A ⧸ (Ideal.span {a}).restrictScalars A) := by
    apply Module.length_eq_add_of_exact f g
    · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro z hz
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
      rw [LinearMap.mem_ker] at hz
      simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply] at hz
      rw [Submodule.Quotient.mk_eq_zero] at hz
      simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hz
      rw [hμapp] at hz
      obtain ⟨c, hc⟩ := hz
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
      refine ⟨c, ?_⟩
      have : a * x = a * (b * c) := by rw [hc]; ring
      exact mul_left_cancel₀ ha this
    · intro w
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
      exact ⟨Submodule.mkQ _ x, rfl⟩
    · rw [LinearMap.exact_iff]
      apply le_antisymm
      · intro z hz
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
        rw [LinearMap.mem_ker] at hz
        simp only [g, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_coe, id_eq] at hz
        rw [Submodule.Quotient.mk_eq_zero] at hz
        simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hz
        obtain ⟨c, rfl⟩ := hz
        refine ⟨Submodule.mkQ _ c, ?_⟩
        simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply]
        rw [hμapp]
      · rintro _ ⟨z, rfl⟩
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
        rw [LinearMap.mem_ker]
        simp only [f, g, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_coe, id_eq]
        rw [Submodule.Quotient.mk_eq_zero]
        simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
        rw [hμapp]
        exact ⟨x, by ring⟩
  exact hlen

/-- Cokernel length is invariant under conjugation by linear equivalences. -/
theorem cokerLen_conj_eq (A : Type*) [CommRing A] {M P : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup P] [Module A P]
    (φ : M →ₗ[A] M) (f : P ≃ₗ[A] M) (g : M ≃ₗ[A] P) :
    Module.length A (P ⧸ LinearMap.range ((g : M →ₗ[A] P) ∘ₗ φ ∘ₗ (f : P →ₗ[A] M)))
      = Module.length A (M ⧸ LinearMap.range φ) := by
  have hrange : LinearMap.range ((g : M →ₗ[A] P) ∘ₗ φ ∘ₗ (f : P →ₗ[A] M))
      = Submodule.map (g : M →ₗ[A] P) (LinearMap.range φ) := by
    rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [hrange]
  exact ((Submodule.Quotient.equiv (LinearMap.range φ) _ g rfl).length_eq).symm

/-- If a linear equivalence `α` intertwines `ψ` and `χ`, their cokernels have equal length. -/
theorem cokerLen_intertwine (A : Type*) [CommRing A] {X Y : Type*}
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (ψ : X →ₗ[A] X) (χ : Y →ₗ[A] Y) (α : X ≃ₗ[A] Y)
    (h : (α : X →ₗ[A] Y) ∘ₗ ψ = (χ : Y →ₗ[A] Y) ∘ₗ (α : X →ₗ[A] Y)) :
    Module.length A (X ⧸ LinearMap.range ψ) = Module.length A (Y ⧸ LinearMap.range χ) := by
  have hχ : χ = (α : X →ₗ[A] Y) ∘ₗ ψ ∘ₗ (α.symm : Y →ₗ[A] X) := by
    apply LinearMap.ext; intro y
    have := LinearMap.congr_fun h (α.symm y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this ⊢
    rw [← this]
  rw [hχ]
  exact (cokerLen_conj_eq A ψ α.symm α).symm

/-- Cokernel length under reindexing of a square matrix is unchanged. -/
theorem cokerLen_reindex (A : Type*) [CommRing A] {k l : Type*}
    [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l]
    (e : k ≃ l) (T : Matrix k k A) :
    Module.length A ((l → A) ⧸ LinearMap.range (Matrix.toLin' (Matrix.reindex e e T)))
      = Module.length A ((k → A) ⧸ LinearMap.range (Matrix.toLin' T)) := by
  rw [Matrix.toLin'_reindex]
  exact cokerLen_conj_eq A (Matrix.toLin' T)
    (LinearEquiv.funCongrLeft A A e) (LinearEquiv.funCongrLeft A A e.symm)

/-- Cokernel of an invertible matrix (unit determinant) is trivial. -/
theorem cokerLen_isUnit (A : Type*) [CommRing A] {m : Type*} [Fintype m] [DecidableEq m]
    (T : Matrix m m A) (hT : IsUnit T.det) :
    Module.length A ((m → A) ⧸ LinearMap.range (Matrix.toLin' T)) = 0 := by
  apply Module.length_eq_zero_iff.mpr
  have hsurj : Function.Surjective (Matrix.toLin' T) := by
    intro y
    refine ⟨T⁻¹.mulVec y, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hT, Matrix.one_mulVec]
  rw [← LinearMap.range_eq_top] at hsurj
  rw [hsurj, Submodule.Quotient.subsingleton_iff]

/-- `length (A ⧸ span {a}) = 0` when `a` is a unit. -/
theorem spanLen_isUnit (A : Type*) [CommRing A] (a : A) (ha : IsUnit a) :
    Module.length A (A ⧸ Ideal.span {a}) = 0 := by
  apply Module.length_eq_zero_iff.mpr
  rw [Submodule.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top.mpr ha]

open Matrix in
/-- For a block-upper-triangular matrix `fromBlocks C D 0 S` with `det C ≠ 0` and `det S ≠ 0`,
the cokernel length splits as `cokerLen C + cokerLen S`. -/
theorem block_cokerLen (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : Matrix ι ι A) (D : Matrix ι κ A) (S : Matrix κ κ A)
    (hSdet : S.det ≠ 0) :
    Module.length A (((ι ⊕ κ) → A) ⧸ LinearMap.range (Matrix.toLin' (Matrix.fromBlocks C D 0 S)))
      = Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' C))
        + Module.length A ((κ → A) ⧸ LinearMap.range (Matrix.toLin' S)) := by
  set B := Matrix.fromBlocks C D 0 S with hB
  set φ : ((ι ⊕ κ) → A) →ₗ[A] ((ι ⊕ κ) → A) := Matrix.toLin' B with hφ
  set pr : ((ι ⊕ κ) → A) →ₗ[A] (κ → A) := LinearMap.funLeft A A Sum.inr with hpr
  set N : Submodule A ((ι ⊕ κ) → A) := LinearMap.ker pr with hN
  have hφapp : ∀ (g : (ι ⊕ κ) → A),
      φ g = Sum.elim (C.mulVec (g ∘ Sum.inl) + D.mulVec (g ∘ Sum.inr))
        (S.mulVec (g ∘ Sum.inr)) := by
    intro g
    rw [hφ, Matrix.toLin'_apply, hB, Matrix.fromBlocks_mulVec]
    simp [Matrix.zero_mulVec]
  have hmemN : ∀ g, g ∈ N ↔ g ∘ Sum.inr = 0 := by
    intro g; rw [hN, LinearMap.mem_ker, hpr]; rfl
  have hφinr : ∀ g, (φ g) ∘ Sum.inr = S.mulVec (g ∘ Sum.inr) := by
    intro g; rw [hφapp]; rfl
  have hφinl : ∀ g, (φ g) ∘ Sum.inl = C.mulVec (g ∘ Sum.inl) + D.mulVec (g ∘ Sum.inr) := by
    intro g; rw [hφapp]; rfl
  have hSinj : Function.Injective (Matrix.toLin' S) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hSdet hx
  have hφN : N ≤ Submodule.comap φ N := by
    intro g hg
    rw [Submodule.mem_comap, hmemN]
    rw [hmemN] at hg
    rw [hφinr, hg, Matrix.mulVec_zero]
  have hbar_inj : Function.Injective (N.mapQ N φ hφN) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective N z
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero] at hz
    rw [hmemN, hφinr] at hz
    have hgr : g ∘ Sum.inr = 0 := hSinj (by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hz, Matrix.mulVec_zero])
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN]
    exact hgr
  rw [matrix_cokerLen_devissage A _ N φ hφN hbar_inj]
  -- Identify the two pieces.
  -- Quotient piece: (M/N) ⧸ range φ̄  ≅  cokerLen S
  have hprsurj : Function.Surjective pr :=
    LinearMap.funLeft_surjective_of_injective A A Sum.inr Sum.inr_injective
  let β : (((ι ⊕ κ) → A) ⧸ N) ≃ₗ[A] (κ → A) :=
    LinearMap.quotKerEquivOfSurjective pr hprsurj
  have hβ : ∀ g, β (Submodule.Quotient.mk g) = g ∘ Sum.inr := fun g => rfl
  have hpieceS : Module.length A ((((ι ⊕ κ) → A) ⧸ N) ⧸ LinearMap.range (N.mapQ N φ hφN))
      = Module.length A ((κ → A) ⧸ LinearMap.range (Matrix.toLin' S)) := by
    refine cokerLen_intertwine A (N.mapQ N φ hφN) (Matrix.toLin' S) β (LinearMap.ext fun z => ?_)
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective N z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, hβ, hβ, Matrix.toLin'_apply]
    exact hφinr g
  -- Sub piece: N ⧸ range (φ.restrict) ≅ cokerLen C
  let fwd : N →ₗ[A] (ι → A) := (LinearMap.funLeft A A Sum.inl).comp N.subtype
  let bwd : (ι → A) →ₗ[A] N :=
    { toFun := fun h => ⟨Sum.elim h 0, by rw [hmemN]; ext j; simp⟩
      map_add' := by intro x y; apply Subtype.ext; ext i; cases i <;> simp [Sum.elim]
      map_smul' := by intro c x; apply Subtype.ext; ext i; cases i <;> simp [Sum.elim] }
  let γ : N ≃ₗ[A] (ι → A) := LinearEquiv.ofLinearMap fwd bwd
    (LinearMap.ext fun _ => rfl)
    (by
      apply LinearMap.ext; intro g; apply Subtype.ext; apply funext; intro i
      cases i with
      | inl a => rfl
      | inr b =>
        simp only [fwd, bwd, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk,
          AddHom.coe_mk, LinearMap.id_coe, id_eq, Sum.elim_inr, Pi.zero_apply]
        exact (congrFun ((hmemN g.val).mp g.property) b).symm)
  have hγ : ∀ (g : N), γ g = (g : (ι ⊕ κ) → A) ∘ Sum.inl := fun g => rfl
  have hpieceC : Module.length A (N ⧸ LinearMap.range (φ.restrict hφN))
      = Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' C)) := by
    apply cokerLen_intertwine A (φ.restrict hφN) (Matrix.toLin' C) γ
    apply LinearMap.ext
    intro g
    have hg := (hmemN g.val).mp g.property
    have hkey : (φ (g : (ι ⊕ κ) → A)) ∘ Sum.inl = C.mulVec ((g : (ι ⊕ κ) → A) ∘ Sum.inl) := by
      rw [hφinl, hg, Matrix.mulVec_zero, add_zero]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.restrict_apply]
    change (φ (g : (ι ⊕ κ) → A)) ∘ Sum.inl = Matrix.toLin' C (γ g)
    rw [hγ, Matrix.toLin'_apply]
    exact hkey
  rw [hpieceC, hpieceS]

open Matrix in
/-- The block-lower-triangular counterpart: for `fromBlocks C 0 W S`, the cokernel length
splits as `cokerLen C + cokerLen S`. -/
theorem block_cokerLen_lower (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Ring.KrullDimLE 1 A]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : Matrix ι ι A) (W : Matrix κ ι A) (S : Matrix κ κ A)
    (hCdet : C.det ≠ 0) :
    Module.length A (((ι ⊕ κ) → A) ⧸ LinearMap.range (Matrix.toLin' (Matrix.fromBlocks C 0 W S)))
      = Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' C))
        + Module.length A ((κ → A) ⧸ LinearMap.range (Matrix.toLin' S)) := by
  have hswap : Matrix.reindex (Equiv.sumComm ι κ) (Equiv.sumComm ι κ) (Matrix.fromBlocks C 0 W S)
      = Matrix.fromBlocks S W 0 C := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.reindex, Matrix.fromBlocks, Matrix.submatrix]
  rw [← cokerLen_reindex A (Equiv.sumComm ι κ) (Matrix.fromBlocks C 0 W S), hswap,
    block_cokerLen A S W C hCdet, add_comm]

open Ring in
/-- Over a one-dimensional Noetherian local domain, `length (A ⧸ span {a})` is finite for
`a ≠ 0`. -/
@[ega "IV 21.10.13" "(i) for M=A, A a domain", ega "IV 21.6.5" "special case"]
theorem spanLen_ne_top (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A] (a : A) (ha : a ≠ 0) :
    Module.length A (A ⧸ Ideal.span {a}) ≠ ⊤ := by
  set K := FractionRing A
  have ha' : algebraMap A K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  have ha0 : a ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero ha
  have hord : Ring.ord A a = Module.length A (A ⧸ Ideal.span {a}) := rfl
  rw [← hord]
  intro htop
  have h0 : Ring.ordMonoidWithZeroHom A a = 0 := by
    simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ha0, ite_true,
      htop]
    rfl
  have hu : Ring.ordFrac A (K := K) (algebraMap A K a) ≠ 0 :=
    (ha'.isUnit.map (Ring.ordFrac A)).ne_zero
  rw [Ring.ordFrac_eq_ord A (x := a) ha, h0] at hu
  exact hu rfl

/-- `length (A ⧸ span {a ^ k}) = k · length (A ⧸ span {a})`. -/
@[sga "7 X 2.14" "partial"]
theorem spanLen_pow (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A] (a : A) (ha : a ≠ 0) (k : ℕ) :
    Module.length A (A ⧸ Ideal.span {a ^ k}) = k * Module.length A (A ⧸ Ideal.span {a}) := by
  induction k with
  | zero => simp [Submodule.Quotient.subsingleton_iff, Ideal.span_singleton_one]
  | succ m ih =>
    have hak : a ^ m ≠ 0 := pow_ne_zero m ha
    rw [pow_succ, length_span_mul A (a ^ m) a hak, ih]
    push_cast
    ring

/-- Multiplicativity of cokernel length under matrix product, for arbitrary (finite) index. -/
theorem cokerLen_mul (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T₁ T₂ : Matrix ι ι A) (h₁ : T₁.det ≠ 0) :
    Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' (T₁ * T₂)))
      = Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' T₁))
        + Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' T₂)) := by
  have hinj : ∀ (T : Matrix ι ι A), T.det ≠ 0 → Function.Injective (Matrix.toLin' T) := by
    intro T hT
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hT hx
  rw [Matrix.toLin'_mul]
  rw [matrix_cokerLen_mul_helper A (ι → A) (Matrix.toLin' T₁) (Matrix.toLin' T₂) (hinj T₁ h₁)]
  rw [add_comm]

/-! ### The matrix base case in length form (Stacks 02QH)

For a square matrix `T` over a one-dimensional Noetherian local domain `A` with `T.det ≠ 0`, the
`A`-length of the cokernel of `T : Aᵐ → Aᵐ` equals the `A`-length of `A ⧸ (det T)`.

This is the analytic content of the matrix base case, stated without the `ordInt` and `.toNat`
wrappers so that the proof works purely with `Module.length`, valued in `ℕ∞`, which is additive
over short exact sequences with no finiteness bookkeeping at intermediate steps.

Both sides are multiplicative under matrix product and agree on scalar matrices, and the closure
is an induction on `m` by Schur clearing, needing no Smith normal form or principal ideal domain.
The pieces are: multiplicativity `cokerLen (T₁ * T₂) = cokerLen T₁ + cokerLen T₂`; the scalar
case `cokerLen (a • 1) = m * length (A ⧸ span {a})`; the dévissage step for a block-triangular
`T`, resting on the short exact sequence of cokernels
`0 → coker(φ|_N) → coker φ → coker φ̄ → 0` for an `N`-preserving endomorphism; and the induction
on `m` wiring these together with the Schur clearing `E₋ · T` block-upper-triangular,
`det E₋ = t₁₁ᵐ`, and Schur complement `S = t₁₁ T₀ - w vᵀ` with `det S ≠ 0`, peeled off by
multiplicativity.

Both `cokerLen` and `length (A ⧸ span {det})` are finite, since `det T ≠ 0` makes `toLin' T`
injective over a domain and so the cokernel torsion of finite length, but the `ℕ∞` statement
needs no `.toNat` juggling.
-/
open Matrix in
/-- The corner core of the Schur-clearing inductive step, on `Fin 1 ⊕ Fin n`-indexed matrices
with nonzero `(0,0)` entry. -/
theorem step_sumform_corner (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Ring.KrullDimLE 1 A] (n : ℕ)
    (IH : ∀ (S : Matrix (Fin n) (Fin n) A), S.det ≠ 0 →
      Module.length A ((Fin n → A) ⧸ LinearMap.range (Matrix.toLin' S))
        = Module.length A (A ⧸ Ideal.span {S.det}))
    (T' : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) A) (hT' : T'.det ≠ 0)
    (ha : T' (Sum.inl 0) (Sum.inl 0) ≠ 0) :
    Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T'))
      = Module.length A (A ⧸ Ideal.span {T'.det}) := by
  set a := T' (Sum.inl 0) (Sum.inl 0) with hadef
  set t := T'.toBlocks₁₁ with htdef
  set v := T'.toBlocks₁₂ with hvdef
  set w := T'.toBlocks₂₁ with hwdef
  set T0 := T'.toBlocks₂₂ with hT0def
  have hTblock : T' = Matrix.fromBlocks t v w T0 := (Matrix.fromBlocks_toBlocks T').symm
  have hta : t = a • (1 : Matrix (Fin 1) (Fin 1) A) := by
    ext i j; fin_cases i; fin_cases j; simp [htdef, Matrix.toBlocks₁₁, hadef]
  set Em := Matrix.fromBlocks (a • (1 : Matrix (Fin 1) (Fin 1) A)) 0 (-w)
    (a • (1 : Matrix (Fin n) (Fin n) A)) with hEmdef
  set S := a • T0 - w * v with hSdef
  have hprod : Em * T' = Matrix.fromBlocks (a • t) (a • v) 0 S := by
    rw [hEmdef, hTblock, Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · rw [hta]; simp [Matrix.mul_smul, Matrix.smul_mul]
    · simp [hSdef]; abel
  have hat : a • t = (a * a) • (1 : Matrix (Fin 1) (Fin 1) A) := by rw [hta, smul_smul]
  have hdetEm : Em.det = a ^ (n + 1) := by
    rw [hEmdef, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul, Matrix.det_smul,
      Matrix.det_one, Matrix.det_one, mul_one, mul_one, Fintype.card_fin, Fintype.card_fin, pow_one]
    ring
  have hdetEm_ne : Em.det ≠ 0 := by rw [hdetEm]; exact pow_ne_zero _ ha
  have hdetC : (a • t).det = a ^ 2 := by
    rw [hat, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, pow_one]; ring
  have : (a • t).det ≠ 0 := by rw [hdetC]; exact pow_ne_zero _ ha
  have hdetprod1 : (Em * T').det = a ^ (n + 1) * T'.det := by rw [Matrix.det_mul, hdetEm]
  have hdetprod2 : (Em * T').det = a ^ 2 * S.det := by
    rw [hprod, Matrix.det_fromBlocks_zero₂₁, hdetC]
  have hdetrel : a ^ (n + 1) * T'.det = a ^ 2 * S.det := by rw [← hdetprod1, hdetprod2]
  have hSdet_ne : S.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdetrel
    exact (mul_ne_zero (pow_ne_zero _ ha) hT') hdetrel
  have hcok1 : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' (Em * T')))
      = Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' Em))
        + Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T')) :=
    cokerLen_mul A Em T' hdetEm_ne
  have hcok2 : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' (Em * T')))
      = Module.length A ((Fin 1 → A) ⧸ LinearMap.range (Matrix.toLin' (a • t)))
        + Module.length A ((Fin n → A) ⧸ LinearMap.range (Matrix.toLin' S)) := by
    rw [hprod]; exact block_cokerLen A (a • t) (a • v) S hSdet_ne
  have hcokEm : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' Em))
      = Module.length A ((Fin 1 → A) ⧸ LinearMap.range (Matrix.toLin' (a • (1 : Matrix (Fin 1) (Fin
          1) A))))
        + Module.length A ((Fin n → A) ⧸ LinearMap.range
            (Matrix.toLin' (a • (1 : Matrix (Fin n) (Fin n) A)))) := by
    rw [hEmdef]
    exact block_cokerLen_lower A (a • (1 : Matrix (Fin 1) (Fin 1) A)) (-w)
      (a • (1 : Matrix (Fin n) (Fin n) A))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, pow_one]; exact ha)
  set sa := Module.length A (A ⧸ Ideal.span {a}) with hsa
  have hsa_ne : sa ≠ ⊤ := spanLen_ne_top A a ha
  have hcokEm_val : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' Em))
      = (↑(n + 1) : ℕ∞) * sa := by
    rw [hcokEm, matrix_cokerLen_scalar A 1 a, matrix_cokerLen_scalar A n a, ← hsa]
    push_cast; ring
  have hcokC_val : Module.length A ((Fin 1 → A) ⧸ LinearMap.range (Matrix.toLin' (a • t)))
      = (2 : ℕ∞) * sa := by
    rw [hat, matrix_cokerLen_scalar A 1 (a * a),
      length_span_mul A a a ha, ← hsa]
    push_cast; ring
  have hcokS : Module.length A ((Fin n → A) ⧸ LinearMap.range (Matrix.toLin' S))
      = Module.length A (A ⧸ Ideal.span {S.det}) := IH S hSdet_ne
  have hcokEq : (↑(n + 1) : ℕ∞) * sa
        + Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T'))
      = (2 : ℕ∞) * sa + Module.length A (A ⧸ Ideal.span {S.det}) := by
    rw [← hcokEm_val, ← hcokC_val, ← hcokS, ← hcok1, ← hcok2]
  have hdet_eq : (↑(n + 1) : ℕ∞) * sa + Module.length A (A ⧸ Ideal.span {T'.det})
      = (2 : ℕ∞) * sa + Module.length A (A ⧸ Ideal.span {S.det}) := by
    have key : Module.length A (A ⧸ Ideal.span {a ^ (n + 1) * T'.det})
        = Module.length A (A ⧸ Ideal.span {a ^ 2 * S.det}) := by rw [hdetrel]
    rw [length_span_mul A (a ^ (n + 1)) T'.det (pow_ne_zero _ ha),
      length_span_mul A (a ^ 2) S.det (pow_ne_zero _ ha),
      spanLen_pow A a ha, spanLen_pow A a ha, ← hsa] at key
    -- key : L(T'.det) + (n+1)*sa = L(S.det) + 2*sa
    rw [add_comm ((↑(n + 1) : ℕ∞) * sa), add_comm ((2 : ℕ∞) * sa)]
    exact key
  have hfin : (↑(n + 1) : ℕ∞) * sa ≠ ⊤ := WithTop.mul_ne_top (ENat.natCast_ne_top _) hsa_ne
  exact WithTop.add_left_cancel hfin (hcokEq.trans hdet_eq.symm)

open Matrix in
/-- The inductive step after a permutation reduction arranging a nonzero `(0,0)` corner. -/
theorem step_sumform (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Ring.KrullDimLE 1 A] (n : ℕ)
    (IH : ∀ (S : Matrix (Fin n) (Fin n) A), S.det ≠ 0 →
      Module.length A ((Fin n → A) ⧸ LinearMap.range (Matrix.toLin' S))
        = Module.length A (A ⧸ Ideal.span {S.det}))
    (T' : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) A) (hT' : T'.det ≠ 0) :
    Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T'))
      = Module.length A (A ⧸ Ideal.span {T'.det}) := by
  -- column `inl 0` is nonzero
  obtain ⟨r, hr⟩ : ∃ i, T' i (Sum.inl 0) ≠ 0 := by
    by_contra h
    push Not at h
    exact hT' (Matrix.det_eq_zero_of_column_eq_zero (Sum.inl 0) h)
  set σ := Equiv.swap (Sum.inl 0 : Fin 1 ⊕ Fin n) r with hσ
  set P := σ.permMatrix A with hP
  have hPunit : IsUnit P.det := by
    rw [hP, Matrix.det_permutation]
    exact (Int.isUnit_iff.mpr (by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h])).map (Int.castRingHom
          A)
  have hPdet_ne : P.det ≠ 0 := hPunit.ne_zero
  -- corner of P * T'
  have hcorner : (P * T') (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
    have happ : (P * T') (Sum.inl 0) (Sum.inl 0) = T' (σ (Sum.inl 0)) (Sum.inl 0) := by
      rw [hP]
      simp [Equiv.Perm.permMatrix, Matrix.mul_apply, PEquiv.toMatrix, Equiv.toPEquiv_apply]
    rw [happ, hσ, Equiv.swap_apply_left]
    exact hr
  have hPT'det : (P * T').det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hPdet_ne hT'
  -- cokernel: cokerLen (P*T') = cokerLen P + cokerLen T' = cokerLen T'
  have hcokP : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' P)) = 0 :=
    cokerLen_isUnit A P hPunit
  have hcok : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' (P * T')))
      = Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T')) := by
    rw [cokerLen_mul A P T' hPdet_ne, hcokP, zero_add]
  -- span: spanLen (det (P*T')) = spanLen (det T')
  have hspan : Module.length A (A ⧸ Ideal.span {(P * T').det})
      = Module.length A (A ⧸ Ideal.span {T'.det}) := by
    rw [Matrix.det_mul, length_span_mul A P.det T'.det hPdet_ne, spanLen_isUnit A P.det hPunit,
      add_zero]
  -- apply the corner core to P * T'
  have hcore := step_sumform_corner A n IH (P * T') hPT'det hcorner
  rw [← hcok, hcore, hspan]

/-! ### The inductive step of `matrix_cokerLen_eq_spanLen`

Given the identity for all `n × n` matrices as induction hypothesis, prove it for an
`(n+1) × (n+1)` matrix `T` with `T.det ≠ 0`. This is the Schur clearing step:

  * Permutation reduction (II.4b): a permutation `P` (an isomorphism, `cokerLen P = 0`, and
    `det P = ±1` a unit so `length (A/span{det P}) = 0`) moves a row with nonzero first entry to
    the top, so WLOG `T 0 0 ≠ 0`.  Peel `P` via `matrix_cokerLen_mul` + `length_span_mul`.
  * Schur clearing: left-multiply `T` by the block-lower-triangular clearing matrix
    `E₋ = [[t₀₀, 0], [-w, t₀₀ • I]]` (`w` the first column below `t₀₀`); `det E₋ = t₀₀^(n+1)` and
    `E₋ T` is block-UPPER-triangular with diagonal blocks `t₀₀²` (a `1×1`) and the Schur
    complement `S = t₀₀ • T₀ - w ⬝ vᵀ ∈ M_n(A)`, with `det (E₋ T) = t₀₀² · det S` and
    `det (E₋ T) = t₀₀^(n+1) · det T`, so `det S ≠ 0`.
  * Block-upper-triangular dévissage (II.4a, via `matrix_cokerLen_devissage` with `N = A·e₀`):
    `cokerLen (E₋ T) = length (A/span{t₀₀²}) + cokerLen S`, and by `IH` on `S`,
    `cokerLen S = length (A/span{det S})`.
  * Recombine on the span side with `length_span_mul` using the two determinant relations.
-/

/-- Over a one-dimensional Noetherian local domain `A`, if the cokernel length of `toLin' S`
equals `length (A ⧸ span {det S})` for every `n × n` matrix `S` with `det S ≠ 0`, then the same
holds for every `(n+1) × (n+1)` matrix `T` with `det T ≠ 0`. -/
theorem matrix_cokerLen_eq_spanLen_step
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (n : ℕ)
    (IH : ∀ (S : Matrix (Fin n) (Fin n) A), S.det ≠ 0 →
      Module.length A ((Fin n → A) ⧸ LinearMap.range (Matrix.toLin' S))
        = Module.length A (A ⧸ Ideal.span {S.det}))
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (hT : T.det ≠ 0) :
    Module.length A ((Fin (n + 1) → A) ⧸ LinearMap.range (Matrix.toLin' T))
      = Module.length A (A ⧸ Ideal.span {T.det}) := by
  -- Reindex to `Fin 1 ⊕ Fin n` and apply the Schur-clearing reduction `step_sumform`.
  set e : Fin (n + 1) ≃ (Fin 1 ⊕ Fin n) :=
    (finCongr (add_comm n 1)).trans finSumFinEquiv.symm with he
  set T' := Matrix.reindex e e T with hT'def
  have hdetT' : T'.det = T.det := by rw [hT'def, Matrix.det_reindex_self]
  have hT'ne : T'.det ≠ 0 := by rw [hdetT']; exact hT
  have hcok : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T'))
      = Module.length A ((Fin (n + 1) → A) ⧸ LinearMap.range (Matrix.toLin' T)) :=
    cokerLen_reindex A e T
  rw [← hcok, step_sumform A n IH T' hT'ne, hdetT']

/-- For a square matrix `T` over a one-dimensional Noetherian local domain with `det T ≠ 0`,
the cokernel length of `toLin' T` equals `length (A ⧸ span {det T})`. -/
@[ega "IV 21.10.17.3" "special case"]
theorem matrix_cokerLen_eq_spanLen
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (m : ℕ) (T : Matrix (Fin m) (Fin m) A) (hT : T.det ≠ 0) :
    Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' T))
      = Module.length A (A ⧸ Ideal.span {T.det}) := by
  -- Stacks 02QH; the standard length-of-cokernel = ord-of-det identity).
  -- WIRING (VERIFIED): induction on `m`.  Base case `m = 0` is the zero module on both sides;
  -- the inductive step is `matrix_cokerLen_eq_spanLen_step` (the Part-II.4 Schur-clearing core).
  -- `T`/`hT` depend on `m`, so prove the universally-quantified statement by induction.
  suffices h : ∀ (k : ℕ) (S : Matrix (Fin k) (Fin k) A), S.det ≠ 0 →
      Module.length A ((Fin k → A) ⧸ LinearMap.range (Matrix.toLin' S))
        = Module.length A (A ⧸ Ideal.span {S.det}) by
    exact h m T hT
  intro k
  induction k with
  | zero =>
    intro S _
    have hdet : S.det = 1 := by simp [Matrix.det_fin_zero]
    rw [hdet, Ideal.span_singleton_one]
    have hl : Module.length A ((Fin 0 → A) ⧸ LinearMap.range (Matrix.toLin' S)) = 0 :=
      Module.length_eq_zero_iff.mpr ⟨fun a b => Subsingleton.elim a b⟩
    rw [hl]
    symm
    exact Module.length_eq_zero_iff.mpr ⟨fun a b => Subsingleton.elim a b⟩
  | succ n IH =>
    intro S hS
    exact matrix_cokerLen_eq_spanLen_step A n IH S hS

/-- The order of vanishing of `det T` equals the length of the cokernel of `toLin' T`. -/
@[ega "IV 21.10.17.3" "special case"]
theorem ordInt_matrix_det_eq_length_cokernel
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (m : ℕ) (T : Matrix (Fin m) (Fin m) A) (hT : T.det ≠ 0)
    (hTK : algebraMap A K T.det ≠ 0) :
    ordInt A (algebraMap A K T.det) hTK =
      ((Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' T))).toNat : ℤ) := by
  -- CITATION: Stacks Tag 02QH matrix base case.  Reduced (this iteration) to the pure `ℕ∞`
  -- length identity `matrix_cokerLen_eq_spanLen` via the already-proven `ordInt_algebraMap`
  -- applied to `r = T.det`.  SANITY CHECK PASSED.
  rw [ordInt_algebraMap A T.det hT hTK]
  rw [matrix_cokerLen_eq_spanLen A m T hT]

/-! ## Inputs for the 02QH kernel `ordInt_baseChangeDet_eq_length_cokernel`

The proof works with the integer
**defect** of an injective endomorphism `ψ` of a finite torsion-free `A`-module `N` whose base
change is a `K`-automorphism:

  `Δ(N,ψ) := (length_A (N ⧸ range ψ)).toNat  −  ordInt A (det (ψ.baseChange K))`.

The goal `ordInt_baseChangeDet_eq_length_cokernel` is exactly `Δ(M,φ) = 0`.

The argument (Route γ) is:
* (Lemma C) `Δ` of an endomorphism of a finite-length module is `0` (`length ker = length coker`);
* (Lemma B) `Δ(Aʳ, T) = 0` for a matrix `T` with `det T ≠ 0` — this is the PROVEN matrix base
  case `ordInt_matrix_det_eq_length_cokernel`;
* (Step 1) a full-rank free submodule `F ≅ Aʳ ⊆ M` with finite-length quotient `Q = M/F`;
* (Lemma A) `Δ` is additive over the SES `0 → F → M → Q → 0` when the endomorphism preserves `F`;
* (Step 2) replace `φ` by `ψ = a·φ` (`a ≠ 0 ∈ A`) so that `ψ` preserves `F`; then
  `Δ(M,ψ) = Δ(F,ψ|F) + Δ(Q,ψ̄) = 0 + 0 = 0` (Lemmas A,B,C);
* (Lemma D) the scalar identity `Δ(M, a·id) = 0` (same machinery, A+B+C);
* (comp) `Δ` is additive under composition `Δ(M, a·φ) = Δ(M, a·id) + Δ(M, φ)`,
  hence `Δ(M,φ) = Δ(M,ψ) − Δ(M, a·id) = 0`.

The reusable analytic content is packaged as the four lemmas
`length_ker_eq_length_coker_finiteLength`, `length_quot_smul_eq_rank_mul_ord`,
`exists_fullRank_free_submodule` and `defect_devissage_free`, assembled in the kernel proof.
-/

/-- For an endomorphism `ψ` of a finite-length `A`-module `L`, the kernel and cokernel have equal
`A`-length. Both `0 → ker ψ → L → im ψ → 0` and `0 → im ψ → L → coker ψ → 0` are short exact, so
additivity of `Module.length` gives
`length L = length ker + length im = length im + length coker`. -/
@[ega "IV 21.10.13" "(iii)"]
theorem length_ker_eq_length_coker_finiteLength
    (A : Type*) [CommRing A]
    (L : Type*) [AddCommGroup L] [Module A L] (hL : Module.length A L ≠ ⊤)
    (ψ : L →ₗ[A] L) :
    Module.length A (LinearMap.ker ψ) = Module.length A (L ⧸ LinearMap.range ψ) := by
  -- Use `Module.length_eq_add_of_exact` on the two SES through `im ψ ≅ L ⧸ ker ψ`.
  -- SES (1): 0 → ker ψ → L → L ⧸ ker ψ → 0
  have h1 : Module.length A L
      = Module.length A (LinearMap.ker ψ) + Module.length A (L ⧸ LinearMap.ker ψ) :=
    Module.length_eq_add_of_exact (LinearMap.ker ψ).subtype (LinearMap.ker ψ).mkQ
      Subtype.coe_injective (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  -- L ⧸ ker ψ ≅ range ψ
  have heq : Module.length A (L ⧸ LinearMap.ker ψ) = Module.length A (LinearMap.range ψ) :=
    (LinearMap.quotKerEquivRange ψ).length_eq
  -- SES (2): 0 → range ψ → L → L ⧸ range ψ → 0
  have h2 : Module.length A L
      = Module.length A (LinearMap.range ψ) + Module.length A (L ⧸ LinearMap.range ψ) :=
    Module.length_eq_add_of_exact (LinearMap.range ψ).subtype (LinearMap.range ψ).mkQ
      Subtype.coe_injective (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  -- combine: length(ker) + length(range) = length(range) + length(coker)
  rw [heq] at h1
  rw [h1, add_comm (Module.length A (LinearMap.ker ψ))] at h2
  -- h2 : range + ker = range + coker
  have hrange_ne : Module.length A (LinearMap.range ψ) ≠ ⊤ := by
    have hle := Module.length_le_of_injective (LinearMap.range ψ).subtype Subtype.coe_injective
    intro h; apply hL; exact top_le_iff.mp (h ▸ hle)
  exact WithTop.add_left_cancel hrange_ne h2

/-- STEP 1 (Route γ).  A finitely generated torsion-free module `M` over the `1`-dimensional
Noetherian local domain `A` contains a free `A`-submodule `F ≅ Aʳ` of full rank
`r = finrank K (M ⊗ K)` whose quotient `M ⧸ F` has finite length. Concretely there is an
injective `A`-linear map `j : (Fin r → A) →ₗ[A] M` with
`Module.length A (M ⧸ LinearMap.range j) ≠ ⊤`.
(Choose `x₁,…,x_r ∈ M` mapping to a `K`-basis of `M ⊗ K`; torsion-freeness ⟹ `A`-independent ⟹ `F`
free; `(M/F) ⊗ K = 0` ⟹ `M/F` torsion f.g. ⟹ finite length.) -/
theorem exists_fullRank_free_submodule
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M] :
    ∃ j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M,
      Function.Injective j ∧ Module.length A (M ⧸ LinearMap.range j) ≠ ⊤ := by
  classical
  have : FiniteDimensional K (TensorProduct A K M) := inferInstance
  -- Artinian helper: A/(a) is Artinian for a ≠ 0 (dim A/(a) ≤ dim A - 1 = 0).
  have hArt : ∀ (a : A), a ≠ 0 → IsArtinianRing (A ⧸ Ideal.span {a}) := by
    intro a ha
    rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
    refine ⟨inferInstance, ?_⟩
    rw [Ring.krullDimLE_iff]
    have hmem : a ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero ha
    have hq := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hmem
    have hA : ringKrullDim A ≤ ((1:ℕ):WithBot ℕ∞) := Ring.krullDimLE_iff.mp inferInstance
    have h : ringKrullDim (A ⧸ Ideal.span {a}) + 1 ≤ ((1:ℕ):WithBot ℕ∞) := le_trans hq hA
    set d := ringKrullDim (A ⧸ Ideal.span {a}) with hd
    have h' : d + 1 ≤ ((1:ℕ∞):WithBot ℕ∞) := by rw [← WithBot.coe_natCast] at h; exact_mod_cast h
    change d ≤ ((0:ℕ):WithBot ℕ∞)
    rw [show ((0:ℕ):WithBot ℕ∞) = ((0:ℕ∞):WithBot ℕ∞) by norm_cast]
    rw [WithBot.le_coe_iff]
    intro a' hda
    rw [hda] at h'
    have h2 : a' + 1 ≤ 1 := by exact_mod_cast h'
    cases a' with
    | top => simp at h2
    | coe n =>
      rw [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_le_natCast] at h2
      have : n = 0 := by omega
      subst this; simp
  -- The image of `M → K ⊗ M` (via `m ↦ 1 ⊗ₜ m`) `K`-spans `K ⊗ M`.
  have hspan : Submodule.span K (Set.range (fun m : M => (1:K) ⊗ₜ[A] m)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul k m =>
        have hkm : k ⊗ₜ[A] m = k • ((1:K) ⊗ₜ[A] m) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hkm]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    | add p q hp hq => exact Submodule.add_mem _ (hp Submodule.mem_top) (hq Submodule.mem_top)
  -- Choose `x₁,…,x_r ∈ M` whose images `1 ⊗ₜ xᵢ` form a `K`-basis of `K ⊗ M`.
  obtain ⟨x, bM, hbM⟩ :
      ∃ (x : Fin (Module.finrank K (TensorProduct A K M)) → M)
        (bM : Module.Basis (Fin (Module.finrank K (TensorProduct A K M))) K (TensorProduct A K M)),
        ∀ i, bM i = (1:K) ⊗ₜ[A] x i := by
    obtain ⟨b, hbsub, hbspan, hbli⟩ :=
      exists_linearIndependent K (Set.range (fun m : M => (1:K) ⊗ₜ[A] m))
    rw [hspan] at hbspan
    have hsple : ⊤ ≤ Submodule.span K (Set.range (Subtype.val : ↥b → TensorProduct A K M)) := by
      rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hbspan]
    set basis : Module.Basis (↥b) K (TensorProduct A K M) := Module.Basis.mk hbli hsple with hbasis
    have : Fintype (↥b) := FiniteDimensional.fintypeBasisIndex basis
    have hcard : Fintype.card (↥b) = Module.finrank K (TensorProduct A K M) :=
      (Module.finrank_eq_card_basis basis).symm
    set eqv : Fin (Module.finrank K (TensorProduct A K M)) ≃ ↥b :=
      (Fintype.equivFinOfCardEq hcard).symm with heqv
    have hmem : ∀ i, ((eqv i : TensorProduct A K M)) ∈
        Set.range (fun m : M => (1:K) ⊗ₜ[A] m) := fun i => hbsub (eqv i).property
    choose x hx using hmem
    refine ⟨x, basis.reindex eqv.symm, ?_⟩
    intro i
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hbasis, Module.Basis.mk_apply]
    exact (hx i).symm
  -- The (injective) embedding `ι : M → K ⊗ M`, `m ↦ 1 ⊗ₜ m`, via localization.
  set ι : M →ₗ[A] TensorProduct A K M := (TensorProduct.mk A K M) 1 with hιdef
  have hιinj : Function.Injective ι := by
    have : IsLocalizedModule (nonZeroDivisors A) ι := by
      rw [hιdef, isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) K]
      exact TensorProduct.isBaseChange A M K
    intro m m' h
    rw [← sub_eq_zero] at h ⊢
    rw [← map_sub, IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)] at h
    obtain ⟨s, hs⟩ := h
    have hs0 : (s : A) ≠ 0 := nonZeroDivisors.ne_zero s.property
    refine smul_right_injective M hs0 ?_
    simp only [smul_zero]; exact hs
  have hιx : ∀ i, ι (x i) = bM i := fun i => by rw [hιdef]; exact (hbM i).symm
  -- The candidate map `j : Aʳ → M`, `eᵢ ↦ xᵢ`.
  set j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M :=
    Fintype.linearCombination A x with hjdef
  -- Injectivity of `j` from `K`-independence of `1 ⊗ₜ xᵢ` and injectivity of `A → K`.
  have hjinj : Function.Injective j := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : ι (j v) = 0 := by rw [hv]; exact map_zero ι
    rw [hjdef, Fintype.linearCombination_apply, map_sum] at h0
    have h0' : ∑ i, (algebraMap A K (v i)) • bM i = 0 := by
      rw [← h0]; apply Finset.sum_congr rfl; intro i _
      rw [map_smul, hιx i, algebraMap_smul]
    have hli := bM.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have hz := hli (fun i => algebraMap A K (v i)) h0'
    funext i
    exact (FaithfulSMul.algebraMap_injective A K) ((hz i).trans (map_zero _).symm)
  refine ⟨j, hjinj, ?_⟩
  -- Every element of `M` becomes a `K`-combination of the `1 ⊗ₜ xᵢ`; clearing denominators
  -- shows some nonzero scalar carries it into `range j`.
  have htorM : ∀ m : M, ∃ a : A, a ≠ 0 ∧ a • m ∈ LinearMap.range j := by
    intro m
    set c := fun i => (bM.repr (ι m)) i with hc
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) c
    set a : A := (b : A) with ha
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero b.property
    choose d hd using hb
    refine ⟨a, ha0, ⟨d, ?_⟩⟩
    apply hιinj
    rw [hjdef, Fintype.linearCombination_apply, map_smul, map_sum]
    conv_rhs => rw [← Module.Basis.sum_repr bM (ι m)]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hιx i, ← algebraMap_smul (R := A) K (d i) (bM i), hd i, smul_assoc]
  -- Hence `Q = M ⧸ range j` is a torsion module: each element is killed by a nonzero scalar.
  have htorQ : ∀ q : M ⧸ LinearMap.range j, ∃ a : A, a ≠ 0 ∧ a • q = 0 := by
    intro q
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha0, hmem⟩ := htorM m
    refine ⟨a, ha0, ?_⟩
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hmem
  -- `Q` is finitely generated and torsion, hence annihilated by a single nonzero `a`.
  obtain ⟨a, ha0, hann⟩ : ∃ a : A, a ≠ 0 ∧ ∀ q : M ⧸ LinearMap.range j, a • q = 0 := by
    obtain ⟨s, hs⟩ := (Module.finite_def.mp (by infer_instance) :
      (⊤ : Submodule A (M ⧸ LinearMap.range j)).FG)
    choose f hf0 hf using htorQ
    set a : A := ∏ g ∈ s, f g with ha
    have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun g _ => hf0 g)
    refine ⟨a, ha0, ?_⟩
    have hgen : ∀ g ∈ s, a • g = 0 := by
      intro g hg
      rw [ha, ← Finset.prod_erase_mul _ _ hg, mul_smul, hf g, smul_zero]
    intro q
    have hq : q ∈ (⊤ : Submodule A (M ⧸ LinearMap.range j)) := Submodule.mem_top
    rw [← hs] at hq
    induction hq using Submodule.span_induction with
    | mem y hy => exact hgen y hy
    | zero => exact smul_zero a
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_comm, hy, smul_zero]
  -- `Q` is a finite module over the Artinian ring `A/(a)`, hence Artinian over `A`.
  have hArtQ : IsArtinian A (M ⧸ LinearMap.range j) := by
    set I : Ideal A := Ideal.span {a} with hI
    have htor : Module.IsTorsionBySet A (M ⧸ LinearMap.range j) (I : Set A) := by
      intro q r
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp r.property
      rw [← hc, mul_smul, hann]; simp
    let : Module (A ⧸ I) (M ⧸ LinearMap.range j) := htor.module
    have : IsScalarTower A (A ⧸ I) (M ⧸ LinearMap.range j) := htor.isScalarTower
    have : Module.Finite (A ⧸ I) (M ⧸ LinearMap.range j) :=
      Module.Finite.of_restrictScalars_finite A (A ⧸ I) (M ⧸ LinearMap.range j)
    have : IsArtinianRing (A ⧸ I) := hArt a ha0
    have : IsArtinian (A ⧸ I) (M ⧸ LinearMap.range j) := isArtinian_of_fg_of_artinian'
    exact isArtinian_of_surjective_algebraMap (S := A) (R := A ⧸ I)
      (M := M ⧸ LinearMap.range j) Ideal.Quotient.mk_surjective
  -- Noetherian + Artinian = finite length, so the length is not `⊤`.
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, hArtQ⟩

/-- DÉVISSAGE — MATRIX OF `ψ` ON THE FREE SUBMODULE (Route γ, Step 0).  If `ψ` preserves the
submodule `range j` for an INJECTIVE `j`, then there is a (unique) `A`-linear `S : Aʳ → Aʳ` with
`ψ ∘ₗ j = j ∘ₗ S`.  (Universal property of the injective `j`: each `ψ (j x) ∈ range j` has a unique
preimage under `j`; assemble into a linear map via the linear equiv `Aʳ ≃ range j` coming
from injectivity, using `LinearEquiv.ofInjective j` and `LinearMap.codRestrict`.) -/
theorem exists_matrix_of_preserves_range
    (A : Type*) [CommRing A]
    (M : Type*) [AddCommGroup M] [Module A M]
    (n : ℕ)
    (ψ : M →ₗ[A] M)
    (j : (Fin n → A) →ₗ[A] M)
    (hjinj : Function.Injective j)
    (hpres : ∀ x, ψ (j x) ∈ LinearMap.range j) :
    ∃ S : (Fin n → A) →ₗ[A] (Fin n → A), ψ ∘ₗ j = j ∘ₗ S := by
  refine ⟨(LinearEquiv.ofInjective j hjinj).symm.toLinearMap ∘ₗ
      (LinearMap.codRestrict (LinearMap.range j) (ψ ∘ₗ j) hpres), ?_⟩
  ext x
  simp only [LinearMap.comp_apply]
  have : (LinearEquiv.ofInjective j hjinj) ((LinearEquiv.ofInjective j hjinj).symm
      ⟨ψ (j x), hpres x⟩) = ⟨ψ (j x), hpres x⟩ :=
    (LinearEquiv.ofInjective j hjinj).apply_symm_apply _
  have h2 := congrArg (Submodule.subtype (LinearMap.range j)) this
  simp

/-- DÉVISSAGE — DET SIDE (Route γ).  If `ψ` preserves the full-rank free submodule `range j`
(with `j` injective, finite-length quotient), and `S : Aʳ → Aʳ` is the matrix of `ψ` on that free
submodule (the unique map with `j ∘ₗ S = ψ ∘ₗ j`), then the base-change determinant of `ψ` equals
`algebraMap A K (det S)`.

*Proof.* Tensor `ψ ∘ₗ j = j ∘ₗ S` with the flat `A`-algebra `K` to get
`(ψ⊗K) ∘ (j⊗K) = (j⊗K) ∘ (S⊗K)`. Now `j⊗K` is a `K`-isomorphism, by full rank `r`,
torsion cokernel `Q⊗K = 0` and flatness of `K`, so `ψ⊗K` is conjugate to `S⊗K`. Finally
`det` is conjugation-invariant
(`LinearMap.det_conj`) and `det (S.baseChange K) = algebraMap A K (det S)`
(`LinearMap.det_baseChange`, `S` an endo of the free module `Fin r → A`). -/
@[ega "II 6.4.2" "special case"]
theorem det_baseChange_eq_algebraMap_det
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (ψ : M →ₗ[A] M)
    (j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M)
    (hjinj : Function.Injective j)
    (S : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A]
        (Fin (Module.finrank K (TensorProduct A K M)) → A))
    (hS : ψ ∘ₗ j = j ∘ₗ S) :
    LinearMap.det (ψ.baseChange K) = algebraMap A K (LinearMap.det S) := by
  have : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  have hjKinj : Function.Injective (j.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap j hjinj
  have : FiniteDimensional K (TensorProduct A K M) := inferInstance
  have : FiniteDimensional K (TensorProduct A K (Fin (Module.finrank K (TensorProduct A K M)) →
      A)) :=
    inferInstance
  have hdim : Module.finrank K (TensorProduct A K (Fin (Module.finrank K (TensorProduct A K M)) →
      A))
      = Module.finrank K (TensorProduct A K M) := by
    rw [Module.finrank_baseChange]; simp
  have hbij : Function.Bijective (j.baseChange K) := by
    refine ⟨hjKinj, ?_⟩
    have hr : Module.finrank K (LinearMap.range (j.baseChange K))
        = Module.finrank K (TensorProduct A K M) := by
      rw [LinearMap.finrank_range_of_inj hjKinj, hdim]
    rw [← LinearMap.range_eq_top]
    exact Submodule.eq_top_of_finrank_eq hr
  set e : (TensorProduct A K (Fin (Module.finrank K (TensorProduct A K M)) → A)) ≃ₗ[K]
      (TensorProduct A K M) := LinearEquiv.ofBijective (j.baseChange K) hbij with he
  have hint : (ψ.baseChange K) ∘ₗ (j.baseChange K) = (j.baseChange K) ∘ₗ (S.baseChange K) := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hS]
  have hconj : ψ.baseChange K = (e : _ →ₗ[K] _) ∘ₗ (S.baseChange K) ∘ₗ (e.symm : _ →ₗ[K] _) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have hey : e y = (j.baseChange K) y := rfl
    rw [hey]
    have := LinearMap.congr_fun hint y
    simp only [LinearMap.comp_apply] at this
    exact this
  rw [hconj, LinearMap.det_conj, LinearMap.det_baseChange]

/-- Dévissage on the length side. With `ψ` injective preserving the full-rank free submodule
`range j` (finite-length quotient `Q = M ⧸ range j`) and `S : Aʳ → Aʳ` its matrix on the free part
(`j ∘ₗ S = ψ ∘ₗ j`), the cokernel of `ψ` on `M` has the SAME length as the cokernel of `S` on `Aʳ`.

*Proof.* The map `j` carries `range S` onto `range (ψ|F)`, giving
`length(Aʳ/range S) = length(F/range(ψ|F))`.  The snake lemma for the SES `0 → F → M → Q → 0` with
`ψ` acting (`ψ|F` on `F`, `ψ̄` on `Q`) yields a 6-term exact sequence; `ker ψ = 0`, `ker (ψ|F) = 0`
reduce it to `0 → ker ψ̄ → F/range(ψ|F) → M/range ψ → Q/range ψ̄ → 0`.  Splitting into two SES and
using `Module.length_eq_add_of_exact` gives `length(M/range ψ) − length(F/range(ψ|F)) =
length(Q/range ψ̄) − length(ker ψ̄)`, which vanishes by Lemma C
(`length_ker_eq_length_coker_finiteLength`, `Q` finite length — `ψ̄` need NOT be injective). -/
theorem length_quot_range_eq_of_intertwine
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (ψ : M →ₗ[A] M) (hψinj : Function.Injective ψ)
    (j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M)
    (hjinj : Function.Injective j)
    (hjlen : Module.length A (M ⧸ LinearMap.range j) ≠ ⊤)
    (S : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A]
        (Fin (Module.finrank K (TensorProduct A K M)) → A))
    (hS : ψ ∘ₗ j = j ∘ₗ S) :
    Module.length A (M ⧸ LinearMap.range ψ) =
      Module.length A ((Fin (Module.finrank K (TensorProduct A K M)) → A) ⧸ LinearMap.range S) := by
  classical
  set F := LinearMap.range j with hFdef
  -- ψ preserves F = range j, since ψ (j x) = j (S x) ∈ range j.
  have hjSeq : ∀ x, ψ (j x) = j (S x) := by
    intro x
    have := LinearMap.congr_fun hS x
    simp only [LinearMap.comp_apply] at this
    exact this
  have hψFmem : ∀ x ∈ F, ψ x ∈ F := by
    rintro _ ⟨x, rfl⟩
    rw [hjSeq x]
    exact ⟨S x, rfl⟩
  have hψF : F ≤ Submodule.comap ψ F := hψFmem
  set ψF := ψ.restrict hψFmem with hψFdef
  set ψbar := F.mapQ F ψ hψF with hψbardef
  -- STEP 1: length(Aʳ/range S) = length(F/range ψF), via the iso j : Aʳ ≃ₗ F.
  have step1 : Module.length A ((Fin (Module.finrank K (TensorProduct A K M)) → A) ⧸
      LinearMap.range S)
      = Module.length A (LinearMap.range j ⧸ LinearMap.range ψF) := by
    apply cokerLen_intertwine A S ψF (LinearEquiv.ofInjective j hjinj)
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hψFdef, LinearMap.coe_restrict_apply]
    rw [LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply]
    exact (hjSeq x).symm
  -- Q-finite-length: length(M/F) ≠ ⊤
  have hQfin : Module.length A (M ⧸ F) ≠ ⊤ := by rw [hFdef]; exact hjlen
  -- f : F/range ψF → M/range ψ  induced by F.subtype
  have hf : LinearMap.range ψF ≤ Submodule.comap F.subtype (LinearMap.range ψ) := by
    rintro _ ⟨z, rfl⟩
    rw [Submodule.mem_comap]
    refine ⟨(z : M), ?_⟩
    rw [hψFdef, Submodule.subtype_apply, LinearMap.coe_restrict_apply]
  set f : (F ⧸ LinearMap.range ψF) →ₗ[A] (M ⧸ LinearMap.range ψ) :=
    Submodule.mapQ (LinearMap.range ψF) (LinearMap.range ψ) F.subtype hf with hfdef
  -- g : M/range ψ → Q/range ψbar  induced by F.mkQ
  have hg : LinearMap.range ψ ≤ Submodule.comap F.mkQ (LinearMap.range ψbar) := by
    rintro _ ⟨m, rfl⟩
    rw [Submodule.mem_comap]
    refine ⟨F.mkQ m, ?_⟩
    rw [hψbardef, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  set g : (M ⧸ LinearMap.range ψ) →ₗ[A] ((M ⧸ F) ⧸ LinearMap.range ψbar) :=
    Submodule.mapQ (LinearMap.range ψ) (LinearMap.range ψbar) F.mkQ hg with hgdef
  -- g is surjective
  have hgsurj : Function.Surjective g := by
    intro w
    obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range ψbar) w
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective F q
    refine ⟨(LinearMap.range ψ).mkQ m, ?_⟩
    simp only [hgdef, Submodule.mkQ_apply, Submodule.mapQ_apply]
  -- exactness at M/range ψ : range f = ker g
  have hexact : LinearMap.range f = LinearMap.ker g := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range ψF) z
      rw [LinearMap.mem_ker]
      simp only [hfdef, hgdef, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.subtype_apply]
      rw [Submodule.Quotient.mk_eq_zero]
      have hx0 : (Submodule.Quotient.mk (x : M) : M ⧸ F) = 0 :=
        (Submodule.Quotient.mk_eq_zero F).mpr x.property
      rw [hx0]
      exact zero_mem _
    · intro z hz
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range ψ) z
      rw [LinearMap.mem_ker] at hz
      simp only [hgdef, Submodule.mkQ_apply, Submodule.mapQ_apply] at hz
      rw [Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨q, hq⟩ := hz
      obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective F q
      rw [hψbardef, Submodule.mkQ_apply, Submodule.mapQ_apply] at hq
      have hmem : m - ψ m' ∈ F := (Submodule.Quotient.eq F).mp hq.symm
      refine ⟨(LinearMap.range ψF).mkQ ⟨m - ψ m', hmem⟩, ?_⟩
      simp only [hfdef, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.subtype_apply]
      rw [Submodule.Quotient.eq]
      exact ⟨-m', by simp⟩
  -- eq1: SES  0 → range f → M/range ψ → Q/range ψbar → 0
  have eq1 : Module.length A (M ⧸ LinearMap.range ψ)
      = Module.length A (LinearMap.range f)
        + Module.length A ((M ⧸ F) ⧸ LinearMap.range ψbar) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype g Subtype.coe_injective hgsurj
      (by rw [LinearMap.exact_iff, Submodule.range_subtype, hexact])
  -- eq2: SES  0 → ker f → F/range ψF → range f → 0
  have eq2 : Module.length A (F ⧸ LinearMap.range ψF)
      = Module.length A (LinearMap.ker f) + Module.length A (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict Subtype.coe_injective
      f.surjective_rangeRestrict
      (by rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict])
  -- eq4: Lemma C on the finite-length quotient Q = M/F, applied to ψbar
  have eq4 : Module.length A (LinearMap.ker ψbar)
      = Module.length A ((M ⧸ F) ⧸ LinearMap.range ψbar) :=
    length_ker_eq_length_coker_finiteLength A (M ⧸ F) hQfin ψbar
  -- eq3: ker f ≅ ker ψbar  (the snake connecting iso), so equal length.
  have eq3 : Module.length A (LinearMap.ker f) = Module.length A (LinearMap.ker ψbar) := by
    -- G = preimage of F under ψ;  F ≤ G.
    set G := Submodule.comap ψ F with hGdef
    have hFG : F ≤ G := hψF
    -- θ : G →ₗ F  is ψ restricted (lands in F since G = comap ψ F).
    have hθmem : ∀ x ∈ G, ψ x ∈ F := fun x hx => hx
    set θ : G →ₗ[A] F := ψ.restrict hθmem with hθdef
    -- surjG : G →ₗ ker ψbar,  x ↦ [x]_F
    have hsg : ∀ x : G, F.mkQ (G.subtype x) ∈ LinearMap.ker ψbar := by
      intro x
      rw [LinearMap.mem_ker, hψbardef, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact x.property
    set surjG : G →ₗ[A] (LinearMap.ker ψbar) :=
      LinearMap.codRestrict (LinearMap.ker ψbar) (F.mkQ ∘ₗ G.subtype) hsg with hsgdef
    -- θ' : G →ₗ ker f,  x ↦ [ψ x]_{range ψF}
    have htf : ∀ x : G, (LinearMap.range ψF).mkQ (θ x) ∈ LinearMap.ker f := by
      intro x
      rw [LinearMap.mem_ker, hfdef, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.subtype_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨G.subtype x, ?_⟩
      rw [hθdef, Submodule.subtype_apply, LinearMap.coe_restrict_apply]
    set θ' : G →ₗ[A] (LinearMap.ker f) :=
      LinearMap.codRestrict (LinearMap.ker f) ((LinearMap.range ψF).mkQ ∘ₗ θ) htf with hθ'def
    -- surjG surjective
    have hsg_surj : Function.Surjective surjG := by
      rintro ⟨z, hz⟩
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective F z
      rw [LinearMap.mem_ker, hψbardef, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero] at hz
      refine ⟨⟨m, hz⟩, ?_⟩
      apply Subtype.ext
      simp only [hsgdef, LinearMap.codRestrict_apply, LinearMap.comp_apply,
        Submodule.subtype_apply, Submodule.mkQ_apply]
    -- θ' surjective
    have hθ'_surj : Function.Surjective θ' := by
      rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range ψF) z
      rw [LinearMap.mem_ker, hfdef, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.subtype_apply, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨m, hm⟩ := hz
      have hmG : m ∈ G := by rw [hGdef, Submodule.mem_comap, hm]; exact w.property
      refine ⟨⟨m, hmG⟩, ?_⟩
      apply Subtype.ext
      simp only [hθ'def, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
      congr 1
      exact Subtype.ext (by rwa [hθdef, LinearMap.coe_restrict_apply])
    -- ker surjG = ker θ' = F restricted to G
    have hkereq : LinearMap.ker surjG = LinearMap.ker θ' := by
      ext x
      constructor
      · intro hx
        rw [LinearMap.mem_ker] at hx ⊢
        -- from hx : surjG x = 0 get ↑x ∈ F
        have hx0 : F.mkQ (G.subtype x) = 0 := by
          simpa [hsgdef, LinearMap.codRestrict_apply, LinearMap.comp_apply] using
            congrArg Subtype.val hx
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx0
        -- so ψ ↑x = ψ-image of an element of F, i.e. θ x ∈ range ψF
        apply Subtype.ext
        simp only [hθ'def, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          ZeroMemClass.coe_zero]
        rw [Submodule.Quotient.mk_eq_zero]
        refine ⟨⟨G.subtype x, hx0⟩, ?_⟩
        apply Subtype.ext
        simp only [hθdef, hψFdef, LinearMap.coe_restrict_apply, Submodule.subtype_apply]
      · intro hx
        rw [LinearMap.mem_ker] at hx ⊢
        have hx0 : (LinearMap.range ψF).mkQ (θ x) = 0 := by
          simpa [hθ'def, LinearMap.codRestrict_apply, LinearMap.comp_apply] using
            congrArg Subtype.val hx
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx0
        obtain ⟨y, hy⟩ := hx0
        -- hy : ψF y = θ x, i.e. ψ ↑y = ψ ↑x, ψ inj ⟹ ↑x = ↑y ∈ F
        have hxF : (G.subtype x : M) ∈ F := by
          have h1 : ψ (G.subtype x) = ψ (y : M) := by
            simpa only [hθdef, hψFdef, LinearMap.coe_restrict_apply, Submodule.subtype_apply]
              using (congrArg Subtype.val hy).symm
          rw [hψinj h1]; exact y.property
        apply Subtype.ext
        simp only [hsgdef, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          ZeroMemClass.coe_zero]
        rw [Submodule.Quotient.mk_eq_zero]
        exact hxF
    -- assemble via the two quotient-by-kernel equivalences
    have e1 := LinearMap.quotKerEquivOfSurjective surjG hsg_surj
    have e2 := LinearMap.quotKerEquivOfSurjective θ' hθ'_surj
    rw [← e2.length_eq, ← hkereq, e1.length_eq]
  -- Assemble step 2.
  have step2 : Module.length A (M ⧸ LinearMap.range ψ)
      = Module.length A (F ⧸ LinearMap.range ψF) := by
    rw [eq1, eq2, eq3, eq4, add_comm]
  rw [step2, ← step1]

/-- LEMMA A + assembly (Route γ).  Defect dévissage over a full-rank free submodule.  If `M` is
finite torsion-free over the `1`-dim Noetherian local domain `A`, `ψ : M →ₗ M` is injective with
`det (ψ.baseChange K) ≠ 0`, and `ψ` preserves a full-rank free submodule (equivalently the defect
splits over the SES `0 → F → M → Q → 0`), then `Δ(M,ψ) = 0`, i.e.
`ordInt A (det (ψ.baseChange K)) = (length_A (M ⧸ range ψ)).toNat`.

This bundles Lemma A (snake-lemma additivity of `Δ` over the SES, with block-triangular det
multiplicativity), Lemma B (matrix base case on `F`), and Lemma C (finite-length quotient `Q`).
It is the heaviest remaining analytic obligation; it is the defect-vanishing for a SINGLE
endomorphism that preserves a chosen full-rank free submodule. -/
@[ega "IV 21.10.17.3" "special case"]
theorem defect_devissage_free
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (ψ : M →ₗ[A] M) (hψinj : Function.Injective ψ)
    (j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M)
    (hjinj : Function.Injective j)
    (hjlen : Module.length A (M ⧸ LinearMap.range j) ≠ ⊤)
    (hpres : ∀ x, ψ (j x) ∈ LinearMap.range j)
    (hdet : LinearMap.det (ψ.baseChange K) ≠ 0) :
    ordInt A (LinearMap.det (ψ.baseChange K)) hdet =
      ((Module.length A (M ⧸ LinearMap.range ψ)).toNat : ℤ) := by
  classical
  -- Step 0: build the matrix `S : Aʳ → Aʳ` of `ψ` on the free submodule `range j`, via the
  -- universal property of the injective `j`: each `ψ (j eᵢ) ∈ range j` has a unique preimage.
  -- `S := j.comp⁻¹ (ψ ∘ₗ j)`; concretely choose preimages with `Classical.choice`/`hpres`.
  -- Use `LinearMap.range j ≅ (Fin r → A)` (j injective) to define S with `j ∘ₗ S = ψ ∘ₗ j`.
  have hSexists : ∃ S : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A]
      (Fin (Module.finrank K (TensorProduct A K M)) → A), ψ ∘ₗ j = j ∘ₗ S :=
    exists_matrix_of_preserves_range A M _ ψ j hjinj hpres
  obtain ⟨S, hS⟩ := hSexists
  -- Step 0 (det): det(ψ⊗K) = algebraMap A K (det S).
  have hdetS : LinearMap.det (ψ.baseChange K) = algebraMap A K (LinearMap.det S) :=
    det_baseChange_eq_algebraMap_det A K M ψ j hjinj S hS
  -- det S ≠ 0 (algebraMap injective on the domain A).
  have hSne : LinearMap.det S ≠ 0 := by
    intro h
    apply hdet
    rw [hdetS, h, map_zero]
  have hSneK : algebraMap A K (LinearMap.det S) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hSne
  -- Step 1 (matrix base case via the matrix `T := toMatrix' S`, `S = toLin' T`, `det S = det T`).
  set T := LinearMap.toMatrix' S with hT
  have hST : S = Matrix.toLin' T := by rw [hT, Matrix.toLin'_toMatrix']
  have hTdet : T.det = LinearMap.det S := by rw [hT, LinearMap.det_toMatrix']
  have hTne : T.det ≠ 0 := by rw [hTdet]; exact hSne
  have hTneK : algebraMap A K T.det ≠ 0 := by rw [hTdet]; exact hSneK
  -- matrix base case: ord(alg(det T)) = length(Aʳ/range(toLin' T)).toNat
  have hmbc :
      ordInt A (algebraMap A K T.det) hTneK =
        ((Module.length A ((Fin (Module.finrank K (TensorProduct A K M)) → A) ⧸
            LinearMap.range (Matrix.toLin' T))).toNat : ℤ) :=
    ordInt_matrix_det_eq_length_cokernel A K (Module.finrank K (TensorProduct A K M)) T hTne hTneK
  -- Step 2 (length side): length(M/range ψ) = length(Aʳ/range S) = length(Aʳ/range(toLin' T)).
  have hlen : Module.length A (M ⧸ LinearMap.range ψ) =
      Module.length A ((Fin (Module.finrank K (TensorProduct A K M)) → A) ⧸ LinearMap.range S) :=
    length_quot_range_eq_of_intertwine A K M ψ hψinj j hjinj hjlen S hS
  -- Assemble. Rewrite ordInt(det(ψ⊗K)) to ordInt(alg(det T)) via proof-irrelevant congruence.
  have ordA_congr : ∀ (x y : K) (hx : x ≠ 0) (hy : y ≠ 0), x = y →
      ordInt A x hx = ordInt A y hy := by
    intro x y hx hy h; subst h; rfl
  have e1 : ordInt A (LinearMap.det (ψ.baseChange K)) hdet =
      ordInt A (algebraMap A K T.det) hTneK :=
    ordA_congr _ _ _ _ (by rw [hdetS, hTdet])
  rw [e1, hmbc, hlen, hST]

/-- COMPOSITION ADDITIVITY (Route γ, the cokernel-length part of `comp`).  For injective
endomorphisms `f, g` of a finite torsion-free `A`-module `M`, both base-changing to
`K`-automorphisms
(so all three cokernels are torsion of finite length), the cokernel length is additive under
composition:
`length_A (M ⧸ range (g ∘ f)) = length_A (M ⧸ range f) + length_A (M ⧸ range g)`.
(Snake lemma `0 → coker f → coker (g∘f) → coker g → 0`; `Module.length_eq_add_of_exact`.)  The
`ord∘det` side is multiplicative by `LinearMap.det_comp` + `map_mul` + `ordInt_mul`, handled inline
in the kernel.  Compare the matrix analogue `matrix_cokerLen_mul`, already proven. -/
theorem cokerLen_comp_add
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (f g : M →ₗ[A] M) (hg : Function.Injective g) :
    Module.length A (M ⧸ LinearMap.range (g ∘ₗ f)) =
      Module.length A (M ⧸ LinearMap.range f) + Module.length A (M ⧸ LinearMap.range g) := by
  -- Directly reuse the proven general helper with φ = g, ψ = f (only g-injectivity needed).
  exact matrix_cokerLen_mul_helper A M g f hg

