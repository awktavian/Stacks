module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Flat descent for a comparison of sheaves of modules

Let `A → B` be a flat ring map. This file proves the local-to-global step that turns an
isomorphism over the members of a finite cover into an isomorphism over the union, for a
comparison

  `B ⊗[A] M U ⟶ N U`

between an `A`-module-valued sheaf `M` and a `B`-module-valued sheaf `N` on a frame of opens.
It is the engine of degree-zero flat base change for the sections of a quasi-coherent module
([Stacks, Tag 02KH] part (2) for `i = 0`), which is proved in
`StacksFrontier/AlgebraicGeometry/PullbackSections/Qcqs.lean`; nothing here mentions schemes.

## Main definitions

* `Stacks.FlatSectionsDescent.Comparison`: the data of a comparison — restriction maps on both
  sides, the comparison map, the two sheaf axioms needed, and their compatibilities.
* `Stacks.FlatSectionsDescent.Comparison.baseChangeMap`: the induced `B`-linear map
  `B ⊗[A] M U ⟶ N U`.

## Main results

* `Stacks.FlatSectionsDescent.injective_liftBaseChange_of_pi` and
  `Stacks.FlatSectionsDescent.bijective_liftBaseChange_of_pair`: the two purely algebraic steps.
  The first says that injectivity of a base change can be checked on a finite family of
  quotients whose joint kernel is zero; the second is the Mayer–Vietoris step, deducing
  bijectivity over a union from bijectivity over the two pieces and injectivity over the
  intersection.
* `Stacks.FlatSectionsDescent.Comparison.injective_baseChangeMap_of_iSup` and
  `Stacks.FlatSectionsDescent.Comparison.bijective_baseChangeMap_of_iSup`: **the induction.**
  The comparison is injective over a finite union of opens on which it is injective, and
  bijective over a finite union of opens on which it is bijective provided it is injective over
  the pairwise intersections.

## Implementation notes

Flatness is used three times and only through Mathlib: `Module.Flat.lTensor_exact` and
`Module.Flat.lTensor_preserves_injective_linearMap` for the two algebraic steps, and the
distributivity of `⊗` over finite products (`TensorProduct.piRight`, `TensorProduct.prodRight`)
to read off the components. The algebraic steps are stated for abstract modules so that the
tensor-product manipulations never run at a sheaf-section type; the induction then only applies
them.

The lattice of opens is taken abstractly, as an `Order.Frame`, and the target sheaf is indexed by
the *source* lattice: in the application `N U` is the sections of the pulled-back module over the
preimage of `U`, and that the preimage preserves suprema and infima is checked at the application
site rather than assumed here.

Only separation is asked of the target `N`; gluing is needed for the source `M` alone, and only
for a pair of opens.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 058S](https://stacks.math.columbia.edu/tag/058S)
-/

@[expose] public noncomputable section

universe u

open TensorProduct


namespace Stacks.FlatSectionsDescent

/-! ### Two scalar-structure helpers, proved at abstract types -/

/-- Two scalar structures given by ring maps through a commuting square form a tower. -/
theorem isScalarTower_of_smul_eq {A B R M : Type*} [CommRing A] [CommRing B] [CommRing R]
    [AddCommGroup M] [Module R M] [Algebra A B] [Module A M] [Module B M]
    (ψ : B →+* R) (hB : ∀ (b : B) (m : M), b • m = ψ b • m)
    (α : A →+* R) (hA : ∀ (a : A) (m : M), a • m = α a • m)
    (hcomp : ∀ a, α a = ψ (algebraMap A B a)) :
    IsScalarTower A B M := by
  refine ⟨fun a b m => ?_⟩
  rw [hB, hA, hB, Algebra.smul_def, map_mul, mul_smul, hcomp]

/-- An additive map that is semilinear along a commuting square of ring maps is linear for the
two induced scalar structures. -/
theorem map_smul_of_smul_eq {A R R' M N : Type*} [CommRing A] [CommRing R] [CommRing R']
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N] [Module A M] [Module A N]
    (α : A →+* R) (hM : ∀ (a : A) (m : M), a • m = α a • m)
    (β : A →+* R') (hN : ∀ (a : A) (n : N), a • n = β a • n)
    (f : R →+* R') (hf : ∀ a, β a = f (α a))
    (g : M →+ N) (hg : ∀ (r : R) (m : M), g (r • m) = f r • g m) (a : A) (m : M) :
    g (a • m) = a • g m := by
  rw [hM, hg, hN, hf]


variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

section Square

variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
  {N N' : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']

/-- Given a commuting square `cmp' ∘ r = s ∘ cmp`, the base changes of `cmp` and `cmp'` satisfy
`cmp'.liftBaseChange B ∘ lTensor B r = s ∘ cmp.liftBaseChange B`. -/
theorem liftBaseChange_lTensor
    (cmp : M →ₗ[A] N) (cmp' : M' →ₗ[A] N') (r : M →ₗ[A] M') (s : N →ₗ[B] N')
    (h : ∀ m, cmp' (r m) = s (cmp m)) (x : B ⊗[A] M) :
    cmp'.liftBaseChange B (LinearMap.lTensor B r x) =
      s (cmp.liftBaseChange B x) := by
  induction x with
  | add x y hx hy => simp [hx, hy]
  | tmul b m => simp [h m]

end Square

section Tmul

variable {M N : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- The base change of `cmp` is determined by its values on pure tensors. -/
theorem liftBaseChange_eq_of_tmul (cmp : M →ₗ[A] N) (g : B ⊗[A] M →+ N)
    (h : ∀ (b : B) (m : M), g (b ⊗ₜ[A] m) = b • cmp m) (x : B ⊗[A] M) :
    cmp.liftBaseChange B x = g x := by
  induction x with
  | add u v hu hv => rw [map_add, map_add, hu, hv]
  | tmul b m => rw [LinearMap.liftBaseChange_tmul, h]

/-- Bijectivity of the base change of `cmp`, read off a bijection agreeing with it on pure
tensors. -/
theorem bijective_liftBaseChange_of_tmul (cmp : M →ₗ[A] N) (g : B ⊗[A] M →+ N)
    (hg : Function.Bijective g) (h : ∀ (b : B) (m : M), g (b ⊗ₜ[A] m) = b • cmp m) :
    Function.Bijective (cmp.liftBaseChange B) := by
  rwa [show (cmp.liftBaseChange B : B ⊗[A] M → N) = g from
    funext (liftBaseChange_eq_of_tmul cmp g h)]

/-- A bijective base change exhibits the target as a base change. -/
theorem isBaseChange_of_bijective_liftBaseChange (cmp : M →ₗ[A] N)
    (h : Function.Bijective (cmp.liftBaseChange B)) : IsBaseChange B cmp :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective (cmp.liftBaseChange B) h)
    (fun m => by simp)

end Tmul

section Pi

variable [Module.Flat A B] {ι : Type*} [Finite ι]
  {M : Type*} [AddCommGroup M] [Module A M]
  {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module A (Mi i)]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {Ni : ι → Type*} [∀ i, AddCommGroup (Ni i)] [∀ i, Module A (Ni i)]
  [∀ i, Module B (Ni i)] [∀ i, IsScalarTower A B (Ni i)]

omit [Module.Flat A B] [Finite ι] in
/-- The components of the base change of a map into a finite product. -/
theorem piRightHom_lTensor_pi (r : ∀ i, M →ₗ[A] Mi i) (i : ι) (x : B ⊗[A] M) :
    TensorProduct.piRightHom A B B Mi (LinearMap.lTensor B (LinearMap.pi r) x) i =
      LinearMap.lTensor B (r i) x := by
  induction x with
  | add u v hu hv => simp [hu, hv]
  | tmul b m => simp

/-- **Injectivity from a finite cover.** -/
theorem injective_liftBaseChange_of_pi
    (cmp : M →ₗ[A] N) (cmpi : ∀ i, Mi i →ₗ[A] Ni i)
    (r : ∀ i, M →ₗ[A] Mi i) (s : ∀ i, N →ₗ[B] Ni i)
    (hsq : ∀ i m, cmpi i (r i m) = s i (cmp m))
    (hsep : ∀ m : M, (∀ i, r i m = 0) → m = 0)
    (hi : ∀ i, Function.Injective ((cmpi i).liftBaseChange B)) :
    Function.Injective (cmp.liftBaseChange B) := by
  classical
  cases nonempty_fintype ι
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  have hρ : Function.Injective (LinearMap.pi r) :=
    (injective_iff_map_eq_zero _).mpr fun m hm =>
      hsep m fun i => congrFun hm i
  have hL : Function.Injective (LinearMap.lTensor B (LinearMap.pi r)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hρ
  have h0 : ∀ i, LinearMap.lTensor B (r i) x = 0 := by
    intro i
    refine hi i ?_
    rw [liftBaseChange_lTensor cmp (cmpi i) (r i) (s i) (hsq i) x, hx, map_zero,
      map_zero]
  refine (injective_iff_map_eq_zero _).mp hL x ?_
  refine (TensorProduct.piRight A B B Mi).injective ?_
  rw [map_zero]
  refine funext fun i => ?_
  rw [TensorProduct.piRight_apply, piRightHom_lTensor_pi r i x, h0 i]
  rfl

end Pi

section Pair

variable [Module.Flat A B]
  {M M₁ M₂ M₀ : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₀] [Module A M₀]
  {N N₁ N₂ N₀ : Type*}
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  [AddCommGroup N₁] [Module A N₁] [Module B N₁] [IsScalarTower A B N₁]
  [AddCommGroup N₂] [Module A N₂] [Module B N₂] [IsScalarTower A B N₂]
  [AddCommGroup N₀] [Module A N₀] [Module B N₀] [IsScalarTower A B N₀]

omit [Module.Flat A B] in
private theorem prodRight_lTensor_prod (r₁ : M →ₗ[A] M₁) (r₂ : M →ₗ[A] M₂) (x : B ⊗[A] M) :
    TensorProduct.prodRight A B B M₁ M₂ (LinearMap.lTensor B (LinearMap.prod r₁ r₂) x) =
      (LinearMap.lTensor B r₁ x, LinearMap.lTensor B r₂ x) := by
  induction x with
  | add u v hu hv => simp [hu, hv]
  | tmul b m => simp

omit [Module.Flat A B] in
private theorem lTensor_diff (s₁ : M₁ →ₗ[A] M₀) (s₂ : M₂ →ₗ[A] M₀)
    (w : B ⊗[A] (M₁ × M₂)) :
    LinearMap.lTensor B (s₁ ∘ₗ LinearMap.fst A M₁ M₂ - s₂ ∘ₗ LinearMap.snd A M₁ M₂) w =
      LinearMap.lTensor B s₁ (TensorProduct.prodRight A B B M₁ M₂ w).1 -
        LinearMap.lTensor B s₂ (TensorProduct.prodRight A B B M₁ M₂ w).2 := by
  induction w with
  | add u v hu hv =>
      simp only [map_add, hu, hv, Prod.fst_add, Prod.snd_add]
      abel
  | tmul b m => simp

/-- **Mayer-Vietoris.** -/
theorem bijective_liftBaseChange_of_pair
    (cmp : M →ₗ[A] N) (cmp₁ : M₁ →ₗ[A] N₁) (cmp₂ : M₂ →ₗ[A] N₂)
    (cmp₀ : M₀ →ₗ[A] N₀)
    (r₁ : M →ₗ[A] M₁) (r₂ : M →ₗ[A] M₂) (s₁ : M₁ →ₗ[A] M₀) (s₂ : M₂ →ₗ[A] M₀)
    (ρ₁ : N →ₗ[B] N₁) (ρ₂ : N →ₗ[B] N₂) (σ₁ : N₁ →ₗ[B] N₀) (σ₂ : N₂ →ₗ[B] N₀)
    (hsq₁ : ∀ m, cmp₁ (r₁ m) = ρ₁ (cmp m))
    (hsq₂ : ∀ m, cmp₂ (r₂ m) = ρ₂ (cmp m))
    (hsq₁' : ∀ m, cmp₀ (s₁ m) = σ₁ (cmp₁ m))
    (hsq₂' : ∀ m, cmp₀ (s₂ m) = σ₂ (cmp₂ m))
    (hMcomm : ∀ m, s₁ (r₁ m) = s₂ (r₂ m))
    (hMsep : ∀ m : M, r₁ m = 0 → r₂ m = 0 → m = 0)
    (hMglue : ∀ (x₁ : M₁) (x₂ : M₂), s₁ x₁ = s₂ x₂ → ∃ m, r₁ m = x₁ ∧ r₂ m = x₂)
    (hNcomm : ∀ n, σ₁ (ρ₁ n) = σ₂ (ρ₂ n))
    (hNsep : ∀ n : N, ρ₁ n = 0 → ρ₂ n = 0 → n = 0)
    (h₁ : Function.Bijective (cmp₁.liftBaseChange B))
    (h₂ : Function.Bijective (cmp₂.liftBaseChange B))
    (h₀ : Function.Injective (cmp₀.liftBaseChange B)) :
    Function.Bijective (cmp.liftBaseChange B) := by
  have hRinj : Function.Injective (LinearMap.prod r₁ r₂) :=
    (injective_iff_map_eq_zero _).mpr fun m hm =>
      hMsep m (congrArg Prod.fst hm) (congrArg Prod.snd hm)
  have htsep : ∀ x : B ⊗[A] M, LinearMap.lTensor B r₁ x = 0 →
      LinearMap.lTensor B r₂ x = 0 → x = 0 := by
    intro x h1 h2
    refine (injective_iff_map_eq_zero _).mp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := B) _ hRinj) x ?_
    refine (TensorProduct.prodRight A B B M₁ M₂).injective ?_
    rw [prodRight_lTensor_prod r₁ r₂ x, h1, h2, map_zero]
    rfl
  have hd : ∀ (x₁ : M₁) (x₂ : M₂),
      (s₁ ∘ₗ LinearMap.fst A M₁ M₂ - s₂ ∘ₗ LinearMap.snd A M₁ M₂) (x₁, x₂) = 0 ↔
        s₁ x₁ = s₂ x₂ := fun x₁ x₂ => by simp [sub_eq_zero]
  have hex : Function.Exact (LinearMap.prod r₁ r₂)
      (s₁ ∘ₗ LinearMap.fst A M₁ M₂ - s₂ ∘ₗ LinearMap.snd A M₁ M₂) := by
    intro z
    constructor
    · intro hz
      obtain ⟨m, hm1, hm2⟩ := hMglue z.1 z.2 ((hd z.1 z.2).mp hz)
      exact ⟨m, Prod.ext hm1 hm2⟩
    · rintro ⟨m, rfl⟩
      exact (hd (r₁ m) (r₂ m)).mpr (hMcomm m)
  have hexT := Module.Flat.lTensor_exact (M := B) hex
  have htglue : ∀ (y₁ : B ⊗[A] M₁) (y₂ : B ⊗[A] M₂),
      LinearMap.lTensor B s₁ y₁ = LinearMap.lTensor B s₂ y₂ →
      ∃ x : B ⊗[A] M, LinearMap.lTensor B r₁ x = y₁ ∧ LinearMap.lTensor B r₂ x = y₂ := by
    intro y₁ y₂ hy
    obtain ⟨z, hpz⟩ := (TensorProduct.prodRight A B B M₁ M₂).surjective (y₁, y₂)
    have hz : LinearMap.lTensor B
        (s₁ ∘ₗ LinearMap.fst A M₁ M₂ - s₂ ∘ₗ LinearMap.snd A M₁ M₂) z = 0 := by
      rw [lTensor_diff s₁ s₂ z, hpz, hy, sub_self]
    obtain ⟨x, hx⟩ := (hexT z).mp hz
    have hcomp := prodRight_lTensor_prod r₁ r₂ x
    rw [hx, hpz] at hcomp
    exact ⟨x, (congrArg Prod.fst hcomp).symm, (congrArg Prod.snd hcomp).symm⟩
  have e₁ := liftBaseChange_lTensor cmp cmp₁ r₁ ρ₁ hsq₁
  have e₂ := liftBaseChange_lTensor cmp cmp₂ r₂ ρ₂ hsq₂
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    refine htsep x (h₁.injective ?_) (h₂.injective ?_)
    · rw [e₁, hx, map_zero, map_zero]
    · rw [e₂, hx, map_zero, map_zero]
  · intro n
    obtain ⟨y₁, hy₁⟩ := h₁.surjective (ρ₁ n)
    obtain ⟨y₂, hy₂⟩ := h₂.surjective (ρ₂ n)
    have key : LinearMap.lTensor B s₁ y₁ = LinearMap.lTensor B s₂ y₂ := by
      refine h₀ ?_
      rw [liftBaseChange_lTensor cmp₁ cmp₀ s₁ σ₁ hsq₁' y₁,
        liftBaseChange_lTensor cmp₂ cmp₀ s₂ σ₂ hsq₂' y₂, hy₁, hy₂, hNcomm n]
    obtain ⟨x, hx₁, hx₂⟩ := htglue y₁ y₂ key
    refine ⟨x, sub_eq_zero.mp (hNsep (cmp.liftBaseChange B x - n) ?_ ?_)⟩
    · rw [map_sub, ← e₁, hx₁, hy₁, sub_self]
    · rw [map_sub, ← e₂, hx₂, hy₂, sub_self]
end Pair



/-! ### The local-to-global induction -/

section Lattice

/-- The data of a comparison, over a flat ring map `A → B`, between a sheaf of `A`-modules on a
space `X` and a sheaf of `B`-modules indexed by the opens of `X`. -/
structure Comparison (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (L : Type u) [Order.Frame L]
    (M : L → Type u) [∀ U, AddCommGroup (M U)] [∀ U, Module A (M U)]
    (N : L → Type u) [∀ U, AddCommGroup (N U)] [∀ U, Module A (N U)]
    [∀ U, Module B (N U)] [∀ U, IsScalarTower A B (N U)] where
  /-- Restriction in the source. -/
  resM : ∀ {U V : L}, V ≤ U → M U →ₗ[A] M V
  /-- Restriction in the target. -/
  resN : ∀ {U V : L}, V ≤ U → N U →ₗ[B] N V
  /-- The comparison map. -/
  cmp : ∀ U, M U →ₗ[A] N U
  resM_resM : ∀ {U V W : L} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : M U),
    resM h₂ (resM h₁ x) = resM (h₂.trans h₁) x
  resN_resN : ∀ {U V W : L} (h₁ : V ≤ U) (h₂ : W ≤ V) (y : N U),
    resN h₂ (resN h₁ y) = resN (h₂.trans h₁) y
  cmp_res : ∀ {U V : L} (h : V ≤ U) (x : M U),
    cmp V (resM h x) = resN h (cmp U x)
  sepM : ∀ (U : L) (cov : Set (L)) (hcov : ∀ V ∈ cov, V ≤ U) (_hU : U ≤ sSup cov)
    (x : M U), (∀ V (hV : V ∈ cov), resM (hcov V hV) x = 0) → x = 0
  sepN : ∀ (U : L) (cov : Set (L)) (hcov : ∀ V ∈ cov, V ≤ U) (_hU : U ≤ sSup cov)
    (y : N U), (∀ V (hV : V ∈ cov), resN (hcov V hV) y = 0) → y = 0
  glueM : ∀ (U₁ U₂ : L) (x₁ : M U₁) (x₂ : M U₂),
    resM (inf_le_left : U₁ ⊓ U₂ ≤ U₁) x₁ = resM (inf_le_right : U₁ ⊓ U₂ ≤ U₂) x₂ →
    ∃ y : M (U₁ ⊔ U₂), resM (le_sup_left : U₁ ≤ U₁ ⊔ U₂) y = x₁ ∧
      resM (le_sup_right : U₂ ≤ U₁ ⊔ U₂) y = x₂

namespace Comparison

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
  {L : Type u} [Order.Frame L]
  {M : L → Type u} [∀ U, AddCommGroup (M U)] [∀ U, Module A (M U)]
  {N : L → Type u} [∀ U, AddCommGroup (N U)] [∀ U, Module A (N U)]
  [∀ U, Module B (N U)] [∀ U, IsScalarTower A B (N U)]

/-- The base change of the comparison map: `B ⊗[A] M U ⟶ N U`. -/
def baseChangeMap (c : Comparison A B L M N) (U : L) : B ⊗[A] M U →ₗ[B] N U :=
  (c.cmp U).liftBaseChange B

omit [Module.Flat A B] in
/-- Every section of `M` over `⊥` is zero. -/
theorem subsingleton_M_bot (c : Comparison A B L M N) (x : M ⊥) : x = 0 :=
  c.sepM ⊥ ∅ (by simp) (by simp) x (by simp)

omit [Module.Flat A B] in
/-- Every section of `N` over `⊥` is zero. -/
theorem subsingleton_N_bot (c : Comparison A B L M N) (y : N ⊥) : y = 0 :=
  c.sepN ⊥ ∅ (by simp) (by simp) y (by simp)

omit [Module.Flat A B] in
/-- The base change map `B ⊗[A] M ⊥ ⟶ N ⊥` is bijective. -/
theorem bijective_baseChangeMap_bot (c : Comparison A B L M N) :
    Function.Bijective (c.baseChangeMap ⊥) := by
  have h : ∀ z : B ⊗[A] M (⊥ : L), z = 0 := by
    intro z
    induction z with
    | add u v hu hv => rw [hu, hv, add_zero]
    | tmul b m => rw [c.subsingleton_M_bot m, TensorProduct.tmul_zero]
  exact ⟨fun x y _ => by rw [h x, h y], fun n => ⟨0, by rw [map_zero, c.subsingleton_N_bot n]⟩⟩

/-- **Injectivity is local on a finite cover.** -/
theorem injective_baseChangeMap_of_iSup (c : Comparison A B L M N) {ι : Type*} [Finite ι]
    (U : L) (V : ι → L)
    (hV : ∀ i, V i ≤ U) (hU : U ≤ ⨆ i, V i)
    (h : ∀ i, Function.Injective (c.baseChangeMap (V i))) :
    Function.Injective (c.baseChangeMap U) :=
  injective_liftBaseChange_of_pi (c.cmp U) (fun i => c.cmp (V i))
    (fun i => c.resM (hV i)) (fun i => c.resN (hV i)) (fun i m => c.cmp_res (hV i) m)
    (fun x hx => c.sepM U (Set.range V) (by rintro W ⟨i, rfl⟩; exact hV i)
      (by rwa [sSup_range]) x (by rintro W ⟨i, rfl⟩; exact hx i)) h

/-- **Bijectivity is local on a finite cover, given injectivity on the pairwise
intersections.** -/
theorem bijective_baseChangeMap_of_iSup (c : Comparison A B L M N) {ι : Type*} [Finite ι]
    (U : L) (V : ι → L)
    (hV : ∀ i, V i ≤ U) (hU : U ≤ ⨆ i, V i)
    (hb : ∀ i, Function.Bijective (c.baseChangeMap (V i)))
    (hinj : ∀ i j, Function.Injective (c.baseChangeMap (V i ⊓ V j))) :
    Function.Bijective (c.baseChangeMap U) := by
  classical
  cases nonempty_fintype ι
  obtain rfl : U = ⨆ i, V i := le_antisymm hU (iSup_le hV)
  have step : ∀ s : Finset ι, Function.Bijective (c.baseChangeMap (⨆ i ∈ s, V i)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        rw [show (⨆ i ∈ (∅ : Finset ι), V i) = ⊥ by simp]
        exact c.bijective_baseChangeMap_bot
    | @insert a s ha ih =>
        rw [Finset.iSup_insert]
        set W := ⨆ i ∈ s, V i with hW
        have hdist : V a ⊓ W = ⨆ i : {x // x ∈ s}, (V a ⊓ V i) := by
          rw [hW, iSup_subtype', inf_iSup_eq]
        have h0 : Function.Injective (c.baseChangeMap (V a ⊓ W)) := by
          refine c.injective_baseChangeMap_of_iSup (V a ⊓ W) (fun i : {x // x ∈ s} => V a ⊓ V i)
            (fun i => by rw [hdist]; exact le_iSup (fun j : {x // x ∈ s} => V a ⊓ V j) i)
            (le_of_eq hdist) (fun i => (hinj a i).comp (fun _ _ h => h))
        refine bijective_liftBaseChange_of_pair (c.cmp (V a ⊔ W)) (c.cmp (V a))
          (c.cmp W) (c.cmp (V a ⊓ W))
          (c.resM le_sup_left) (c.resM le_sup_right) (c.resM inf_le_left) (c.resM inf_le_right)
          (c.resN le_sup_left) (c.resN le_sup_right) (c.resN inf_le_left) (c.resN inf_le_right)
          (fun m => c.cmp_res _ m) (fun m => c.cmp_res _ m)
          (fun m => c.cmp_res _ m) (fun m => c.cmp_res _ m) ?_ ?_ ?_ ?_ ?_ (hb a) ih h0
        · intro m; rw [c.resM_resM, c.resM_resM]
        · exact fun m h1 h2 => c.sepM _ {V a, W} (by simp) (by simp) m
            (by rintro Z (rfl | rfl); exacts [h1, h2])
        · intro x₁ x₂ hx; exact c.glueM (V a) W x₁ x₂ hx
        · intro n; rw [c.resN_resN, c.resN_resN]
        · exact fun n h1 h2 => c.sepN _ {V a, W} (by simp) (by simp) n
            (by rintro Z (rfl | rfl); exacts [h1, h2])
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), V i) = ⨆ i, V i := by simp
  have := step Finset.univ
  rwa [hu] at this

end Comparison

end Lattice

end Stacks.FlatSectionsDescent

end
