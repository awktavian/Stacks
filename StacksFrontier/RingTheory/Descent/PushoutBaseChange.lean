module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change across a pushout square of rings, and descent along a finite flat cover

Let `R → A` and `R → B` be ring maps and let `D` be their tensor product, presented as a ring
`D` receiving `A` and `B` with `A ⊗[R] B ≃ D`. For an `A`-module `M` the two ways of changing
the base of `M` to `D` — tensoring over `R` with `B`, and tensoring over `A` with `D` — agree,
and a comparison map out of `B ⊗[R] M` is therefore bijective as soon as the base change
comparison over `A → D` is.

The second half of the file is a descent statement for a finite cover: given an exact sequence
describing the sections over the base as the equalizer of the sections over the members of a
cover, and the same description after base change along a flat module, a comparison map from the
base change of the sections over the base is bijective.

## Main definitions

* `Module.Descent.pushoutLinearEquiv`: an `R`-linear identification `A ⊗[R] B ≃ D` multiplying
  the two images together is `A`-linear.
* `Module.Descent.pushoutBaseChangeEquiv`: the resulting identification
  `B ⊗[R] M ≃ D ⊗[A] M` for an `A`-module `M`.

## Main results

* `Module.Descent.bijective_pushout_comparison`: a comparison map out of `B ⊗[R] M` is bijective
  when the base change comparison over `A → D` is.
* `Module.Descent.bijective_of_flat_descent`: flat descent of a base-change comparison across a
  finite cover.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open TensorProduct

namespace Module.Descent

/-! ### Base change across a pushout square of rings -/

section Pushout

variable {R A B D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R D] [Algebra A D] [Algebra B D]

/-- An `R`-linear identification `A ⊗[R] B ≃ₗ[R] D` which sends `a ⊗ₜ b` to the product of the
images of `a` and `b` in `D` is automatically `A`-linear. -/
def pushoutLinearEquiv (e : A ⊗[R] B ≃ₗ[R] D)
    (he : ∀ (a : A) (b : B), e (a ⊗ₜ b) = algebraMap A D a * algebraMap B D b) :
    A ⊗[R] B ≃ₗ[A] D where
  toFun := e
  map_add' := e.map_add
  map_smul' := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b => simp [he, Algebra.smul_def, mul_assoc]
    | add z w hz hw => simp [hz, hw, smul_add]
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- `Module.Descent.pushoutLinearEquiv` has the same underlying function as the `R`-linear
identification it upgrades. -/
@[simp]
lemma pushoutLinearEquiv_apply (e : A ⊗[R] B ≃ₗ[R] D)
    (he : ∀ (a : A) (b : B), e (a ⊗ₜ b) = algebraMap A D a * algebraMap B D b)
    (z : A ⊗[R] B) : pushoutLinearEquiv e he z = e z := rfl

variable [IsScalarTower R A D]

/-- Across a pushout square of rings, the base change `B ⊗[R] M` of an `A`-module `M` along
`R → B` is `R`-linearly identified with its base change `D ⊗[A] M` along `A → D`. -/
def pushoutBaseChangeEquiv (e : A ⊗[R] B ≃ₗ[R] D)
    (he : ∀ (a : A) (b : B), e (a ⊗ₜ b) = algebraMap A D a * algebraMap B D b)
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    B ⊗[R] M ≃ₗ[R] D ⊗[A] M :=
  (TensorProduct.comm R B M).trans
    (((TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M B).symm.trans
        ((TensorProduct.congr (LinearEquiv.refl A M) (pushoutLinearEquiv e he)).trans
          (TensorProduct.comm A M D))).restrictScalars R)

/-- `Module.Descent.pushoutBaseChangeEquiv` on a pure tensor. -/
lemma pushoutBaseChangeEquiv_tmul (e : A ⊗[R] B ≃ₗ[R] D)
    (he : ∀ (a : A) (b : B), e (a ⊗ₜ b) = algebraMap A D a * algebraMap B D b)
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    (b : B) (x : M) :
    pushoutBaseChangeEquiv e he (b ⊗ₜ x) = algebraMap B D b ⊗ₜ x := by
  simp [pushoutBaseChangeEquiv, he]

/-- A comparison map `ξ` out of `B ⊗[R] M` across a pushout square of rings, sending `b ⊗ₜ x` to
the image of `b` acting on the base change of `x`, is bijective whenever the base change
comparison `κ` over `A → D` is. -/
theorem bijective_pushout_comparison (e : A ⊗[R] B ≃ₗ[R] D)
    (he : ∀ (a : A) (b : B), e (a ⊗ₜ b) = algebraMap A D a * algebraMap B D b)
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    {N : Type*} [AddCommGroup N] [Module D N] [Module R N] [IsScalarTower R D N]
    (κ : D ⊗[A] M →ₗ[D] N) (hκ : Function.Bijective κ)
    (ξ : B ⊗[R] M →ₗ[R] N)
    (hξ : ∀ (b : B) (x : M), ξ (b ⊗ₜ x) = algebraMap B D b • κ (1 ⊗ₜ x)) :
    Function.Bijective ξ := by
  have key : ∀ z : B ⊗[R] M, ξ z = κ (pushoutBaseChangeEquiv e he z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
        have hsm : (algebraMap B D b) • ((1 : D) ⊗ₜ[A] x) = (algebraMap B D b) ⊗ₜ[A] x := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hξ b x, pushoutBaseChangeEquiv_tmul, ← hsm, κ.map_smul]
    | add z w hz hw => simp [hz, hw]
  have hfun : (ξ : B ⊗[R] M → N) = (κ : D ⊗[A] M → N) ∘ (pushoutBaseChangeEquiv e he) :=
    funext key
  exact hfun ▸ hκ.comp (pushoutBaseChangeEquiv e he).bijective

end Pushout

/-! ### Descent of a base-change comparison across a finite cover -/

/-- Flat descent of a base-change comparison across a finite cover.

The sections over the base are described as the equalizer of the sections over the members of a
finite cover, through an injective `ε` whose image is the kernel of the difference `φ` of the two
restrictions to the double overlaps; the same data after base change along a flat module `Bm` is
described by an injective `εU` equalizing two maps `ρ` and `ρ'`. Given comparison isomorphisms
`ψ`, `ψ'` on the members and on the double overlaps compatible with the restrictions, the
comparison `θ` at the base is bijective. -/
theorem bijective_of_flat_descent
    {R : Type*} [CommRing R]
    {Bm : Type*} [AddCommGroup Bm] [Module R Bm] [Module.Flat R Bm]
    {N : Type*} [AddCommGroup N] [Module R N]
    {MU : Type*} [AddCommGroup MU] [Module R MU]
    {I : Type*} [Finite I]
    {Mi : I → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module R (Mi i)]
    {Mp : I × I → Type*} [∀ p, AddCommGroup (Mp p)] [∀ p, Module R (Mp p)]
    {MUi : I → Type*} [∀ i, AddCommGroup (MUi i)] [∀ i, Module R (MUi i)]
    {MUp : I × I → Type*} [∀ p, AddCommGroup (MUp p)] [∀ p, Module R (MUp p)]
    (ε : N →ₗ[R] (∀ i, Mi i)) (hε : Function.Injective ε)
    (δ : ∀ p : I × I, Mi p.1 →ₗ[R] Mp p) (δ' : ∀ p : I × I, Mi p.2 →ₗ[R] Mp p)
    (φ : (∀ i, Mi i) →ₗ[R] (∀ p : I × I, Mp p))
    (hφ : ∀ (m : ∀ i, Mi i) (p : I × I), φ m p = δ p (m p.1) - δ' p (m p.2))
    (hex : Function.Exact ε φ)
    (εU : MU →ₗ[R] (∀ i, MUi i)) (hεU : Function.Injective εU)
    (ρ : ∀ p : I × I, MUi p.1 →ₗ[R] MUp p) (ρ' : ∀ p : I × I, MUi p.2 →ₗ[R] MUp p)
    (hρ : ∀ (t : MU) (p : I × I), ρ p (εU t p.1) = ρ' p (εU t p.2))
    (ψ : ∀ i, (Bm ⊗[R] Mi i) ≃ₗ[R] MUi i)
    (ψ' : ∀ p : I × I, (Bm ⊗[R] Mp p) ≃ₗ[R] MUp p)
    (hψ : ∀ (p : I × I) (b : Bm) (x : Mi p.1), ψ' p (b ⊗ₜ δ p x) = ρ p (ψ p.1 (b ⊗ₜ x)))
    (hψ' : ∀ (p : I × I) (b : Bm) (y : Mi p.2), ψ' p (b ⊗ₜ δ' p y) = ρ' p (ψ p.2 (b ⊗ₜ y)))
    (θ : (Bm ⊗[R] N) →ₗ[R] MU)
    (hθ : ∀ (b : Bm) (n : N) (i : I), εU (θ (b ⊗ₜ n)) i = ψ i (b ⊗ₜ ε n i)) :
    Function.Bijective θ := by
  classical
  let _ := Fintype.ofFinite I
  set e₁ : Bm ⊗[R] (∀ i, Mi i) ≃ₗ[R] (∀ i, Bm ⊗[R] Mi i) :=
    TensorProduct.piRight R R Bm Mi with he₁
  set e₂ : Bm ⊗[R] (∀ p : I × I, Mp p) ≃ₗ[R] (∀ p : I × I, Bm ⊗[R] Mp p) :=
    TensorProduct.piRight R R Bm Mp with he₂
  set E : (Bm ⊗[R] N) →ₗ[R] (∀ i, Bm ⊗[R] Mi i) :=
    e₁.toLinearMap ∘ₗ ε.lTensor Bm with hEdef
  set Φ : (∀ i, Bm ⊗[R] Mi i) →ₗ[R] (∀ p : I × I, Bm ⊗[R] Mp p) :=
    LinearMap.pi (fun p : I × I =>
      (δ p).lTensor Bm ∘ₗ LinearMap.proj p.1 - (δ' p).lTensor Bm ∘ₗ LinearMap.proj p.2)
    with hΦdef
  have hΦ : ∀ (z : ∀ i, Bm ⊗[R] Mi i) (p : I × I),
      Φ z p = (δ p).lTensor Bm (z p.1) - (δ' p).lTensor Bm (z p.2) := by
    intro z p; simp [hΦdef]
  have hE : ∀ (b : Bm) (n : N) (i : I), E (b ⊗ₜ n) i = b ⊗ₜ ε n i := by
    intro b n i; simp [hEdef, he₁]
  have hsq : ∀ w : Bm ⊗[R] (∀ i, Mi i), Φ (e₁ w) = e₂ (φ.lTensor Bm w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
        funext p
        simp only [he₁, he₂, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
          LinearMap.lTensor_tmul, hΦ, hφ, TensorProduct.tmul_sub]
    | add x y hx hy => simp [hx, hy]
  have hfinj : Function.Injective (ε.lTensor Bm) :=
    Module.Flat.lTensor_preserves_injective_linearMap ε hε
  have hfex : Function.Exact (ε.lTensor Bm) (φ.lTensor Bm) := Module.Flat.lTensor_exact Bm hex
  have hEinj : Function.Injective E := fun x y hxy =>
    hfinj (e₁.injective (by simpa [hEdef] using hxy))
  have hEex : Function.Exact E Φ := by
    intro y
    constructor
    · intro hy
      have h1 : e₂ (φ.lTensor Bm (e₁.symm y)) = 0 := by
        rw [← hsq, e₁.apply_symm_apply, hy]
      obtain ⟨x, hx⟩ := (hfex _).mp (e₂.map_eq_zero_iff.1 h1)
      exact ⟨x, by simp [hEdef, hx, e₁.apply_symm_apply]⟩
    · rintro ⟨x, rfl⟩
      simpa [hEdef, hfex.apply_apply_eq_zero] using hsq (ε.lTensor Bm x)
  have hθ' : ∀ (z : Bm ⊗[R] N) (i : I), εU (θ z) i = ψ i (E z i) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => intro i; simp
    | tmul b n => intro i; rw [hE b n i]; exact hθ b n i
    | add x y hx hy => intro i; simp [hx i, hy i]
  have hψe : ∀ (p : I × I) (w : Bm ⊗[R] Mi p.1),
      ψ' p ((δ p).lTensor Bm w) = ρ p (ψ p.1 w) := by
    intro p w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simpa using hψ p b x
    | add x y hx hy => simp [hx, hy]
  have hψe' : ∀ (p : I × I) (w : Bm ⊗[R] Mi p.2),
      ψ' p ((δ' p).lTensor Bm w) = ρ' p (ψ p.2 w) := by
    intro p w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b y => simpa using hψ' p b y
    | add x y hx hy => simp [hx, hy]
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have : E z = 0 := by
      funext i
      refine (ψ i).injective ?_
      rw [← hθ' z i, hz]
      simp
    exact hEinj (this.trans (map_zero E).symm)
  · intro t
    set z : ∀ i, Bm ⊗[R] Mi i := fun i => (ψ i).symm (εU t i) with hzdef
    have hz0 : Φ z = 0 := by
      funext p
      refine (ψ' p).injective ?_
      rw [hΦ z p, map_sub, hψe p (z p.1), hψe' p (z p.2)]
      simp only [hzdef, LinearEquiv.apply_symm_apply]
      rw [hρ t p, sub_self]
      simp
    obtain ⟨z₀, hz₀⟩ := (hEex z).mp hz0
    refine ⟨z₀, hεU ?_⟩
    funext i
    rw [hθ' z₀ i, hz₀]
    simp [hzdef]

end Module.Descent

end
