module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import StacksCore.Tactic.StacksAttribute

/-! # Finiteness conditions are stable under base change

Stacks tag 05G5. For a ring map `R → S`, an `S`-module `M`, and a ring map `R → R'`, write
`S' = S ⊗[R] R'` and `M' = M ⊗[R] R'`. The tag asserts four stability statements: `M'` is a
finite (resp. finitely presented) `S'`-module when `M` is one over `S`, and `R' → S'` is of
finite type (resp. finite presentation) when `R → S` is.

Clauses (3) and (4) are Mathlib instances and are tagged directly at the bottom of the file.

Clauses (1) and (2) are stated on the tag's literal `M ⊗[R] R'`, and reaching that is the work
here, because **Mathlib provides no `S'`-action on `M ⊗[R] R'`**. It supplies exactly one of the
two commuting actions in either tensor order: `Module S (M ⊗[R] R')` is an instance but
`Module R' (M ⊗[R] R')` is not, and flipping the factors flips which one is missing. So the
right-factor action `rightModule` is built by hand, the two scalar towers and the commuting
class it needs are checked, and `TensorProduct.Algebra.module` — the `def` Mathlib deliberately
keeps off the instance list for exactly this situation — assembles them.

All of that is installed with `attribute [local instance]`, following Mathlib's own use of
`TensorProduct.Algebra.module`. The consequence is deliberate and worth stating plainly: the
*statements* of `Module.Finite.tensorBaseChange` and `Module.FinitePresentation.tensorBaseChange`
mention an `S'`-action that is in scope only in this file, so they record that 05G5 is proved
rather than serving as reusable API. Downstream code wanting these facts should use
`Module.Finite.base_change` on `S' ⊗[S] M` and cross `Module.tensorBaseChangeEquiv`, which is
why that equiv is public, `S`-linear, needs none of the local instances, and is pinned on
generators.

Global instances are *not* a safe alternative here: at `M := R'` the ring `R' ⊗[R] R'` would
acquire two competing `R'`-actions, one from each tensor factor.
-/

@[expose] public section

open scoped TensorProduct

variable {R S M R' : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [CommRing R'] [Algebra R R']

/-- The base change of an `S`-module `M` along `S → S' = S ⊗[R] R'` is the tag's
`M' = M ⊗[R] R'`.

`S`-linear, and independent of the local instances below, so this is the form downstream code
should use to move between Mathlib's `S' ⊗[S] M` and the tag's `M ⊗[R] R'`. -/
noncomputable def Module.tensorBaseChangeEquiv :
    ((S ⊗[R] R') ⊗[S] M) ≃ₗ[S] (M ⊗[R] R') :=
  (TensorProduct.comm S _ M).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M R')

@[simp]
theorem Module.tensorBaseChangeEquiv_tmul (s : S) (r : R') (m : M) :
    Module.tensorBaseChangeEquiv ((s ⊗ₜ[R] r) ⊗ₜ[S] m) = (s • m) ⊗ₜ[R] r := by
  simp [Module.tensorBaseChangeEquiv]

/-! ### The `S'`-action on the tag's literal `M ⊗[R] R'` -/

/-- The right-factor action of `R'` on `M ⊗[R] R'`, by multiplication on the second factor.
Mathlib has the left-factor analogue but not this one; see the module docstring. -/
@[instance_reducible]
noncomputable def rightModule : Module R' (M ⊗[R] R') where
  smul r' x := LinearMap.lTensor M (LinearMap.mulLeft R r') x
  one_smul x := by
    change LinearMap.lTensor M (LinearMap.mulLeft R (1 : R')) x = x
    simp
  mul_smul a b x := by
    change LinearMap.lTensor M (LinearMap.mulLeft R (a * b)) x
      = LinearMap.lTensor M (LinearMap.mulLeft R a)
          (LinearMap.lTensor M (LinearMap.mulLeft R b) x)
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    congr 2
    ext y
    simp
  smul_zero a := by
    change LinearMap.lTensor M (LinearMap.mulLeft R a) 0 = 0
    simp
  smul_add a x y := by
    change LinearMap.lTensor M (LinearMap.mulLeft R a) (x + y)
      = LinearMap.lTensor M (LinearMap.mulLeft R a) x
        + LinearMap.lTensor M (LinearMap.mulLeft R a) y
    simp
  add_smul a b x := by
    change LinearMap.lTensor M (LinearMap.mulLeft R (a + b)) x
      = LinearMap.lTensor M (LinearMap.mulLeft R a) x
        + LinearMap.lTensor M (LinearMap.mulLeft R b) x
    induction x with
    | tmul m y => simp [LinearMap.mulLeft, add_mul, TensorProduct.tmul_add]
    | add u v hu hv => simp only [map_add, hu, hv]; abel
  zero_smul x := by
    change LinearMap.lTensor M (LinearMap.mulLeft R (0 : R')) x = 0
    simp

attribute [local instance] rightModule

@[simp]
theorem rightModule_smul_tmul (r' : R') (m : M) (x : R') :
    (r' • (m ⊗ₜ[R] x) : M ⊗[R] R') = m ⊗ₜ[R] (r' * x) := rfl

local instance : IsScalarTower R R' (M ⊗[R] R') where
  smul_assoc a b x := by
    induction x with
    | tmul m y => simp [TensorProduct.smul_tmul']
    | add u v hu hv => simp only [smul_add, hu, hv]

local instance : SMulCommClass S R' (M ⊗[R] R') where
  smul_comm s r' x := by
    induction x with
    | tmul m y => simp [TensorProduct.smul_tmul']
    | add u v hu hv => simp only [smul_add, hu, hv]

/-- The `S'`-action on the tag's literal `M ⊗[R] R'`, assembled from the commuting `S`- and
`R'`-actions.

Note this is a *named* instance for this one type rather than
`attribute [local instance] TensorProduct.Algebra.module`. Switching that on file-wide is a trap:
`(S ⊗[R] R') ⊗[S] M` also carries commuting `S`- and `R'`-actions, so it would acquire a second
`Module (S ⊗[R] R')` structure competing with the canonical `TensorProduct.leftModule`, and
`Module.Finite.base_change` would no longer typecheck against it. -/
@[instance_reducible]
noncomputable def literalModule : Module (S ⊗[R] R') (M ⊗[R] R') :=
  TensorProduct.Algebra.module

attribute [local instance] literalModule

@[simp]
theorem literalModule_smul_tmul (s : S) (r : R') (x : M ⊗[R] R') :
    ((s ⊗ₜ[R] r : S ⊗[R] R') • x) = s • r • x := rfl

theorem Module.tensorBaseChangeEquiv_smul (c : S ⊗[R] R') (x : (S ⊗[R] R') ⊗[S] M) :
    Module.tensorBaseChangeEquiv (c • x) = c • Module.tensorBaseChangeEquiv x := by
  induction c with
  | tmul s r =>
    induction x with
    | tmul c' m =>
      induction c' with
      | tmul s' r' =>
        simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', mul_smul]
      | add u v hu hv => simp [TensorProduct.add_tmul, hu, hv]
    | add u v hu hv => simp [hu, hv]
  | add u v hu hv => simp [add_smul, hu, hv]

/-- `Module.tensorBaseChangeEquiv` upgraded to `S'`-linearity against the locally installed
`S'`-action. This is what carries finiteness onto the tag's literal object. -/
noncomputable def Module.tensorBaseChangeEquiv' :
    ((S ⊗[R] R') ⊗[S] M) ≃ₗ[S ⊗[R] R'] (M ⊗[R] R') :=
  { Module.tensorBaseChangeEquiv with
    map_smul' := Module.tensorBaseChangeEquiv_smul }

/-- **Stacks 05G5 (1)**: if `M` is a finite `S`-module then `M' = M ⊗[R] R'` is a finite
`S' = S ⊗[R] R'`-module. -/
@[stacks 05G5 "(1)"]
theorem Module.Finite.tensorBaseChange [Module.Finite S M] :
    Module.Finite (S ⊗[R] R') (M ⊗[R] R') :=
  have : Module.Finite (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M) :=
    Module.Finite.base_change S (S ⊗[R] R') M
  Module.Finite.equiv Module.tensorBaseChangeEquiv'

/-- **Stacks 05G5 (2)**: if `M` is a finitely presented `S`-module then `M' = M ⊗[R] R'` is a
finitely presented `S' = S ⊗[R] R'`-module. -/
@[stacks 05G5 "(2)"]
theorem Module.FinitePresentation.tensorBaseChange [Module.FinitePresentation S M] :
    Module.FinitePresentation (S ⊗[R] R') (M ⊗[R] R') :=
  have : Module.FinitePresentation (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M) :=
    instFinitePresentationTensorProduct
  Module.FinitePresentation.of_equiv Module.tensorBaseChangeEquiv'

add_to_stacks 05G5 "(3): if `R → S` is of finite type then so is the base change `R' → S'`."
  Algebra.FiniteType.baseChange
add_to_stacks 05G5 "(4): if `R → S` is of finite presentation then so is the base change
  `R' → S'`." Algebra.FinitePresentation.baseChange
