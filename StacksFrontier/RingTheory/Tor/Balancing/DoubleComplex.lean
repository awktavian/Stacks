module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Double complexes, their edge complexes and the staircase descent

First-quadrant homological double complexes `DoubleCx` of `R`-modules, the horizontal and
vertical cokernels `RObj`, `UObj` with their edge complexes and homologies `RHom`, `UHom`,
the row and column resolution conditions, morphisms of double complexes `DCxHom` and their
induced maps, the total complex `Hthird` with its Koszul sign, and the staircase descent
used to compare the total homology with the edge homologies.

This is part of the split of `StacksFrontier.RingTheory.Tor.Balancing`.
-/

@[expose] public section

open LinearMap Submodule

namespace Stacks.Tor.DoubleComplex

universe u
variable {R : Type u} [CommRing R]

/-! ## Double complexes -/

/-- A first-quadrant homological double complex of `R`-modules with commuting
differentials.  The differentials are reindexed so their targets are always at
nonnegative index: `d i j : A_{i+1,j} → A_{i,j}` and `δ i j : A_{i,j+1} → A_{i,j}`. -/
@[sga "4 XVII 0.4" "special case"]
structure DoubleCx (R : Type u) [CommRing R] where
  /-- The bigraded family of modules `A_{i,j}`. -/
  A : ℕ → ℕ → ModuleCat.{u} R
  /-- The horizontal differential `d : A_{i+1,j} → A_{i,j}` (lowers the first index). -/
  d : ∀ i j, A (i + 1) j →ₗ[R] A i j
  /-- The vertical differential `δ : A_{i,j+1} → A_{i,j}` (lowers the second index). -/
  δ : ∀ i j, A i (j + 1) →ₗ[R] A i j
  /-- `d ∘ d = 0`. -/
  dd : ∀ i j, (d i j).comp (d (i + 1) j) = 0
  /-- `δ ∘ δ = 0`. -/
  δδ : ∀ i j, (δ i j).comp (δ i (j + 1)) = 0
  /-- `d` and `δ` commute. -/
  comm : ∀ i j, (δ i j).comp (d i (j + 1)) = (d i j).comp (δ (i + 1) j)

/-! ## Generic homology of a nonnegatively graded chain complex -/

/-- Homology of a nonnegatively graded chain complex of `R`-modules given by
objects `C i` and differentials `bd i : C (i+1) → C i`.  For `i = 0` it is the
cokernel `C 0 / im (bd 0)`, and for `i+1` it is `ker (bd i) / im (bd (i+1))`.
The result agrees with the usual homology whenever `bd i ∘ bd (i+1) = 0`. -/
def homology (C : ℕ → ModuleCat.{u} R) (bd : ∀ i, C (i + 1) →ₗ[R] C i) :
    ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R ((C 0) ⧸ LinearMap.range (bd 0))
  | (i + 1) => ModuleCat.of R ((LinearMap.ker (bd i)) ⧸
      (LinearMap.range (bd (i + 1))).comap (LinearMap.ker (bd i)).subtype)

/-- A chain map between two such complexes: `f i : C i → C' i` commuting with the
differentials. -/
structure ChainHom (C C' : ℕ → ModuleCat.{u} R)
    (bd : ∀ i, C (i + 1) →ₗ[R] C i) (bd' : ∀ i, C' (i + 1) →ₗ[R] C' i) where
  /-- The components of the chain map. -/
  f : ∀ i, C i →ₗ[R] C' i
  /-- Compatibility with the differentials. -/
  comm : ∀ i, (f i).comp (bd i) = (bd' i).comp (f (i + 1))

/-- The map induced on homology by a chain map. -/
noncomputable def homologyMap {C C' : ℕ → ModuleCat.{u} R}
    {bd : ∀ i, C (i + 1) →ₗ[R] C i} {bd' : ∀ i, C' (i + 1) →ₗ[R] C' i}
    (φ : ChainHom C C' bd bd') : ∀ i, homology C bd i →ₗ[R] homology C' bd' i
  | 0 => by
      refine Submodule.mapQ _ _ (φ.f 0) ?_
      rintro _ ⟨x, rfl⟩
      exact ⟨φ.f 1 x, by
        have := congrArg (fun (g : _ →ₗ[R] _) => g x) (φ.comm 0); simpa using this.symm⟩
  | (i + 1) => by
      refine Submodule.mapQ _ _ ((φ.f (i + 1)).restrict (p := LinearMap.ker (bd i))
        (q := LinearMap.ker (bd' i)) ?_) ?_
      · intro x hx
        simp only [LinearMap.mem_ker] at hx ⊢
        have := congrArg (fun (g : _ →ₗ[R] _) => g x) (φ.comm i)
        simp only [LinearMap.comp_apply] at this
        rw [← this, hx, map_zero]
      · rintro ⟨y, hy⟩ hh
        simp only [Submodule.mem_comap, Submodule.subtype_apply] at hh ⊢
        obtain ⟨z, rfl⟩ := hh
        refine ⟨φ.f (i + 2) z, ?_⟩
        have := congrArg (fun (g : _ →ₗ[R] _) => g z) (φ.comm (i + 1))
        simp only [LinearMap.comp_apply] at this
        simp only [LinearMap.restrict_apply]
        rw [← this]

/-! ## The two edge complexes -/

/-- The module `R(A)_j = Coker(d : A_{1,j} → A_{0,j})`. -/
def DoubleCx.RObj (A : DoubleCx R) (j : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (A.A 0 j ⧸ LinearMap.range (A.d 0 j))

/-- The module `U(A)_i = Coker(δ : A_{i,1} → A_{i,0})`. -/
def DoubleCx.UObj (A : DoubleCx R) (i : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (A.A i 0 ⧸ LinearMap.range (A.δ i 0))

/-- The induced vertical differential `δ̄` on the horizontal cokernels `R(A)_•`. -/
def DoubleCx.RDiff (A : DoubleCx R) (j : ℕ) : A.RObj (j + 1) →ₗ[R] A.RObj j :=
  Submodule.mapQ _ _ (A.δ 0 j) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨(A.δ 1 j) x, by
      have := congrArg (fun (g : _ →ₗ[R] _) => g x) (A.comm 0 j); simpa using this.symm⟩)

/-- The induced horizontal differential `d̄` on the vertical cokernels `U(A)_•`. -/
def DoubleCx.UDiff (A : DoubleCx R) (i : ℕ) : A.UObj (i + 1) →ₗ[R] A.UObj i :=
  Submodule.mapQ _ _ (A.d i 0) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨(A.d i 1) x, by
      have := congrArg (fun (g : _ →ₗ[R] _) => g x) (A.comm i 0); simpa using this⟩)

/-- The induced differential `δ̄` sends the class of `x` to the class of `δ x`. -/
@[simp] theorem DoubleCx.RDiff_mk (A : DoubleCx R) (j : ℕ) (x : A.A 0 (j + 1)) :
    (A.RDiff j) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (A.δ 0 j x) :=
  Submodule.mapQ_apply _ _ _ _

/-- The induced differential `d̄` sends the class of `x` to the class of `d x`. -/
@[simp] theorem DoubleCx.UDiff_mk (A : DoubleCx R) (i : ℕ) (x : A.A (i + 1) 0) :
    (A.UDiff i) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (A.d i 0 x) :=
  Submodule.mapQ_apply _ _ _ _

/-- The homology `H_i(R(A)_•)` of the edge complex of horizontal cokernels. -/
def DoubleCx.RHom (A : DoubleCx R) (i : ℕ) : ModuleCat.{u} R :=
  homology A.RObj A.RDiff i

/-- The homology `H_i(U(A)_•)` of the edge complex of vertical cokernels. -/
def DoubleCx.UHom (A : DoubleCx R) (i : ℕ) : ModuleCat.{u} R :=
  homology A.UObj A.UDiff i

/-! ## Resolution conditions -/

/-- Each row `A_{•,j}` is a resolution of `R(A)_j`: the rows are exact in
positive horizontal degree, i.e. `ker (d i j) = range (d (i+1) j)`. -/
def DoubleCx.RowResolution (A : DoubleCx R) : Prop :=
  ∀ i j, LinearMap.ker (A.d i j) = LinearMap.range (A.d (i + 1) j)

/-- Each column `A_{i,•}` is a resolution of `U(A)_i`: the columns are exact in
positive vertical degree, i.e. `ker (δ i j) = range (δ i (j+1))`. -/
def DoubleCx.ColResolution (A : DoubleCx R) : Prop :=
  ∀ i j, LinearMap.ker (A.δ i j) = LinearMap.range (A.δ i (j + 1))

/-! ## Morphisms of double complexes and induced maps -/

/-- A morphism of double complexes: a family `Φ i j : A_{i,j} → B_{i,j}`
commuting with both differentials. -/
structure DCxHom (A B : DoubleCx R) where
  /-- The components of the morphism. -/
  Φ : ∀ i j, A.A i j →ₗ[R] B.A i j
  /-- Compatibility with the horizontal differential. -/
  commd : ∀ i j, (Φ i j).comp (A.d i j) = (B.d i j).comp (Φ (i + 1) j)
  /-- Compatibility with the vertical differential. -/
  commδ : ∀ i j, (Φ i j).comp (A.δ i j) = (B.δ i j).comp (Φ i (j + 1))

/-- The induced map on horizontal cokernels `R(A)_j → R(B)_j`. -/
def DCxHom.RMap {A B : DoubleCx R} (Ψ : DCxHom A B) (j : ℕ) :
    A.RObj j →ₗ[R] B.RObj j :=
  Submodule.mapQ _ _ (Ψ.Φ 0 j) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨Ψ.Φ 1 j x, by
      have := congrArg (fun (g : _ →ₗ[R] _) => g x) (Ψ.commd 0 j); simpa using this.symm⟩)

/-- The induced map on vertical cokernels `U(A)_i → U(B)_i`. -/
def DCxHom.UMap {A B : DoubleCx R} (Ψ : DCxHom A B) (i : ℕ) :
    A.UObj i →ₗ[R] B.UObj i :=
  Submodule.mapQ _ _ (Ψ.Φ i 0) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨Ψ.Φ i 1 x, by
      have := congrArg (fun (g : _ →ₗ[R] _) => g x) (Ψ.commδ i 0); simpa using this.symm⟩)

/-- The induced map on horizontal cokernels sends the class of `x` to the class of `Φ 0 j x`. -/
@[simp] theorem DCxHom.RMap_mk {A B : DoubleCx R} (Ψ : DCxHom A B) (j : ℕ) (x : A.A 0 j) :
    (Ψ.RMap j) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Ψ.Φ 0 j x) :=
  Submodule.mapQ_apply _ _ _ _

/-- The induced map on vertical cokernels sends the class of `x` to the class of `Φ i 0 x`. -/
@[simp] theorem DCxHom.UMap_mk {A B : DoubleCx R} (Ψ : DCxHom A B) (i : ℕ) (x : A.A i 0) :
    (Ψ.UMap i) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Ψ.Φ i 0 x) :=
  Submodule.mapQ_apply _ _ _ _

/-- The induced chain map on the `R`-edge complexes. -/
def DCxHom.RChainHom {A B : DoubleCx R} (Ψ : DCxHom A B) :
    ChainHom A.RObj B.RObj A.RDiff B.RDiff where
  f := Ψ.RMap
  comm j := by
    apply Submodule.linearMap_qext
    ext x
    change (Ψ.RMap j) (A.RDiff j (Submodule.Quotient.mk x)) =
      (B.RDiff j) (Ψ.RMap (j + 1) (Submodule.Quotient.mk x))
    rw [DoubleCx.RDiff_mk, DCxHom.RMap_mk, DCxHom.RMap_mk, DoubleCx.RDiff_mk]
    have := congrArg (fun (g : _ →ₗ[R] _) => g x) (Ψ.commδ 0 j)
    simp only [LinearMap.comp_apply] at this
    rw [this]

/-- The induced chain map on the `U`-edge complexes. -/
def DCxHom.UChainHom {A B : DoubleCx R} (Ψ : DCxHom A B) :
    ChainHom A.UObj B.UObj A.UDiff B.UDiff where
  f := Ψ.UMap
  comm i := by
    apply Submodule.linearMap_qext
    ext x
    change (Ψ.UMap i) (A.UDiff i (Submodule.Quotient.mk x)) =
      (B.UDiff i) (Ψ.UMap (i + 1) (Submodule.Quotient.mk x))
    rw [DoubleCx.UDiff_mk, DCxHom.UMap_mk, DCxHom.UMap_mk, DoubleCx.UDiff_mk]
    have := congrArg (fun (g : _ →ₗ[R] _) => g x) (Ψ.commd i 0)
    simp only [LinearMap.comp_apply] at this
    rw [this]

/-- The map induced by `Ψ` on `H_i(R(-)_•)`. -/
noncomputable def DCxHom.RHomMap {A B : DoubleCx R} (Ψ : DCxHom A B) (i : ℕ) :
    A.RHom i →ₗ[R] B.RHom i :=
  homologyMap Ψ.RChainHom i

/-- The map induced by `Ψ` on `H_i(U(-)_•)`. -/
noncomputable def DCxHom.UHomMap {A B : DoubleCx R} (Ψ : DCxHom A B) (i : ℕ) :
    A.UHom i →ₗ[R] B.UHom i :=
  homologyMap Ψ.UChainHom i

/-! ## The total complex and the comparison isomorphisms

The comparison goes through `Hthird A i`, the degree-`i` homology of the *total complex* of `A`.
The total degree-`i` chain group is the dependent product `∀ k : Fin (i+1), A_{k, i-k}` over the
`i`-th antidiagonal, with total differential `D = d ⊕ ±δ`. When the rows and columns are
resolutions, the two edge projections
  `Hthird A i → H_i(R(A)_•)`   (the `k = 0` component `a_{0,i}`)
  `Hthird A i → H_i(U(A)_•)`   (the `k = i` component `a_{i,0}`)
are both isomorphisms, and the canonical isomorphism is `cmpU ∘ cmpR⁻¹`. -/

/-- The total degree-`i` chain group of the double complex `A`: the dependent
product over the `i`-th antidiagonal `{(k, i-k) : k = 0,…,i}`.  An element is a
zig-zag tuple `(a_{0,i}, a_{1,i-1}, …, a_{i,0})` with `a_k ∈ A_{k, i-k}`. -/
abbrev TotChain (A : DoubleCx R) (i : ℕ) : Type u :=
  ∀ k : Fin (i + 1), A.A k (i - (k : ℕ))

/-! ### The total complex and its Koszul sign

`Hthird A i` is the degree-`i` homology of the total complex of `A`: cycles for the
total differential `D` (the sign-adjusted zig-zag relations
`d(a_{k,i-k}) = δ(a_{k-1,i-k+1})`) modulo boundaries, the "trivial zig-zags" that
are the image of `D` from total degree `i+1`.  Concretely it is a quotient of a
cycle submodule of `TotChain A i` by a boundary submodule.

The total differential `Dtot A i : TotChain A (i+1) →ₗ[R] TotChain A i` is built
componentwise from `A.d` and `A.δ`.  Since the `comm` field is the *commuting*
relation `δ ∘ d = d ∘ δ` with no sign, the naive `D = d + δ` has `D² = 2·dδ ≠ 0`;
the total differential must therefore carry the Koszul sign, using `d` together
with `(-1)^k · δ` on the `k`-th component, which makes the cross terms cancel. -/

/-- Transport an element of `A.A a b` to `A.A a' b'` along index equalities. -/
def transp (A : DoubleCx R) (a a' b b' : ℕ) (ha : a = a')
    (hb : b = b') : (A.A a b) ≃ₗ[R] (A.A a' b') := by
  subst ha; subst hb; exact LinearEquiv.refl R _

/-- The total differential `Dtot A i : TotChain A (i+1) →ₗ[R] TotChain A i`,
built componentwise from `A.d` and the Koszul-signed `A.δ`. -/
def Dtot (A : DoubleCx R) (i : ℕ) :
    TotChain A (i + 1) →ₗ[R] TotChain A i :=
  LinearMap.pi (fun m : Fin (i + 1) =>
    have hd1 : (m.succ : ℕ) = (m : ℕ) + 1 := Fin.val_succ m
    have hd2 : i + 1 - (m.succ : ℕ) = i - (m : ℕ) := by rw [hd1]; omega
    have hδ1 : (m.castSucc : ℕ) = (m : ℕ) := Fin.val_castSucc m
    have hδ2 : i + 1 - (m.castSucc : ℕ) = (i - (m : ℕ)) + 1 := by rw [hδ1]; omega
    ((A.d (m : ℕ) (i - (m : ℕ))).comp
        ((transp A (m.succ : ℕ) ((m : ℕ) + 1) (i + 1 - (m.succ : ℕ)) (i - (m : ℕ)) hd1
            hd2).toLinearMap.comp
          (LinearMap.proj m.succ)))
      + ((-1 : R) ^ (m : ℕ)) •
        ((A.δ (m : ℕ) (i - (m : ℕ))).comp
          ((transp A (m.castSucc : ℕ) (m : ℕ) (i + 1 - (m.castSucc : ℕ)) ((i - (m : ℕ)) + 1) hδ1
              hδ2).toLinearMap.comp
            (LinearMap.proj m.castSucc))))

/-- **The canonical third object** `H_i(A) = H_i(Tot A)`: the degree-`i` homology
of the total complex with chain groups `TotChain A n` and differential `Dtot`. -/
def Hthird (A : DoubleCx R) (i : ℕ) : ModuleCat.{u} R :=
  homology (fun n => ModuleCat.of R (TotChain A n)) (fun n => Dtot A n) i

-- Without this option, `rw` does not find its pattern in this proof.
set_option backward.isDefEq.respectTransparency false in
/-- The k=0 edge projection as a chain map from the total complex to `R(A)_•`. -/
def cmpRChainHom (A : DoubleCx R) :
    ChainHom (fun n => ModuleCat.of R (TotChain A n)) A.RObj
      (fun n => Dtot A n) A.RDiff where
  f := fun n => (Submodule.mkQ (LinearMap.range (A.d 0 n))).comp
    (LinearMap.proj (0 : Fin (n + 1)))
  comm n := by
    refine LinearMap.ext fun b => ?_
    simp only [LinearMap.comp_apply]
    change (A.d 0 n).range.mkQ ((Dtot A n b) (0 : Fin (n + 1)))
      = A.RDiff n ((A.d 0 (n + 1)).range.mkQ (b (0 : Fin (n + 2))))
    simp only [Dtot, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearMap.proj_apply, map_add,
      Fin.val_zero, Nat.sub_zero, pow_zero, one_smul]
    have hrhs : A.RDiff n ((A.d 0 (n + 1)).range.mkQ (b (0 : Fin (n + 2))))
        = (A.d 0 n).range.mkQ (A.δ 0 n (b (0 : Fin (n + 2)))) := by
      rw [Submodule.mkQ_apply, DoubleCx.RDiff_mk, Submodule.mkQ_apply]
    rw [hrhs]
    have hd0 : (A.d 0 n).range.mkQ
          ((A.d 0 n)
            ((transp A (↑(Fin.succ (0 : Fin (n + 1)))) (0 + 1)
              (n + 1 - ↑(Fin.succ (0 : Fin (n + 1)))) n (by simp) (by simp))
              (b (Fin.succ (0 : Fin (n + 1)))))) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self _ _
    simp only [hd0, zero_add]
    have hcollapse :
        transp A (↑(Fin.castSucc (0 : Fin (n + 1)))) (0 : ℕ)
            (n + 1 - ↑(Fin.castSucc (0 : Fin (n + 1)))) (n + 1) (Eq.refl _) (Eq.refl _) =
          LinearEquiv.refl R (A.A 0 (n + 1)) := by
      apply LinearEquiv.ext
      intro x
      rfl
    have hidx : Fin.castSucc (0 : Fin (n + 1)) = 0 := Fin.ext rfl
    have hb0 : b (Fin.castSucc (0 : Fin (n + 1))) = b 0 := Eq.refl _
    simp only [one_smul, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe, hcollapse, hb0]
    rfl

/-- The forward edge comparison `cmpRfwd : H_i(Tot A) →ₗ[R] H_i(R(A)_•)`, sending the class of
a zig-zag tuple `(a_{0,i}, …, a_{i,0})` to the class of `a_{0,i}` in
`R(A)_i = Coker (d : A_{1,i} → A_{0,i})`. It is an isomorphism when the rows of `A` are exact in
positive degree. -/
noncomputable def cmpRfwd (A : DoubleCx R) (i : ℕ) : Hthird A i →ₗ[R] A.RHom i :=
  homologyMap (cmpRChainHom A) i

/-! ### Choice of preimages and the staircase descent -/

/-- If `y` lies in the range of `f`, choose a preimage. -/
noncomputable def chooseLift {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {y : N}
    (h : y ∈ LinearMap.range f) : M := h.choose

/-- The chosen preimage of `y` under `f` does map to `y`. -/
theorem chooseLift_spec {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {y : N}
    (h : y ∈ LinearMap.range f) : f (chooseLift f h) = y := h.choose_spec

/-- Shift the double complex one step to the right: `(shiftR A)_{i,j} = A_{i+1,j}`. -/
def DoubleCx.shiftR (A : DoubleCx R) : DoubleCx R where
  A i j := A.A (i + 1) j
  d i j := A.d (i + 1) j
  δ i j := A.δ (i + 1) j
  dd i j := A.dd (i + 1) j
  δδ i j := A.δδ (i + 1) j
  comm i j := A.comm (i + 1) j

/-- If the rows of `A` are exact in positive degree then so are the rows of the
right shift of `A`. -/
theorem DoubleCx.shiftR_RowResolution (A : DoubleCx R) (h : A.RowResolution) :
    A.shiftR.RowResolution := fun i j => h (i + 1) j

/-- If the columns of `A` are exact in positive degree then so are the columns of
the right shift of `A`. -/
theorem DoubleCx.shiftR_ColResolution (A : DoubleCx R) (h : A.ColResolution) :
    A.shiftR.ColResolution := fun i j => h (i + 1) j

/-- The "vertical 1-cycle" predicate on the top of a staircase. -/
def DoubleCx.StairCycle (A : DoubleCx R) : ∀ (n : ℕ), A.A 0 n → Prop
  | 0, _ => True
  | (m + 1), a => A.δ 0 m a ∈ LinearMap.range (A.d 0 m)

/-- The cycle condition propagates one step down the staircase. -/
theorem DoubleCx.stairCycle_step (A : DoubleCx R) (hrow : A.RowResolution)
    (m : ℕ) (a : A.A 0 (m + 1)) (hmem : A.δ 0 m a ∈ LinearMap.range (A.d 0 m)) :
    A.shiftR.StairCycle m (chooseLift (A.d 0 m) hmem) := by
  have hspec : A.d 0 m (chooseLift (A.d 0 m) hmem) = A.δ 0 m a :=
    chooseLift_spec (A.d 0 m) hmem
  cases m with
  | zero => exact trivial
  | succ k =>
      show A.δ 1 k (chooseLift (A.d 0 (k + 1)) hmem) ∈ LinearMap.range (A.d 1 k)
      rw [← hrow 0 k, LinearMap.mem_ker]
      have hc := congrArg (fun (g : _ →ₗ[R] _) => g (chooseLift (A.d 0 (k + 1)) hmem))
        (A.comm 0 k)
      simp only [LinearMap.comp_apply] at hc
      rw [← hc, hspec]
      have hdd := congrArg (fun (g : _ →ₗ[R] _) => g a) (A.δδ 0 k)
      simpa using hdd

/-- The forward staircase descent. -/
noncomputable def DoubleCx.stair (A : DoubleCx R) (hrow : A.RowResolution) :
    ∀ (n : ℕ) (a : A.A 0 n), A.StairCycle n a → A.A n 0
  | 0, a, _ => a
  | (m + 1), a, h =>
      A.shiftR.stair (A.shiftR_RowResolution hrow) m (chooseLift (A.d 0 m) h)
        (A.stairCycle_step hrow m a h)

/-- The full staircase tuple: all antidiagonal components of the zig-zag. -/
noncomputable def DoubleCx.stairTuple (A : DoubleCx R) (hrow : A.RowResolution) :
    ∀ (n : ℕ) (a : A.A 0 n), A.StairCycle n a → (∀ m : Fin (n + 1), A.A m (n - m))
  | 0, a, _ =>
      Fin.cases (motive := fun k : Fin 1 => A.A (k : ℕ) (0 - (k : ℕ))) a (fun j => j.elim0)
  | (m + 1), a, h =>
      Fin.cases (motive := fun k : Fin (m + 2) => A.A (k : ℕ) ((m + 1) - (k : ℕ))) a
        (fun j =>
          transp A ((j : ℕ) + 1) ((j : ℕ) + 1) (m - (j : ℕ)) (m + 1 - ((j : ℕ) + 1))
            rfl (by omega)
            (A.shiftR.stairTuple (A.shiftR_RowResolution hrow) m (chooseLift (A.d 0 m) h)
              (A.stairCycle_step hrow m a h) j))

/-- The `k = 0` component of the staircase tuple built from `a` is `a` itself. -/
theorem stairTuple_zero (A : DoubleCx R) (hrow : A.RowResolution)
    (m : ℕ) (a : A.A 0 (m + 1)) (h : A.StairCycle (m + 1) a) :
    A.stairTuple hrow (m + 1) a h 0 = a := rfl

/-- The components of the staircase tuple at positive index are the components of
the staircase tuple of the right shift of `A`, transported along the antidiagonal
index equality. -/
theorem stairTuple_succ (A : DoubleCx R) (hrow : A.RowResolution)
    (m : ℕ) (a : A.A 0 (m + 1)) (h : A.StairCycle (m + 1) a) (j : Fin (m + 1)) :
    A.stairTuple hrow (m + 1) a h j.succ =
      transp A ((j : ℕ) + 1) ((j : ℕ) + 1) (m - (j : ℕ)) (m + 1 - ((j : ℕ) + 1))
        rfl (by omega)
        (A.shiftR.stairTuple (A.shiftR_RowResolution hrow) m (chooseLift (A.d 0 m) h)
          (A.stairCycle_step hrow m a h) j) := rfl

/-- Transport collapses along trivial index equalities. -/
@[simp] theorem transp_rfl (A : DoubleCx R) (a b : ℕ) (x : A.A a b) :
    transp A a a b b rfl rfl x = x := rfl

/-- Transport composes. -/
theorem transp_trans (A : DoubleCx R) (a a' a'' b b' b'' : ℕ)
    (ha : a = a') (ha' : a' = a'') (hb : b = b') (hb' : b' = b'')
    (x : A.A a b) :
    transp A a' a'' b' b'' ha' hb' (transp A a a' b b' ha hb x)
      = transp A a a'' b b'' (ha.trans ha') (hb.trans hb') x := by
  subst ha; subst ha'; subst hb; subst hb'; rfl

/-- `d` commutes with transport in the second index. -/
theorem d_transp (A : DoubleCx R) (a a' b b' : ℕ) (ha : a + 1 = a' + 1)
    (ha2 : a = a') (hb : b = b') (x : A.A (a + 1) b) :
    A.d a' b' (transp A (a + 1) (a' + 1) b b' ha hb x)
      = transp A a a' b b' ha2 hb (A.d a b x) := by
  subst ha2; subst hb; rfl

/-- `δ` commutes with transport in the first index. -/
theorem δ_transp (A : DoubleCx R) (a a' b b' : ℕ) (ha : a = a')
    (hb : b + 1 = b' + 1) (hb2 : b = b') (x : A.A a (b + 1)) :
    A.δ a' b' (transp A a a' (b + 1) (b' + 1) ha hb x)
      = transp A a a' b b' ha hb2 (A.δ a b x) := by
  subst ha; subst hb2; rfl

/-- The `m`-th component of the total differential: `A.d` applied to the component
at `m.succ`, plus `(-1)^m` times `A.δ` applied to the component at `m.castSucc`. -/
theorem Dtot_apply (A : DoubleCx R) (i : ℕ)
    (x : ∀ k : Fin (i + 2), A.A k (i + 1 - (k : ℕ))) (m : Fin (i + 1)) :
    Dtot A i x m =
      A.d (m : ℕ) (i - (m : ℕ))
          (transp A (m.succ : ℕ) ((m : ℕ) + 1) (i + 1 - (m.succ : ℕ)) (i - (m : ℕ))
            (Fin.val_succ m) (by rw [Fin.val_succ]; omega) (x m.succ))
        + ((-1 : R) ^ (m : ℕ)) •
          A.δ (m : ℕ) (i - (m : ℕ))
            (transp A (m.castSucc : ℕ) (m : ℕ) (i + 1 - (m.castSucc : ℕ)) ((i - (m : ℕ)) + 1)
              (Fin.val_castSucc m) (by rw [Fin.val_castSucc]; omega) (x m.castSucc)) := by
  rfl

/-- Transport on `shiftR` reduces to transport on `A` with shifted first index. -/
theorem shiftR_transp (A : DoubleCx R) (a a' b b' : ℕ) (ha : a = a') (hb : b = b')
    (x : A.shiftR.A a b) :
    transp A.shiftR a a' b b' ha hb x
      = transp A (a + 1) (a' + 1) b b' (by rw [ha]) hb x := by
  subst ha; subst hb; rfl

/-- `stairTuple` at a `j.succ.castSucc` index. -/
theorem stairTuple_succ_castSucc (A : DoubleCx R) (hrow : A.RowResolution)
    (m : ℕ) (a : A.A 0 (m + 1)) (h : A.StairCycle (m + 1) a) (j : Fin m) :
    A.stairTuple hrow (m + 1) a h j.succ.castSucc =
      transp A ((j.castSucc : ℕ) + 1) ((j.castSucc : ℕ) + 1)
        (m - (j.castSucc : ℕ)) (m + 1 - ((j.castSucc : ℕ) + 1)) rfl (by omega)
        (A.shiftR.stairTuple (A.shiftR_RowResolution hrow) m (chooseLift (A.d 0 m) h)
          (A.stairCycle_step hrow m a h) j.castSucc) :=
  stairTuple_succ A hrow m a h j.castSucc

-- Without this option, `rw` does not find its pattern in this proof.
set_option backward.isDefEq.respectTransparency false in
/-- The unsigned zig-zag relation `stairTuple_step`, with the antidiagonal second index a free
variable `b` and `hb : n - ↑j = b`. -/
theorem stairTuple_step' :
    ∀ (n : ℕ) (A : DoubleCx R) (hrow : A.RowResolution)
      (a : A.A 0 (n + 1)) (h : A.StairCycle (n + 1) a) (j : Fin (n + 1))
      (b : ℕ) (hb : n - (j : ℕ) = b),
      A.d (j : ℕ) b
          (transp A (j.succ : ℕ) ((j : ℕ) + 1) (n + 1 - (j.succ : ℕ)) b
            (Fin.val_succ j) (by rw [Fin.val_succ, ← hb]; omega)
            (A.stairTuple hrow (n + 1) a h j.succ))
        = A.δ (j : ℕ) b
          (transp A (j.castSucc : ℕ) (j : ℕ) (n + 1 - (j.castSucc : ℕ)) (b + 1)
            (Fin.val_castSucc j) (by rw [Fin.val_castSucc, ← hb]; omega)
            (A.stairTuple hrow (n + 1) a h j.castSucc)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro A hrow a h j
      refine Fin.cases ?_ ?_ j
      · intro b hb
        simp only [Fin.val_zero, Nat.sub_zero] at hb
        subst hb
        simp only [stairTuple_succ, Fin.val_succ, Fin.val_castSucc, Fin.val_zero,
          transp_trans, d_transp]
        cases n <;>
          simp only [DoubleCx.stairTuple, Fin.cases_zero, Nat.sub_zero, chooseLift_spec] <;> rfl
      · rcases n with _ | k
        · exact fun j => j.elim0
        · intro j' b hb
          have key := ih k k.lt_succ_self A.shiftR (A.shiftR_RowResolution hrow)
            (chooseLift (A.d 0 (k+1)) h) (A.stairCycle_step hrow (k+1) a h) j' b
            (by rw [Fin.val_succ] at hb; omega)
          rw [shiftR_transp, shiftR_transp] at key
          conv_lhs => rw [stairTuple_succ A hrow (k+1) a h j'.succ]
          conv_rhs => rw [stairTuple_succ_castSucc A hrow (k+1) a h j']
          simp only [Fin.val_succ, Fin.val_castSucc] at key ⊢
          rw [transp_trans, transp_trans]
          exact key

/-- The unsigned zig-zag relation satisfied by the staircase tuple `t`:
`d (t (j+1)) = δ (t j)` on every antidiagonal index `j`. -/
theorem stairTuple_step :
    ∀ (n : ℕ) (A : DoubleCx R) (hrow : A.RowResolution)
      (a : A.A 0 (n + 1)) (h : A.StairCycle (n + 1) a) (j : Fin (n + 1)),
      A.d (j : ℕ) (n - (j : ℕ))
          (transp A (j.succ : ℕ) ((j : ℕ) + 1) (n + 1 - (j.succ : ℕ)) (n - (j : ℕ))
            (Fin.val_succ j) (by rw [Fin.val_succ]; omega)
            (A.stairTuple hrow (n + 1) a h j.succ))
        = A.δ (j : ℕ) (n - (j : ℕ))
          (transp A (j.castSucc : ℕ) (j : ℕ) (n + 1 - (j.castSucc : ℕ)) ((n - (j : ℕ)) + 1)
            (Fin.val_castSucc j) (by rw [Fin.val_castSucc]; omega)
            (A.stairTuple hrow (n + 1) a h j.castSucc)) :=
  fun n A hrow a h j => stairTuple_step' n A hrow a h j (n - (j : ℕ)) rfl

end Stacks.Tor.DoubleComplex
