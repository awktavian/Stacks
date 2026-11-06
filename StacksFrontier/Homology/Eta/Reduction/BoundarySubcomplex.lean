module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Eta.Cohomology
public import StacksFrontier.Homology.Eta.Complex
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.LaurentAway
@[expose] public section

-- The eta terms and the tensor total complex are unfolded repeatedly below.

universe u v
/-! ## The boundary subcomplex of the reduction (Tag 0F7S) -/

namespace Stacks.Eta.Reduction

noncomputable section

open scoped nonZeroDivisors
open CategoryTheory

variable {A : Type u} [CommRing A]

private theorem fpow_injective (f : A) {M : Type*} [AddCommGroup M] [Module A M]
    (hM : ∀ x : M, f • x = 0 → x = 0) (i : ℤ) :
    Function.Injective (EtaPow.fpowMap f M i) :=
  fun _ _ h => EtaPow.toLoc_injective_of_isSMulRegular
    (EtaPow.isSMulRegular_of_smul_eq_zero hM)
    (EtaPow.fUnit_zpow_smul_injective i h)

private def fpowRangeEquiv (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    C.X i ≃ₗ[A] LinearMap.range (EtaPow.fpowMap f (C.X i) i) :=
  LinearEquiv.ofInjective (EtaPow.fpowMap f (C.X i) i) (fpow_injective f (hC i) i)

private def coefficient (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    EtaComplex.term f C i →ₗ[A] C.X i :=
  (fpowRangeEquiv f C hC i).symm.toLinearMap.comp
    (((EtaComplex.term f C i).subtype.codRestrict
      (LinearMap.range (EtaPow.fpowMap f (C.X i) i))) fun x => by
        rw [← EtaPow.fpowSub_eq_range]
        exact x.2.1)

private theorem fpow_coefficient (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (x : EtaComplex.term f C i) :
    EtaPow.fpowMap f (C.X i) i (coefficient f C hC i x) = x := by
  change ((fpowRangeEquiv f C hC i)
    (coefficient f C hC i x) : EtaPow.Loc f (C.X i)) = x
  simp [coefficient]

private theorem coefficient_fpow (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (x : C.X i)
    (hx : EtaPow.fpowMap f (C.X i) i x ∈ EtaComplex.term f C i) :
    coefficient f C hC i ⟨EtaPow.fpowMap f (C.X i) i x, hx⟩ = x := by
  exact fpow_injective f (hC i) i (fpow_coefficient f C hC i ⟨EtaPow.fpowMap f (C.X i) i x, hx⟩)

private def barDifferential (f : A) (C : EtaComplex.Complex.{u, v} A)
    (i j : ℤ) :
    ((C.X i) ⧸ LinearMap.range (EtaComplex.scalarMap f (C.X i))) →ₗ[A]
      ((C.X j) ⧸ LinearMap.range (EtaComplex.scalarMap f (C.X j))) := by
  by_cases h : i + 1 = j
  · subst j
    exact Submodule.mapQ _ _ (C.d i (i + 1)).hom (by
      rintro _ ⟨x, rfl⟩
      exact ⟨(C.d i (i + 1)).hom x, by
        change f • (C.d i (i + 1)).hom x = (C.d i (i + 1)).hom (f • x)
        exact (map_smul _ _ _).symm⟩)
  · exact 0

private theorem barDifferential_mk (f : A)
    (C : EtaComplex.Complex.{u, v} A) (i : ℤ) (x : C.X i) :
    barDifferential f C i (i + 1) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((C.d i (i + 1)).hom x) := by
  simp [barDifferential]

private theorem barDifferential_zero (f : A)
    (C : EtaComplex.Complex.{u, v} A) (i j : ℤ) (h : i + 1 ≠ j) :
    barDifferential f C i j = 0 := by
  simp [barDifferential, h]

private theorem barDifferential_comp (f : A)
    (C : EtaComplex.Complex.{u, v} A) (i : ℤ)
    (x : (C.X i) ⧸ LinearMap.range (EtaComplex.scalarMap f (C.X i))) :
    barDifferential f C (i + 1) (i + 1 + 1) (barDifferential f C i (i + 1) x) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [barDifferential_mk]
  have h := ConcreteCategory.congr_hom (C.d_comp_d i (i + 1) (i + 1 + 1)) x
  change (C.d (i + 1) (i + 1 + 1)).hom ((C.d i (i + 1)).hom x) = 0 at h
  rw [show (C.d (i + 1) (i + 1 + 1)).hom ((C.d i (i + 1)).hom x) = 0 by
    exact h]
  rfl

private def shiftedEta (f : A) (C : EtaComplex.Complex.{u, v} A)
    (i : ℤ) : C.X i →ₗ[A] EtaComplex.term f C i :=
  ((EtaPow.fpowMap f (C.X i) (i + 1)).codRestrict _ fun x => by
    rw [EtaComplex.mem_term]
    constructor
    · exact EtaComplex.powerSubmodule_step f i
        ((EtaPow.fpowSub_eq_range (f := f) (M := C.X i) (i + 1)).ge ⟨x, rfl⟩)
    · rw [EtaPow.fpowMap_apply, EtaPow.fLoc_zpow_smul, EtaPow.fLoc_toLoc]
      exact (EtaPow.fpowSub_eq_range (f := f) (M := C.X (i + 1)) (i + 1)).ge
        ⟨(C.d i (i + 1)).hom x, rfl⟩)

private def shiftedClass (f : A) (C : EtaComplex.Complex.{u, v} A)
    (i : ℤ) : C.X i →ₗ[A] EtaComplex.QuotientTerm f C i :=
  (Submodule.mkQ _).comp (shiftedEta f C i)

private theorem shiftedClass_smul (f : A) (C : EtaComplex.Complex.{u, v} A)
    (i : ℤ) (x : C.X i) : shiftedClass f C i (f • x) = 0 := by
  rw [shiftedClass, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  refine ⟨shiftedEta f C i x, ?_⟩
  apply Subtype.ext
  change f • EtaPow.fpowMap f (C.X i) (i + 1) x =
    EtaPow.fpowMap f (C.X i) (i + 1) (f • x)
  exact (map_smul _ _ _).symm

private def boundaryClass (f : A) (C : EtaComplex.Complex.{u, v} A)
    (i : ℤ) :
    ((C.X i) ⧸ LinearMap.range (EtaComplex.scalarMap f (C.X i))) →ₗ[A]
      EtaComplex.QuotientTerm f C i :=
  Submodule.liftQ _ (shiftedClass f C i) (by
    rintro _ ⟨x, rfl⟩
    exact shiftedClass_smul f C i x)

private theorem boundaryClass_mk (f : A)
    (C : EtaComplex.Complex.{u, v} A) (i : ℤ) (x : C.X i) :
    boundaryClass f C i (Submodule.Quotient.mk x) = shiftedClass f C i x := by
  rfl

private theorem fpow_succ (f : A) {M : Type*} [AddCommGroup M] [Module A M]
    (i : ℤ) (x : M) :
    EtaPow.fpowMap f M (i + 1) x = EtaPow.fpowMap f M i (f • x) := by
  simp only [EtaPow.fpowMap_apply, ← EtaPow.fUnit_zpow_one_smul_toLoc,
    EtaPow.fUnit_zpow_smul_smul]

private theorem locD_fpow (f : A) {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (d : M →ₗ[A] N) (i : ℤ) (x : M) :
    EtaPow.fLoc f d (EtaPow.fpowMap f M i x) = EtaPow.fpowMap f N i (d x) := by
  simp only [EtaPow.fpowMap_apply, EtaPow.fLoc_zpow_smul, EtaPow.fLoc_toLoc]

private abbrev Bar (f : A) (C : EtaComplex.Complex.{u, v} A) (i : ℤ) :=
  (C.X i) ⧸ LinearMap.range (EtaComplex.scalarMap f (C.X i))

private abbrev boundaries (f : A) (C : EtaComplex.Complex.{u, v} A) (i : ℤ) :=
  LinearMap.range (barDifferential f C (i - 1) i)

private abbrev cycles (f : A) (C : EtaComplex.Complex.{u, v} A) (i : ℤ) :=
  LinearMap.ker (barDifferential f C i (i + 1))

/-- An element of `Bar f C (i + 1)` is a boundary iff it is `d` of an element of `Bar f C i`. -/
private theorem mem_boundaries_succ_iff (f : A) (C : EtaComplex.Complex.{u, v} A) (i : ℤ)
    (y : Bar f C (i + 1)) :
    y ∈ boundaries f C (i + 1) ↔ ∃ x, barDifferential f C i (i + 1) x = y := by
  unfold boundaries
  rw [add_sub_cancel_right]
  exact LinearMap.mem_range

private theorem mk_smul (f : A) {M : Type*} [AddCommGroup M] [Module A M] (x : M) :
    (Submodule.Quotient.mk (f • x) : M ⧸ LinearMap.range (EtaComplex.scalarMap f M)) = 0 :=
  Submodule.Quotient.mk_eq_zero _ |>.mpr ⟨x, rfl⟩

private theorem fpow_mem_term_iff (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (x : C.X i) :
    EtaPow.fpowMap f (C.X i) i x ∈ EtaComplex.term f C i ↔
      (Submodule.Quotient.mk x : Bar f C i) ∈ cycles f C i := by
  rw [EtaComplex.mem_term, LinearMap.mem_ker, barDifferential_mk,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨_, hd⟩
    rw [locD_fpow, EtaPow.fpowSub_eq_range] at hd
    obtain ⟨y, hy⟩ := hd
    exact ⟨y, fpow_injective f (hC (i + 1)) i ((fpow_succ f i y).symm.trans hy)⟩
  · rintro ⟨y, hy⟩
    refine ⟨(EtaPow.fpowSub_eq_range i).ge ⟨x, rfl⟩, ?_⟩
    rw [locD_fpow, EtaPow.fpowSub_eq_range]
    exact ⟨y, (fpow_succ f i y).trans (congrArg (EtaPow.fpowMap f _ i) hy)⟩

private theorem coefficient_mem (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (x : EtaComplex.term f C i) :
    (Submodule.Quotient.mk (coefficient f C hC i x) : Bar f C i) ∈ cycles f C i := by
  apply (fpow_mem_term_iff f C hC i _).mp
  rw [fpow_coefficient]
  exact x.2

private def cycleProjection (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    EtaComplex.QuotientTerm f C i →ₗ[A] cycles f C i :=
  Submodule.liftQ _
    (((Submodule.mkQ _).comp (coefficient f C hC i)).codRestrict _
      (coefficient_mem f C hC i)) (by
        rintro _ ⟨x, rfl⟩
        apply Subtype.ext
        change Submodule.Quotient.mk (coefficient f C hC i (f • x)) = 0
        rw [map_smul]
        exact mk_smul f _)

private theorem cycleProjection_mk (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (x : EtaComplex.term f C i) :
    (cycleProjection f C hC i (Submodule.Quotient.mk x) : Bar f C i) =
      Submodule.Quotient.mk (coefficient f C hC i x) := rfl

private theorem cycleProjection_fpow (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (x : C.X i)
    (hx : EtaPow.fpowMap f (C.X i) i x ∈ EtaComplex.term f C i) :
    (cycleProjection f C hC i (Submodule.Quotient.mk
      (⟨EtaPow.fpowMap f (C.X i) i x, hx⟩ : EtaComplex.term f C i)) : Bar f C i) =
        Submodule.Quotient.mk x := by
  rw [cycleProjection_mk, coefficient_fpow]

private theorem cycleProjection_surjective (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    Function.Surjective (cycleProjection f C hC i) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine ⟨Submodule.Quotient.mk (⟨_, (fpow_mem_term_iff f C hC i x).mpr hz⟩ :
    EtaComplex.term f C i), ?_⟩
  exact Subtype.ext (cycleProjection_fpow f C hC i x _)

private theorem boundaryClass_eq_zero_iff (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (x : Bar f C i) :
    boundaryClass f C i x = 0 ↔ barDifferential f C i (i + 1) x = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [boundaryClass_mk, barDifferential_mk]
  change Submodule.Quotient.mk (shiftedEta f C i x) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y, hy⟩
    have heq : coefficient f C hC i y = x := by
      apply fpow_injective f (hC i) (i + 1)
      rw [fpow_succ, map_smul, fpow_coefficient]
      exact congrArg Subtype.val hy
    rw [← heq, ← barDifferential_mk]
    exact coefficient_mem f C hC i y
  · intro hx
    have hm := (fpow_mem_term_iff f C hC i x).mpr (by
      change barDifferential f C i (i + 1) (Submodule.Quotient.mk x) = 0
      rwa [barDifferential_mk])
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    change f • EtaPow.fpowMap f (C.X i) i x = EtaPow.fpowMap f (C.X i) (i + 1) x
    rw [fpow_succ, map_smul]

private def factorRange {M N P : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (g : M →ₗ[A] N) (k : M →ₗ[A] P) (h : LinearMap.ker g ≤ LinearMap.ker k) :
    LinearMap.range g →ₗ[A] P :=
  (Submodule.liftQ _ k h).comp g.quotKerEquivRange.symm.toLinearMap

private theorem factorRange_apply {M N P : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (g : M →ₗ[A] N) (k : M →ₗ[A] P) (h : LinearMap.ker g ≤ LinearMap.ker k)
    (x : M) (hx : g x ∈ LinearMap.range g) :
    factorRange g k h ⟨g x, hx⟩ = k x := by
  simp [factorRange, LinearMap.quotKerEquivRange_symm_apply_image]

private def boundaryInclusion (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    boundaries f C (i + 1) →ₗ[A] EtaComplex.QuotientTerm f C i :=
  (factorRange (barDifferential f C i (i + 1)) (boundaryClass f C i)
    (fun x hx => (boundaryClass_eq_zero_iff f C hC i x).mpr hx)).comp
      (Submodule.inclusion (by unfold boundaries; rw [add_sub_cancel_right]))

private theorem boundaryInclusion_apply (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (x : Bar f C i)
    (hx : barDifferential f C i (i + 1) x ∈ boundaries f C (i + 1)) :
    boundaryInclusion f C hC i ⟨barDifferential f C i (i + 1) x, hx⟩ =
      boundaryClass f C i x :=
  factorRange_apply (barDifferential f C i (i + 1)) (boundaryClass f C i)
    (fun x hx => (boundaryClass_eq_zero_iff f C hC i x).mpr hx) x _

private theorem boundaryInclusion_injective (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    Function.Injective (boundaryInclusion f C hC i) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨b, hb⟩ hz
  obtain ⟨x, rfl⟩ := (mem_boundaries_succ_iff f C i b).mp hb
  rw [boundaryInclusion_apply] at hz
  exact Subtype.ext ((boundaryClass_eq_zero_iff f C hC i x).mp hz)

private theorem cycleProjection_boundaryClass (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (x : Bar f C i) :
    cycleProjection f C hC i (boundaryClass f C i x) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  apply Subtype.ext
  rw [boundaryClass_mk]
  change (cycleProjection f C hC i (Submodule.Quotient.mk (shiftedEta f C i x)) :
    Bar f C i) = 0
  rw [cycleProjection_mk]
  have hc : coefficient f C hC i (shiftedEta f C i x) = f • x := by
    apply fpow_injective f (hC i) i
    rw [fpow_coefficient]
    exact fpow_succ f i x
  rw [hc, mk_smul]

private theorem cycleProjection_boundaryInclusion (f : A)
    (C : EtaComplex.Complex.{u, v} A) (hC : EtaComplex.IsTorsionFree f C)
    (i : ℤ) (b : boundaries f C (i + 1)) :
    cycleProjection f C hC i (boundaryInclusion f C hC i b) = 0 := by
  obtain ⟨b, hb⟩ := b
  obtain ⟨x, rfl⟩ := (mem_boundaries_succ_iff f C i b).mp hb
  exact (congrArg (cycleProjection f C hC i)
    (boundaryInclusion_apply f C hC i x _)).trans
      (cycleProjection_boundaryClass f C hC i x)

private theorem boundaryInclusion_exact (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    Function.Exact (boundaryInclusion f C hC i) (cycleProjection f C hC i) := by
  intro q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hc := congrArg Subtype.val hq
    change Submodule.Quotient.mk (coefficient f C hC i x) = (0 : Bar f C i) at hc
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hc
    have hx : shiftedEta f C i y = x := by
      apply Subtype.ext
      change EtaPow.fpowMap f (C.X i) (i + 1) y = x
      rw [fpow_succ, show f • y = coefficient f C hC i x from hy, fpow_coefficient]
    refine ⟨⟨barDifferential f C i (i + 1) (Submodule.Quotient.mk y),
      (mem_boundaries_succ_iff f C i _).mpr ⟨_, rfl⟩⟩, ?_⟩
    rw [boundaryInclusion_apply, boundaryClass_mk]
    exact congrArg Submodule.Quotient.mk hx
  · rintro ⟨b, rfl⟩
    exact cycleProjection_boundaryInclusion f C hC i b

private theorem boundaries_le_cycles (f : A) (C : EtaComplex.Complex.{u, v} A)
    (i : ℤ) : boundaries f C i ≤ cycles f C i := by
  rintro _ ⟨x, rfl⟩
  have hi : i - 1 + 1 = i := by omega
  change barDifferential f C i (i + 1) (barDifferential f C (i - 1) i x) = 0
  have h := barDifferential_comp f C (i - 1) x
  rw [hi] at h
  exact h

private theorem quotientDifferential_comp (f : A) (C : EtaComplex.Complex.{u, v} A)
    (i : ℤ) (q : EtaComplex.QuotientTerm f C i) :
    EtaComplex.quotientDifferential f C (i + 1)
      (EtaComplex.quotientDifferential f C i q) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [EtaComplex.quotientDifferential_mk, EtaComplex.etaDifferential_comp]
  rfl

private def boundaryLift (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    boundaries f C i →ₗ[A] EtaComplex.QuotientTerm f C i := by
  have hi : i - 1 + 1 = i := by omega
  exact hi ▸ ((EtaComplex.quotientDifferential f C (i - 1)).comp
    (boundaryInclusion f C hC (i - 1)))

private theorem boundaryLift_next (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (b : boundaries f C (i + 1)) :
    boundaryLift f C hC (i + 1) b =
      EtaComplex.quotientDifferential f C i (boundaryInclusion f C hC i b) := by
  have he : boundaryLift f C hC (i + 1) =
      (EtaComplex.quotientDifferential f C i).comp (boundaryInclusion f C hC i) := by
    apply eq_of_heq
    unfold boundaryLift
    dsimp only
    apply (eqRec_heq_self _ _).trans
    have hh : ∀ j k : ℤ, j = k → HEq
        ((EtaComplex.quotientDifferential f C j).comp (boundaryInclusion f C hC j))
        ((EtaComplex.quotientDifferential f C k).comp (boundaryInclusion f C hC k)) := by
      intro j k h
      subst k
      rfl
    exact hh _ _ (by omega)
  exact congrArg (fun g => g b) he

private theorem quotientDifferential_boundaryLift (f : A)
    (C : EtaComplex.Complex.{u, v} A) (hC : EtaComplex.IsTorsionFree f C)
    (i : ℤ) (b : boundaries f C i) :
    EtaComplex.quotientDifferential f C i (boundaryLift f C hC i b) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
  rw [boundaryLift_next, quotientDifferential_comp]

private theorem cycleProjection_boundaryLift (f : A)
    (C : EtaComplex.Complex.{u, v} A) (hC : EtaComplex.IsTorsionFree f C)
    (i : ℤ) (b : boundaries f C i) :
    (cycleProjection f C hC i (boundaryLift f C hC i b) : Bar f C i) = b := by
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨b, hb⟩ := b
  obtain ⟨x, rfl⟩ := (mem_boundaries_succ_iff f C j b).mp hb
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [boundaryLift_next]
  have he := boundaryInclusion_apply f C hC j (Submodule.Quotient.mk x) hb
  rw [he, boundaryClass_mk]
  change (cycleProjection f C hC (j + 1)
    (EtaComplex.quotientDifferential f C j (Submodule.Quotient.mk (shiftedEta f C j x))) :
      Bar f C (j + 1)) = _
  rw [EtaComplex.quotientDifferential_mk, cycleProjection_mk]
  have hc : coefficient f C hC (j + 1)
      (EtaComplex.etaDifferential f C j (shiftedEta f C j x)) =
        (C.d j (j + 1)).hom x := by
    apply fpow_injective f (hC (j + 1)) (j + 1)
    rw [fpow_coefficient, EtaComplex.etaDifferential_val]
    exact locD_fpow f _ _ _
  rw [hc]
  exact (barDifferential_mk f C j x).symm

private theorem coprod_injective (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    Function.Injective (LinearMap.coprod (boundaryInclusion f C hC i)
      (boundaryLift f C hC i)) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, b⟩ h
  change boundaryInclusion f C hC i a + boundaryLift f C hC i b = 0 at h
  have hb := congrArg (fun q => (cycleProjection f C hC i q : Bar f C i)) h
  simp only [map_add, cycleProjection_boundaryInclusion, ZeroMemClass.coe_zero,
    cycleProjection_boundaryLift, zero_add, map_zero] at hb
  have hb' : b = 0 := Subtype.ext hb
  subst b
  simp only [map_zero, add_zero] at h
  have ha := boundaryInclusion_injective f C hC i (h.trans (map_zero _).symm)
  exact Prod.ext ha rfl

private abbrev boundarySum (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :=
  LinearMap.coprod (boundaryInclusion f C hC i) (boundaryLift f C hC i)

private abbrev reducedCohomology (f : A) (C : EtaComplex.Complex.{u, v} A) (i : ℤ) :=
  (cycles f C i) ⧸ (boundaries f C i).comap (cycles f C i).subtype

private theorem cycleProjection_mem_boundaries_iff (f : A)
    (C : EtaComplex.Complex.{u, v} A) (hC : EtaComplex.IsTorsionFree f C)
    (i : ℤ) (q : EtaComplex.QuotientTerm f C i) :
    (cycleProjection f C hC i q : Bar f C i) ∈ boundaries f C i ↔
      q ∈ LinearMap.range (boundarySum f C hC i) := by
  constructor
  · intro hq
    let b : boundaries f C i := ⟨_, hq⟩
    have hz : cycleProjection f C hC i (q - boundaryLift f C hC i b) = 0 := by
      apply Subtype.ext
      simp only [map_sub, Submodule.coe_sub, cycleProjection_boundaryLift]
      exact sub_self _
    obtain ⟨a, ha⟩ := (boundaryInclusion_exact f C hC i _).mp hz
    refine ⟨(a, b), ?_⟩
    change boundaryInclusion f C hC i a + boundaryLift f C hC i b = q
    rw [ha, sub_add_cancel]
  · rintro ⟨⟨a, b⟩, rfl⟩
    change (cycleProjection f C hC i
      (boundaryInclusion f C hC i a + boundaryLift f C hC i b) : Bar f C i) ∈ _
    rw [map_add, cycleProjection_boundaryInclusion, zero_add,
      cycleProjection_boundaryLift]
    exact b.2

private def cohomologyProjection (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    (EtaComplex.QuotientTerm f C i ⧸ LinearMap.range (boundarySum f C hC i)) →ₗ[A]
      reducedCohomology f C i :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp (cycleProjection f C hC i)) (by
    intro q hq
    change Submodule.Quotient.mk (cycleProjection f C hC i q) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (cycleProjection_mem_boundaries_iff f C hC i q).mpr hq)

private theorem cohomologyProjection_mk (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (q : EtaComplex.QuotientTerm f C i) :
    cohomologyProjection f C hC i (Submodule.Quotient.mk q) =
      Submodule.Quotient.mk (cycleProjection f C hC i q) := rfl

private def cohomologyEquiv (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    (EtaComplex.QuotientTerm f C i ⧸ LinearMap.range (boundarySum f C hC i)) ≃ₗ[A]
      reducedCohomology f C i :=
  LinearEquiv.ofBijective (cohomologyProjection f C hC i) ⟨by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [cohomologyProjection_mk, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact (cycleProjection_mem_boundaries_iff f C hC i q).mp hq, by
    intro h
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    obtain ⟨q, rfl⟩ := cycleProjection_surjective f C hC i z
    exact ⟨Submodule.Quotient.mk q, rfl⟩⟩

private theorem cohomologyEquiv_mk (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (q : EtaComplex.QuotientTerm f C i) :
    cohomologyEquiv f C hC i (Submodule.Quotient.mk q) =
      Submodule.Quotient.mk (cycleProjection f C hC i q) := rfl

private theorem quotientDifferential_boundarySum (f : A)
    (C : EtaComplex.Complex.{u, v} A) (hC : EtaComplex.IsTorsionFree f C)
    (i : ℤ) (a : boundaries f C (i + 1)) (b : boundaries f C i) :
    EtaComplex.quotientDifferential f C i (boundarySum f C hC i (a, b)) =
      boundaryLift f C hC (i + 1) a := by
  change EtaComplex.quotientDifferential f C i
    (boundaryInclusion f C hC i a + boundaryLift f C hC i b) = _
  rw [map_add, quotientDifferential_boundaryLift, add_zero, boundaryLift_next]

private def boundaryQuotientDifferential (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    (EtaComplex.QuotientTerm f C i ⧸ LinearMap.range (boundarySum f C hC i)) →ₗ[A]
      (EtaComplex.QuotientTerm f C (i + 1) ⧸
        LinearMap.range (boundarySum f C hC (i + 1))) :=
  Submodule.mapQ _ _ (EtaComplex.quotientDifferential f C i) (by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change EtaComplex.quotientDifferential f C i (boundarySum f C hC i (a, b)) ∈
      LinearMap.range (boundarySum f C hC (i + 1))
    rw [quotientDifferential_boundarySum]
    exact ⟨(0, a), by simp [boundarySum]⟩)

private theorem boundaryQuotientDifferential_mk (f : A)
    (C : EtaComplex.Complex.{u, v} A) (hC : EtaComplex.IsTorsionFree f C)
    (i : ℤ) (q : EtaComplex.QuotientTerm f C i) :
    boundaryQuotientDifferential f C hC i (Submodule.Quotient.mk q) =
      Submodule.Quotient.mk (EtaComplex.quotientDifferential f C i q) := rfl

private def cohomologyDifferential (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) :
    reducedCohomology f C i →ₗ[A] reducedCohomology f C (i + 1) :=
  (cohomologyEquiv f C hC (i + 1)).toLinearMap.comp
    ((boundaryQuotientDifferential f C hC i).comp
      (cohomologyEquiv f C hC i).symm.toLinearMap)

private theorem cohomologyDifferential_mk (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (q : EtaComplex.QuotientTerm f C i) :
    cohomologyDifferential f C hC i
      (cohomologyEquiv f C hC i (Submodule.Quotient.mk q)) =
        cohomologyEquiv f C hC (i + 1)
          (Submodule.Quotient.mk (EtaComplex.quotientDifferential f C i q)) := by
  simp only [cohomologyDifferential, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, boundaryQuotientDifferential_mk]

private theorem cohomologyDifferential_comp (f : A) (C : EtaComplex.Complex.{u, v} A)
    (hC : EtaComplex.IsTorsionFree f C) (i : ℤ) (h : reducedCohomology f C i) :
    cohomologyDifferential f C hC (i + 1) (cohomologyDifferential f C hC i h) = 0 := by
  obtain ⟨q, rfl⟩ := (cohomologyEquiv f C hC i).surjective h
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [cohomologyDifferential_mk, cohomologyDifferential_mk, quotientDifferential_comp]
  exact map_zero _

private theorem boundaryInclusion_representative (f : A)
    (C : EtaComplex.Complex.{u, v} A) (hC : EtaComplex.IsTorsionFree f C)
    (i : ℤ) (y : C.X (i + 1)) (hy : Submodule.Quotient.mk y ∈ boundaries f C (i + 1))
    (y' : C.X (i + 1)) (x : C.X i) (heq : y = f • y' + (C.d i (i + 1)).hom x) :
    ∃ heta : EtaPow.fpowMap f (C.X i) (i + 1) x ∈ EtaComplex.term f C i,
      boundaryInclusion f C hC i ⟨Submodule.Quotient.mk y, hy⟩ =
        Submodule.Quotient.mk
          (⟨EtaPow.fpowMap f (C.X i) (i + 1) x, heta⟩ : EtaComplex.term f C i) := by
  have hyx : (Submodule.Quotient.mk y : Bar f C (i + 1)) =
      barDifferential f C i (i + 1) (Submodule.Quotient.mk x) := by
    rw [heq, barDifferential_mk]
    change (Submodule.mkQ _) (f • y' + (C.d i (i + 1)).hom x) = _
    rw [map_add, Submodule.mkQ_apply, mk_smul, zero_add]
    rfl
  have hb : barDifferential f C i (i + 1) (Submodule.Quotient.mk x) ∈
      boundaries f C (i + 1) := hyx ▸ hy
  have he : (⟨Submodule.Quotient.mk y, hy⟩ : boundaries f C (i + 1)) =
      ⟨barDifferential f C i (i + 1) (Submodule.Quotient.mk x), hb⟩ := Subtype.ext hyx
  refine ⟨(shiftedEta f C i x).2, ?_⟩
  rw [he, boundaryInclusion_apply, boundaryClass_mk]
  rfl

private theorem boundaryLift_representative_next (f : A)
    (C : EtaComplex.Complex.{u, v} A) (hC : EtaComplex.IsTorsionFree f C)
    (j : ℤ) (x : C.X (j + 1)) (hx : Submodule.Quotient.mk x ∈ boundaries f C (j + 1))
    (x' : C.X (j + 1)) (z : C.X j) (heq : x = f • x' + (C.d j (j + 1)).hom z) :
    ∃ heta : EtaPow.fpowMap f (C.X (j + 1)) (j + 1) ((C.d j (j + 1)).hom z) ∈
        EtaComplex.term f C (j + 1),
      boundaryLift f C hC (j + 1) ⟨Submodule.Quotient.mk x, hx⟩ =
        Submodule.Quotient.mk
          (⟨EtaPow.fpowMap f (C.X (j + 1)) (j + 1) ((C.d j (j + 1)).hom z), heta⟩ :
            EtaComplex.term f C (j + 1)) := by
  obtain ⟨hz, he⟩ := boundaryInclusion_representative f C hC j x hx x' z heq
  let w : EtaComplex.term f C j := ⟨_, hz⟩
  have hw : (EtaComplex.etaDifferential f C j w : EtaPow.Loc f (C.X (j + 1))) =
      EtaPow.fpowMap f (C.X (j + 1)) (j + 1) ((C.d j (j + 1)).hom z) :=
    locD_fpow f _ _ _
  refine ⟨hw ▸ (EtaComplex.etaDifferential f C j w).2, ?_⟩
  rw [boundaryLift_next, he, EtaComplex.quotientDifferential_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hw)

private theorem boundaryLift_representative (f : A)
    (C : EtaComplex.Complex.{u, v} A) (hC : EtaComplex.IsTorsionFree f C)
    (i : ℤ) (x : C.X i) (hx : Submodule.Quotient.mk x ∈ boundaries f C i)
    (x' : C.X i) (z : C.X (i - 1)) (heq : x = f • x' + (C.d (i - 1) i).hom z) :
    ∃ heta : EtaPow.fpowMap f (C.X i) i ((C.d (i - 1) i).hom z) ∈ EtaComplex.term f C i,
      boundaryLift f C hC i ⟨Submodule.Quotient.mk x, hx⟩ =
        Submodule.Quotient.mk
          (⟨EtaPow.fpowMap f (C.X i) i ((C.d (i - 1) i).hom z), heta⟩ :
            EtaComplex.term f C i) := by
  have h := boundaryLift_representative_next f C hC (i - 1)
  rw [sub_add_cancel] at h
  exact h x hx x' z heq

/-- **Stacks 0F7S.** Modulo a nonzerodivisor `f`, the eta complex has an acyclic
subcomplex with degree-`i` term `B^(i+1) ⊕ B^i`, and the quotient complex has the
cohomology modules of `M/fM` as its terms, with the induced differential transported
along the equivalences `e`. The final three clauses give the
representative formulas for the maps `t`, `s`, and `s'` from the source. -/
@[stacks 0F7S]
theorem exists_boundary_subcomplex_of_etaQuotient
    (f : A) (_hf : f ∈ nonZeroDivisors A)
    (C : EtaComplex.Complex.{u, v} A) (hC : EtaComplex.IsTorsionFree f C) :
    let barTerm : ℤ → Type (max u v) := fun i =>
      (C.X i) ⧸ LinearMap.range (EtaComplex.scalarMap f (C.X i))
    ∃ barD : ∀ i j, barTerm i →ₗ[A] barTerm j,
      (∀ i (x : C.X i),
        barD i (i + 1) (Submodule.Quotient.mk x) =
          Submodule.Quotient.mk ((C.d i (i + 1)).hom x)) ∧
      (∀ i j, i + 1 ≠ j → barD i j = 0) ∧
      (∀ i (x : barTerm i), barD (i + 1) (i + 1 + 1) (barD i (i + 1) x) = 0) ∧
      let B : ∀ i, Submodule A (barTerm i) := fun i =>
        LinearMap.range (barD (i - 1) i)
      let Z : ∀ i, Submodule A (barTerm i) := fun i => LinearMap.ker (barD i (i + 1))
      let H : ℤ → Type (max u v) := fun i =>
        (Z i) ⧸ (B i).comap (Z i).subtype
      let Q : ℤ → Type (max u v) := fun i => EtaComplex.QuotientTerm f C i
      ∃ (hBZ : ∀ i, B i ≤ Z i)
        (s : ∀ i, B (i + 1) →ₗ[A] Q i)
        (s' : ∀ i, B i →ₗ[A] Q i)
        (t : ∀ i, Q i →ₗ[A] Z i)
        (e : ∀ i,
          (Q i ⧸ LinearMap.range (LinearMap.coprod (s i) (s' i))) ≃ₗ[A] H i),
        (∀ i, Function.Injective (LinearMap.coprod (s i) (s' i))) ∧
        (∀ i, Function.Injective (s i)) ∧
        (∀ i, Function.Surjective (t i)) ∧
        (∀ i, Function.Exact (s i) (t i)) ∧
        (∀ i (bNext : B (i + 1)) (b : B i),
          t i (s i bNext + s' i b) = ⟨b, hBZ i b.2⟩) ∧
        (∀ i (bNext : B (i + 1)) (b : B i),
          EtaComplex.quotientDifferential f C i (s i bNext + s' i b) =
            s' (i + 1) bNext) ∧
        (∀ i, Function.Exact
          (fun p : B i × B (i - 1) => ((0 : B (i + 1)), p.1))
          (fun p : B (i + 1) × B i => ((0 : B (i + 1 + 1)), p.1))) ∧
        (∀ i (q : Q i),
          e i (Submodule.Quotient.mk q) = Submodule.Quotient.mk (t i q)) ∧
        (∃ dH : ∀ i, H i →ₗ[A] H (i + 1),
          (∀ i (q : Q i),
            e (i + 1) (Submodule.Quotient.mk
              (EtaComplex.quotientDifferential f C i q)) =
                dH i (e i (Submodule.Quotient.mk q))) ∧
          (∀ i (h : H i), dH (i + 1) (dH i h) = 0)) ∧
        (∀ i (x : C.X i)
            (hx : EtaPow.fpowMap f (C.X i) i x ∈ EtaComplex.term f C i),
          ∃ hz : Submodule.Quotient.mk x ∈ Z i,
            t i (Submodule.Quotient.mk
              (⟨EtaPow.fpowMap f (C.X i) i x, hx⟩ : EtaComplex.term f C i)) =
                ⟨Submodule.Quotient.mk x, hz⟩) ∧
        (∀ i (y : C.X (i + 1)) (hy : Submodule.Quotient.mk y ∈ B (i + 1))
            (y' : C.X (i + 1)) (x : C.X i)
            (_heq : y = f • y' + (C.d i (i + 1)).hom x),
          ∃ heta : EtaPow.fpowMap f (C.X i) (i + 1) x ∈ EtaComplex.term f C i,
            s i ⟨Submodule.Quotient.mk y, hy⟩ =
              Submodule.Quotient.mk
                (⟨EtaPow.fpowMap f (C.X i) (i + 1) x, heta⟩ :
                  EtaComplex.term f C i)) ∧
        (∀ i (x : C.X i) (hx : Submodule.Quotient.mk x ∈ B i)
            (x' : C.X i) (z : C.X (i - 1))
            (_heq : x = f • x' + (C.d (i - 1) i).hom z),
          ∃ heta : EtaPow.fpowMap f (C.X i) i ((C.d (i - 1) i).hom z) ∈
              EtaComplex.term f C i,
            s' i ⟨Submodule.Quotient.mk x, hx⟩ =
              Submodule.Quotient.mk
                (⟨EtaPow.fpowMap f (C.X i) i ((C.d (i - 1) i).hom z), heta⟩ :
                  EtaComplex.term f C i)) := by
  refine ⟨barDifferential f C, barDifferential_mk f C, barDifferential_zero f C,
    barDifferential_comp f C, ?_⟩
  refine ⟨boundaries_le_cycles f C, boundaryInclusion f C hC, boundaryLift f C hC,
    cycleProjection f C hC, cohomologyEquiv f C hC, ?_⟩
  refine ⟨coprod_injective f C hC, boundaryInclusion_injective f C hC,
    cycleProjection_surjective f C hC, boundaryInclusion_exact f C hC,
    ?_, ?_, ?_, cohomologyEquiv_mk f C hC, ?_, ?_,
    boundaryInclusion_representative f C hC, boundaryLift_representative f C hC⟩
  · intro i a b
    apply Subtype.ext
    rw [map_add, cycleProjection_boundaryInclusion, zero_add]
    exact cycleProjection_boundaryLift f C hC i b
  · exact quotientDifferential_boundarySum f C hC
  · intro i p
    constructor
    · intro hp
      have hp1 : p.1 = 0 := congrArg Prod.snd hp
      refine ⟨(p.2, 0), ?_⟩
      exact Prod.ext hp1.symm rfl
    · rintro ⟨⟨a, b⟩, rfl⟩
      rfl
  · refine ⟨cohomologyDifferential f C hC, ?_, cohomologyDifferential_comp f C hC⟩
    intro i q
    exact (cohomologyDifferential_mk f C hC i q).symm
  · intro i x hx
    refine ⟨(fpow_mem_term_iff f C hC i x).mp hx, ?_⟩
    exact Subtype.ext (cycleProjection_fpow f C hC i x hx)

end

end Stacks.Eta.Reduction

/-! ## The fractional-power filtration and its Bockstein operator (Tag 0GSP) -/

namespace Stacks.EtaComplex.FractionalPowerBockstein

noncomputable section

-- The cokernels of the fractional-power inclusions are compared up to defeq throughout.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open EtaPow

variable {A : Type u} [CommRing A]

/-- The fractional power ideal `fⁱA ⊆ A[1/f]`, as an `A`-module. -/
abbrev fractionalPowerIdeal (f : A) (i : ℤ) : ModuleCat.{u} A :=
  ModuleCat.of A (fpowSub f A i)

/-- Consecutive fractional powers are nested: `fⁱ⁺¹A ⊆ fⁱA`. -/
lemma fractionalPowerIdeal_succ_le (f : A) (i : ℤ) :
    fpowSub f A (i + 1) ≤ fpowSub f A i := by
  intro x hx
  rw [mem_fpowSub] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  refine ⟨f * a, ?_⟩
  change Stacks.GradedLaurent.awayUnit f ^ i • (toLoc f A) (f • a) = _
  rw [map_smul, ← fUnit_units_smul, ← mul_smul, ← zpow_add_one]

/-- The canonical inclusion `fⁱ⁺¹A → fⁱA` inside `A[1/f]`. -/
def fractionalPowerInclusion (f : A) (i : ℤ) :
    fractionalPowerIdeal f (i + 1) ⟶ fractionalPowerIdeal f i :=
  ModuleCat.ofHom (Submodule.inclusion (fractionalPowerIdeal_succ_le f i))

/-- The functor `N ↦ M• ⊗_A N`, using `N` as a complex concentrated in degree zero. -/
abbrev tensorWithCochainComplex (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CategoryTheory.Functor (ModuleCat.{u} A) (CochainComplex (ModuleCat.{u} A) ℤ) :=
  HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0 ⋙
    (MonoidalCategory.curriedTensor (ModuleCat.{u} A)).map₂CochainComplex.obj M

/-- The functor `tensorWithCochainComplex M` sends the zero morphism to zero. -/
@[simp]
lemma tensorWithCochainComplex_map_zero
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (X Y : ModuleCat.{u} A) :
    (tensorWithCochainComplex M).map (0 : X ⟶ Y) = 0 := by
  change HomologicalComplex.mapBifunctorMap (𝟙 M)
      ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).map
        (0 : X ⟶ Y)) _ _ = 0
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp

/-- The canonical inclusion `F₁/F₂ → F₀/F₂`. -/
def quotientInclusion {F₀ F₁ F₂ : ModuleCat.{u} A}
    (a : F₂ ⟶ F₁) (b : F₁ ⟶ F₀) : cokernel a ⟶ cokernel (a ≫ b) :=
  cokernel.desc a (b ≫ cokernel.π (a ≫ b)) (by
    simpa only [Category.assoc] using cokernel.condition (a ≫ b))

/-- The canonical projection `F₀/F₂ → F₀/F₁`. -/
def quotientProjection {F₀ F₁ F₂ : ModuleCat.{u} A}
    (a : F₂ ⟶ F₁) (b : F₁ ⟶ F₀) : cokernel (a ≫ b) ⟶ cokernel b :=
  cokernel.desc (a ≫ b) (cokernel.π b) (by
    simp only [Category.assoc, cokernel.condition, comp_zero])

/-- The upper row `M ⊗ fⁱ⁺¹A → M ⊗ fⁱA → M ⊗ (fⁱA/fⁱ⁺¹A)`. -/
def powerIdealShortComplex (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (i : ℤ) : ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  let T := tensorWithCochainComplex M
  let b := fractionalPowerInclusion f i
  ShortComplex.mk (T.map b) (T.map (cokernel.π b)) (by
    rw [← T.map_comp, cokernel.condition]
    exact tensorWithCochainComplex_map_zero M _ _)

/-- The lower row `M ⊗ (fⁱ⁺¹A/fⁱ⁺²A) → M ⊗ (fⁱA/fⁱ⁺²A) →
M ⊗ (fⁱA/fⁱ⁺¹A)` defining the Bockstein operator. -/
def successivePowerQuotientShortComplex
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A) (i : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  let T := tensorWithCochainComplex M
  let a := fractionalPowerInclusion f (i + 1)
  let b := fractionalPowerInclusion f i
  ShortComplex.mk (T.map (quotientInclusion a b)) (T.map (quotientProjection a b)) (by
    rw [← T.map_comp]
    have hzero : quotientInclusion a b ≫ quotientProjection a b = 0 := by
      apply (cancel_epi (cokernel.π a)).1
      simp [quotientInclusion, quotientProjection, Category.assoc]
    rw [hzero]
    exact tensorWithCochainComplex_map_zero M _ _)

/-- The canonical morphism from the unquotiented row to the successive-quotient row. -/
def powerIdealBocksteinDiagram
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A) (i : ℤ) :
    powerIdealShortComplex M f i ⟶ successivePowerQuotientShortComplex M f i :=
  let T := tensorWithCochainComplex M
  let a := fractionalPowerInclusion f (i + 1)
  let b := fractionalPowerInclusion f i
  { τ₁ := T.map (cokernel.π a)
    τ₂ := T.map (cokernel.π (a ≫ b))
    τ₃ := 𝟙 _
    comm₁₂ := by
      change T.map (cokernel.π a) ≫ T.map (quotientInclusion a b) =
        T.map b ≫ T.map (cokernel.π (a ≫ b))
      rw [← T.map_comp, ← T.map_comp]
      congr 1
      simp [quotientInclusion]
    comm₂₃ := by
      change T.map (cokernel.π (a ≫ b)) ≫ T.map (quotientProjection a b) =
        T.map (cokernel.π b) ≫ 𝟙 _
      rw [← T.map_comp, Category.comp_id]
      congr 1
      simp [quotientProjection] }

/-- The Bockstein operator in degree `n`, the connecting morphism of the lower row. -/
def powerBocksteinOperator (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (i n : ℤ) (hLower : (successivePowerQuotientShortComplex M f i).ShortExact) :
    (successivePowerQuotientShortComplex M f i).X₃.homology n ⟶
      (successivePowerQuotientShortComplex M f i).X₁.homology (n + 1) :=
  hLower.δ n (n + 1) (by simp [ComplexShape.up])

open CategoryTheory.MonoidalCategory HomologicalComplex

/-- The only nonzero summand in degree `n` of `M ⊗ N[0]` is `Mⁿ ⊗ N`. -/
def tensorSingleTermIso (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : ModuleCat.{u} A) (n : ℤ) :
    M.X n ⊗ N ≅ ((tensorWithCochainComplex M).obj N).X n := by
  let K := (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).obj N
  let F := curriedTensor (ModuleCat A)
  let e := singleObjXSelf (ComplexShape.up ℤ) 0 N
  let j := ιMapBifunctor M K F (ComplexShape.up ℤ) n 0 n (by simp)
  let p : (HomologicalComplex.mapBifunctor M K F (ComplexShape.up ℤ)).X n ⟶ (M.X n ⊗ K.X 0) :=
    mapBifunctorDesc fun a b hab =>
      if h : b = 0 then by
        subst b
        have ha : a = n := by simpa using hab
        subst a
        exact 𝟙 _
      else 0
  have hjp : j ≫ p = 𝟙 _ := by
    dsimp [j, p]
    simp
  have hpj : p ≫ j = 𝟙 _ := by
    apply mapBifunctor.hom_ext
    intro a b hab
    by_cases hb : b = 0
    · subst b
      have ha : a = n := by simpa using hab
      subst a
      simp [j, p]
    · have hz := (F.obj (M.X a)).map_isZero
          (isZero_single_obj_X (ComplexShape.up ℤ) 0 N b hb)
      exact hz.eq_of_src _ _
  exact (tensorIso (Iso.refl _) e.symm) ≪≫ ⟨j, p, hjp, hpj⟩

/-- The isomorphism `tensorSingleTermIso M N n : Mⁿ ⊗ N ≅ (M ⊗ N[0])ⁿ` is natural in `N`. -/
lemma tensorSingleTermIso_naturality
    (M : CochainComplex (ModuleCat.{u} A) ℤ) {N P : ModuleCat.{u} A}
    (g : N ⟶ P) (n : ℤ) :
    (M.X n ◁ g) ≫ (tensorSingleTermIso M P n).hom =
      (tensorSingleTermIso M N n).hom ≫ ((tensorWithCochainComplex M).map g).f n := by
  dsimp [tensorSingleTermIso, tensorWithCochainComplex]
  simp only [tensorIso_hom, Iso.refl_hom, Iso.symm_hom, id_tensorHom,
    Functor.map₂HomologicalComplex_obj_map, Category.assoc, ι_mapBifunctorMap,
    curriedTensor_obj_obj, id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    curriedTensor_obj_map, Category.id_comp]
  rw [single_map_f_self]
  simp [whiskerLeft_comp, Category.assoc]

/-- The termwise tensor comparison is natural in the module. -/
def tensorSingleEvalIso (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    tensorLeft (M.X n) ≅ tensorWithCochainComplex M ⋙
      HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n :=
  NatIso.ofComponents (fun N => tensorSingleTermIso M N n)
    (fun g => tensorSingleTermIso_naturality M g n)

/-- A right exact functor sends the cokernel sequence `X → Y → coker g` to an exact sequence. -/
lemma map_cokernel_exact
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [F.PreservesZeroMorphisms]
    [PreservesFiniteColimits F] {X Y : ModuleCat.{u} A} (g : X ⟶ Y) :
    ((ShortComplex.cokernelSequence g).map F).Exact :=
  (ShortComplex.cokernelSequence_exact g).map_of_epi_of_preservesCokernel F
    inferInstance inferInstance

/-- For a right exact functor `F`, an element of `F Y` killed by `F (cokernel.π g)` lies in the
image of `F g`. -/
lemma map_cokernel_exact_apply
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [F.PreservesZeroMorphisms]
    [PreservesFiniteColimits F] {X Y : ModuleCat.{u} A} (g : X ⟶ Y)
    (y : F.obj Y) (hy : F.map (cokernel.π g) y = 0) :
    ∃ x, F.map g x = y :=
  (ShortComplex.moduleCat_exact_iff _).mp (map_cokernel_exact F g) y hy

/-- The composite `F₁/F₂ → F₀/F₂ → F₀/F₁` of `quotientInclusion` and `quotientProjection` is
zero. -/
lemma quotientInclusion_comp_projection {X Y Z : ModuleCat.{u} A}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    quotientInclusion a b ≫ quotientProjection a b = 0 := by
  apply (cancel_epi (cokernel.π a)).1
  simp [quotientInclusion, quotientProjection, Category.assoc]

/-- A right exact functor preserves the successive-cokernel sequence when it sends
its outer inclusion to a monomorphism. -/
lemma map_quotient_shortExact
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [F.PreservesZeroMorphisms]
    [PreservesFiniteColimits F] {X Y Z : ModuleCat.{u} A} (a : X ⟶ Y) (b : Y ⟶ Z)
    [Mono (F.map b)] :
    ((ShortComplex.mk (quotientInclusion a b) (quotientProjection a b)
      (quotientInclusion_comp_projection a b)).map F).ShortExact := by
  have h₁ : F.map (cokernel.π a) ≫ F.map (quotientInclusion a b) =
      F.map b ≫ F.map (cokernel.π (a ≫ b)) := by
    simp only [← F.map_comp, quotientInclusion, cokernel.π_desc]
  have h₂ : F.map (cokernel.π (a ≫ b)) ≫ F.map (quotientProjection a b) =
      F.map (cokernel.π b) := by
    simp only [← F.map_comp, quotientProjection, cokernel.π_desc]
  have hmono : Mono (F.map (quotientInclusion a b)) := by
    rw [ModuleCat.mono_iff_injective]
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (F.map (cokernel.π a))).mp
      inferInstance x
    have hy : F.map (cokernel.π (a ≫ b)) (F.map b y) = 0 := by
      rw [← ModuleCat.comp_apply, ← h₁]
      exact hx
    obtain ⟨z, hz⟩ := map_cokernel_exact_apply F (a ≫ b) _ hy
    have hzy : F.map a z = y := (ModuleCat.mono_iff_injective (F.map b)).mp
      inferInstance (by simpa only [F.map_comp, ModuleCat.comp_apply] using hz)
    rw [← hzy, ← ModuleCat.comp_apply, ← F.map_comp, cokernel.condition, F.map_zero]
    rfl
  refine ShortComplex.ShortExact.mk' ?_ hmono (epi_of_epi_fac h₂)
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective
    (F.map (cokernel.π (a ≫ b)))).mp inferInstance x
  have hy : F.map (cokernel.π b) y = 0 := by
    rw [← h₂]
    exact hx
  obtain ⟨z, hz⟩ := map_cokernel_exact_apply F b y hy
  refine ⟨F.map (cokernel.π a) z, ?_⟩
  change F.map (quotientInclusion a b) (F.map (cokernel.π a) z) = _
  rw [← ModuleCat.comp_apply, h₁, ModuleCat.comp_apply, hz]

/-- Multiplication by `fⁱ` identifies `A` with its fractional power ideal. -/
def fractionalPowerIso (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    ModuleCat.of A A ≅ fractionalPowerIdeal f i := by
  let g := (EtaPow.fpowMap f A i).codRestrict (EtaPow.fpowSub f A i)
    (fun x => (EtaPow.fpowSub_eq_range i).ge ⟨x, rfl⟩)
  refine (LinearEquiv.ofBijective g ⟨?_, ?_⟩).toModuleIso
  · intro x y h
    apply EtaPow.toLoc_injective_of_isSMulRegular (f := f) (M := A)
      (EtaPow.isSMulRegular_of_smul_eq_zero (f := f) (M := A)
        (fun x hx => (mem_nonZeroDivisors_iff.mp hf).1 x hx))
    exact EtaPow.fUnit_zpow_smul_injective i (congrArg Subtype.val h)
  · intro x
    obtain ⟨y, hy⟩ := EtaPow.mem_fpowSub.mp x.property
    exact ⟨y, Subtype.ext hy⟩

/-- The isomorphism `fractionalPowerIso f hf i` sends `x` to `fⁱ x` in `A[1/f]`. -/
lemma fractionalPowerIso_hom_apply (f : A) (hf : f ∈ nonZeroDivisors A)
    (i : ℤ) (x : A) :
    ((fractionalPowerIso f hf i).hom x : EtaPow.Loc f A) =
      Stacks.GradedLaurent.awayUnit f ^ i • EtaPow.toLoc f A x := rfl

/-- Under `fractionalPowerIso`, the inclusion `fⁱ⁺¹A → fⁱA` corresponds to multiplication by `f`
on `A`. -/
lemma fractionalPowerIso_hom_inclusion (f : A)
    (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    (fractionalPowerIso f hf (i + 1)).hom ≫ fractionalPowerInclusion f i =
      (f • 𝟙 (ModuleCat.of A A)) ≫ (fractionalPowerIso f hf i).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((fractionalPowerIso f hf (i + 1)).hom x : EtaPow.Loc f A) =
    ((fractionalPowerIso f hf i).hom (f • x) : EtaPow.Loc f A)
  rw [fractionalPowerIso_hom_apply, fractionalPowerIso_hom_apply]
  rw [map_smul, ← EtaPow.fUnit_units_smul, ← mul_smul, ← zpow_add_one]

/-- If `f` is a nonzerodivisor on `A` and on `N`, then `N ⊗ fⁱ⁺¹A → N ⊗ fⁱA` is injective. -/
lemma tensorLeft_fractionalPowerInclusion_mono
    (N : ModuleCat.{u} A) (f : A) (hf : f ∈ nonZeroDivisors A)
    (hN : IsSMulRegular N f) (i : ℤ) :
    Mono ((tensorLeft N).map (fractionalPowerInclusion f i)) := by
  have : Mono (f • 𝟙 N) := by
    rw [ModuleCat.mono_iff_injective]
    exact hN
  have hm : Mono (f • 𝟙 (N ⊗ ModuleCat.of A A)) :=
    mono_of_mono_fac (show (f • 𝟙 (N ⊗ ModuleCat.of A A)) ≫ (ρ_ N).hom =
      (ρ_ N).hom ≫ (f • 𝟙 N) by simp)
  have hm' : Mono ((tensorLeft N).map (f • 𝟙 (ModuleCat.of A A))) := by
    rw [Functor.map_smul]
    rw [(tensorLeft N).map_id]
    exact hm
  have : Mono ((tensorLeft N).map (fractionalPowerIso f hf i).hom) :=
    IsIso.mono_of_iso _
  have hc := congrArg ((tensorLeft N).map) (fractionalPowerIso_hom_inclusion f hf i)
  simp only [Functor.map_comp] at hc
  have : Mono ((tensorLeft N).map (fractionalPowerIso f hf (i + 1)).hom ≫
      (tensorLeft N).map (fractionalPowerInclusion f i)) := by
    rw [hc]
    exact (mono_comp_iff_of_mono _ _).mpr hm'
  exact (mono_comp_iff_of_isIso
    ((tensorLeft N).map (fractionalPowerIso f hf (i + 1)).hom) _).mp this

/-- A short complex `S` of modules is sent by `N ↦ M• ⊗_A N` to a short exact sequence of
complexes when `Mⁿ ⊗ S` is short exact for every `n`. -/
lemma tensorWithCochainComplex_map_shortExact
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    [(tensorWithCochainComplex M).PreservesZeroMorphisms]
    (S : ShortComplex (ModuleCat.{u} A))
    (hS : ∀ n, (S.map (tensorLeft (M.X n))).ShortExact) :
    (S.map (tensorWithCochainComplex M)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    ShortComplex.shortExact_of_iso (S.mapNatIso (tensorSingleEvalIso M n)) (hS n)

/-- Both rows of the power-ideal diagram are short exact for torsion-free terms. -/
theorem powerIdealRows_shortExact
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (hM : ∀ n, IsSMulRegular (M.X n) f)
    (i : ℤ) :
    (powerIdealShortComplex M f i).ShortExact ∧
      (successivePowerQuotientShortComplex M f i).ShortExact := by
  have : (tensorWithCochainComplex M).PreservesZeroMorphisms :=
    ⟨tensorWithCochainComplex_map_zero M⟩
  have hUpper : (powerIdealShortComplex M f i).ShortExact := by
    apply tensorWithCochainComplex_map_shortExact M
      (ShortComplex.cokernelSequence (fractionalPowerInclusion f i))
    intro q
    have hm := tensorLeft_fractionalPowerInclusion_mono (M.X q) f hf (hM q) i
    exact ShortComplex.ShortExact.mk' (map_cokernel_exact _ _) hm
      (inferInstance : Epi ((tensorLeft (M.X q)).map
        (cokernel.π (fractionalPowerInclusion f i))))
  have hLower : (successivePowerQuotientShortComplex M f i).ShortExact := by
    apply tensorWithCochainComplex_map_shortExact M
      (ShortComplex.mk _ _ (quotientInclusion_comp_projection
        (fractionalPowerInclusion f (i + 1)) (fractionalPowerInclusion f i)))
    intro q
    have := tensorLeft_fractionalPowerInclusion_mono (M.X q) f hf (hM q) i
    exact map_quotient_shortExact _ _ _
  exact ⟨hUpper, hLower⟩

/-- **Stacks 0GSP.** For the actual fractional power ideals in `A[1/f]`, the Bockstein
operator for the successive-quotient row equals the connecting morphism of the unquotiented
row followed by cohomology of the canonical reduction `fⁱ⁺¹A → fⁱ⁺¹A/fⁱ⁺²A`, after
tensoring both rows with `M`. The definitions above formally identify every object and map
with the power-ideal diagram in the source. -/
@[stacks 0GSP]
theorem powerBocksteinOperator_eq_connectingHom_comp_reduction
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (hM : ∀ n, IsSMulRegular (M.X n) f)
    (i n : ℤ) :
    ∃ (hUpper : (powerIdealShortComplex M f i).ShortExact)
      (hLower : (successivePowerQuotientShortComplex M f i).ShortExact),
      powerBocksteinOperator M f i n hLower =
        hUpper.δ n (n + 1) (by simp [ComplexShape.up]) ≫
          HomologicalComplex.homologyMap
            ((tensorWithCochainComplex M).map
              (cokernel.π (fractionalPowerInclusion f (i + 1)))) (n + 1) := by
  obtain ⟨hUpper, hLower⟩ := powerIdealRows_shortExact f hf M hM i
  refine ⟨hUpper, hLower, ?_⟩
  simpa [powerBocksteinOperator, powerIdealBocksteinDiagram] using
    (HomologicalComplex.HomologySequence.δ_naturality
      (powerIdealBocksteinDiagram M f i) hUpper hLower n (n + 1)
      (by simp [ComplexShape.up])).symm

end

end Stacks.EtaComplex.FractionalPowerBockstein

/-! ## The Bockstein complex (Tag 0GSQ) -/

namespace EtaPow.Bockstein

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaComplex.FractionalPowerBockstein

variable {A : Type u} [CommRing A]

/-- The short exactness of the sequence
`M ⊗ (fⁱ⁺¹A/fⁱ⁺²A) → M ⊗ (fⁱA/fⁱ⁺²A) → M ⊗ (fⁱA/fⁱ⁺¹A)`.
This is the lower row of the power-ideal Bockstein diagram. -/
theorem successivePowerQuotientShortExact (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ) :
    (successivePowerQuotientShortComplex M f i).ShortExact :=
  Classical.choose (Classical.choose_spec
    (powerBocksteinOperator_eq_connectingHom_comp_reduction f hf M hM i i))

/-- The Bockstein map
`Hⁱ(M ⊗ fⁱA/fⁱ⁺¹A) ⟶ Hⁱ⁺¹(M ⊗ fⁱ⁺¹A/fⁱ⁺²A)` induced by the
canonical successive-quotient short exact sequence. -/
def bocksteinOperator (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ) :
    (successivePowerQuotientShortComplex M f i).X₃.homology i ⟶
      (successivePowerQuotientShortComplex M f (i + 1)).X₃.homology (i + 1) :=
  powerBocksteinOperator M f i i (successivePowerQuotientShortExact f hf M hM i)

/-- The canonical Bockstein connecting maps for three consecutive fractional power ideals
form a differential: `βⁱ⁺¹ ∘ βⁱ = 0`.

This is what makes `bocksteinComplex` a complex. -/
theorem bockstein_comp_bockstein (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ) :
    bocksteinOperator f hf M hM i ≫ bocksteinOperator f hf M hM (i + 1) = 0 :=
  by
    obtain ⟨hUpper, hLower, hβ⟩ :=
      powerBocksteinOperator_eq_connectingHom_comp_reduction f hf M hM i i
    let T := tensorWithCochainComplex M
    let a : fractionalPowerIdeal f (i + 1 + 1 + 1) ⟶
        fractionalPowerIdeal f (i + 1 + 1) :=
      fractionalPowerInclusion f (i + 1 + 1)
    let b : fractionalPowerIdeal f (i + 1 + 1) ⟶ fractionalPowerIdeal f (i + 1) :=
      fractionalPowerInclusion f (i + 1)
    let q : fractionalPowerIdeal f (i + 1) ⟶ cokernel (a ≫ b) :=
      cokernel.π (a ≫ b)
    have hq : T.map q ≫ T.map (quotientProjection a b) = T.map (cokernel.π b) := by
      rw [← T.map_comp]
      congr 1
      simp [q, quotientProjection]
    have hhom : HomologicalComplex.homologyMap (T.map q) (i + 1) ≫
        HomologicalComplex.homologyMap (T.map (quotientProjection a b)) (i + 1) =
        HomologicalComplex.homologyMap (T.map (cokernel.π b)) (i + 1) := by
      rw [← HomologicalComplex.homologyMap_comp, hq]
    let hr : (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) := by simp
    have hcomp :=
      (successivePowerQuotientShortExact f hf M hM (i + 1)).comp_δ
        (i + 1) (i + 1 + 1) hr
    change HomologicalComplex.homologyMap (T.map (quotientProjection a b)) (i + 1) ≫
        (successivePowerQuotientShortExact f hf M hM (i + 1)).δ
          (i + 1) (i + 1 + 1) hr = 0 at hcomp
    have hzero : HomologicalComplex.homologyMap (T.map (cokernel.π b)) (i + 1) ≫
        (successivePowerQuotientShortExact f hf M hM (i + 1)).δ
          (i + 1) (i + 1 + 1) hr = 0 := by
      dsimp [successivePowerQuotientShortComplex] at hcomp ⊢
      rw [← hhom, Category.assoc, hcomp]
      exact comp_zero
    change powerBocksteinOperator M f i i (successivePowerQuotientShortExact f hf M hM i) ≫
        powerBocksteinOperator M f (i + 1) (i + 1)
          (successivePowerQuotientShortExact f hf M hM (i + 1)) = 0
    rw [hβ]
    dsimp [powerBocksteinOperator, powerIdealShortComplex,
      successivePowerQuotientShortComplex, T, b] at hzero ⊢
    rw [Category.assoc]
    rw [hzero]
    exact comp_zero

/-- **Stacks 0GSQ.** The complex `Hᵇ(M/f)` has term
`Hⁱ(M ⊗ fⁱA/fⁱ⁺¹A)` in degree `i` and the canonical Bockstein map as its differential. -/
@[stacks 0GSQ]
def bocksteinComplex (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.of
    (fun i ↦ (successivePowerQuotientShortComplex M f i).X₃.homology i)
    (bocksteinOperator f hf M hM)
    (by intro i; exact bockstein_comp_bockstein f hf M hM i)

/-- The degree-`i` term of the Bockstein complex is the cohomology of the
corresponding fractional-power quotient complex. -/
@[simp]
theorem bocksteinComplex_X (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ) :
    (bocksteinComplex f hf M hM).X i =
      (successivePowerQuotientShortComplex M f i).X₃.homology i := rfl

/-- The differential of the Bockstein complex is the connecting morphism of the
successive-quotient short exact sequence. -/
theorem bocksteinComplex_d (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ) :
    (bocksteinComplex f hf M hM).d i (i + 1) = bocksteinOperator f hf M hM i := by
  simp only [bocksteinComplex, CochainComplex.of_d]

end

end EtaPow.Bockstein

/-! ## The eta complex modulo a nonzerodivisor (Tag 0F7T) -/

namespace Stacks.EtaComplex.ModNonzerodivisor

open Stacks.EtaComplex.FractionalPowerBockstein

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open scoped nonZeroDivisors TensorProduct

variable {A : Type u} [CommRing A]

/-- The tensor complex `η_f M ⊗_A A/fA`. -/
abbrev etaTensorMod (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  (Stacks.EtaComplex.FractionalPowerBockstein.tensorWithCochainComplex (EtaComplex.etaObject.{u, u}
    f M)).obj
    (ModuleCat.of A (A ⧸ Ideal.span {f}))

/-- The class of `fⁱ` in `fⁱA/fⁱ⁺¹A`. -/
noncomputable def fractionalPowerClass (f : A) (i : ℤ) :
    (cokernel (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerInclusion f i) :
      ModuleCat.{u} A) :=
  (cokernel.π (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerInclusion f i)).hom
    ⟨EtaPow.fpowMap f A i 1, EtaPow.mem_fpowSub.mpr ⟨1, rfl⟩⟩

/-- The representative `x' ⊗ fⁱ` in the degree-`i` term of
`M ⊗ (fⁱA/fⁱ⁺¹A)`. -/
noncomputable def bocksteinRepresentative
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A) (i : ℤ) (x : M.X i) :
    (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f i).X₃.X i :=
  (Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso M
      (cokernel (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerInclusion f i)) i).hom
    (x ⊗ₜ[A] fractionalPowerClass f i)

/-- The standard degreewise equivalence
`(η_f M)ⁱ ⊗_A A/fA ≅ (η_f M)ⁱ/f(η_f M)ⁱ`. -/
noncomputable def etaTensorQuotientTermIso
    (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (EtaComplex.etaObject f M).X i ⊗ ModuleCat.of A (A ⧸ Ideal.span {f}) ≅
      (EtaComplex.quotientObject f M).X i :=
  LinearEquiv.toModuleIso
    (TensorProduct.tensorQuotEquivQuotSMul (EtaComplex.term f M i) (Ideal.span {f}) ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (by
        rw [Submodule.ideal_span_singleton_smul]
        rw [Submodule.pointwise_smul_def, Submodule.map_top]
        congr 1))

/-- The assertion that `x' ⊗ fⁱ` is a cocycle in
`M ⊗ (fⁱA/fⁱ⁺¹A)`. -/
abbrev IsBocksteinRepresentativeCycle
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A) (i : ℤ) (x : M.X i) : Prop :=
  ((Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f i).X₃.d i (i
    + 1)).hom
    (bocksteinRepresentative M f i x) = 0

/-- The cohomology class of a cocycle `x' ⊗ fⁱ`. -/
noncomputable def bocksteinRepresentativeClass
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A) (i : ℤ) (x : M.X i)
    (hx : IsBocksteinRepresentativeCycle M f i x) :
    (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
      i).X₃.homology i :=
  ((Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
    i).X₃.homologyπ i).hom
    ((Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
      i).X₃.cyclesMk
      (bocksteinRepresentative M f i x) (i + 1) (by simp) hx)

section EtaBocksteinConstruction

-- The tensor total complex is compared with its single nonzero summand up to defeq.
set_option backward.isDefEq.respectTransparency false

private lemma tensorSingleTermIso_d
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (N : ModuleCat.{u} A) (i : ℤ) :
    (Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso M N i).hom ≫
        ((Stacks.EtaComplex.FractionalPowerBockstein.tensorWithCochainComplex M).obj N).d i (i + 1)
          =
      (M.d i (i + 1) ▷ N) ≫ (Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso M N (i +
        1)).hom := by
  change (Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso M N i).hom ≫
      (mapBifunctor M ((single (ModuleCat A) (ComplexShape.up ℤ) 0).obj N)
        (curriedTensor (ModuleCat A)) (ComplexShape.up ℤ)).d i (i + 1) = _
  dsimp only [Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso]
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom, id_tensorHom,
    Category.assoc, mapBifunctor.d_eq, Preadditive.comp_add,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
  rw [mapBifunctor.d₁_eq _ _ _ _ (show i + 1 = i + 1 from rfl) _ _ (by simp),
    mapBifunctor.d₂_eq _ _ _ _ _ (show (0 : ℤ) + 1 = 1 from rfl) _ (by simp)]
  simp [HomologicalComplex.single_obj_d, MonoidalCategory.whisker_exchange_assoc]

private lemma etaTensorQuotientTermIso_tmul
    (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (x : EtaComplex.term f M i) (a : A) :
    (etaTensorQuotientTermIso f M i).hom (x ⊗ₜ[A] Ideal.Quotient.mk _ a) =
      Submodule.Quotient.mk (a • x) := by
  change (Submodule.quotEquivOfEq _ _ (by
    rw [Submodule.ideal_span_singleton_smul]
    rw [Submodule.pointwise_smul_def, Submodule.map_top]
    congr 1))
    (TensorProduct.tensorQuotEquivQuotSMul _ _ (x ⊗ₜ[A] Ideal.Quotient.mk _ a)) = _
  rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
  rfl

-- The component maps unfold both the eta complex and the tensor total complex.
private def tensorQuotientIso
    (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    etaTensorMod f M ≅ EtaComplex.quotientObject.{u, u} f M :=
  HomologicalComplex.Hom.isoOfComponents
    (C₁ := etaTensorMod f M) (C₂ := EtaComplex.quotientObject.{u, u} f M)
    (fun i => (Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso
      (EtaComplex.etaObject.{u, u} f M)
      (ModuleCat.of A (A ⧸ Ideal.span {f})) i).symm ≪≫
        etaTensorQuotientTermIso f M i) (by
      intro i j hij
      subst j
      change ((Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso
        (EtaComplex.etaObject.{u, u} f M)
        (ModuleCat.of A (A ⧸ Ideal.span {f})) i).inv ≫
          (etaTensorQuotientTermIso f M i).hom) ≫ _ =
        _ ≫ (Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso
          (EtaComplex.etaObject.{u, u} f M)
          (ModuleCat.of A (A ⧸ Ideal.span {f})) (i + 1)).inv ≫
            (etaTensorQuotientTermIso f M (i + 1)).hom
      apply (cancel_epi (Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso
        (EtaComplex.etaObject.{u, u} f M)
        (ModuleCat.of A (A ⧸ Ideal.span {f})) i).hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [Category.assoc, tensorSingleTermIso_d]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      simp only [EtaComplex.quotientObject_d, EtaComplex.etaObject_d]
      symm
      change (etaTensorQuotientTermIso f M (i + 1)).hom
        (EtaComplex.etaDifferential f M i x ⊗ₜ[A] Ideal.Quotient.mk _ a) =
          EtaComplex.quotientDifferential f M i
            ((etaTensorQuotientTermIso f M i).hom (x ⊗ₜ[A] Ideal.Quotient.mk _ a))
      rw [etaTensorQuotientTermIso_tmul, etaTensorQuotientTermIso_tmul,
        EtaComplex.quotientDifferential_mk, map_smul])

/-- The degree-`n` term of `M ⊗ f^k A` is `M^n`, the fractional power ideal `f^k A` being free
of rank one on the generator `f^k`. -/
public def powerTermIso
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (k n : ℤ) :
    M.X n ≅ ((Stacks.EtaComplex.FractionalPowerBockstein.tensorWithCochainComplex M).obj
      (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerIdeal f k)).X n :=
  (ρ_ (M.X n)).symm ≪≫
    tensorIso (Iso.refl _) (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerIso f hf k) ≪≫
      Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso M _ n

/-- `powerTermIso` is a map of complexes. -/
public lemma powerTermIso_d
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (k n : ℤ) :
    (powerTermIso f hf M k n).hom ≫
        ((Stacks.EtaComplex.FractionalPowerBockstein.tensorWithCochainComplex M).obj
          (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerIdeal f k)).d n (n + 1) =
      M.d n (n + 1) ≫ (powerTermIso f hf M k (n + 1)).hom := by
  simp only [powerTermIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, id_tensorHom, Category.assoc, tensorSingleTermIso_d]
  rw [MonoidalCategory.whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

/-- **`M ⊗ f^k A` is `M` itself**, as complexes: degreewise `powerTermIso`. -/
public def powerComplexIso
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (k : ℤ) :
    M ≅ (Stacks.EtaComplex.FractionalPowerBockstein.tensorWithCochainComplex M).obj
      (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerIdeal f k) :=
  HomologicalComplex.Hom.isoOfComponents (powerTermIso f hf M k)
    (by intro n m h; subst m; exact powerTermIso_d f hf M k n)

/-- **The reduction of `M` into the `k`-th successive quotient of the fractional-power
filtration:** the chain map `M ⟶ M ⊗ (f^k A/f^{k+1} A)` given by dividing by `f^k` and reducing.

It is degreewise surjective with kernel the `f`-multiples
(`powerReductionMap_surjective`, `powerReductionMap_eq_zero_iff`), so it exhibits every term of
the right-hand side of the algebraic Bockstein complex as `M^j/f M^j`, uniformly in the twist
`k`.  That presentation is what a consumer outside this file needs in order to compare the
fractional-power filtration with another filtration whose successive quotients are also `M/fM`
— for instance the ideal-power filtration of an invertible ideal sheaf at a stalk. -/
public def powerReductionMap
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (k : ℤ) :
    M ⟶ (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f k).X₃ :=
  (powerComplexIso f hf M k).hom ≫
    (Stacks.EtaComplex.FractionalPowerBockstein.tensorWithCochainComplex M).map
      (cokernel.π (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerInclusion f k))

/-- Under `powerTermIso` the inclusion `f^{k+1} A ⊆ f^k A` becomes multiplication by `f`. -/
public lemma powerTermIso_inclusion
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (k n : ℤ) :
    (powerTermIso f hf M (k + 1) n).hom ≫
        ((Stacks.EtaComplex.FractionalPowerBockstein.tensorWithCochainComplex M).map
          (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerInclusion f k)).f n =
      (f • 𝟙 (M.X n)) ≫ (powerTermIso f hf M k n).hom := by
  simp only [powerTermIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, id_tensorHom, Category.assoc]
  rw [← Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso_naturality, ←
    whiskerLeft_comp_assoc,
    Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerIso_hom_inclusion]
  simp

/-- **The reduction into a successive quotient of the fractional-power filtration is degreewise
surjective**, the upper row of the power-ideal diagram being short exact. -/
public lemma powerReductionMap_surjective
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (k n : ℤ) :
    Function.Surjective ((powerReductionMap f hf M k).f n) := by
  have := (Stacks.EtaComplex.FractionalPowerBockstein.powerIdealRows_shortExact f hf M hM k).1.epi_g
  have : Epi ((Stacks.EtaComplex.FractionalPowerBockstein.powerIdealShortComplex M f k).g.f n) :=
    inferInstance
  exact ((ModuleCat.epi_iff_surjective _).mp this).comp
    ((ModuleCat.epi_iff_surjective (powerTermIso f hf M k n).hom).mp inferInstance)

/-- **The kernel of the reduction into a successive quotient of the fractional-power filtration
is exactly the submodule of `f`-multiples**, so that quotient is `M^n/f M^n`. -/
public lemma powerReductionMap_eq_zero_iff
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (k n : ℤ) (x : M.X n) :
    (powerReductionMap f hf M k).f n x = 0 ↔ ∃ y : M.X n, f • y = x := by
  have hs := (Stacks.EtaComplex.FractionalPowerBockstein.powerIdealRows_shortExact f hf M hM k).1
  have he := ShortComplex.moduleCat_exact_iff
    ((Stacks.EtaComplex.FractionalPowerBockstein.powerIdealShortComplex M f k).map
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n))
  have hex := he.mp ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hs n).exact
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hex _ hx
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective
      (powerTermIso f hf M (k + 1) n).hom).mp inferInstance y
    refine ⟨y, (ModuleCat.mono_iff_injective
      (powerTermIso f hf M k n).hom).mp inferInstance ?_⟩
    have heq := ConcreteCategory.congr_hom (powerTermIso_inclusion f hf M k n) y
    exact heq.symm.trans hy
  · rintro ⟨y, rfl⟩
    have heq := ConcreteCategory.congr_hom (powerTermIso_inclusion f hf M k n) y
    change (Stacks.EtaComplex.FractionalPowerBockstein.powerIdealShortComplex M f k).g.f n
      ((powerTermIso f hf M k n).hom (f • y)) = 0
    change ((Stacks.EtaComplex.FractionalPowerBockstein.tensorWithCochainComplex M).map
      (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerInclusion f k)).f n
        ((powerTermIso f hf M (k + 1) n).hom y) =
      (powerTermIso f hf M k n).hom (f • y) at heq
    rw [← heq]
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom
        (Stacks.EtaComplex.FractionalPowerBockstein.powerIdealShortComplex M f k).zero n) _

-- Normalizing the tensor component unfolds the single-term total complex.
/-- **In degree `i` the reduction into the `i`-th successive quotient sends `x` to `x ⊗ f^i`** —
the element named by `bocksteinRepresentative`, which is the representative the source writes
down.  This is the bridge between the two presentations of one and the same term of the
algebraic Bockstein complex: `powerReductionMap`, surjective with kernel the `f`-multiples, and
the pure tensor `x ⊗ f^i`.  A consumer comparing the fractional-power filtration with another
filtration whose successive quotients are also `M/fM` needs both — the first to present the
term, the second to read `etaQuotientToBockstein_mk`. -/
public lemma powerReductionMap_representative
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) (x : M.X i) :
    (powerReductionMap f hf M i).f i x = bocksteinRepresentative M f i x := by
  dsimp only [powerReductionMap, powerComplexIso, HomologicalComplex.Hom.isoOfComponents,
    HomologicalComplex.comp_f, powerTermIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, tensorIso_hom, Iso.refl_hom, id_tensorHom,
    ← Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso_naturality]
  rfl

private lemma cyclesMk_val (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) (x : C.X i) (hx : C.d i (i + 1) x = 0) :
    C.iCycles i (C.cyclesMk x (i + 1) (by simp) hx) = x :=
  C.i_cyclesMk x (i + 1) (by simp) hx

/-- The inclusion of cycles into the underlying module is injective. -/
private lemma iCycles_injective (C : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    Function.Injective (C.iCycles i) :=
  (ModuleCat.mono_iff_injective (C.iCycles i)).mp inferInstance

private lemma chain_comm_apply {C D : CochainComplex (ModuleCat.{u} A) ℤ}
    (p : C ⟶ D) (i j : ℤ) (x : C.X i) :
    D.d i j (p.f i x) = p.f j (C.d i j x) :=
  ConcreteCategory.congr_hom (p.comm i j) x

private def homologyClass (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) (x : C.X i) (hx : C.d i (i + 1) x = 0) : C.homology i :=
  C.homologyπ i (C.cyclesMk x (i + 1) (by simp) hx)

private lemma homologyClass_eq_zero_iff (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) (x : C.X i) (hx : C.d i (i + 1) x = 0) :
    homologyClass C i x hx = 0 ↔ ∃ y : C.X (i - 1), C.d (i - 1) i y = x := by
  have hi := (ModuleCat.mono_iff_injective (C.homologyι i)).mp inferInstance
  rw [← hi.eq_iff]
  change C.homologyι i (C.homologyπ i (C.cyclesMk x (i + 1) (by simp) hx)) =
    C.homologyι i 0 ↔ _
  rw [map_zero, ← ModuleCat.comp_apply, HomologicalComplex.homology_π_ι]
  simp only [ModuleCat.comp_apply, cyclesMk_val]
  have h := (C.sc i).moduleCat_pOpcycles_eq_zero_iff x
  change C.pOpcycles i x = 0 ↔
    ∃ y : C.X ((ComplexShape.up ℤ).prev i), C.d ((ComplexShape.up ℤ).prev i) i y = x at h
  rw [CochainComplex.prev ℤ i] at h
  exact h

private lemma homologyClass_surjective (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) (h : C.homology i) :
    ∃ (x : C.X i) (hx : C.d i (i + 1) x = 0), homologyClass C i x hx = h := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ i)).mp inferInstance h
  have hx : C.d i (i + 1) (C.iCycles i z) = 0 :=
    ConcreteCategory.congr_hom (C.iCycles_d i (i + 1)) z
  refine ⟨C.iCycles i z, hx, ?_⟩
  dsimp only [homologyClass]
  congr 1
  exact iCycles_injective C i (C.i_cyclesMk _ _ _ _)

private lemma fpow_injective (f : A) {N : Type u} [AddCommGroup N] [Module A N]
    (hN : IsSMulRegular N f) (i : ℤ) : Function.Injective (EtaPow.fpowMap f N i) :=
  fun _ _ h => EtaPow.toLoc_injective_of_isSMulRegular hN
    (EtaPow.fUnit_zpow_smul_injective i h)

-- Extract the unique coefficient of an eta representative.
private def coefficient (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ i, IsSMulRegular (M.X i) f) (i : ℤ) :
    EtaComplex.term f M i →ₗ[A] M.X i :=
  (LinearEquiv.ofInjective (EtaPow.fpowMap f (M.X i) i)
    (fpow_injective f (hM i) i)).symm.toLinearMap.comp
      ((EtaComplex.term f M i).subtype.codRestrict
        (LinearMap.range (EtaPow.fpowMap f (M.X i) i)) fun x => by
          rw [← EtaPow.fpowSub_eq_range]
          exact x.2.1)

private lemma fpow_coefficient (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ i, IsSMulRegular (M.X i) f) (i : ℤ) (x : EtaComplex.term f M i) :
    EtaPow.fpowMap f (M.X i) i (coefficient f M hM i x) = x :=
  congrArg Subtype.val
    ((LinearEquiv.ofInjective (EtaPow.fpowMap f (M.X i) i)
      (fpow_injective f (hM i) i)).apply_symm_apply
        ⟨x, by rw [← EtaPow.fpowSub_eq_range]; exact x.2.1⟩)

private lemma coefficient_d (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ i, IsSMulRegular (M.X i) f) (i : ℤ) (x : EtaComplex.term f M i) :
    M.d i (i + 1) (coefficient f M hM i x) =
      f • coefficient f M hM (i + 1) (EtaComplex.etaDifferential f M i x) := by
  apply fpow_injective f (hM (i + 1)) i
  rw [← Stacks.Eta.Reduction.fpow_succ, fpow_coefficient, ← Stacks.Eta.Reduction.locD_fpow,
    fpow_coefficient]
  rfl

private lemma fpow_mem_term (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) (x : M.X i) (y : M.X (i + 1)) (hxy : M.d i (i + 1) x = f • y) :
    EtaPow.fpowMap f (M.X i) i x ∈ EtaComplex.term f M i := by
  rw [EtaComplex.mem_term]
  refine ⟨EtaPow.mem_fpowSub.mpr ⟨x, rfl⟩, ?_⟩
  rw [Stacks.Eta.Reduction.locD_fpow]
  exact EtaPow.mem_fpowSub.mpr
    ⟨y, (Stacks.Eta.Reduction.fpow_succ f i y).trans (congrArg _ hxy.symm)⟩

private lemma powerReductionMap_cycle
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ) (x : EtaComplex.term f M i) :
    (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f i).X₃.d i (i
      + 1)
      ((powerReductionMap f hf M i).f i (coefficient f M hM i x)) = 0 := by
  rw [chain_comm_apply, coefficient_d]
  exact (powerReductionMap_eq_zero_iff f hf M hM i (i + 1) _).mpr ⟨_, rfl⟩

private def etaToCycles
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ) :
    (EtaComplex.etaObject f M).X i ⟶
      (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
        i).X₃.cycles i :=
  (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
    i).X₃.liftCycles
    (ModuleCat.ofHom (((powerReductionMap f hf M i).f i).hom.comp
      (coefficient f M hM i))) (i + 1) (by simp) (by
        exact ModuleCat.hom_ext (LinearMap.ext (powerReductionMap_cycle f hf M hM i)))

private lemma etaToCycles_apply
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ) (x : EtaComplex.term f M i) :
    etaToCycles f hf M hM i x =
      (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
        i).X₃.cyclesMk
        ((powerReductionMap f hf M i).f i (coefficient f M hM i x))
        (i + 1) (by simp) (powerReductionMap_cycle f hf M hM i x) := by
  apply iCycles_injective
  simp only [etaToCycles, ← ModuleCat.comp_apply, HomologicalComplex.liftCycles_i,
    cyclesMk_val]
  rfl

private def quotientToBocksteinTerm
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ) :
    EtaComplex.QuotientTerm f M i →ₗ[A]
      (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
        i).X₃.homology i :=
  Submodule.liftQ _
    ((etaToCycles f hf M hM i ≫
      (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
        i).X₃.homologyπ i).hom) (by
        rintro _ ⟨x, rfl⟩
        change (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
          i).X₃.homologyπ i
          (etaToCycles f hf M hM i (f • x)) = 0
        have hc : etaToCycles f hf M hM i (f • x) = 0 := by
          apply iCycles_injective
          rw [map_zero, etaToCycles_apply, cyclesMk_val, map_smul]
          exact (powerReductionMap_eq_zero_iff f hf M hM i i _).mpr ⟨_, rfl⟩
        rw [hc, map_zero])

private lemma quotientToBocksteinTerm_mk
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ) (x : EtaComplex.term f M i) :
    quotientToBocksteinTerm f hf M hM i (Submodule.Quotient.mk x) =
      homologyClass _ i ((powerReductionMap f hf M i).f i (coefficient f M hM i x))
        (powerReductionMap_cycle f hf M hM i x) := by
  change (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
    i).X₃.homologyπ i
    (etaToCycles f hf M hM i x) = _
  rw [etaToCycles_apply]
  rfl

private lemma homologyMap_class {C D : CochainComplex (ModuleCat.{u} A) ℤ}
    (g : C ⟶ D) (i : ℤ) (x : C.X i) (hx : C.d i (i + 1) x = 0)
    (hy : D.d i (i + 1) (g.f i x) = 0) :
    HomologicalComplex.homologyMap g i (homologyClass C i x hx) =
      homologyClass D i (g.f i x) hy := by
  dsimp only [homologyClass]
  rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality,
    ModuleCat.comp_apply]
  congr 1
  apply iCycles_injective
  rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply,
    cyclesMk_val, cyclesMk_val]

-- The connecting-map formula involves three nested tensor complexes.
private lemma bockstein_class
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ)
    (x : M.X i) (y : M.X (i + 1)) (hxy : M.d i (i + 1) x = f • y)
    (hx : (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
      i).X₃.d i (i + 1)
      ((powerReductionMap f hf M i).f i x) = 0)
    (hy : (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f (i +
      1)).X₃.d
      (i + 1) (i + 1 + 1) ((powerReductionMap f hf M (i + 1)).f (i + 1) y) = 0) :
    EtaPow.Bockstein.bocksteinOperator f hf M hM i
      (homologyClass _ i ((powerReductionMap f hf M i).f i x) hx) =
        homologyClass _ (i + 1) ((powerReductionMap f hf M (i + 1)).f (i + 1) y) hy := by
  obtain ⟨hUpper, hLower, hβ⟩ :=
    powerBocksteinOperator_eq_connectingHom_comp_reduction f hf M hM i i
  have heq : (Stacks.EtaComplex.FractionalPowerBockstein.powerIdealShortComplex M f i).f.f (i + 1)
      ((powerTermIso f hf M (i + 1) (i + 1)).hom y) =
    (Stacks.EtaComplex.FractionalPowerBockstein.powerIdealShortComplex M f i).X₂.d i (i + 1)
      ((powerTermIso f hf M i i).hom x) := by
    have h₁ := ConcreteCategory.congr_hom (powerTermIso_inclusion f hf M i (i + 1)) y
    have h₂ := ConcreteCategory.congr_hom (powerTermIso_d f hf M i i) x
    change _ = (powerTermIso f hf M i (i + 1)).hom (f • y) at h₁
    change _ = (powerTermIso f hf M i (i + 1)).hom (M.d i (i + 1) x) at h₂
    exact h₁.trans ((congrArg _ hxy).symm.trans h₂.symm)
  have hd := hUpper.δ_apply i (i + 1) (by simp)
    ((powerReductionMap f hf M i).f i x) hx
    ((powerTermIso f hf M i i).hom x) rfl
    ((powerTermIso f hf M (i + 1) (i + 1)).hom y) heq
    (i + 1 + 1) (by simp)
  change Stacks.EtaComplex.FractionalPowerBockstein.powerBocksteinOperator M f i i _ _ = _
  rw [hβ, ModuleCat.comp_apply]
  change HomologicalComplex.homologyMap
    ((Stacks.EtaComplex.FractionalPowerBockstein.tensorWithCochainComplex M).map
      (cokernel.π (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerInclusion f (i + 1))))
        (i + 1)
        ((hUpper.δ i (i + 1) (by simp)) (homologyClass _ i _ hx)) = _
  rw [show (hUpper.δ i (i + 1) (by simp)) (homologyClass _ i _ hx) =
    homologyClass _ (i + 1) ((powerTermIso f hf M (i + 1) (i + 1)).hom y) _ from hd]
  exact homologyMap_class
    ((Stacks.EtaComplex.FractionalPowerBockstein.tensorWithCochainComplex M).map
      (cokernel.π (Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerInclusion f (i + 1))))
    (i + 1) ((powerTermIso f hf M (i + 1) (i + 1)).hom y) _ hy

-- The chain map unfolds the connecting morphism and quotient differential.
private def quotientBocksteinMap
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) :
    EtaComplex.quotientObject f M ⟶ EtaPow.Bockstein.bocksteinComplex f hf M hM where
  f i := ModuleCat.ofHom (quotientToBocksteinTerm f hf M hM i)
  comm' i j hij := by
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change (EtaPow.Bockstein.bocksteinComplex f hf M hM).d i (i + 1)
      (quotientToBocksteinTerm f hf M hM i (Submodule.Quotient.mk x)) =
        quotientToBocksteinTerm f hf M hM (i + 1)
          ((EtaComplex.quotientObject f M).d i (i + 1) (Submodule.Quotient.mk x))
    rw [EtaPow.Bockstein.bocksteinComplex_d, EtaComplex.quotientObject_d]
    change EtaPow.Bockstein.bocksteinOperator f hf M hM i
      (quotientToBocksteinTerm f hf M hM i (Submodule.Quotient.mk x)) =
        quotientToBocksteinTerm f hf M hM (i + 1)
          (EtaComplex.quotientDifferential f M i (Submodule.Quotient.mk x))
    rw [EtaComplex.quotientDifferential_mk, quotientToBocksteinTerm_mk,
      quotientToBocksteinTerm_mk]
    exact bockstein_class f hf M hM i _ _ (coefficient_d f M hM i x) _ _

private lemma quotientToBocksteinTerm_surjective
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (i : ℤ) :
    Function.Surjective (quotientToBocksteinTerm f hf M hM i) := by
  intro h
  obtain ⟨z, hz, rfl⟩ := homologyClass_surjective _ i h
  obtain ⟨x, rfl⟩ := powerReductionMap_surjective f hf M hM i i z
  have hd : (powerReductionMap f hf M i).f (i + 1) (M.d i (i + 1) x) = 0 := by
    rw [← chain_comm_apply]
    exact hz
  obtain ⟨y, hy⟩ := (powerReductionMap_eq_zero_iff f hf M hM i (i + 1) _).mp hd
  let w : EtaComplex.term f M i := ⟨_, fpow_mem_term f M i x y hy.symm⟩
  have hw : coefficient f M hM i w = x :=
    fpow_injective f (hM i) i (fpow_coefficient f M hM i w)
  refine ⟨Submodule.Quotient.mk w, ?_⟩
  rw [quotientToBocksteinTerm_mk]
  simp only [hw]

private lemma d_d_apply (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (i j k : ℤ) (x : C.X i) : C.d j k (C.d i j x) = 0 :=
  ConcreteCategory.congr_hom (C.d_comp_d i j k) x

-- Lift homology classes through a surjection with acyclic kernel.
private lemma quasiIso_of_surjective_of_kernel_cycles
    {C D : CochainComplex (ModuleCat.{u} A) ℤ} (p : C ⟶ D)
    (hs : ∀ i, Function.Surjective (p.f i))
    (hk : ∀ (i j : ℤ), i + 1 = j → ∀ (x : C.X j), p.f j x = 0 →
      C.d j (j + 1) x = 0 →
        ∃ y : C.X i, p.f i y = 0 ∧ C.d i j y = x) :
    QuasiIso p := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap,
    ConcreteCategory.isIso_iff_bijective]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := homologyClass_surjective C i z
    have hpx : D.d i (i + 1) (p.f i x) = 0 := by
      rw [chain_comm_apply, hx, map_zero]
    rw [homologyMap_class p i x hx hpx] at hz
    obtain ⟨y, hy⟩ := (homologyClass_eq_zero_iff D i _ hpx).mp hz
    obtain ⟨w, rfl⟩ := hs (i - 1) y
    have hker : p.f i (x - C.d (i - 1) i w) = 0 := by
      rw [map_sub, ← chain_comm_apply, hy, sub_self]
    have hcycle : C.d i (i + 1) (x - C.d (i - 1) i w) = 0 := by
      rw [map_sub, hx, d_d_apply, sub_self]
    obtain ⟨v, hv, hvd⟩ := hk (i - 1) i (by simp) _ hker hcycle
    apply (homologyClass_eq_zero_iff C i x hx).mpr
    refine ⟨w + v, ?_⟩
    rw [map_add, hvd]
    rw [← add_sub_assoc, add_comm, add_sub_cancel_right]
  · intro z
    obtain ⟨y, hy, rfl⟩ := homologyClass_surjective D i z
    obtain ⟨x, rfl⟩ := hs i y
    have hker : p.f (i + 1) (C.d i (i + 1) x) = 0 := by
      rw [← chain_comm_apply]
      exact hy
    obtain ⟨w, hw, hwd⟩ := hk i (i + 1) rfl _ hker (d_d_apply C _ _ _ x)
    have hxw : C.d i (i + 1) (x - w) = 0 := by
      rw [map_sub, hwd, sub_self]
    have hp : p.f i (x - w) = p.f i x := by rw [map_sub, hw, sub_zero]
    refine ⟨homologyClass C i (x - w) hxw, ?_⟩
    have hz : D.d i (i + 1) (p.f i (x - w)) = 0 := by rw [hp]; exact hy
    rw [homologyMap_class p i _ hxw hz]
    simp only [hp]

private lemma powerReductionMap_eq_iff
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) (k n : ℤ) (x y : M.X n) :
    (powerReductionMap f hf M k).f n x = (powerReductionMap f hf M k).f n y ↔
      (Submodule.Quotient.mk x : (M.X n) ⧸
        LinearMap.range (EtaComplex.scalarMap f (M.X n))) = Submodule.Quotient.mk y := by
  rw [← sub_eq_zero, ← map_sub, powerReductionMap_eq_zero_iff f hf M hM, Submodule.Quotient.eq]
  rfl

private lemma powerReductionMap_class_eq_zero_iff
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f)
    (barD : ∀ i j, ((M.X i) ⧸ LinearMap.range (EtaComplex.scalarMap f (M.X i))) →ₗ[A]
      ((M.X j) ⧸ LinearMap.range (EtaComplex.scalarMap f (M.X j))))
    (hbar : ∀ i (x : M.X i), barD i (i + 1) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (M.d i (i + 1) x))
    (i : ℤ) (x : M.X i)
    (hx : (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex M f
      i).X₃.d i (i + 1)
      ((powerReductionMap f hf M i).f i x) = 0) :
    homologyClass _ i ((powerReductionMap f hf M i).f i x) hx = 0 ↔
      (Submodule.Quotient.mk x : (M.X i) ⧸
        LinearMap.range (EtaComplex.scalarMap f (M.X i))) ∈
          LinearMap.range (barD (i - 1) i) := by
  rw [homologyClass_eq_zero_iff]
  have hb (w : M.X (i - 1)) :
      barD (i - 1) i (Submodule.Quotient.mk w) =
        Submodule.Quotient.mk (M.d (i - 1) i w) := by
    have hh := hbar (i - 1) w
    rw [sub_add_cancel] at hh
    exact hh
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := powerReductionMap_surjective f hf M hM i (i - 1) z
    rw [chain_comm_apply] at hz
    exact ⟨Submodule.Quotient.mk w,
      (hb w).trans ((powerReductionMap_eq_iff f hf M hM i i _ _).mp hz)⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨(powerReductionMap f hf M i).f (i - 1) w, ?_⟩
    rw [chain_comm_apply, powerReductionMap_eq_iff f hf M hM]
    exact (hb w).symm.trans hz

-- The boundary subcomplex of 0F7S is exactly the kernel of the comparison.
set_option maxHeartbeats 400000 in
-- The boundary-subcomplex theorem supplies a large dependent tuple of canonical maps.
private lemma quotientBocksteinMap_quasiIso
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ n, IsSMulRegular (M.X n) f) :
    QuasiIso (quotientBocksteinMap f hf M hM) := by
  have htf : EtaComplex.IsTorsionFree f M :=
    fun i x hx => hM i (hx.trans (smul_zero f).symm)
  obtain ⟨barD, hbar, hbar0, hbarcomp, hBZ, s, s', t, e, hinj, hs,
    ht, hst, hts, hds, hac, he, hdH, htformula, hsformula, hs'formula⟩ :=
    Stacks.Eta.Reduction.exists_boundary_subcomplex_of_etaQuotient f hf M htf
  let B := fun i => LinearMap.range (barD (i - 1) i)
  have hkernel (i : ℤ) (q : EtaComplex.QuotientTerm f M i) :
      quotientToBocksteinTerm f hf M hM i q = 0 ↔
        ∃ a : B (i + 1), ∃ b : B i, s i a + s' i b = q := by
    have htzero : quotientToBocksteinTerm f hf M hM i q = 0 ↔
        (t i q).val ∈ B i := by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [quotientToBocksteinTerm_mk,
        powerReductionMap_class_eq_zero_iff f hf M hM barD hbar]
      let c := coefficient f M hM i x
      have hmem : EtaPow.fpowMap f (M.X i) i c ∈ EtaComplex.term f M i := by
        rw [fpow_coefficient]
        exact x.2
      obtain ⟨hz, htz⟩ := htformula i c hmem
      have hex : (⟨EtaPow.fpowMap f (M.X i) i c, hmem⟩ : EtaComplex.term f M i) = x :=
        Subtype.ext (fpow_coefficient f M hM i x)
      rw [hex] at htz
      rw [htz]
    rw [htzero]
    have hezero : (t i q).val ∈ B i ↔
        (Submodule.Quotient.mk q : EtaComplex.QuotientTerm f M i ⧸
          LinearMap.range (LinearMap.coprod (s i) (s' i))) = 0 := by
      rw [← (e i).injective.eq_iff, map_zero, he,
        Submodule.Quotient.mk_eq_zero]
      rfl
    rw [hezero, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨⟨a, b⟩, h⟩
      exact ⟨a, b, h⟩
    · rintro ⟨a, b, h⟩
      exact ⟨(a, b), h⟩
  apply quasiIso_of_surjective_of_kernel_cycles
    (quotientBocksteinMap f hf M hM)
    (quotientToBocksteinTerm_surjective f hf M hM)
  intro i j hij q hq hdq
  subst j
  change quotientToBocksteinTerm f hf M hM (i + 1) q = 0 at hq
  obtain ⟨a, b, rfl⟩ := (hkernel (i + 1) q).mp hq
  rw [EtaComplex.quotientObject_d] at hdq
  change EtaComplex.quotientDifferential f M (i + 1) (s (i + 1) a + s' (i + 1) b) = 0 at hdq
  rw [hds] at hdq
  have ha : a = 0 := by
    have hzero : LinearMap.coprod (s (i + 1 + 1)) (s' (i + 1 + 1)) (0, a) =
        LinearMap.coprod (s (i + 1 + 1)) (s' (i + 1 + 1)) (0, 0) := by
      simpa only [LinearMap.coprod_apply, map_zero, zero_add, add_zero] using hdq
    exact congrArg Prod.snd (hinj (i + 1 + 1) hzero)
  refine ⟨s i b, ?_, ?_⟩
  · exact (hkernel i _).mpr ⟨b, 0, by rw [map_zero, add_zero]⟩
  · rw [EtaComplex.quotientObject_d]
    change EtaComplex.quotientDifferential f M i (s i b) = _
    simpa only [ha, map_zero, zero_add, add_zero] using hds i b 0

set_option maxHeartbeats 1200000 in
-- The displayed subtype unfolds several nested homological-complex constructions.
/-- The standard tensor--quotient map and the source's representative map to the
Bockstein complex, characterized on pure tensors and eta representatives. -/
-- The subtype records the canonical formulas while the construction helpers remain private.
@[no_expose]
noncomputable def etaBocksteinComparison
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ i, IsSMulRegular (M.X i) f) :
    { p : (etaTensorMod f M ≅ EtaComplex.quotientObject.{u, u} f M) ×
        (EtaComplex.quotientObject.{u, u} f M ⟶
          EtaPow.Bockstein.bocksteinComplex f hf M hM) //
      (∀ i, p.1.hom.f i =
        (Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso (EtaComplex.etaObject f M)
          (ModuleCat.of A (A ⧸ Ideal.span {f})) i).inv ≫
            (etaTensorQuotientTermIso f M i).hom) ∧
      (∀ i (x : EtaComplex.term f M i),
        p.1.hom.f i
            ((Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso (EtaComplex.etaObject f
              M)
              (ModuleCat.of A (A ⧸ Ideal.span {f})) i).hom
              (x ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {f}) 1)) =
          Submodule.Quotient.mk x) ∧
      (∀ i (x : EtaComplex.term f M i) (x' : M.X i)
          (_hx : (x : EtaPow.Loc f (M.X i)) = EtaPow.fpowMap f (M.X i) i x'),
        ∃ hz : IsBocksteinRepresentativeCycle M f i x',
          p.2.f i (Submodule.Quotient.mk x) =
            bocksteinRepresentativeClass M f i x' hz) ∧
      QuasiIso (p.1.hom ≫ p.2) } := by
  let e := tensorQuotientIso f M
  let p := quotientBocksteinMap f hf M hM
  refine ⟨(e, p), ?_, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i x
    change (etaTensorQuotientTermIso f M i).hom
      ((Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso (EtaComplex.etaObject.{u, u}
        f M)
        (ModuleCat.of A (A ⧸ Ideal.span {f})) i).inv
          ((Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso (EtaComplex.etaObject.{u,
            u} f M)
            (ModuleCat.of A (A ⧸ Ideal.span {f})) i).hom
              (x ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {f}) 1))) = _
    have hi := ConcreteCategory.congr_hom
      (Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso (EtaComplex.etaObject.{u, u} f
        M)
        (ModuleCat.of A (A ⧸ Ideal.span {f})) i).hom_inv_id
        (x ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {f}) 1)
    change (Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso (EtaComplex.etaObject.{u,
      u} f M)
      (ModuleCat.of A (A ⧸ Ideal.span {f})) i).inv
        ((Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso (EtaComplex.etaObject.{u,
          u} f M)
          (ModuleCat.of A (A ⧸ Ideal.span {f})) i).hom _) =
      (x ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {f}) 1) at hi
    rw [hi, etaTensorQuotientTermIso_tmul, one_smul]
  · intro i x x' hx
    have hc : coefficient f M hM i x = x' :=
      fpow_injective f (hM i) i ((fpow_coefficient f M hM i x).trans hx)
    have hz : IsBocksteinRepresentativeCycle M f i x' := by
      simpa only [hc, powerReductionMap_representative] using
        powerReductionMap_cycle f hf M hM i x
    refine ⟨hz, ?_⟩
    change quotientToBocksteinTerm f hf M hM i (Submodule.Quotient.mk x) = _
    rw [quotientToBocksteinTerm_mk]
    simp only [hc, powerReductionMap_representative]
    rfl
  · have := quotientBocksteinMap_quasiIso f hf M hM
    exact quasiIso_comp e.hom p

end EtaBocksteinConstruction

/-- The standard identification `η_f M ⊗_A A/fA ≅ η_f M/fη_f M`. -/
noncomputable def etaTensorQuotientIso
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ i, IsSMulRegular (M.X i) f) :
    etaTensorMod f M ≅ EtaComplex.quotientObject.{u, u} f M :=
  (etaBocksteinComparison f hf M hM).1.1

/-- The canonical map from `η_f M/fη_f M` to the Bockstein complex of `M/f`. -/
noncomputable def etaQuotientToBockstein
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ i, IsSMulRegular (M.X i) f) :
    EtaComplex.quotientObject.{u, u} f M ⟶
      EtaPow.Bockstein.bocksteinComplex f hf M hM :=
  (etaBocksteinComparison f hf M hM).1.2

set_option maxHeartbeats 800000 in
-- Elaborating the component formula unfolds the tensor complex in both occurrences.
/-- Degreewise, `etaTensorQuotientIso` is precisely the standard
`TensorProduct.tensorQuotEquivQuotSMul` identification. -/
theorem etaTensorQuotientIso_f
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ i, IsSMulRegular (M.X i) f) (i : ℤ) :
    (etaTensorQuotientIso f hf M hM).hom.f i =
      (Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso (EtaComplex.etaObject f M)
        (ModuleCat.of A (A ⧸ Ideal.span {f})) i).inv ≫
          (etaTensorQuotientTermIso f M i).hom :=
  (etaBocksteinComparison f hf M hM).2.1 i

set_option maxHeartbeats 800000 in
-- Elaborating the representative formula unfolds the tensor complex in both occurrences.
/-- The tensor--quotient identification sends `x ⊗ 1` to the class of `x`. -/
theorem etaTensorQuotientIso_tmul_one
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ i, IsSMulRegular (M.X i) f) (i : ℤ)
    (x : EtaComplex.term f M i) :
    (etaTensorQuotientIso f hf M hM).hom.f i
          ((Stacks.EtaComplex.FractionalPowerBockstein.tensorSingleTermIso (EtaComplex.etaObject f
            M)
            (ModuleCat.of A (A ⧸ Ideal.span {f})) i).hom
            (x ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {f}) 1)) =
        Submodule.Quotient.mk x :=
  (etaBocksteinComparison f hf M hM).2.2.1 i x

/-- If `x = fⁱx'`, the comparison sends the class of `x` to the cohomology
class represented by `x' ⊗ fⁱ`, as in the source. -/
theorem etaQuotientToBockstein_mk
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ i, IsSMulRegular (M.X i) f) (i : ℤ)
    (x : EtaComplex.term f M i) (x' : M.X i)
    (hx : (x : EtaPow.Loc f (M.X i)) = EtaPow.fpowMap f (M.X i) i x') :
    ∃ hz : IsBocksteinRepresentativeCycle M f i x',
      (etaQuotientToBockstein f hf M hM).f i (Submodule.Quotient.mk x) =
        bocksteinRepresentativeClass M f i x' hz :=
  (etaBocksteinComparison f hf M hM).2.2.2.1 i x x' hx

/-- **Stacks 0F7T.** If `f` is a nonzerodivisor and every term of `M` is
`f`-torsion-free, the canonical map from `η_f M ⊗_A A/fA` to the Bockstein
complex of `M/f` is a quasi-isomorphism. -/
@[stacks 0F7T]
theorem etaTensorMod_to_bockstein_quasiIso
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ i, IsSMulRegular (M.X i) f) :
    QuasiIso
      ((etaTensorQuotientIso f hf M hM).hom ≫ etaQuotientToBockstein f hf M hM) :=
  (etaBocksteinComparison f hf M hM).2.2.2.2

end

end Stacks.EtaComplex.ModNonzerodivisor

