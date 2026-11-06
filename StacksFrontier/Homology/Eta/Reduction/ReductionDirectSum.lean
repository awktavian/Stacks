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
public import StacksFrontier.Homology.Eta.Reduction.BoundarySubcomplex
public import StacksFrontier.Homology.Eta.Reduction.BocksteinVanishing

@[expose] public section

-- The eta terms and the tensor total complex are unfolded repeatedly below.

universe u v
/-! ## A direct-sum description of the reduction (Tag 0F7Z) -/

namespace Stacks.Eta.ReductionDirectSum

noncomputable section

open scoped nonZeroDivisors

variable {A : Type u} [CommRing A]

private lemma power_smul_mem (f : A) (M : Type*) [AddCommGroup M] [Module A M]
    (j : ℤ) (x : EtaPow.fpowSub f M j) :
    f • (x : EtaPow.Loc f M) ∈ EtaPow.fpowSub f M (j + 1) := by
  have hx := x.2
  rw [EtaPow.mem_fpowSub] at hx ⊢
  obtain ⟨m, hm⟩ := hx
  rw [← hm]
  refine ⟨m, ?_⟩
  simp only [← EtaPow.fUnit_units_smul, smul_smul, zpow_add_one, mul_comm]

private lemma inv_smul_mem (f : A) (M : Type*) [AddCommGroup M] [Module A M]
    (j : ℤ) {x : EtaPow.Loc f M} (hx : x ∈ EtaPow.fpowSub f M (j + 1)) :
    (Stacks.GradedLaurent.awayUnit f)⁻¹ • x ∈ EtaPow.fpowSub f M j := by
  rw [EtaPow.mem_fpowSub] at hx ⊢
  obtain ⟨m, rfl⟩ := hx
  refine ⟨m, ?_⟩
  rw [smul_smul, ← zpow_neg_one, ← zpow_add]
  congr 2
  omega

private lemma f_smul_inv_smul (f : A) (M : Type*) [AddCommGroup M] [Module A M]
    (x : EtaPow.Loc f M) : f • ((Stacks.GradedLaurent.awayUnit f)⁻¹ • x) = x := by
  rw [← EtaPow.fUnit_units_smul, smul_smul]
  simp

private lemma canonicalAux (f : A) (C : EtaComplex.Complex.{u, v} A) (i : ℤ) :
    let P₀ := EtaPow.fpowSub f (C.X i) i
    let P₁ := EtaPow.fpowSub f (C.X i) (i + 1)
    let Q₀ := EtaPow.fpowSub f (C.X (i + 1)) (i + 1)
    let Q₁ := EtaPow.fpowSub f (C.X (i + 1)) (i + 2)
    ∃ g : EtaComplex.term f C i →ₗ[A]
        (P₀ ⧸ P₁.comap P₀.subtype) × (Q₀ ⧸ Q₁.comap Q₀.subtype),
      (∀ x, g x =
        (Submodule.Quotient.mk (⟨x.1, x.2.1⟩ : P₀),
          Submodule.Quotient.mk
            (⟨EtaPow.fLoc f (C.d i (i + 1)).hom x.1, x.2.2⟩ : Q₀))) ∧
      LinearMap.ker g = LinearMap.range
        (EtaComplex.scalarMap f (EtaComplex.term f C i)) := by
  dsimp
  let l : EtaComplex.term f C i →ₗ[A]
      (EtaPow.fpowSub f (C.X i) i ⧸
        (EtaPow.fpowSub f (C.X i) (i + 1)).comap
          (EtaPow.fpowSub f (C.X i) i).subtype) :=
    Submodule.mkQ _ ∘ₗ
      { toFun := fun x => ⟨x.1, x.2.1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  let r : EtaComplex.term f C i →ₗ[A]
      (EtaPow.fpowSub f (C.X (i + 1)) (i + 1) ⧸
        (EtaPow.fpowSub f (C.X (i + 1)) (i + 2)).comap
          (EtaPow.fpowSub f (C.X (i + 1)) (i + 1)).subtype) :=
    Submodule.mkQ _ ∘ₗ
      { toFun := fun x =>
          ⟨EtaPow.fLoc f (C.d i (i + 1)).hom x.1, x.2.2⟩
        map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
        map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  refine ⟨LinearMap.prod l r, ?_, le_antisymm ?_ ?_⟩
  · intro x
    rfl
  · intro x hx
    have hx' :
        (Submodule.Quotient.mk (⟨x.1, x.2.1⟩ : EtaPow.fpowSub f (C.X i) i),
          Submodule.Quotient.mk
            (⟨EtaPow.fLoc f (C.d i (i + 1)).hom x.1, x.2.2⟩ :
              EtaPow.fpowSub f (C.X (i + 1)) (i + 1))) = 0 := hx
    have hx0 := congrArg Prod.fst hx'
    have hx1 := congrArg Prod.snd hx'
    change Submodule.Quotient.mk _ = 0 at hx0
    change Submodule.Quotient.mk _ = 0 at hx1
    rw [Submodule.Quotient.mk_eq_zero] at hx0 hx1
    have hx1' : EtaPow.fLoc f (C.d i (i + 1)).hom x.1 ∈
        EtaPow.fpowSub f (C.X (i + 1)) (i + 2) := hx1
    let yval := (Stacks.GradedLaurent.awayUnit f)⁻¹ • x.1
    have hy0 : yval ∈ EtaPow.fpowSub f (C.X i) i :=
      inv_smul_mem f _ i hx0
    have hdcomm : EtaPow.fLoc f (C.d i (i + 1)).hom yval =
        (Stacks.GradedLaurent.awayUnit f)⁻¹ • EtaPow.fLoc f (C.d i (i + 1)).hom x.1 :=
      Eta.locMap_units_smul (Submonoid.powers f) _ _ _
    have hy1 : EtaPow.fLoc f (C.d i (i + 1)).hom yval ∈
        EtaPow.fpowSub f (C.X (i + 1)) (i + 1) := by
      rw [hdcomm]
      apply inv_smul_mem f _ (i + 1)
      rwa [show (i + 1) + 1 = i + 2 by ring]
    let y : EtaComplex.term f C i := ⟨yval, hy0, hy1⟩
    exact ⟨y, Subtype.ext (f_smul_inv_smul f _ x.1)⟩
  · rintro _ ⟨x, rfl⟩
    apply Prod.ext
    · change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact power_smul_mem f _ i ⟨x.1, x.2.1⟩
    · change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      change EtaPow.fLoc f (C.d i (i + 1)).hom (f • x.1) ∈
        EtaPow.fpowSub f (C.X (i + 1)) (i + 2)
      rw [map_smul]
      have hh := power_smul_mem f _ (i + 1)
        (⟨EtaPow.fLoc f (C.d i (i + 1)).hom x.1, x.2.2⟩ :
          EtaPow.fpowSub f (C.X (i + 1)) (i + 1))
      rw [show (i + 1) + 1 = i + 2 by ring] at hh
      exact hh

/-- **Stacks 0F7Z.** If cycles modulo `f` lift to cycles modulo `f²`, the canonical
map `(1, dⁱ)` embeds the degree-`i` eta term modulo `f` as a product of a submodule
of `fⁱCⁱ/fⁱ⁺¹Cⁱ` and a submodule of `fⁱ⁺¹Cⁱ⁺¹/fⁱ⁺²Cⁱ⁺¹`. -/
@[stacks 0F7Z]
theorem etaQuotient_range_eq_prod_of_cyclesReduction_surjective
    (f : A) (_hf : f ∈ nonZeroDivisors A)
    (C : EtaComplex.Complex.{u, v} A) (hC : EtaComplex.IsTorsionFree f C)
    (i : ℤ) :
    let mul : ∀ _n : ℕ, ∀ j : ℤ, C.X j →ₗ[A] C.X j := fun n j =>
      { toFun := fun x => (f ^ n) • x
        map_add' := fun x y => smul_add (f ^ n) x y
        map_smul' := fun a x => by simp only [RingHom.id_apply, smul_comm a (f ^ n)] }
    let modTerm : ℕ → ℤ → Type (max u v) := fun n j =>
      (C.X j) ⧸ LinearMap.range (mul n j)
    let dMod : ∀ n j, modTerm n j →ₗ[A] modTerm n (j + 1) := fun n j =>
      Submodule.mapQ _ _ (C.d j (j + 1)).hom (by
        rintro _ ⟨x, rfl⟩
        exact ⟨(C.d j (j + 1)).hom x, by
          exact (map_smul (C.d j (j + 1)).hom (f ^ n) x).symm⟩)
    let reduction : ∀ j, modTerm 2 j →ₗ[A] modTerm 1 j := fun j =>
      Submodule.mapQ _ _ LinearMap.id (by
        rintro _ ⟨x, rfl⟩
        refine ⟨f • x, ?_⟩
        change f ^ 1 • (f • x) = f ^ 2 • x
        simp only [pow_one, pow_two, mul_smul])
    (∀ x : modTerm 1 i, dMod 1 i x = 0 →
      ∃ y : modTerm 2 i, dMod 2 i y = 0 ∧ reduction i y = x) →
    let P₀ := EtaPow.fpowSub f (C.X i) i
    let P₁ := EtaPow.fpowSub f (C.X i) (i + 1)
    let Q₀ := EtaPow.fpowSub f (C.X (i + 1)) (i + 1)
    let Q₁ := EtaPow.fpowSub f (C.X (i + 1)) (i + 2)
    let leftPowerQuotient := P₀ ⧸ P₁.comap P₀.subtype
    let rightPowerQuotient := Q₀ ⧸ Q₁.comap Q₀.subtype
    ∃ (canonical : EtaComplex.QuotientTerm f C i →ₗ[A]
          leftPowerQuotient × rightPowerQuotient)
      (Z : Submodule A leftPowerQuotient) (B : Submodule A rightPowerQuotient),
      (∀ x : EtaComplex.term f C i,
        canonical (Submodule.Quotient.mk x) =
          (Submodule.Quotient.mk (⟨x.1, x.2.1⟩ : P₀),
            Submodule.Quotient.mk
              (⟨EtaPow.fLoc f (C.d i (i + 1)).hom x.1, x.2.2⟩ : Q₀))) ∧
      Function.Injective canonical ∧ LinearMap.range canonical = Z.prod B := by
  dsimp
  intro hlift
  obtain ⟨g, hg, hkill⟩ := canonicalAux f C i
  let canonical := Submodule.liftQ _ g hkill.symm.le
  let Z := LinearMap.range (LinearMap.fst A _ _ ∘ₗ canonical)
  let B := LinearMap.range (LinearMap.snd A _ _ ∘ₗ canonical)
  refine ⟨canonical, Z, B, ?_, ?_, ?_⟩
  · intro x
    exact hg x
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' _ _ hkill.symm
  · rw [show canonical = LinearMap.prod
        (LinearMap.fst A _ _ ∘ₗ canonical)
        (LinearMap.snd A _ _ ∘ₗ canonical) by
      ext q <;> rfl]
    apply LinearMap.range_prod_eq
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨m, hm⟩ := EtaPow.mem_fpowSub.mp x.2.1
    have hmcycle : Submodule.mapQ
        (LinearMap.range
          ({ toFun := fun z : C.X i => (f ^ 1) • z
             map_add' := fun z w => smul_add (f ^ 1) z w
             map_smul' := fun a z => by
               simp only [RingHom.id_apply, smul_comm a (f ^ 1)] } : C.X i →ₗ[A] C.X i))
        (LinearMap.range
          ({ toFun := fun z : C.X (i + 1) => (f ^ 1) • z
             map_add' := fun z w => smul_add (f ^ 1) z w
             map_smul' := fun a z => by
               simp only [RingHom.id_apply, smul_comm a (f ^ 1)] } :
            C.X (i + 1) →ₗ[A] C.X (i + 1)))
        (C.d i (i + 1)).hom (by
          intro _ hz
          obtain ⟨z, rfl⟩ := hz
          exact ⟨(C.d i (i + 1)).hom z, by
            exact (map_smul (C.d i (i + 1)).hom (f ^ 1) z).symm⟩)
        (Submodule.Quotient.mk m) = 0 := by
      change Submodule.Quotient.mk ((C.d i (i + 1)).hom m) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨n, hn⟩ := EtaPow.mem_fpowSub.mp x.2.2
      refine ⟨n, ?_⟩
      apply EtaPow.toLoc_injective_of_isSMulRegular
        (EtaPow.isSMulRegular_of_smul_eq_zero (hC (i + 1)))
      have hd := congrArg (EtaPow.fLoc f (C.d i (i + 1)).hom) hm
      rw [EtaPow.fLoc_zpow_smul, EtaPow.fLoc_toLoc] at hd
      rw [← hn] at hd
      apply EtaPow.fUnit_zpow_smul_injective i
      simp only [pow_one]
      change Stacks.GradedLaurent.awayUnit f ^ i • EtaPow.toLoc f (C.X (i + 1)) (f • n) =
        Stacks.GradedLaurent.awayUnit f ^ i • EtaPow.toLoc f (C.X (i + 1)) ((C.d i (i + 1)).hom m)
      rw [map_smul, ← EtaPow.fUnit_units_smul, smul_smul, ← zpow_add_one]
      exact hd.symm
    obtain ⟨y, hycycle, hyred⟩ := hlift (Submodule.Quotient.mk m) hmcycle
    obtain ⟨m', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hdm' : (C.d i (i + 1)).hom m' ∈
        LinearMap.range
          ({ toFun := fun z : C.X (i + 1) => (f ^ 2) • z
             map_add' := fun z w => smul_add (f ^ 2) z w
             map_smul' := fun a z => by
               simp only [RingHom.id_apply, smul_comm a (f ^ 2)] } :
            C.X (i + 1) →ₗ[A] C.X (i + 1)) := by
      change Submodule.Quotient.mk ((C.d i (i + 1)).hom m') = 0 at hycycle
      rw [Submodule.Quotient.mk_eq_zero] at hycycle
      exact hycycle
    obtain ⟨n, hn⟩ := hdm'
    have hx'1 : EtaPow.fLoc f (C.d i (i + 1)).hom
          (EtaPow.fpowMap f (C.X i) i m') ∈
        EtaPow.fpowSub f (C.X (i + 1)) (i + 2) := by
      rw [EtaPow.mem_fpowSub]
      refine ⟨n, ?_⟩
      rw [EtaPow.fpowMap_apply, EtaPow.fLoc_zpow_smul, EtaPow.fLoc_toLoc, ← hn]
      change Stacks.GradedLaurent.awayUnit f ^ (i + 2) • EtaPow.toLoc f (C.X (i + 1)) n =
        Stacks.GradedLaurent.awayUnit f ^ i • EtaPow.toLoc f (C.X (i + 1)) (f ^ 2 • n)
      rw [map_smul, pow_two, mul_smul, ← EtaPow.fUnit_units_smul,
        ← EtaPow.fUnit_units_smul, smul_smul, smul_smul]
      congr 1
      rw [zpow_add, zpow_two, mul_assoc]
    have hx'0 : EtaPow.fpowMap f (C.X i) i m' ∈ EtaPow.fpowSub f (C.X i) i := by
      rw [EtaPow.fpowSub_eq_range]
      exact ⟨m', rfl⟩
    have hx'd : EtaPow.fLoc f (C.d i (i + 1)).hom
          (EtaPow.fpowMap f (C.X i) i m') ∈
        EtaPow.fpowSub f (C.X (i + 1)) (i + 1) := by
      apply EtaComplex.powerSubmodule_step f (i + 1)
      rwa [show (i + 1) + 1 = i + 2 by ring]
    let x' : EtaComplex.term f C i :=
      ⟨EtaPow.fpowMap f (C.X i) i m', hx'0, hx'd⟩
    let q' : EtaComplex.QuotientTerm f C i := Submodule.Quotient.mk x'
    have hright : (LinearMap.snd A _ _ ∘ₗ canonical) q' = 0 := by
      change (canonical q').2 = 0
      rw [show canonical q' = g x' by rfl, hg]
      rw [Submodule.Quotient.mk_eq_zero]
      exact hx'1
    have hleft : (LinearMap.fst A _ _ ∘ₗ canonical) q' =
        (LinearMap.fst A _ _ ∘ₗ canonical) (Submodule.Quotient.mk x) := by
      change (canonical q').1 = (canonical (Submodule.Quotient.mk x)).1
      rw [show canonical q' = g x' by rfl,
        show canonical (Submodule.Quotient.mk x) = g x by rfl, hg, hg]
      rw [Submodule.Quotient.eq, Submodule.mem_comap]
      change EtaPow.fpowMap f (C.X i) i m' - x.1 ∈
        EtaPow.fpowSub f (C.X i) (i + 1)
      rw [EtaPow.fpowMap_apply, ← hm, ← smul_sub, ← map_sub]
      change Submodule.Quotient.mk m' = Submodule.Quotient.mk m at hyred
      rw [Submodule.Quotient.eq] at hyred
      obtain ⟨z, hz⟩ := hyred
      rw [← hz]
      simp only [pow_one]
      change Stacks.GradedLaurent.awayUnit f ^ i • EtaPow.toLoc f (C.X i) (f • z) ∈ _
      rw [map_smul,
        ← EtaPow.fUnit_units_smul, smul_smul, ← zpow_add_one]
      exact EtaPow.mem_fpowSub.mpr ⟨z, rfl⟩
    rw [Submodule.mem_sup]
    refine ⟨Submodule.Quotient.mk x - q', ?_, q', hright, ?_⟩
    · change (LinearMap.fst A _ _ ∘ₗ canonical)
          (Submodule.Quotient.mk x - q') = 0
      rw [map_sub, hleft, sub_self]
    · simp

end

end Stacks.Eta.ReductionDirectSum
