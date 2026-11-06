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

@[expose] public section

-- The eta terms and the tensor total complex are unfolded repeatedly below.

universe u v
/-! ## Vanishing of a Bockstein operator (Tag 0F7Y) -/

namespace Stacks.Eta.BocksteinVanishing

noncomputable section

-- The two rows of the power-ideal diagram are compared up to defeq throughout.

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaComplex.FractionalPowerBockstein

variable {A : Type u} [CommRing A]

/-- The standard short sequence of complexes
`M ⊗ A/f → M ⊗ A/f² → M ⊗ A/f`. The first copy of `A/f` is identified with
`fA/f²A` by multiplication by `f`. -/
def literalPowerQuotientShortComplex
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  let T := tensorWithCochainComplex M
  let mulF : ModuleCat.of A A ⟶ ModuleCat.of A A :=
    ModuleCat.ofHom (LinearMap.lsmul A A f)
  ShortComplex.mk (T.map (quotientInclusion mulF mulF))
    (T.map (quotientProjection mulF mulF)) (by
      rw [← T.map_comp]
      have hzero : quotientInclusion mulF mulF ≫ quotientProjection mulF mulF = 0 := by
        apply (cancel_epi (cokernel.π mulF)).1
        rw [comp_zero, ← Category.assoc, quotientInclusion, cokernel.π_desc]
        rw [Category.assoc, quotientProjection, cokernel.π_desc]
        exact cokernel.condition mulF
      rw [hzero]
      exact tensorWithCochainComplex_map_zero M _ _)

open CategoryTheory.MonoidalCategory

/-- Multiplication by `f` on the coefficient ring. -/
abbrev multiplicationBy (f : A) : ModuleCat.of A A ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (LinearMap.lsmul A A f)

/-- Dividing by the chosen generator identifies successive inclusion with multiplication. -/
@[reassoc]
lemma fractionalPowerInclusion_divide (f : A) (hf : f ∈ nonZeroDivisors A)
    (i : ℤ) :
    fractionalPowerInclusion f i ≫ (fractionalPowerIso f hf i).inv =
      (fractionalPowerIso f hf (i + 1)).inv ≫ multiplicationBy f := by
  rw [← cancel_epi (fractionalPowerIso f hf (i + 1)).hom]
  rw [← Category.assoc, fractionalPowerIso_hom_inclusion, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rfl

/-- The canonical identification `fⁱA/fⁱ⁺¹A ≅ A/fA`. -/
def powerQuotientIso (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    cokernel (fractionalPowerInclusion f i) ≅ cokernel (multiplicationBy f) :=
  cokernel.mapIso _ _ (fractionalPowerIso f hf (i + 1)).symm
    (fractionalPowerIso f hf i).symm (fractionalPowerInclusion_divide f hf i)

/-- The canonical identification `fⁱA/fⁱ⁺²A ≅ A/f²A`. -/
def powerQuotientTwoIso (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    cokernel (fractionalPowerInclusion f (i + 1) ≫ fractionalPowerInclusion f i) ≅
      cokernel (multiplicationBy f ≫ multiplicationBy f) :=
  cokernel.mapIso _ _ (fractionalPowerIso f hf (i + 1 + 1)).symm
    (fractionalPowerIso f hf i).symm (by
      simp only [Iso.symm_hom, Category.assoc, fractionalPowerInclusion_divide,
        fractionalPowerInclusion_divide_assoc])

/-- The isomorphism `powerQuotientIso` is induced by `(fractionalPowerIso f hf i).inv` on the
quotient maps. -/
@[reassoc (attr := simp)]
lemma powerQuotientIso_π (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    cokernel.π (fractionalPowerInclusion f i) ≫ (powerQuotientIso f hf i).hom =
      (fractionalPowerIso f hf i).inv ≫ cokernel.π (multiplicationBy f) := by
  simp [powerQuotientIso]

/-- The isomorphism `powerQuotientTwoIso` is induced by `(fractionalPowerIso f hf i).inv` on the
quotient maps. -/
@[reassoc (attr := simp)]
lemma powerQuotientTwoIso_π (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    cokernel.π (fractionalPowerInclusion f (i + 1) ≫ fractionalPowerInclusion f i) ≫
        (powerQuotientTwoIso f hf i).hom =
      (fractionalPowerIso f hf i).inv ≫
        cokernel.π (multiplicationBy f ≫ multiplicationBy f) := by
  simp [powerQuotientTwoIso]

/-- The quotient identifications preserve the injection of the lower row. -/
@[reassoc]
lemma powerQuotientIso_inclusion (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    (powerQuotientIso f hf (i + 1)).hom ≫
        quotientInclusion (multiplicationBy f) (multiplicationBy f) =
      quotientInclusion (fractionalPowerInclusion f (i + 1))
          (fractionalPowerInclusion f i) ≫ (powerQuotientTwoIso f hf i).hom := by
  apply (cancel_epi (cokernel.π (fractionalPowerInclusion f (i + 1)))).1
  simp [quotientInclusion, Category.assoc, ← fractionalPowerInclusion_divide_assoc]

/-- The quotient identifications preserve reduction modulo `f`. -/
@[reassoc]
lemma powerQuotientIso_projection (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    (powerQuotientTwoIso f hf i).hom ≫
        quotientProjection (multiplicationBy f) (multiplicationBy f) =
      quotientProjection (fractionalPowerInclusion f (i + 1))
          (fractionalPowerInclusion f i) ≫ (powerQuotientIso f hf i).hom := by
  apply (cancel_epi (cokernel.π
    (fractionalPowerInclusion f (i + 1) ≫ fractionalPowerInclusion f i))).1
  simp [quotientProjection]

/-- The canonical comparison of the fractional-power and literal reduction rows. -/
def powerQuotientShortComplexIso (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    successivePowerQuotientShortComplex M f i ≅ literalPowerQuotientShortComplex M f :=
  ShortComplex.isoMk
    ((tensorWithCochainComplex M).mapIso (powerQuotientIso f hf (i + 1)))
    ((tensorWithCochainComplex M).mapIso (powerQuotientTwoIso f hf i))
    ((tensorWithCochainComplex M).mapIso (powerQuotientIso f hf i))
    (by
      change (tensorWithCochainComplex M).map _ ≫ (tensorWithCochainComplex M).map _ =
        (tensorWithCochainComplex M).map _ ≫ (tensorWithCochainComplex M).map _
      simp only [← Functor.map_comp]
      exact congrArg (tensorWithCochainComplex M).map (powerQuotientIso_inclusion f hf i))
    (by
      change (tensorWithCochainComplex M).map _ ≫ (tensorWithCochainComplex M).map _ =
        (tensorWithCochainComplex M).map _ ≫ (tensorWithCochainComplex M).map _
      simp only [← Functor.map_comp]
      exact congrArg (tensorWithCochainComplex M).map (powerQuotientIso_projection f hf i))

/-- The component of the row comparison is the canonical tensor-product map. -/
@[simp]
lemma powerQuotientShortComplexIso_hom_τ₁
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    (powerQuotientShortComplexIso M f hf i).hom.τ₁ =
      (tensorWithCochainComplex M).map (powerQuotientIso f hf (i + 1)).hom := rfl

/-- The component of the row comparison is the canonical tensor-product map. -/
@[simp]
lemma powerQuotientShortComplexIso_hom_τ₂
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    (powerQuotientShortComplexIso M f hf i).hom.τ₂ =
      (tensorWithCochainComplex M).map (powerQuotientTwoIso f hf i).hom := rfl

/-- The component of the row comparison is the canonical tensor-product map. -/
@[simp]
lemma powerQuotientShortComplexIso_hom_τ₃
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    (powerQuotientShortComplexIso M f hf i).hom.τ₃ =
      (tensorWithCochainComplex M).map (powerQuotientIso f hf i).hom := rfl

/-- The literal reduction sequence is short exact for torsion-free terms. -/
theorem literalPowerQuotient_shortExact (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (hM : ∀ n, IsSMulRegular (M.X n) f) :
    (literalPowerQuotientShortComplex M f).ShortExact :=
  ShortComplex.shortExact_of_iso (powerQuotientShortComplexIso M f hf 0)
    (powerIdealRows_shortExact f hf M hM 0).2

/-- The comparison identifies the actual reduction maps on cycles. -/
lemma powerQuotientShortComplexIso_cycles (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (hf : f ∈ nonZeroDivisors A) (i n : ℤ) :
    HomologicalComplex.cyclesMap (successivePowerQuotientShortComplex M f i).g n ≫
        HomologicalComplex.cyclesMap (powerQuotientShortComplexIso M f hf i).hom.τ₃ n =
      HomologicalComplex.cyclesMap (powerQuotientShortComplexIso M f hf i).hom.τ₂ n ≫
        HomologicalComplex.cyclesMap (literalPowerQuotientShortComplex M f).g n := by
  rw [← HomologicalComplex.cyclesMap_comp, ← HomologicalComplex.cyclesMap_comp,
    (powerQuotientShortComplexIso M f hf i).hom.comm₂₃]

/-- The comparison identifies the Bockstein with the literal sequence's boundary. -/
lemma powerQuotientShortComplexIso_δ (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (hf : f ∈ nonZeroDivisors A) (i n : ℤ)
    (hLower : (successivePowerQuotientShortComplex M f i).ShortExact)
    (hLiteral : (literalPowerQuotientShortComplex M f).ShortExact) :
    powerBocksteinOperator M f i n hLower ≫
        HomologicalComplex.homologyMap (powerQuotientShortComplexIso M f hf i).hom.τ₁ (n + 1) =
      HomologicalComplex.homologyMap (powerQuotientShortComplexIso M f hf i).hom.τ₃ n ≫
        hLiteral.δ n (n + 1) (by simp [ComplexShape.up]) :=
  (HomologicalComplex.HomologySequence.δ_naturality
    (powerQuotientShortComplexIso M f hf i).hom hLower hLiteral n (n + 1)
    (by simp [ComplexShape.up]))

/-- Tensoring with the coefficient ring is the identity on cochain complexes. -/
def tensorUnitComplexIso (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    M ≅ (tensorWithCochainComplex M).obj (ModuleCat.of A A) :=
  (HomologicalComplex.rightUnitor M).symm

/-- Tensoring with `fⁱA` is canonically isomorphic to the original complex. -/
def tensorFractionalPowerIso (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    M ≅ (tensorWithCochainComplex M).obj (fractionalPowerIdeal f i) :=
  tensorUnitComplexIso M ≪≫
    (tensorWithCochainComplex M).mapIso (fractionalPowerIso f hf i)

/-- The induced identification on cohomology. -/
def tensorFractionalPowerHomologyIso (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (hf : f ∈ nonZeroDivisors A) (i n : ℤ) :
    M.homology n ≅ ((tensorWithCochainComplex M).obj (fractionalPowerIdeal f i)).homology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (tensorFractionalPowerIso M f hf i)

/-- Tensoring with a fixed complex is linear in the coefficient morphism. -/
lemma tensorWithCochainComplex_map_smul
    (M : CochainComplex (ModuleCat.{u} A) ℤ) {X Y : ModuleCat.{u} A}
    (g : X ⟶ Y) (f : A) :
    (tensorWithCochainComplex M).map (f • g) = f • (tensorWithCochainComplex M).map g := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [← cancel_epi (tensorSingleTermIso M X n).hom]
  simp only [HomologicalComplex.smul_f_apply, Linear.comp_smul,
    ← tensorSingleTermIso_naturality]
  change (tensorLeft (M.X n)).map (f • g) ≫ _ = _
  rw [Functor.map_smul, Linear.smul_comp]
  rfl

/-- Cohomology respects scalar multiplication of cochain maps. -/
lemma homologyMap_smul {M N : CochainComplex (ModuleCat.{u} A) ℤ}
    (g : M ⟶ N) (f : A) (n : ℤ) :
    HomologicalComplex.homologyMap (f • g) n = f • HomologicalComplex.homologyMap g n := by
  change ShortComplex.homologyMap (f • ((HomologicalComplex.shortComplexFunctor _ _ n).map g)) = _
  apply ShortComplex.homologyMap_smul

/-- The upper inclusion is multiplication by `f` under the canonical comparisons. -/
@[reassoc]
lemma tensorFractionalPowerIso_inclusion (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ) :
    (tensorFractionalPowerIso M f hf (i + 1)).hom ≫
        (tensorWithCochainComplex M).map (fractionalPowerInclusion f i) =
      (f • 𝟙 M) ≫ (tensorFractionalPowerIso M f hf i).hom := by
  dsimp only [tensorFractionalPowerIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, fractionalPowerIso_hom_inclusion,
    Functor.map_comp, tensorWithCochainComplex_map_smul, CategoryTheory.Functor.map_id]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]

/-- The upper inclusion on cohomology is multiplication by `f`. -/
@[reassoc]
lemma tensorFractionalPowerHomologyIso_inclusion
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (hf : f ∈ nonZeroDivisors A) (i n : ℤ) :
    (tensorFractionalPowerHomologyIso M f hf (i + 1) n).hom ≫
        HomologicalComplex.homologyMap
          ((tensorWithCochainComplex M).map (fractionalPowerInclusion f i)) n =
      (f • 𝟙 (M.homology n)) ≫ (tensorFractionalPowerHomologyIso M f hf i n).hom := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
  rw [← HomologicalComplex.homologyMap_comp, tensorFractionalPowerIso_inclusion,
    HomologicalComplex.homologyMap_comp, homologyMap_smul, HomologicalComplex.homologyMap_id]
  rfl

/-- Torsion freeness is preserved by the canonical cohomology comparison. -/
lemma tensorFractionalPowerHomology_regular
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : A) (hf : f ∈ nonZeroDivisors A) (i n : ℤ)
    (h : IsSMulRegular (M.homology n) f) :
    IsSMulRegular (((tensorWithCochainComplex M).obj (fractionalPowerIdeal f i)).homology n) f :=
  IsSMulRegular.of_injective (tensorFractionalPowerHomologyIso M f hf i n).inv.hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) h

/-- Lift the ring and modules to a common universe without changing their algebra. -/
abbrev commonUniverseModules : ModuleCat.{v} A ⥤ ModuleCat.{max u v} (ULift.{v} A) :=
  ModuleCat.uliftFunctor.{u} A ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom

/-- The universe-lifting functor `commonUniverseModules` preserves finite colimits. -/
instance : PreservesFiniteColimits (commonUniverseModules (A := A)) :=
  comp_preservesFiniteColimits _ _

/-- The universe-lifting functor `commonUniverseModules` preserves finite limits. -/
instance : PreservesFiniteLimits (commonUniverseModules (A := A)) :=
  comp_preservesFiniteLimits _ _

/-- The universe-lifting functor `commonUniverseModules` preserves homology. -/
instance : (commonUniverseModules (A := A)).PreservesHomology := by infer_instance

/-- A complex over an independently sized ring, represented in their common universe. -/
abbrev commonUniverseComplex (M : CochainComplex (ModuleCat.{v} A) ℤ) :
    CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ :=
  (commonUniverseModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj M

/-- Exact universe lifting commutes with cohomology. -/
def commonUniverseHomologyIso (M : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℤ) :
    (commonUniverseComplex M).homology n ≅ commonUniverseModules.obj (M.homology n) :=
  (M.sc n).mapHomologyIso commonUniverseModules

/-- Universe lifting preserves regularity of scalar multiplication. -/
lemma commonUniverseModules_regular (N : ModuleCat.{v} A) (f : A) (h : IsSMulRegular N f) :
    IsSMulRegular (commonUniverseModules.obj N) (ULift.up f) :=
  fun _ _ hxy => ULift.ext _ _ (h (congrArg ULift.down hxy))

/-- The original torsion-free cohomology hypothesis transfers to the lifted complex. -/
lemma commonUniverseHomology_regular (M : CochainComplex (ModuleCat.{v} A) ℤ) (f : A) (n : ℤ)
    (h : IsSMulRegular (M.homology n) f) :
    IsSMulRegular ((commonUniverseComplex M).homology n) (ULift.up f) :=
  IsSMulRegular.of_injective (commonUniverseHomologyIso M n).hom.hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) (commonUniverseModules_regular _ f h)

/-- A nonzerodivisor stays a nonzerodivisor after lifting the coefficient ring. -/
lemma ulift_mem_nonZeroDivisors (f : A) (hf : f ∈ nonZeroDivisors A) :
    ULift.up f ∈ nonZeroDivisors (ULift.{v} A) := by
  rw [mem_nonZeroDivisors_iff] at hf ⊢
  exact ⟨fun x hx => ULift.ext _ _ (hf.1 x.down (congrArg ULift.down hx)),
    fun x hx => ULift.ext _ _ (hf.2 x.down (congrArg ULift.down hx))⟩

private lemma epi_cyclesMap_iff_epi_homologyMap
    {R : Type u} [Ring R]
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (n : ℤ) :
    Epi (HomologicalComplex.cyclesMap S.g n) ↔
      Epi (HomologicalComplex.homologyMap S.g n) := by
  constructor
  · intro h
    have := h
    have hcomp : Epi (S.X₂.homologyπ n ≫
        HomologicalComplex.homologyMap S.g n) := by
      rw [HomologicalComplex.homologyπ_naturality]
      exact epi_comp _ _
    have := hcomp
    exact epi_of_epi (S.X₂.homologyπ n) (HomologicalComplex.homologyMap S.g n)
  · intro h
    rw [ModuleCat.epi_iff_surjective] at h ⊢
    intro z
    obtain ⟨yH, hyH⟩ := h (S.X₃.homologyπ n z)
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (S.X₂.homologyπ n)).mp inferInstance yH
    have hz : S.X₃.homologyπ n
        (z - HomologicalComplex.cyclesMap S.g n y) = 0 := by
      rw [map_sub, sub_eq_zero, ← ModuleCat.comp_apply,
        ← HomologicalComplex.homologyπ_naturality]
      exact hyH.symm
    let T := ShortComplex.mk (S.X₃.opcyclesToCycles (n - 1) n)
      (S.X₃.homologyπ n) (by simp)
    have hT : T.Exact :=
      (HomologicalComplex.HomologySequence.composableArrows₃_exact
        S.X₃ (n - 1) n (by simp [ComplexShape.up])).exact 1
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff T).mp hT
      (z - HomologicalComplex.cyclesMap S.g n y) (by
      change S.X₃.homologyπ n
        (z - HomologicalComplex.cyclesMap S.g n y) = 0
      exact hz)
    have := hS.epi_g
    obtain ⟨w', rfl⟩ := (ModuleCat.epi_iff_surjective
      (HomologicalComplex.opcyclesMap S.g (n - 1))).mp inferInstance w
    refine ⟨y + S.X₂.opcyclesToCycles (n - 1) n w', ?_⟩
    rw [map_add, ← ModuleCat.comp_apply,
      ← HomologicalComplex.opcyclesToCycles_naturality, ModuleCat.comp_apply, hw]
    abel

private lemma epi_cyclesMap_iff_delta_eq_zero
    {R : Type u} [Ring R]
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (n : ℤ) :
    Epi (HomologicalComplex.cyclesMap S.g n) ↔
      hS.δ n (n + 1) (by simp [ComplexShape.up]) = 0 := by
  rw [epi_cyclesMap_iff_epi_homologyMap S hS n]
  let T := ShortComplex.mk (HomologicalComplex.homologyMap S.g n)
    (hS.δ n (n + 1) (by simp [ComplexShape.up]))
    (hS.comp_δ n (n + 1) (by simp [ComplexShape.up]))
  have hT : T.Exact := hS.homology_exact₃ n (n + 1) (by simp [ComplexShape.up])
  constructor
  · intro hepi
    exact zero_of_epi_comp _ (hS.comp_δ n (n + 1) (by simp [ComplexShape.up]))
  · intro hzero
    exact (ShortComplex.exact_iff_epi T hzero).mp hT

/-- **Stacks 0F7Y.** For a complex of `f`-torsion-free modules, reduction from cycles
modulo `f²` to cycles modulo `f` is surjective if and only if the corresponding Bockstein
operator is zero. Moreover, these equivalent conditions hold if multiplication by `f` is
injective on `Hⁱ⁺¹(M)`. -/
@[stacks 0F7Y]
theorem cyclesReduction_epi_iff_powerBocksteinOperator_eq_zero
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{v} A) ℤ) (hM : ∀ n, IsSMulRegular (M.X n) f)
    (i : ℤ) :
    let K := commonUniverseComplex M
    let f' : ULift.{v} A := ULift.up f
    let hf' := ulift_mem_nonZeroDivisors f hf
    let hK := fun n => commonUniverseModules_regular (M.X n) f (hM n)
    let hLower := (powerIdealRows_shortExact f' hf' K hK i).2
    let cyclesReduction := HomologicalComplex.cyclesMap
      (literalPowerQuotientShortComplex K f').g i
    (Epi cyclesReduction ↔ powerBocksteinOperator K f' i i hLower = 0) ∧
      (IsSMulRegular (M.homology (i + 1)) f → Epi cyclesReduction) := by
  let K := commonUniverseComplex M
  let f' : ULift.{v} A := ULift.up f
  let hf' := ulift_mem_nonZeroDivisors f hf
  let hK := fun n => commonUniverseModules_regular (M.X n) f (hM n)
  let hLower := (powerIdealRows_shortExact f' hf' K hK i).2
  let L := literalPowerQuotientShortComplex K f'
  let hLiteral := literalPowerQuotient_shortExact f' hf' K hK
  let e := powerQuotientShortComplexIso K f' hf' i
  change (Epi (HomologicalComplex.cyclesMap L.g i) ↔
      powerBocksteinOperator K f' i i hLower = 0) ∧
    (IsSMulRegular (M.homology (i + 1)) f →
      Epi (HomologicalComplex.cyclesMap L.g i))
  have hnat : powerBocksteinOperator K f' i i hLower ≫
        HomologicalComplex.homologyMap e.hom.τ₁ (i + 1) =
      HomologicalComplex.homologyMap e.hom.τ₃ i ≫
        hLiteral.δ i (i + 1) (by simp [ComplexShape.up]) :=
    powerQuotientShortComplexIso_δ K f' hf' i i hLower hLiteral
  have hbockstein_iff : powerBocksteinOperator K f' i i hLower = 0 ↔
      hLiteral.δ i (i + 1) (by simp [ComplexShape.up]) = 0 := by
    constructor
    · intro h
      rw [h, zero_comp] at hnat
      exact (cancel_epi
        (HomologicalComplex.homologyMap e.hom.τ₃ i)).mp (by simpa using hnat.symm)
    · intro h
      rw [h, comp_zero] at hnat
      exact (cancel_mono
        (HomologicalComplex.homologyMap e.hom.τ₁ (i + 1))).mp (by simpa using hnat)
  constructor
  · rw [epi_cyclesMap_iff_delta_eq_zero L hLiteral i, hbockstein_iff]
  · intro hregular
    apply (epi_cyclesMap_iff_delta_eq_zero L hLiteral i).2
    apply hbockstein_iff.mp
    obtain ⟨hUpper, hLower', hfactor⟩ :=
      powerBocksteinOperator_eq_connectingHom_comp_reduction f' hf' K hK i i
    have hlower : hLower' = hLower := Subsingleton.elim _ _
    subst hLower'
    rw [hfactor]
    have hregK : IsSMulRegular (K.homology (i + 1)) f' :=
      commonUniverseHomology_regular M f (i + 1) hregular
    have hmonoScalar : Mono (f' • 𝟙 (K.homology (i + 1))) := by
      rw [ModuleCat.mono_iff_injective]
      exact hregK
    have hmonoIncl : Mono (HomologicalComplex.homologyMap
        ((tensorWithCochainComplex K).map (fractionalPowerInclusion f' i)) (i + 1)) := by
      have heq := tensorFractionalPowerHomologyIso_inclusion K f' hf' i (i + 1)
      have : Mono ((tensorFractionalPowerHomologyIso K f' hf' (i + 1) (i + 1)).hom ≫
          HomologicalComplex.homologyMap
            ((tensorWithCochainComplex K).map (fractionalPowerInclusion f' i)) (i + 1)) := by
        rw [heq]
        infer_instance
      exact (mono_comp_iff_of_isIso
        (tensorFractionalPowerHomologyIso K f' hf' (i + 1) (i + 1)).hom _).mp this
    let hij : (ComplexShape.up ℤ).Rel i (i + 1) := by simp [ComplexShape.up]
    have hmonoUpper : Mono (HomologicalComplex.homologyMap
        (powerIdealShortComplex K f' i).f (i + 1)) :=
      hmonoIncl
    have hdelta : hUpper.δ i (i + 1) hij = 0 := by
      apply (cancel_mono
        (HomologicalComplex.homologyMap (powerIdealShortComplex K f' i).f (i + 1))).mp
      rw [hUpper.δ_comp, zero_comp]
    rw [hdelta]
    exact zero_comp

end

end Stacks.Eta.BocksteinVanishing

