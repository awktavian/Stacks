module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks Project, Tag 07KC / Lemma 13.34.2 ("Derived Categories", section
"Derived limits").

Let `A` be an abelian category with *exact countable products*. Then:

1. (Existence of products.) The derived category `D(A)` has countable products.
2. (Computation via termwise products.) For any countable family `(K_i)` of
   objects of `D(A)`, choosing a complex representing each `K_i`, the termwise
   product complex (with the projection chain maps regarded as morphisms in
   `D(A)`) is a product of the family in `D(A)`.
3. (Cohomology of the product.) For every `p` the canonical morphism
   `H^p(∏ K_i) → ∏ H^p(K_i)` induced by the projections is an isomorphism
   in `A`.

# Background and context

Throughout, `A` is an abelian category and "countable" means indexed by a
countable index set `I` (e.g. `I = ℕ`); finite index sets are included.  The
relevant objects are cochain complexes `K = (K^p, d^p)` with
`d^{p+1} ∘ d^p = 0`, i.e. terms of type `CochainComplex A ℤ`.

## Definition 1 (Countable products in `A`).
`A` has countable products if for every countable family `(A_i)_{i ∈ I}` the
product `∏ A_i` (with its projections, satisfying the universal property) exists
in `A`.  In Lean this is the typeclass `HasProductsOfShape I A` for a countable
type `I`.

## Definition 2 (Exact countable products).
`A` has exact countable products if it has countable products and the product
functor is exact, i.e. for every countable family of short exact sequences
`0 → A_i → B_i → C_i → 0` the induced sequence
`0 → ∏ A_i → ∏ B_i → ∏ C_i → 0` is exact.  Since products are always left
exact, the content is right exactness.  In Lean: the product functor is the
limit functor over the discrete category `Discrete I`, and exactness of this
functor is the typeclass `HasExactLimitsOfShape (Discrete I) A`, whose content
is `PreservesFiniteColimits (lim : (Discrete I ⥤ A) ⥤ A)` (left exactness is
automatic for limit functors).

## Definition 3 (Termwise product of complexes).
Given a countable family `(K_i)` of complexes, the termwise product
`∏ K_i` is the complex with `(∏ K_i)^p = ∏ K_i^p` and the differentials induced
by the universal property.  In Lean, when `A` has countable products,
`CochainComplex A ℤ` has countable products as well, computed termwise, and the
termwise product is the categorical product `∏ᶜ K`.  The projection chain maps
are `Pi.π K i`.

## Definition 4 (Derived category `D(A)`).
`D(A)` is the derived category of `A`, the localization of complexes at
quasi-isomorphisms, with localization functor `Q : CochainComplex A ℤ ⥤ D(A)`.
Cohomology descends to functors `H^p : D(A) ⥤ A`
(`DerivedCategory.homologyFunctor A p`).  In Lean this requires the typeclass
`HasDerivedCategory A`.

## Definition 5 (Countable product in `D(A)`).
For a countable family `(K_i)` of objects of `D(A)`, a product `∏ K_i` is an
object `P` together with morphisms `p_i : P → K_i` such that for every `L` the
map `Hom(L, P) → ∏ Hom(L, K_i)`, `α ↦ (p_i ∘ α)`, is a bijection (the universal
property of the categorical product).  `D(A)` has countable products if such a
product exists for every countable family.  In Lean this is
`HasProductsOfShape I (D(A))`, and being a product is expressed via `IsLimit` of
the product fan.
-/

namespace Stacks.DerivedProducts

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe uI

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
variable {I : Type uI} [Countable I]

-- Hypothesis: `A` has exact countable products (Definitions 1 and 2).
-- `HasProductsOfShape I A` is Definition 1; `HasExactLimitsOfShape (Discrete I) A`
-- adds the right-exactness of the product functor of Definition 2.
variable [HasProductsOfShape I A] [HasExactLimitsOfShape (Discrete I) A]

/- **Definition 3 (correctness): termwise product.**
The termwise product complex `∏ᶜ K` has its degree-`p` term equal (canonically
isomorphic) to the product `∏ K_i^p` of the degree-`p` terms.  Concretely, the
canonical comparison morphism `(∏ᶜ K).X p → ∏ᶜ (fun i => (K i).X p)`
(`piComparison` of the degree-`p` evaluation functor) is an isomorphism.  This
characterizes `∏ᶜ K` in `CochainComplex A ℤ` as the termwise product of
Definition 3. -/
omit [HasDerivedCategory A] [Countable I] [HasExactLimitsOfShape (Discrete I) A] in
theorem isIso_piComparison_eval (K : I → CochainComplex A ℤ) (p : ℤ) :
    IsIso (piComparison (HomologicalComplex.eval A (ComplexShape.up ℤ) p) K) := by
  infer_instance

/-- **Statement 2 (Computation via termwise products).**
For any countable family `K : I → CochainComplex A ℤ` of complexes (representing
objects of `D(A)`), the image under `Q` of the termwise product complex `∏ᶜ K`,
together with the projection chain maps `Q.map (Pi.π K i)`, is a product of the
family `(Q.obj (K i))` in `D(A)`, i.e. the corresponding fan is a limit cone.
In particular the product is independent, up to canonical isomorphism in `D(A)`,
of the choice of representing complexes. -/
noncomputable def productFanInDerivedCategory (K : I → CochainComplex A ℤ) :
    Fan (fun i => DerivedCategory.Q.obj (K i)) :=
  Fan.mk (DerivedCategory.Q.obj (∏ᶜ K)) (fun i => DerivedCategory.Q.map (Pi.π K i))

/- ===========================================================================
   Core lemma (★): a countable product of quasi-isomorphisms is a
   quasi-isomorphism.  This is the single place where the *exactness* of
   countable products is used, and it underpins all three statements.
   =========================================================================== -/

/- **Core lemma (★): quasi-isos are stable under `I`-indexed products** (see the
theorem `quasiIso_isStableUnderProductsOfShape` below for the statement).
If `fⱼ : Kⱼ → Lⱼ` are quasi-isomorphisms of cochain complexes for every `j ∈ I`,
then the induced map on termwise products `∏ⱼ fⱼ` (`Limits.Pi.map f`) is again a
quasi-isomorphism.

INFORMAL ARGUMENT (sound, sanity-checked).
For a cochain complex, `Hⁿ` is a *cokernel* (`coker(im dⁿ⁻¹ ↪ ker dⁿ)`).
Products always preserve kernels (left exactness is automatic), but preserving
this cokernel — equivalently the natural iso `Hⁿ(∏ⱼ Kⱼ) ≅ ∏ⱼ Hⁿ(Kⱼ)` — requires
the product functor to be *right exact*, which is exactly the hypothesis
`HasExactLimitsOfShape (Discrete I) A`.  Concretely, under that hypothesis the
product functor `lim : (Discrete I ⥤ A) ⥤ A` (and hence the termwise product on
`CochainComplex A ℤ`) preserves homology: in Lean
`(lim : (Discrete I ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ).PreservesHomology`
is an instance under the present hypotheses.  Therefore `Hⁿ(∏ⱼ fⱼ)` is
identified, via the comparison iso `Hⁿ(∏ⱼ Kⱼ) ≅ ∏ⱼ Hⁿ(Kⱼ)`, with the product
map `∏ⱼ Hⁿ(fⱼ)`.  Each `Hⁿ(fⱼ)` is an isomorphism (as `fⱼ` is a quasi-iso), so
`∏ⱼ Hⁿ(fⱼ)` is an isomorphism (`Pi.map` of isos is iso), and hence `Hⁿ(∏ⱼ fⱼ)`
is an isomorphism for every `n`, i.e. `∏ⱼ fⱼ` is a quasi-iso.

PROOF STRATEGY (Lean).
Use `IsStableUnderProductsOfShape.mk` (`RespectsIso` infers) to reduce to: given
`f j : K₁ j ⟶ K₂ j` with each `quasiIso A _ (f j)`, show `quasiIso A _ (Pi.map f)`.
Then `rw [HomologicalComplex.quasiIso_iff]` and for each `n` use
`quasiIsoAt_iff_isIso_homologyMap` to reduce to `IsIso (homologyMap (Pi.map f) n)`.
Build the comparison: the termwise product is `lim` of the discrete diagram, and
`lim.PreservesHomology` gives a natural iso
`(homologyFunctor _ _ n).map (Pi.map f)` ≅ `Pi.map (fun j => homologyMap (f j) n)`
(assemble from `HomologicalComplex.homologyFunctorIso` + `ShortComplex.homologyFunctorIso`
of the product functor, or transport through `eval` which preserves products via
`isIso_piComparison_eval`).  Conclude with `Pi.map` of isos being iso. -/
omit [Countable I] in
/-- Naturality of `piComparison`: for any functor `F` and family of maps `f`,
`piComparison F X₁ ≫ Pi.map (F.map ∘ f) = F.map (Pi.map f) ≫ piComparison F X₂`.
A purely formal product-API fact (no exactness used). -/
@[ega "0 18.3.3" "more general"]
theorem piComparison_naturality {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (X₁ X₂ : I → C) [HasProduct X₁] [HasProduct X₂]
    [HasProduct (fun j => F.obj (X₁ j))] [HasProduct (fun j => F.obj (X₂ j))]
    (f : (j : I) → X₁ j ⟶ X₂ j) :
    piComparison F X₁ ≫ Limits.Pi.map (fun j => F.map (f j))
      = F.map (Limits.Pi.map f) ≫ piComparison F X₂ := by
  ext j
  simp only [Category.assoc, Limits.piComparison_comp_π, Limits.Pi.map_π,
    Limits.piComparison_comp_π_assoc, ← F.map_comp]

omit [Countable I] in
/-- Helper: a functor between categories with `I`-products preserves `Discrete I`
products as soon as every `piComparison` is an isomorphism. -/
theorem preservesLimitsOfShape_discrete_of_isIso_piComparison
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    [HasProductsOfShape I C] [HasProductsOfShape I D]
    (h : ∀ (X : I → C), IsIso (piComparison F X)) :
    PreservesLimitsOfShape (Discrete I) F := by
  have inst : ∀ (X : I → C), PreservesLimit (Discrete.functor X) F := by
    intro X
    have := h X
    exact PreservesProduct.of_iso_comparison F X
  exact preservesLimitsOfShape_of_discrete F

/- **(A.main) The homology functor preserves `I`-indexed products.**
For each `n`, the homology functor `Hⁿ : CochainComplex A ℤ ⥤ A` preserves
products indexed by the countable set `I`.  THIS is the only place where the
exactness hypothesis `HasExactLimitsOfShape (Discrete I) A` is used.

INFORMAL ARGUMENT.
Factor `Hⁿ ≅ ShortComplex.homologyFunctor A ∘ shortComplexFunctor A _ n`
(`HomologicalComplex.homologyFunctorIso`).  It suffices that each factor
preserves `I`-products:
  • `shortComplexFunctor A _ n` preserves `I`-products — limits in
    `ShortComplex A` are computed objectwise and each degree-evaluation
    `eval A _ m` preserves products (`isIso_piComparison_eval`); products of the
    zero-composite condition are zero.
  • `ShortComplex.homologyFunctor A` preserves `I`-products — homology of a short
    complex is built from kernels/images/cokernels (finite limits + finite
    colimits), and the product functor `lim : (Discrete I ⥤ A) ⥤ A` preserves
    homology under the exactness hypothesis (`(lim).PreservesHomology` is an
    instance here, combining automatic left-exactness of a limit with the
    right-exactness supplied by `HasExactLimitsOfShape (Discrete I) A`).  Use
    `ShortComplex.functorEquivalence (Discrete I) A` together with
    `ShortComplex.homologyFunctorIso (lim)` to transport the preservation.
A composite of product-preserving functors preserves products.

PROOF STRATEGY (Lean).  Establish two `PreservesLimitsOfShape (Discrete I)`
instances (one per factor), then transport along `homologyFunctorIso` via
`preservesLimitsOfShape_of_natIso` / `Functor.preservesLimitsOfShape_of_iso`. -/

omit [Countable I] in
/-- Helper: `piComparison` of a composite functor factors. -/
theorem piComparison_comp_eq {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (K : I → C)
    [HasProduct K] [HasProduct (fun i => F.obj (K i))]
    [HasProduct (fun i => G.obj (F.obj (K i)))]
    [HasProduct (fun i => (F ⋙ G).obj (K i))] :
    piComparison (F ⋙ G) K
      = G.map (piComparison F K) ≫ piComparison G (fun i => F.obj (K i)) := by
  apply Limits.Pi.hom_ext
  intro i
  have key : (piComparison G fun i => F.obj (K i)) ≫ Pi.π (fun b => (F ⋙ G).obj (K b)) i
      = G.map (Pi.π (fun i => F.obj (K i)) i) :=
    Limits.piComparison_comp_π G (fun i => F.obj (K i)) i
  rw [Limits.piComparison_comp_π (F ⋙ G) K i, Functor.comp_map, Category.assoc, key,
    ← G.map_comp, Limits.piComparison_comp_π F K i]

/-- If `piComparison (F ⋙ G) K` and `piComparison G (F ∘ K)` are isomorphisms, so is
`G.map (piComparison F K)`. -/
private theorem isIso_map_piComparison {J C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (K : J → C)
    [HasProduct K] [HasProduct (fun i => F.obj (K i))]
    [HasProduct (fun i => G.obj (F.obj (K i)))] [HasProduct (fun i => (F ⋙ G).obj (K i))]
    (h : IsIso (piComparison (F ⋙ G) K)) [IsIso (piComparison G (fun i => F.obj (K i)))] :
    IsIso (G.map (piComparison F K)) := by
  rw [piComparison_comp_eq F G K] at h
  exact IsIso.of_isIso_comp_right _ (piComparison G fun i => F.obj (K i))

omit [Countable I] in
omit [HasDerivedCategory A] [HasExactLimitsOfShape (Discrete I) A] in
/-- **Lemma A**: the short-complex functor `shortComplexFunctor A _ n` preserves
`I`-indexed products.  No exactness needed: limits in `ShortComplex A` are
componentwise (`ShortComplex.isIso_of_isIso` from the three `τ`-components), and
each component of `piComparison (shortComplexFunctor _ n)` is, via the `rfl`
identities `shortComplexFunctor _ n ⋙ ShortComplex.πᵢ = eval _ _ (·)`, a
`piComparison (eval _ _ m)` which is iso by `isIso_piComparison_eval`.
PROOF PLAN: `apply preservesLimitsOfShape_discrete_of_isIso_piComparison`; for the
family `K`, show the three components `(piComparison _ K).τ₁/.τ₂/.τ₃` are iso (each
equals `ShortComplex.πᵢ.map (piComparison _ K)`, then relate to `piComparison (eval _ _ m) K`
through the composite-functor `piComparison` identity — see closer note: may need a
`piComparison_comp_eq` helper_07kc because `set_option backward.isDefEq.respectTransparency false`
blocks the bare `rfl` between `πᵢ.obj (∏ᶜ ·)` and `∏ᶜ (eval.obj ∘ ·)`), then
`exact ShortComplex.isIso_of_isIso _`. -/
theorem preservesLimitsOfShape_shortComplexFunctor (n : ℤ) :
    PreservesLimitsOfShape (Discrete I)
      (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n) := by
  -- Lemma A: componentwise via eval; NO exactness. (verified-reducible per closer report)
  apply preservesLimitsOfShape_discrete_of_isIso_piComparison
  intro K
  set F := HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n with hF
  -- Establish the three component isos
  have hτ₁ : IsIso (piComparison F K).τ₁ :=
    isIso_map_piComparison F ShortComplex.π₁ K
      (isIso_piComparison_eval (A := A) K ((ComplexShape.up ℤ).prev n))
  have hτ₂ : IsIso (piComparison F K).τ₂ :=
    isIso_map_piComparison F ShortComplex.π₂ K (isIso_piComparison_eval (A := A) K n)
  have hτ₃ : IsIso (piComparison F K).τ₃ :=
    isIso_map_piComparison F ShortComplex.π₃ K
      (isIso_piComparison_eval (A := A) K ((ComplexShape.up ℤ).next n))
  exact ShortComplex.isIso_of_isIso _

omit [Countable I] in
omit [HasDerivedCategory A] in
/-- **Lemma B (the exactness core)**: `ShortComplex.homologyFunctor A` preserves
`I`-indexed products.  THIS is the only place `HasExactLimitsOfShape (Discrete I) A`
is used (it makes `(lim : (Discrete I ⥤ A) ⥤ A).PreservesHomology` an instance).
PROOF PLAN: use
`preservesLimitsOfShape_discrete_of_isIso_piComparison`,
i.e. for `S : I → ShortComplex A` show `IsIso (piComparison (ShortComplex.homologyFunctor A) S)`.
Build the canonical iso `Hₐ(∏ S) ≅ ∏ (Hₐ ∘ S)` from:
  • `ShortComplex.homologyFunctorIso (lim_A) : lim_A.mapShortComplex ⋙ homologyFunctor A
     ≅ homologyFunctor (Discrete I ⥤ A) ⋙ lim_A`  (uses `(lim_A).PreservesHomology`);
  • `ShortComplex.functorEquivalence (Discrete I) A` to identify the product on
    `ShortComplex A` with `lim_A.mapShortComplex` through `e.inverse`;
  • `lim_A` preserving `Discrete I` limits (instance) for the RHS.
Then check this composite EQUALS `piComparison (homologyFunctor A) S` (`Pi.hom_ext`
+ the `mapHomologyIso`/`functorEquivalence` simp lemmas) so it is iso.  The
compatibility verification is the bulk of the work. -/
theorem preservesLimitsOfShape_shortComplexHomologyFunctor :
    PreservesLimitsOfShape (Discrete I) (ShortComplex.homologyFunctor A) := by
  -- Lemma B: homology commutes with I-products; USES exactness via (lim_A).PreservesHomology.
  apply preservesLimitsOfShape_discrete_of_isIso_piComparison
  intro S
  set H : ShortComplex A ⥤ A := ShortComplex.homologyFunctor A with hH
  set lim_A : (Discrete I ⥤ A) ⥤ A := lim with hlim
  let T : ShortComplex (Discrete I ⥤ A) :=
    (ShortComplex.FunctorEquivalence.inverse (Discrete I) A).obj (Discrete.functor S)
  let τ : (i : Discrete I) → (lim_A ⟶ (evaluation (Discrete I) A).obj i) := fun i =>
    { app := fun X => limit.π X i, naturality := by intro X Y f; exact limMap_π f i }
  let μ : (∏ᶜ S : ShortComplex A) ≅ lim_A.mapShortComplex.obj T :=
    ShortComplex.isoMk
      (preservesLimitIso ShortComplex.π₁ (Discrete.functor S))
      (preservesLimitIso ShortComplex.π₂ (Discrete.functor S))
      (preservesLimitIso ShortComplex.π₃ (Discrete.functor S))
      (by
        apply limit.hom_ext; intro j
        rw [Category.assoc]
        rw [show (lim_A.mapShortComplex.obj T).f
            = lim_A.map ((Discrete.functor S).whiskerLeft ShortComplex.π₁Toπ₂) from rfl]
        erw [limMap_π]
        simp only [Functor.whiskerLeft_app, ShortComplex.π₁Toπ₂_app]
        rw [← Category.assoc, preservesLimitIso_hom_π, ShortComplex.π₁_map, Category.assoc]
        erw [preservesLimitIso_hom_π]
        exact (limit.π (Discrete.functor S) j).comm₁₂)
      (by
        apply limit.hom_ext; intro j
        rw [Category.assoc]
        rw [show (lim_A.mapShortComplex.obj T).g
            = lim_A.map ((Discrete.functor S).whiskerLeft ShortComplex.π₂Toπ₃) from rfl]
        erw [limMap_π]
        simp only [Functor.whiskerLeft_app, ShortComplex.π₂Toπ₃_app]
        rw [← Category.assoc, preservesLimitIso_hom_π, ShortComplex.π₂_map, Category.assoc]
        erw [preservesLimitIso_hom_π]
        exact (limit.π (Discrete.functor S) j).comm₂₃)
  let ν : (ShortComplex.homologyFunctor (Discrete I ⥤ A)).obj T
        ≅ Discrete.functor (fun i => H.obj (S i)) :=
    Discrete.natIso (fun i =>
      ((ShortComplex.homologyFunctorIso ((evaluation (Discrete I) A).obj i)).app T).symm)
  have hcomp : ∀ i : Discrete I,
      μ.hom ≫ T.mapNatTrans (τ i) = limit.π (Discrete.functor S) i := by
    intro i
    apply ShortComplex.Hom.ext
    · rw [ShortComplex.comp_τ₁, ShortComplex.mapNatTrans_τ₁]
      show (preservesLimitIso ShortComplex.π₁ (Discrete.functor S)).hom ≫ limit.π _ i = _
      rw [preservesLimitIso_hom_π]; rfl
    · rw [ShortComplex.comp_τ₂, ShortComplex.mapNatTrans_τ₂]
      show (preservesLimitIso ShortComplex.π₂ (Discrete.functor S)).hom ≫ limit.π _ i = _
      rw [preservesLimitIso_hom_π]; rfl
    · rw [ShortComplex.comp_τ₃, ShortComplex.mapNatTrans_τ₃]
      show (preservesLimitIso ShortComplex.π₃ (Discrete.functor S)).hom ≫ limit.π _ i = _
      rw [preservesLimitIso_hom_π]; rfl
  let α : H.obj (∏ᶜ S) ≅ (∏ᶜ fun i => H.obj (S i) : A) :=
    H.mapIso μ ≪≫ (ShortComplex.homologyFunctorIso lim_A).app T ≪≫ HasLimit.isoOfNatIso ν
  have hpi : piComparison H S = α.hom := by
    apply Limits.Pi.hom_ext
    intro i
    rw [Limits.piComparison_comp_π]
    simp only [α, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    rw [show (Pi.π (fun b => H.obj (S b)) i)
        = limit.π (Discrete.functor (fun b => H.obj (S b))) ⟨i⟩ from rfl]
    rw [HasLimit.isoOfNatIso_hom_π]
    rw [show ((ShortComplex.homologyFunctorIso lim_A).app T).hom
        = (T.mapHomologyIso lim_A).hom from rfl]
    rw [show limit.π ((ShortComplex.homologyFunctor (Discrete I ⥤ A)).obj T) ⟨i⟩
        = (τ ⟨i⟩).app T.homology from rfl]
    rw [show ν.hom.app ⟨i⟩
        = (T.mapHomologyIso ((evaluation (Discrete I) A).obj ⟨i⟩)).inv from by simp [ν]; rfl]
    have hnat := ShortComplex.homologyMap_mapNatTrans T (τ ⟨i⟩)
    rw [← hnat]
    show H.map (Pi.π S i) = H.map μ.hom ≫ ShortComplex.homologyMap (T.mapNatTrans (τ ⟨i⟩))
    rw [← ShortComplex.homologyFunctor_map, ← H.map_comp, hcomp ⟨i⟩]
  rw [hpi]
  infer_instance

omit [HasDerivedCategory A] [Countable I] in
theorem preservesLimitsOfShape_homologyFunctor (n : ℤ) :
    PreservesLimitsOfShape (Discrete I)
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n) := by
  -- SANITY CHECK PASSED (this is the de-facto core obligation; uses exactness)
  -- Assemble from Lemma A + Lemma B via the DEFINITIONAL factorization
  --   homologyFunctor = shortComplexFunctor ⋙ ShortComplex.homologyFunctor (rfl)
  -- and that a composite of product-preserving functors preserves products.
  have := preservesLimitsOfShape_shortComplexFunctor (A := A) (I := I) n
  have := preservesLimitsOfShape_shortComplexHomologyFunctor (A := A) (I := I)
  have hrfl : HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n
      = HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n
          ⋙ ShortComplex.homologyFunctor A := rfl
  rw [hrfl]
  infer_instance

omit [HasDerivedCategory A] [Countable I] in
theorem quasiIso_isStableUnderProductsOfShape :
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsStableUnderProductsOfShape I := by
  -- SANITY CHECK PASSED
  -- Reduce to: for each `n`, `homologyMap (Pi.map f) n` is iso, given each `f j`
  -- a quasi-iso. Conjugate `homologyMap (Pi.map f) n = Hⁿ.map (Pi.map f)` through
  -- the comparison isos `piComparison Hⁿ Xᵢ` (iso by
  -- `preservesLimitsOfShape_homologyFunctor`) and `Pi.map (Hⁿ.map ∘ f)` (iso since
  -- each `Hⁿ (f j)` is iso); naturality is `piComparison_naturality`.
  apply MorphismProperty.IsStableUnderProductsOfShape.mk
  intro X₁ X₂ _ _ f hf
  rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hpres := preservesLimitsOfShape_homologyFunctor (A := A) (I := I) n
  set F := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n with hF
  show IsIso (F.map (Limits.Pi.map f))
  have hfj : ∀ j, IsIso (F.map (f j)) := by
    intro j
    have hq := hf j
    rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff] at hq
    have h2 := hq n
    rw [quasiIsoAt_iff_isIso_homologyMap] at h2
    exact h2
  have hpc1 : IsIso (piComparison F X₁) := inferInstance
  have hpc2 : IsIso (piComparison F X₂) := inferInstance
  have hpm : IsIso (Limits.Pi.map (fun j => F.map (f j))) := by
    have : ∀ j, IsIso (F.map (f j)) := hfj
    infer_instance
  have hnat := piComparison_naturality F X₁ X₂ f
  have hrw : F.map (Limits.Pi.map f)
      = piComparison F X₁ ≫ Limits.Pi.map (fun j => F.map (f j)) ≫ inv (piComparison F X₂) := by
    rw [← Category.assoc, hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hrw]
  infer_instance

/- ===========================================================================
   `Q` preserves `I`-indexed products, via the homotopy category `K(A)`.

   The FALSE lemma `isLocalization_pi_const` (a countable product of localization
   functors need NOT be a localization functor for a property with only
   `ContainsIdentities`; it requires a calculus of fractions) has been removed.
   Instead we factor `Q ≅ quotient ⋙ Qh` (`DerivedCategory.quotientCompQhIso`)
   and show each factor preserves `Discrete I`-products:

   * `quotient : CochainComplex A ℤ ⥤ K(A)` — proved below, with no open goals
     (`preservesLimitsOfShape_quotient`), using that termwise products of complexes
     descend to products in `K(A)` (the key technical input is
     `homotopyPiOfComponents`: a homotopy of maps into a termwise product is
     assembled from componentwise homotopies).
   * `Qh : K(A) ⥤ D(A)` — this is the localization of `K(A)` at
     `HomotopyCategory.quasiIso A (up ℤ)`, which DOES have a left calculus of
     fractions; see `preservesLimitsOfShape_Qh`.
   =========================================================================== -/

/-- The canonical iso `(∏ᶜ K).X q ≅ ∏ᶜ (fun i => (K i).X q)`: the termwise product
complex evaluates in each degree to the product of the degree terms (the
degree-`q` evaluation functor preserves `I`-products). -/
noncomputable def evalProdIso (K : I → CochainComplex A ℤ) (q : ℤ) :
    (∏ᶜ K).X q ≅ (∏ᶜ fun i => (K i).X q) :=
  @asIso _ _ _ _ (piComparison (HomologicalComplex.eval A (ComplexShape.up ℤ) q) K)
    (isIso_piComparison_eval K q)

omit [HasDerivedCategory A] [Countable I] [HasExactLimitsOfShape (Discrete I) A] in
@[reassoc, simp] lemma evalProdIso_hom_π (K : I → CochainComplex A ℤ) (q : ℤ) (i : I) :
    (evalProdIso K q).hom ≫ Pi.π _ i = (Pi.π K i).f q := by
  simp only [evalProdIso, asIso_hom]
  exact piComparison_comp_π (HomologicalComplex.eval A (ComplexShape.up ℤ) q) K i

omit [HasDerivedCategory A] [Countable I] [HasExactLimitsOfShape (Discrete I) A] in
/-- Maps into `(∏ᶜ K).X n` are determined by their composites with the
`(Pi.π K i).f n` (joint monomorphism). -/
lemma hom_ext_πf {M : CochainComplex A ℤ} {K : I → CochainComplex A ℤ} {n : ℤ}
    {φ ψ : M.X n ⟶ (∏ᶜ K).X n} (h : ∀ i, φ ≫ (Pi.π K i).f n = ψ ≫ (Pi.π K i).f n) : φ = ψ := by
  rw [← cancel_mono (evalProdIso K n).hom]
  apply Limits.Pi.hom_ext
  intro i
  rw [Category.assoc, Category.assoc, evalProdIso_hom_π, h i]

omit [HasDerivedCategory A] [Countable I] [HasExactLimitsOfShape (Discrete I) A] in
@[reassoc, simp] lemma inv_πf (K : I → CochainComplex A ℤ) (q : ℤ) (i : I) :
    (evalProdIso K q).inv ≫ (Pi.π K i).f q = Pi.π _ i := by
  rw [← evalProdIso_hom_π, Iso.inv_hom_id_assoc]

/-- **Key technical input.** A homotopy of two maps `f, g : M ⟶ ∏ᶜ K` into a
termwise product complex can be assembled from componentwise homotopies
`f ≫ Pi.π K i ~ g ≫ Pi.π K i`. -/
noncomputable def homotopyPiOfComponents (M : CochainComplex A ℤ) (K : I → CochainComplex A ℤ)
    (f g : M ⟶ ∏ᶜ K) (H : ∀ i, Homotopy (f ≫ Pi.π K i) (g ≫ Pi.π K i)) :
    Homotopy f g where
  hom p q := Pi.lift (fun i => (H i).hom p q) ≫ (evalProdIso K q).inv
  zero p q hpq := by
    have : (Pi.lift (fun i => (H i).hom p q) : M.X p ⟶ _) = 0 := by
      apply Limits.Pi.hom_ext; intro i
      rw [Limits.Pi.lift_comp_π, Limits.zero_comp]
      exact (H i).zero p q hpq
    rw [this, Limits.zero_comp]
  comm n := by
    apply hom_ext_πf
    intro i
    have hcomm := (H i).comm n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at hcomm
    have key : ∀ p q : ℤ, (Pi.lift (fun i => (H i).hom p q) ≫ (evalProdIso K q).inv) ≫ (Pi.π K
        i).f q
        = (H i).hom p q := by
      intro p q; rw [Category.assoc, inv_πf, Limits.Pi.lift_comp_π]
    rw [Preadditive.add_comp, Preadditive.add_comp,
      ← dNext_comp_right, ← prevD_comp_right]
    simp only [key]
    exact hcomm

/-- The image under `quotient` of the termwise product complex, with the projection
maps, is a product fan in `K(A)`. -/
noncomputable def isLimitQuotientProductFan (K : I → CochainComplex A ℤ) :
    IsLimit (Fan.mk ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (∏ᶜ K))
      (fun i => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (Pi.π K i))) := by
  refine Fan.IsLimit.mk _
    (fun s => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        (Pi.lift (fun i => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).preimage (s.proj i))))
    ?_ ?_
  · intro s i
    change (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map _ ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (Pi.π K i) = s.proj i
    rw [← Functor.map_comp, Limits.Pi.lift_comp_π, Functor.map_preimage]
  · intro s m hm
    have hm' : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).preimage m) = m := Functor.map_preimage
            _ _
    rw [← hm']
    refine HomotopyCategory.eq_of_homotopy _ _ (homotopyPiOfComponents _ _ _ _ (fun i => ?_))
    have h2 : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).preimage m ≫ Pi.π K i)
        = (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          ((Pi.lift (fun i => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).preimage (s.proj
              i)))
            ≫ Pi.π K i) := by
      rw [Functor.map_comp, Functor.map_comp, hm', ← Functor.map_comp,
        Limits.Pi.lift_comp_π, Functor.map_preimage]
      exact hm i
    exact Classical.choice ((Quotient.functor_map_eq_iff _ _ _).mp h2)

instance hasProductHomotopyCategory (G : I → HomotopyCategory A (ComplexShape.up ℤ)) :
    HasProduct G := by
  have : G = fun i => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (G i).as := by
    funext i; obtain ⟨Y⟩ := G i; rfl
  rw [this]; exact ⟨_, isLimitQuotientProductFan (fun i => (G i).as)⟩

instance hasProductsOfShape_homotopyCategory :
    HasProductsOfShape I (HomotopyCategory A (ComplexShape.up ℤ)) :=
  ⟨fun F => hasLimit_of_iso (Discrete.natIsoFunctor (F := F)).symm⟩

instance preservesProduct_quotient (K : I → CochainComplex A ℤ) :
    PreservesLimit (Discrete.functor K) (HomotopyCategory.quotient A (ComplexShape.up ℤ)) := by
  set Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have hiso := isLimitQuotientProductFan K
  have heq : piComparison Q K
      = (hiso.conePointUniqueUpToIso (limit.isLimit (Discrete.functor (fun i => Q.obj (K
          i))))).hom := by
    apply Limits.Pi.hom_ext
    intro i
    rw [piComparison_comp_π]
    exact (IsLimit.conePointUniqueUpToIso_hom_comp hiso
      (limit.isLimit (Discrete.functor (fun i => Q.obj (K i)))) ⟨i⟩).symm
  have : IsIso (piComparison Q K) := by rw [heq]; infer_instance
  exact PreservesProduct.of_iso_comparison _ K

/-- **`quotient` preserves `I`-indexed products** (proof-complete). -/
instance preservesLimitsOfShape_quotient :
    PreservesLimitsOfShape (Discrete I) (HomotopyCategory.quotient A (ComplexShape.up ℤ)) :=
  preservesLimitsOfShape_of_discrete _

/- ===========================================================================
   `Qh` preserves `I`-indexed products.  This is the genuine remaining content of
   Tag 07KC.  It is decomposed (FORMAL SKETCH) into two well-isolated subgoals:

   (B) `localizationPreservesProductsOfShape_of_leftCalculusOfFractions`: the
       GENERAL categorical fact that a localization at a class `W` *with a left
       calculus of fractions*, whose source has `I`-products and along which `W`
       is stable, preserves `I`-products.  This is the countable/arbitrary-index
       analogue of Mathlib's `Localization.preservesProductsOfShape` (which is
       stated only for `[Finite J]` and does NOT use a calculus of fractions).
       It is INDEPENDENT of `A`, the derived category, and exactness — purely a
       fact about localizations with a left calculus of fractions.

   (A) `quasiIso_homotopyCategory_isStableUnderProductsOfShape`: the homotopy-
       category class `HomotopyCategory.quasiIso A (up ℤ)` is stable under
       `I`-products.  This is the lift of the complex-level core lemma ★
       (`quasiIso_isStableUnderProductsOfShape`) along `quotient`, using
       `HomotopyCategory.quotient_map_mem_quasiIso_iff` and
       `preservesLimitsOfShape_quotient`.

   `preservesLimitsOfShape_Qh` then just applies (B) to `L = Qh`,
   `W = HomotopyCategory.quasiIso A (up ℤ)` (which HAS a left calculus of
   fractions — this is exactly why we route through K(A) and not cochain
   complexes), with stability supplied by (A) and `I`-products in K(A) by
   `hasProductsOfShape_homotopyCategory`.
   =========================================================================== -/

/- **Subgoal (B) — the general localization lemma (the hard core).**
A localization functor `L : C ⥤ D` at a morphism class `W` that admits a *left
calculus of fractions* preserves `Discrete I`-products, provided `C` has them and
`W` is stable under them.

PROOF SKETCH.  Fix a product cone `(P, pᵢ)` in `C`
(`P = ∏ᶜ Kᵢ`, `pᵢ = Pi.π`).  Show `L.mapCone` of it is a limit via
`preservesLimit_of_preserves_limit_cone` / `mkFanLimit`.
  • EXISTENCE: given `αᵢ : L.obj X ⟶ L.obj (K i)`, use `Localization.exists_leftFraction`
    to write `αᵢ = L(sᵢ)⁻¹ ∘ L(fᵢ)` with `sᵢ ∈ W`; set `s := Limits.Pi.map s'` where
    `s'` lifts `sᵢ` to a common scheme (use that `W` is stable under `I`-products to
    get `s ∈ W`, hence `L(s)` iso), and `f := Pi.lift fᵢ`; then
    `α := L(s)⁻¹ ∘ L(f)` satisfies `L(pᵢ) ∘ α = αᵢ`.  The single morphism
    `∏ sᵢ ∈ W` is the structural substitute for an "infinite common denominator".
  • UNIQUENESS: if `L(pᵢ) ∘ α = L(pᵢ) ∘ α'`, represent `α, α'` over a common
    denominator `t ∈ W` by complex maps `g, g' : X ⟶ V`; via
    `MorphismProperty.map_eq_iff_postcomp` (the left-CoF equality criterion
    `L f₁ = L f₂ ↔ ∃ Z s, W s ∧ f₁ ≫ s = f₂ ≫ s`), for each `i` get `cᵢ ∈ W` with
    `cᵢ ∘ (aᵢ ∘ g) = cᵢ ∘ (aᵢ ∘ g')`; assemble `e := (∏ cᵢ) ∘ ⟨aᵢ⟩` and use
    stability (`∏ cᵢ ∈ W`) plus the product universal property to obtain a single
    `w ∈ W` with `w ∘ g = w ∘ g'`, hence `L(g) = L(g')` and `α = α'`.
KEY API: `Localization.exists_leftFraction`, `MorphismProperty.map_eq_iff_postcomp`,
`MorphismProperty.LeftFraction`, `preservesLimit_of_preserves_limit_cone`,
`PreservesProduct.of_iso_comparison`.  Compare the FINITE Mathlib proof
`Localization.preservesProductsOfShape` for the cone-level scaffolding. -/
/- ---------------------------------------------------------------------------
   FORMAL SKETCH of subgoal (B).

   The naive "direct construction of the localized product cone via fractions"
   has a genuinely CIRCULAR uniqueness step (the
   uniqueness reduces to joint-monicity of the localized projections, which is
   equivalent to the goal).  The CORRECT route (Strategy 1) is to MIMIC Mathlib's
   FINITE proof `Localization.preservesProductsOfShape`, whose ONLY use of
   `[Finite J]` is to synthesize the functor-category localization instance
     `((whiskeringRight (Discrete I) C D).obj L).IsLocalization (W.functorCategory (Discrete I))`.
   Everything else in Mathlib's `HasProductsOfShapeAux` machinery
   (`const ⊣ limitFunctor` via `constLimAdj.localization`, `Localization.lift`,
   `Localization.fac`, `isLimitConeOfAdj`) is index-agnostic.

   So (B) is decomposed into:
   (B1) `functorCategory_discrete_isMultiplicative` : `W^I` is multiplicative
        (objectwise, using `[W.ContainsIdentities]` and composition-stability of `W`).
   (B2) `functorCategory_discrete_hasLeftCalculusOfFractions` : `W^I` has a LEFT
        CALCULUS OF FRACTIONS (the Ore/cancellation axioms hold objectwise by
        discreteness of `Discrete I`; choice over `I` assembles the components).
   (B3) `isLocalization_whiskeringRight_discrete` : `L^I` is a localization for
        `W^I`, for arbitrary (in particular countable) `I`.  Proved via the
        explicit fractions model: `W^I.Localization ≃ (Discrete I ⥤ W.Localization)`
        (componentwise) composed with the
        whiskering of the localization equivalence `W.Localization ≃ D` of `C`.
   Then (B) itself reuses Mathlib's adjunction-transport argument with (B3) as the
   crucial instance (no finiteness needed).
   --------------------------------------------------------------------------- -/

/-- **(B1)** The objectwise property `W^I = W.functorCategory (Discrete I)` is
multiplicative.  Components: identities are objectwise `𝟙` (in `W` by
`[W.ContainsIdentities]`), composition is objectwise (in `W` by composition
stability).  Equality of natural transformations on the discrete category is
componentwise, so all checks reduce to `W` componentwise.
PROOF PLAN: `constructor` to split into `ContainsIdentities` and
`IsStableUnderComposition`; `intro`; `apply` the corresponding `W` field
componentwise (a morphism in `Discrete I ⥤ C` evaluated at `⟨i⟩` lands in `C`). -/
instance functorCategory_discrete_isMultiplicative
    {C : Type*} [Category C] (W : MorphismProperty C)
    [W.IsMultiplicative] :
    (W.functorCategory (Discrete I)).IsMultiplicative := by
  refine
    { toContainsIdentities := ⟨fun X j => ?_⟩
      toIsStableUnderComposition := ⟨fun f g hf hg j => ?_⟩ }
  · simpa using W.id_mem (X.obj j)
  · simpa using W.comp_mem _ _ (hf j) (hg j)

/-- **(B2)** The objectwise property `W^I` has a LEFT CALCULUS OF FRACTIONS.
This is the structural heart of the countability-free argument.  By discreteness
of `Discrete I`, a natural transformation is exactly an `I`-indexed family of
morphisms with NO naturality squares, so the two Ore-type axioms of
`HasLeftCalculusOfFractions` are verified componentwise and reassembled via
`Classical.choice` over `I`.
PROOF PLAN:
`refine MorphismProperty.HasLeftCalculusOfFractions.mk ?_ ?_` (the
`IsMultiplicative` instance comes from (B1)).
  • `exists_leftFraction`: given a `RightFraction X Y` in `Discrete I ⥤ C`
    (data `X ←s'← Z' →f'→ Y`-style; check exact field names of
    `MorphismProperty.RightFraction`), apply `W.exists_leftFraction` componentwise
    (each component is a `W.RightFraction (X.obj ⟨i⟩) (Y.obj ⟨i⟩)`), `choose` the
    component left fractions, assemble the codomain family and the maps as a
    natural transformation on `Discrete I` (use `Discrete.natTrans`), and check the
    roof equation componentwise (`NatTrans.ext`/`funext` + discreteness).
  • `ext`: given `f₁ f₂ : X ⟶ Y`, `s : X' ⟶ X` with `W^I s` and `s ≫ f₁ = s ≫ f₂`,
    apply `W`'s `ext` field componentwise (from `[W.HasLeftCalculusOfFractions]`),
    `choose` the per-component `t i` and codomain, assemble `t : Y ⟶ Y'` via
    `Discrete.natTrans`, conclude `W^I t` (objectwise) and `f₁ ≫ t = f₂ ≫ t`
    (componentwise).
KEY API: `MorphismProperty.HasLeftCalculusOfFractions.mk`,
`MorphismProperty.RightFraction`/`.exists_leftFraction`,
`MorphismProperty.HasLeftCalculusOfFractions.ext`, `Discrete.natTrans`,
`Discrete.functor`, `NatTrans.ext`, `Classical.choice`. -/
instance functorCategory_discrete_hasLeftCalculusOfFractions
    {C : Type*} [Category C] (W : MorphismProperty C)
    [W.HasLeftCalculusOfFractions] :
    (W.functorCategory (Discrete I)).HasLeftCalculusOfFractions := by
  -- SANITY CHECK PASSED
  apply MorphismProperty.HasLeftCalculusOfFractions.mk
  · intro X Y φ
    have hcomp : ∀ i, ∃ ψ : W.LeftFraction (X.obj i) (Y.obj i),
        (φ.f.app i) ≫ ψ.s = (φ.s.app i) ≫ ψ.f := by
      intro i
      exact (MorphismProperty.RightFraction.mk (φ.s.app i) (φ.hs i) (φ.f.app i)).exists_leftFraction
    choose ψ hψ using hcomp
    refine ⟨{ Y' := Discrete.functor (fun i => (ψ (Discrete.mk i)).Y')
              f := Discrete.natTrans (fun i => (ψ i).f)
              s := Discrete.natTrans (fun i => (ψ i).s)
              hs := fun j => (ψ j).hs }, ?_⟩
    ext j
    simpa using hψ j
  · intro X' X Y f₁ f₂ s hs hsf
    have hcomp : ∀ i, ∃ (Y' : C) (t : Y.obj i ⟶ Y'), ∃ (_ : W t),
        (f₁.app i) ≫ t = (f₂.app i) ≫ t := by
      intro i
      have happ : (s.app i) ≫ (f₁.app i) = (s.app i) ≫ (f₂.app i) := by
        have := NatTrans.congr_app hsf i
        simpa using this
      exact MorphismProperty.HasLeftCalculusOfFractions.ext (f₁.app i) (f₂.app i) (s.app i) (hs i)
          happ
    choose Y' t ht hcomp using hcomp
    refine ⟨Discrete.functor (fun i => Y' (Discrete.mk i)), Discrete.natTrans (fun i => t i),
        fun j => ht j, ?_⟩
    ext j
    simpa using hcomp j

/- **(B3)** For arbitrary `I`, the functor `L^I = (whiskeringRight (Discrete I) C D).obj L`
is a localization for `W^I = W.functorCategory (Discrete I)`.  This is the COUNTABLE
analogue of Mathlib's `[Finite J]`-only instance (which goes by
`Finite.induction_empty_option`); we instead use the explicit left-calculus-of-fractions
description of localized Hom-sets, which makes `I` irrelevant.

PROOF PLAN:
Build an equivalence `W^I.Localization ≃ (Discrete I ⥤ W.Localization)` (objectwise,
(★★)), whisker the localization equivalence `G : W.Localization ≃ D` of `C`
(`Localization.uniq W.Q L W` style), and conclude via
`Functor.IsLocalization.of_equivalences` that `L^I` is a localization for `W^I`.
The `IsInvertedBy` hypothesis of `of_equivalences` is `Localization.inverts L W`
componentwise; the `≤ isoClosure.inverseImage` hypothesis is the comparison.
ALTERNATIVELY, if the explicit-model equivalence proves too heavy, this can be
proved separately in general: it is a self-contained, finiteness-free
category-theory fact.
KEY API: `Functor.IsLocalization.of_equivalences`, `Localization.uniq`,
`MorphismProperty.LeftFraction`/`LeftFractionRel`, `whiskeringRight`,
`CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions` (from (B2)),
`Localization.inverts`. -/
omit [Countable I] in
/-- The objectwise property `W^I` is inverted by `L^I` for any localization `L` of `W`:
indeed `(L^I.map f).app i = L.map (f.app i)`, which is an iso whenever `W (f.app i)`
(`Localization.inverts`), and a natural transformation on a discrete category is an
isomorphism as soon as each component is. -/
theorem isInvertedBy_whiskeringRight_discrete
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] :
    (W.functorCategory (Discrete I)).IsInvertedBy ((whiskeringRight (Discrete I) C D).obj L) := by
  intro X Y f hf
  have : ∀ j : Discrete I, IsIso ((((whiskeringRight (Discrete I) C D).obj L).map f).app j) :=
    fun j => Localization.inverts L W (f.app j) (hf j)
  exact NatIso.isIso_of_isIso_app _

omit [Countable I] in
/-- **Transfer step for (B3).**  If the *canonical* whiskered localization functor
`Q^I = (whiskeringRight (Discrete I) C W.Localization).obj W.Q` is a localization for
`W^I`, then so is `L^I` for *any* localization `L` of `W`.  We transport along the
equivalence `W.Localization ≌ D` coming from `Localization.uniq W.Q L W`, whiskered by
`Discrete I` (`Equivalence.congrRight`), using `Functor.IsLocalization.of_equivalences`
with the identity equivalence on the source.  The crucial definitional fact is
`Q^I ⋙ (Equivalence.congrRight G).functor = (whiskeringRight _ _ _).obj (W.Q ⋙ G.functor)`,
which holds by `rfl`. -/
theorem isLocalization_whiskeringRight_discrete_of_Q
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [((whiskeringRight (Discrete I) C W.Localization).obj W.Q).IsLocalization
        (W.functorCategory (Discrete I))] :
    ((whiskeringRight (Discrete I) C D).obj L).IsLocalization
      (W.functorCategory (Discrete I)) := by
  let G : W.Localization ≌ D := Localization.uniq W.Q L W
  let GI : (Discrete I ⥤ W.Localization) ≌ (Discrete I ⥤ D) := Equivalence.congrRight G
  have ebase : W.Q ⋙ G.functor ≅ L := Localization.compUniqFunctor W.Q L W
  have eI : ((whiskeringRight (Discrete I) C D).obj L)
      ≅ (((whiskeringRight (Discrete I) C W.Localization).obj W.Q) ⋙ GI.functor) := by
    refine (?_ : ((whiskeringRight (Discrete I) C D).obj L)
        ≅ (whiskeringRight (Discrete I) C D).obj (W.Q ⋙ G.functor)).trans (eqToIso rfl)
    exact ((whiskeringRight (Discrete I) C D)).mapIso ebase.symm
  have : CatCommSq (CategoryTheory.Equivalence.refl (C := Discrete I ⥤ C)).functor
      ((whiskeringRight (Discrete I) C W.Localization).obj W.Q)
      ((whiskeringRight (Discrete I) C D).obj L)
      GI.functor := CatCommSq.mk (by
        refine (Functor.leftUnitor _).trans (eI.trans ?_)
        exact eqToIso rfl)
  refine Functor.IsLocalization.of_equivalences
    ((whiskeringRight (Discrete I) C W.Localization).obj W.Q) (W.functorCategory (Discrete I))
    ((whiskeringRight (Discrete I) C D).obj L) (W.functorCategory (Discrete I))
    (CategoryTheory.Equivalence.refl) GI ?_ ?_
  · intro X Y f hf
    exact MorphismProperty.le_isoClosure _ _ hf
  · exact isInvertedBy_whiskeringRight_discrete L W

/-- **Transport of a left-fraction map between two localizations.** If `L : C ⥤ D` and
`L' : C ⥤ E` both invert `W` (and `L` is a localization), and `Φ : D ⥤ E` satisfies
`L ⋙ Φ ≅ L'` (witnessed by `fac`), then for any left fraction `φ`, `Φ` carries `φ.map L`
to `φ.map L'` conjugated by `fac`.  This is the computational heart that lets us compare
the comparison functor `Φ` of (B3-core) on Hom-sets with the componentwise data. -/
theorem map_transport_leftFraction {C D E : Type*} [Category C] [Category D] [Category E]
    (W : MorphismProperty C) (L : C ⥤ D) (L' : C ⥤ E) [L.IsLocalization W]
    (hL : W.IsInvertedBy L) (hL' : W.IsInvertedBy L')
    (Φ : D ⥤ E) (fac : L ⋙ Φ ≅ L') {X Y : C} (φ : W.LeftFraction X Y) :
    Φ.map (φ.map L hL) = fac.hom.app X ≫ φ.map L' hL' ≫ fac.inv.app Y := by
  have hiso : IsIso (Φ.map (L.map φ.s)) := Functor.map_isIso _ _
  have nat : ∀ {P Q : C} (h : P ⟶ Q),
      Φ.map (L.map h) = fac.hom.app P ≫ L'.map h ≫ fac.inv.app Q := by
    intro P Q h
    have hh := fac.hom.naturality h
    simp only [Functor.comp_obj, Functor.comp_map] at hh ⊢
    rw [← reassoc_of% hh]
    simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  rw [← cancel_mono (Φ.map (L.map φ.s))]
  rw [← Φ.map_comp, MorphismProperty.LeftFraction.map_comp_map_s, nat φ.f, nat φ.s]
  have hms := MorphismProperty.LeftFraction.map_comp_map_s φ L' hL'
  simp only [Functor.comp_obj, Category.assoc]
  rw [← Category.assoc (fac.inv.app Y) (fac.hom.app Y), Iso.inv_hom_id_app fac Y,
    Category.id_comp, reassoc_of% hms]

/-- The componentwise left fraction of a left fraction in `Discrete I ⥤ C` for `W^I`. -/
def compFraction {C : Type*} [Category C] (W : MorphismProperty C)
    {X Y : Discrete I ⥤ C} (φ : (W.functorCategory (Discrete I)).LeftFraction X Y) (i : I) :
    W.LeftFraction (X.obj ⟨i⟩) (Y.obj ⟨i⟩) :=
  { Y' := φ.Y'.obj ⟨i⟩, f := φ.f.app ⟨i⟩, s := φ.s.app ⟨i⟩, hs := φ.hs ⟨i⟩ }

omit [Countable I] in
/-- The `i`-th component of `φ.map Q^I` is the `W.Q`-map of the `i`-th component fraction. -/
theorem compFraction_map_eq {C : Type*} [Category C] (W : MorphismProperty C)
    {X Y : Discrete I ⥤ C} (φ : (W.functorCategory (Discrete I)).LeftFraction X Y)
    (hinv : (W.functorCategory (Discrete I)).IsInvertedBy
      ((whiskeringRight (Discrete I) C W.Localization).obj W.Q)) (i : I) :
    (φ.map ((whiskeringRight (Discrete I) C W.Localization).obj W.Q) hinv).app ⟨i⟩
      = (compFraction W φ i).map W.Q (Localization.inverts W.Q W) := by
  have hi : IsIso (((whiskeringRight (Discrete I) C W.Localization).obj W.Q).map φ.s) :=
    hinv _ φ.hs
  rw [MorphismProperty.LeftFraction.map, MorphismProperty.LeftFraction.map]
  simp only [compFraction]
  rw [NatTrans.comp_app, NatIso.isIso_inv_app]
  rfl

omit [Countable I] in
/-- Assemble componentwise `LeftFractionRel` into one for `W^I` on `Discrete I ⥤ C`
(choice over `I` + discreteness). -/
theorem leftFractionRel_assemble {C : Type*} [Category C] (W : MorphismProperty C)
    {X Y : Discrete I ⥤ C} (φ₁ φ₂ : (W.functorCategory (Discrete I)).LeftFraction X Y)
    (h : ∀ i, MorphismProperty.LeftFractionRel (compFraction W φ₁ i) (compFraction W φ₂ i)) :
    MorphismProperty.LeftFractionRel φ₁ φ₂ := by
  choose Z t₁ t₂ hs hf hW using h
  refine ⟨Discrete.functor (fun i => Z i), Discrete.natTrans (fun i => t₁ i.as),
    Discrete.natTrans (fun i => t₂ i.as), ?_, ?_, ?_⟩
  · ext j; obtain ⟨i⟩ := j; simpa [compFraction] using hs i
  · ext j; obtain ⟨i⟩ := j; simpa [compFraction] using hf i
  · intro j; simpa [compFraction] using hW j.as

/-- **(B3-core)** The CANONICAL whiskered localization functor
`Q^I = (whiskeringRight (Discrete I) C W.Localization).obj W.Q` is a localization for the
objectwise property `W^I = W.functorCategory (Discrete I)`.  This is the single
self-contained, finiteness-free core fact behind (B3); everything else (transport to an
arbitrary localization `L`) is handled by `isLocalization_whiskeringRight_discrete_of_Q`.

PROOF PLAN:
Show the comparison functor
  `Φ := Localization.lift Q^I (isInvertedBy_whiskeringRight_discrete W.Q W) W^I.Q`
      : W^I.Localization ⥤ (Discrete I ⥤ W.Localization)
is an equivalence, then conclude via `Functor.IsLocalization.of_equivalence_target` (using
that `W^I.Q` is a localization by B1).  `Φ` is essentially surjective because `Q^I` is
(objectwise via `W.Q.objObjPreimageIso` + `Discrete.functor`/`NatIso.ofComponents`);
fully-faithfulness is the objectwise/discrete left-fraction Hom-set comparison (B2,
`MorphismProperty.LeftFraction.*`, single-mediator equivalence valid under CoF). -/
instance isLocalization_whiskeringRight_discrete_canonical
    {C : Type*} [Category C] (W : MorphismProperty C)
    [W.HasLeftCalculusOfFractions] :
    ((whiskeringRight (Discrete I) C W.Localization).obj W.Q).IsLocalization
      (W.functorCategory (Discrete I)) := by
  set WI : MorphismProperty (Discrete I ⥤ C) := W.functorCategory (Discrete I) with hWI
  set QI : (Discrete I ⥤ C) ⥤ (Discrete I ⥤ W.Localization) :=
    (whiskeringRight (Discrete I) C W.Localization).obj W.Q with hQI
  have hinv : WI.IsInvertedBy QI := isInvertedBy_whiskeringRight_discrete W.Q W
  set Φ : WI.Localization ⥤ (Discrete I ⥤ W.Localization) :=
    Localization.lift QI hinv WI.Q with hΦ
  have fac : WI.Q ⋙ Φ ≅ QI := Localization.fac QI hinv WI.Q
  -- Core Hom-set injectivity on objects in the image of WI.Q
  have core_inj : ∀ (X Y : Discrete I ⥤ C) (g₁ g₂ : WI.Q.obj X ⟶ WI.Q.obj Y),
      Φ.map g₁ = Φ.map g₂ → g₁ = g₂ := by
    intro X Y g₁ g₂ heq
    obtain ⟨φ₁, hφ₁⟩ := Localization.exists_leftFraction WI.Q WI g₁
    obtain ⟨φ₂, hφ₂⟩ := Localization.exists_leftFraction WI.Q WI g₂
    rw [hφ₁, hφ₂]
    rw [MorphismProperty.LeftFraction.map_eq_iff WI.Q WI]
    apply leftFractionRel_assemble
    intro i
    rw [← MorphismProperty.LeftFraction.map_eq_iff W.Q W]
    rw [← compFraction_map_eq W φ₁ hinv i, ← compFraction_map_eq W φ₂ hinv i]
    have hmt₁ := map_transport_leftFraction WI WI.Q QI (Localization.inverts WI.Q WI) hinv Φ fac φ₁
    have hmt₂ := map_transport_leftFraction WI WI.Q QI (Localization.inverts WI.Q WI) hinv Φ fac φ₂
    rw [hφ₁, hφ₂] at heq
    rw [hmt₁, hmt₂] at heq
    have hcancel : φ₁.map QI hinv = φ₂.map QI hinv := by
      have := heq
      rw [cancel_epi (fac.hom.app X)] at this
      rwa [cancel_mono (fac.inv.app Y)] at this
    rw [hcancel]
  -- Core Hom-set surjectivity on objects in the image of WI.Q
  have core_surj : ∀ (X Y : Discrete I ⥤ C) (h : Φ.obj (WI.Q.obj X) ⟶ Φ.obj (WI.Q.obj Y)),
      ∃ g : WI.Q.obj X ⟶ WI.Q.obj Y, Φ.map g = h := by
    intro X Y h
    set h' : QI.obj X ⟶ QI.obj Y := fac.inv.app X ≫ h ≫ fac.hom.app Y with hh'
    have hcomp : ∀ i, ∃ ψ : W.LeftFraction (X.obj ⟨i⟩) (Y.obj ⟨i⟩),
        h'.app ⟨i⟩ = ψ.map W.Q (Localization.inverts W.Q W) := by
      intro i
      exact Localization.exists_leftFraction W.Q W (h'.app ⟨i⟩)
    choose ψ hψ using hcomp
    set Ψ : WI.LeftFraction X Y :=
      { Y' := Discrete.functor (fun i => (ψ i).Y')
        f := Discrete.natTrans (fun i => (ψ i.as).f)
        s := Discrete.natTrans (fun i => (ψ i.as).s)
        hs := fun j => (ψ j.as).hs } with hΨ
    refine ⟨Ψ.map WI.Q (Localization.inverts WI.Q WI), ?_⟩
    rw [map_transport_leftFraction WI WI.Q QI (Localization.inverts WI.Q WI) hinv Φ fac Ψ]
    have hcf : ∀ i, compFraction W Ψ i = ψ i := by
      intro i
      simp only [compFraction]
      rfl
    have hΨQI : Ψ.map QI hinv = h' := by
      ext j
      obtain ⟨i⟩ := j
      rw [compFraction_map_eq W Ψ hinv i, hcf i]
      exact (hψ i).symm
    rw [hΨQI, hh']
    simp only [Iso.hom_inv_id_app_assoc, Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id]
  -- WI.Q is essentially surjective (it is a localization)
  have : EssSurj WI.Q := Localization.essSurj WI.Q WI
  -- Faithful Φ (reduce arbitrary objects to the image of WI.Q via objObjPreimageIso)
  have hFaithful : Faithful Φ := by
    refine ⟨fun {a b} g₁ g₂ heq => ?_⟩
    set eX : WI.Q.obj (WI.Q.objPreimage a) ≅ a := WI.Q.objObjPreimageIso a with heX
    set eY : WI.Q.obj (WI.Q.objPreimage b) ≅ b := WI.Q.objObjPreimageIso b with heY
    have key : eX.hom ≫ g₁ ≫ eY.inv = eX.hom ≫ g₂ ≫ eY.inv := by
      apply core_inj
      simp only [Functor.map_comp, heq]
    calc g₁ = eX.inv ≫ (eX.hom ≫ g₁ ≫ eY.inv) ≫ eY.hom := by
              simp [Iso.inv_hom_id_assoc]
      _ = eX.inv ≫ (eX.hom ≫ g₂ ≫ eY.inv) ≫ eY.hom := by rw [key]
      _ = g₂ := by simp [Iso.inv_hom_id_assoc]
  -- Full Φ
  have hFull : Full Φ := by
    refine ⟨fun {a b} h => ?_⟩
    set eX : WI.Q.obj (WI.Q.objPreimage a) ≅ a := WI.Q.objObjPreimageIso a with heX
    set eY : WI.Q.obj (WI.Q.objPreimage b) ≅ b := WI.Q.objObjPreimageIso b with heY
    obtain ⟨g', hg'⟩ := core_surj (WI.Q.objPreimage a) (WI.Q.objPreimage b)
      (Φ.map eX.hom ≫ h ≫ Φ.map eY.inv)
    refine ⟨eX.inv ≫ g' ≫ eY.hom, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, hg']
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id,
       Category.assoc]
    simp []
  have : Φ.IsEquivalence := by
    have : EssSurj Φ := by
      constructor
      intro Y
      refine ⟨WI.Q.obj (Discrete.functor (fun i => W.Q.objPreimage (Y.obj ⟨i⟩))), ?_⟩
      set X : Discrete I ⥤ C := Discrete.functor (fun i => W.Q.objPreimage (Y.obj ⟨i⟩)) with hX
      have hYiso : QI.obj X ≅ Y :=
        NatIso.ofComponents (fun j => by
          refine eqToIso ?_ ≪≫ W.Q.objObjPreimageIso (Y.obj j)
          obtain ⟨i⟩ := j
          rfl) (by
          rintro ⟨a⟩ ⟨b⟩ ⟨⟨(rfl : a = b)⟩⟩
          simp)
      exact ⟨(fac.app X) ≪≫ hYiso⟩
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  exact Functor.IsLocalization.of_equivalence_target WI.Q WI QI Φ.asEquivalence fac

instance isLocalization_whiskeringRight_discrete
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions] :
    ((whiskeringRight (Discrete I) C D).obj L).IsLocalization
      (W.functorCategory (Discrete I)) := by
  -- SANITY CHECK PASSED
  -- By `isLocalization_whiskeringRight_discrete_of_Q` (finiteness-free) it suffices to prove
  -- the canonical-model statement `isLocalization_whiskeringRight_discrete_canonical`.
  have := isLocalization_whiskeringRight_discrete_canonical (I := I) W
  exact isLocalization_whiskeringRight_discrete_of_Q L W

omit [Countable I] in
theorem localizationPreservesProductsOfShape_of_leftCalculusOfFractions
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions]
    [HasProductsOfShape I C] [W.IsStableUnderProductsOfShape I] :
    PreservesLimitsOfShape (Discrete I) L := by
  -- SANITY CHECK PASSED
  -- Mimic Mathlib's `Localization.preservesProductsOfShape`.  Its `HasProductsOfShapeAux`
  -- machinery (`const ⊣ limitFunctor` via `constLimAdj.localization`, `Localization.lift`,
  -- `Localization.fac`, `isLimitConeOfAdj`) is finiteness-agnostic; the ONLY use of
  -- `[Finite J]` there is to synthesize `isLocalization_whiskeringRight_discrete` (B3),
  -- which we now have for arbitrary `I`.  With that instance in scope, the SAME proof
  -- term applies.
  --   • `lim ⋙ L` inverts `W^I`:  `fun _ _ f hf => Localization.inverts L W _
  -- (MorphismProperty.limMap f hf)`
  --     (uses `[W.IsStableUnderProductsOfShape I]` for `limMap`).
  --   • `limitFunctor := Localization.lift (lim ⋙ L) (inverts) ((whiskeringRight ..).obj L)`.
  --   • `compLimitFunctorIso := Localization.fac _ _ _`.
  --   • two `CatCommSq` instances (`Functor.compConstIso` for `const`; `compLimitFunctorIso.symm`
  --     for `lim`).
  --   • `adj := constLimAdj.localization L W ((whiskeringRight ..).obj L) (W.functorCategory
  -- (Discrete I))
  --       (Functor.const _) limitFunctor`.
  --   • `isLimitMapCone F := (isLimitConeOfAdj adj (F ⋙ L)).ofIsoLimit (Cone.ext ...)`.
  --   • conclude `preservesLimit_of_preserves_limit_cone (limit.isLimit F) (isLimitMapCone F)`.
  -- If the inlined adjunction term proves fiddly, one can instead transcribe
  -- Mathlib's `Mathlib/CategoryTheory/Localization/FiniteProducts.lean` body verbatim
  -- (only dropping `[Finite J]`).
  have : ((whiskeringRight (Discrete I) C D).obj L).IsLocalization
      (W.functorCategory (Discrete I)) := isLocalization_whiskeringRight_discrete L W
  -- Transcribe Mathlib's `Localization.HasProductsOfShapeAux`, dropping `[Finite I]`.
  set L' : (Discrete I ⥤ C) ⥤ (Discrete I ⥤ D) :=
    (whiskeringRight (Discrete I) C D).obj L with hL'
  have inverts : (W.functorCategory (Discrete I)).IsInvertedBy (lim ⋙ L) :=
    fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)
  -- The candidate limit functor for the localized category.
  let limitFunctor : (Discrete I ⥤ D) ⥤ D := Localization.lift _ inverts L'
  let compLimitFunctorIso : L' ⋙ limitFunctor ≅ lim ⋙ L := Localization.fac _ inverts L'
  let sq₁ : CatCommSq (Functor.const (Discrete I)) L L' (Functor.const (Discrete I)) :=
    ⟨(Functor.compConstIso _ _).symm⟩
  let sq₂ : CatCommSq lim L' L limitFunctor := ⟨compLimitFunctorIso.symm⟩
  let adj : Functor.const _ ⊣ limitFunctor :=
    constLimAdj.localization L W L' (W.functorCategory (Discrete I))
      (Functor.const _) limitFunctor
  have adj_counit_app := fun (F : Discrete I ⥤ C) =>
    constLimAdj.localization_counit_app L W L' (W.functorCategory (Discrete I))
      (Functor.const _) limitFunctor F
  refine ⟨fun {F} => preservesLimit_of_preserves_limit_cone (limit.isLimit F) ?_⟩
  refine IsLimit.ofIsoLimit (Limits.isLimitConeOfAdj adj (F ⋙ L))
    (Cone.ext (compLimitFunctorIso.app F) ?_)
  intro j
  obtain ⟨a'⟩ := j
  have hsq1 : sq₁.iso = (Functor.compConstIso (Discrete I) L).symm := rfl
  have e2 : (CatCommSq.iso (Functor.const (Discrete I)) L L'
      (Functor.const (Discrete I))).inv = (Functor.compConstIso (Discrete I) L).hom := by
    show sq₁.iso.inv = (Functor.compConstIso (Discrete I) L).hom
    rw [hsq1, Iso.symm_inv]
  have e1 : (CatCommSq.iso lim L' L limitFunctor).inv = compLimitFunctorIso.hom := by
    show sq₂.iso.inv = compLimitFunctorIso.hom
    rw [show sq₂.iso = compLimitFunctorIso.symm from rfl, Iso.symm_inv]
  have hc : adj.counit.app (F ⋙ L) =
      (Functor.const (Discrete I)).map (compLimitFunctorIso.hom.app F) ≫
        (Functor.compConstIso (Discrete I) L).hom.app (lim.obj F) ≫
        L'.map (constLimAdj.counit.app F) := by
    rw [← e1, ← e2]; exact adj_counit_app F
  dsimp [Cone.ext, Functor.const, coneOfAdj]
  rw [hc]
  simp [constLimAdj, Functor.compConstIso, L', whiskeringRight]

omit [HasDerivedCategory A] [Countable I] in
/-- **Subgoal (A) — stability of homotopy-category quasi-isos under `I`-products.**
The class `HomotopyCategory.quasiIso A (up ℤ)` on `K(A)` is stable under
`I`-indexed products.

PROOF SKETCH.  `MorphismProperty.IsStableUnderProductsOfShape.mk`: given
`uᵢ : Lᵢ ⟶ Mᵢ` in `K(A)` with each `uᵢ` a (homotopy-class) quasi-iso, show
`Pi.map u` is a quasi-iso.  Lift each `uᵢ` to a complex map `ũᵢ` (objects of
`K(A)` are complexes; `quotient` is full and identity-on-objects, so
`uᵢ = quotient(ũᵢ)`); by `HomotopyCategory.quotient_map_mem_quasiIso_iff` each
`ũᵢ` is a complex quasi-iso, so by ★ (`quasiIso_isStableUnderProductsOfShape`)
`Pi.map ũ` is a complex quasi-iso; transport along `preservesLimitsOfShape_quotient`
(quotient sends `∏ᶜ ũ` to `Pi.map u` up to the canonical product-comparison iso)
and apply `quotient_map_mem_quasiIso_iff` again. -/
theorem quasiIso_homotopyCategory_isStableUnderProductsOfShape :
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).IsStableUnderProductsOfShape I := by
  -- SANITY CHECK PASSED
  set Q := HomotopyCategory.quotient A (ComplexShape.up ℤ) with hQ
  apply MorphismProperty.IsStableUnderProductsOfShape.mk
  intro X₁ X₂ _ _ f hf
  -- Lift each `f i` to a complex map `g i` whose `Q`-image is `f i`.
  set K₁ : I → CochainComplex A ℤ := fun i => (X₁ i).as with hK₁
  set K₂ : I → CochainComplex A ℤ := fun i => (X₂ i).as with hK₂
  set g : ∀ i, K₁ i ⟶ K₂ i := fun i => Q.preimage (f i) with hg
  have hgmap : ∀ i, Q.map (g i) = f i := fun i => Q.map_preimage (f i)
  -- Each `g i` is a complex quasi-iso.
  have hgqi : ∀ i, HomologicalComplex.quasiIso A (ComplexShape.up ℤ) (g i) := by
    intro i
    rw [← HomotopyCategory.quotient_map_mem_quasiIso_iff]
    rw [hgmap i]
    exact hf i
  -- The product `Pi.map g` is a complex quasi-iso (★-lemma).
  have hprodqi : HomologicalComplex.quasiIso A (ComplexShape.up ℤ) (Limits.Pi.map g) := by
    have hstable := quasiIso_isStableUnderProductsOfShape (A := A) (I := I)
    have heq : Limits.Pi.map g
        = Limits.limMap (Discrete.natTrans (fun X => g X.as)) := rfl
    rw [heq]
    exact MorphismProperty.limMap
      (W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _ (fun j => hgqi j.as)
  -- Hence `Q.map (Pi.map g)` is a quasi-iso in `K(A)`.
  have hQprod : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) (Q.map (Limits.Pi.map g)) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact hprodqi
  -- Transport `Q.map (Pi.map g)` to `Pi.map f` via the product comparison isos.
  -- Comparison isos `∏ᶜ Xⱼ ≅ Q.obj (∏ᶜ Kⱼ)` from `isLimitQuotientProductFan`.
  set φ₁ : (∏ᶜ X₁) ≅ Q.obj (∏ᶜ K₁) :=
    (limit.isLimit (Discrete.functor X₁)).conePointUniqueUpToIso (isLimitQuotientProductFan K₁)
    with hφ₁
  set φ₂ : (∏ᶜ X₂) ≅ Q.obj (∏ᶜ K₂) :=
    (limit.isLimit (Discrete.functor X₂)).conePointUniqueUpToIso (isLimitQuotientProductFan K₂)
    with hφ₂
  -- Projection-characterisation of the comparison hom.
  have hπ₁ : ∀ i, φ₁.hom ≫ Q.map (Pi.π K₁ i) = Pi.π X₁ i := fun i =>
    (limit.isLimit (Discrete.functor X₁)).conePointUniqueUpToIso_hom_comp
      (isLimitQuotientProductFan K₁) ⟨i⟩
  have hπ₂ : ∀ i, φ₂.hom ≫ Q.map (Pi.π K₂ i) = Pi.π X₂ i := fun i =>
    (limit.isLimit (Discrete.functor X₂)).conePointUniqueUpToIso_hom_comp
      (isLimitQuotientProductFan K₂) ⟨i⟩
  -- The comparison square commutes.
  have hsq : Limits.Pi.map f ≫ φ₂.hom = φ₁.hom ≫ Q.map (Limits.Pi.map g) := by
    refine (isLimitQuotientProductFan K₂).hom_ext (fun j => ?_)
    obtain ⟨i⟩ := j
    show (Limits.Pi.map f ≫ φ₂.hom) ≫ Q.map (Pi.π K₂ i)
      = (φ₁.hom ≫ Q.map (Limits.Pi.map g)) ≫ Q.map (Pi.π K₂ i)
    rw [Category.assoc, hπ₂ i, Limits.Pi.map_π]
    rw [Category.assoc, ← Functor.map_comp, Limits.Pi.map_π, Functor.map_comp,
      ← Category.assoc, hπ₁ i]
    -- goal: Pi.π X₁ i ≫ f i = Pi.π X₁ i ≫ Q.map (g i)
    rw [hgmap i]
  -- Transport membership along the arrow iso.
  rw [show Limits.Pi.map f
      = φ₁.hom ≫ Q.map (Limits.Pi.map g) ≫ φ₂.inv by
        rw [← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]]
  -- `quasiIso` respects iso and contains identities, so pre/post composition by isos is fine.
  have hi1 : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) φ₁.hom :=
    MorphismProperty.of_isIso _ _
  have hi2 : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) φ₂.inv :=
    MorphismProperty.of_isIso _ _
  exact (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).comp_mem _ _ hi1
    ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).comp_mem _ _ hQprod hi2)

omit [Countable I] in
theorem preservesLimitsOfShape_Qh :
    PreservesLimitsOfShape (Discrete I) (DerivedCategory.Qh (C := A)) := by
  -- Apply the general localization lemma (B) to `Qh` / `HomotopyCategory.quasiIso`,
  -- which HAS a left calculus of fractions; stability is (A), I-products in K(A)
  -- come from `hasProductsOfShape_homotopyCategory`.
  have := quasiIso_homotopyCategory_isStableUnderProductsOfShape (A := A) (I := I)
  exact localizationPreservesProductsOfShape_of_leftCalculusOfFractions
    DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

omit [Countable I] in
theorem preservesLimitsOfShape_Q :
    PreservesLimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) := by
  -- `Q ≅ quotient ⋙ Qh`, and each factor preserves `Discrete I`-products.
  have := preservesLimitsOfShape_quotient (A := A) (I := I)
  have := preservesLimitsOfShape_Qh (A := A) (I := I)
  have : PreservesLimitsOfShape (Discrete I)
      (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    comp_preservesLimitsOfShape _ _
  exact preservesLimitsOfShape_of_natIso (DerivedCategory.quotientCompQhIso A)

omit [Countable I] in
/-- **Statement 1 (Existence of products).**
The derived category `D(A)` has countable products (Definition 5).

INFORMAL ARGUMENT (sound, sanity-checked).
`Q` is essentially surjective (`(DerivedCategory.Q).EssSurj` is an instance) and,
by `preservesLimitsOfShape_Q`, preserves `I`-indexed products.  Given any family
`X : I → D(A)`, choose for each `i` a complex `K i` with `Q.obj (K i) ≅ X i`
(essential surjectivity).  Then `CochainComplex A ℤ` has the product `∏ᶜ K`
(`HasProductsOfShape I (CochainComplex A ℤ)` infers), and `Q` carries its limit
cone to a limit cone over `i ↦ Q.obj (K i)`; transporting along the isos
`Q.obj (K i) ≅ X i` (`HasLimit.iso`/`Limits.HasLimit.ofIso`-style transport, or
`hasLimitOfIso`) yields a product of `X`.  Hence `D(A)` has products of shape `I`.

PROOF STRATEGY (Lean).
`constructor; intro X` (unfold `HasProductsOfShape` to `∀ family, HasProduct`).
Pick reps `K i := (Q.objPreimage (X i))` with `Q.objObjPreimageIso`.
Use `preservesLimitsOfShape_Q` to get the mapped cone of `∏ᶜ K` is a limit
(`isLimitOfPreserves`), giving `HasProduct (fun i => Q.obj (K i))`; then transport
`HasProduct` along the natural iso `Q.obj (K ·) ≅ X` via
`hasProduct_of_iso`/`HasLimit.ofIso` (`Discrete.natIso` of the objectwise isos). -/
@[stacks 07KC "(1)"]
theorem hasProductsOfShape_derivedCategory :
    HasProductsOfShape I (DerivedCategory A) := by
  -- SANITY CHECK PASSED
  have := preservesLimitsOfShape_Q (A := A) (I := I)
  constructor
  intro X
  set K : I → CochainComplex A ℤ := fun i => DerivedCategory.Q.objPreimage (X.obj ⟨i⟩) with hK
  have hcone := isLimitOfPreserves DerivedCategory.Q (productIsProduct K)
  have : HasProduct (fun i => DerivedCategory.Q.obj (K i)) :=
    ⟨⟨_, Fan.isLimitMapConeEquiv DerivedCategory.Q K (Fan.mk (∏ᶜ K) (Pi.π K)) hcone⟩⟩
  have e : Discrete.functor (fun i => DerivedCategory.Q.obj (K i)) ≅ X :=
    Discrete.natIso (fun i => DerivedCategory.Q.objObjPreimageIso (X.obj i))
  exact hasLimit_of_iso e

universe u v

/-- The countable-products instance specialized to `ℕ`. Keeping the index universe out of
the public constant is useful when this instance occurs in the type of a universe-polymorphic
theorem. -/
theorem hasProductsOfShape_nat
    {A : Type u} [Category.{v, u} A] [Abelian A] [HasDerivedCategory A]
    [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A] :
    HasProductsOfShape ℕ (DerivedCategory A) :=
  hasProductsOfShape_derivedCategory

omit [Countable I] in
/-- **Statement 2 (Computation via termwise products).**
For any countable family `K : I → CochainComplex A ℤ` of complexes (representing
objects of `D(A)`), the image under `Q` of the termwise product complex `∏ᶜ K`,
together with the projection chain maps `Q.map (Pi.π K i)`, is a product of the
family `(Q.obj (K i))` in `D(A)`, i.e. the corresponding fan is a limit cone.
In particular the product is independent, up to canonical isomorphism in `D(A)`,
of the choice of representing complexes. -/
@[stacks 07KC "(2)"]
theorem isLimit_productFanInDerivedCategory (K : I → CochainComplex A ℤ) :
    Nonempty (IsLimit (productFanInDerivedCategory K)) := by
  -- SANITY CHECK PASSED
  -- INFORMAL ARGUMENT (sound, sanity-checked).
  -- This is the concrete-cone form of `preservesLimitsOfShape_Q`.  The fan
  -- `productFanInDerivedCategory K = Fan.mk (Q.obj (∏ᶜ K)) (fun i => Q.map (Pi.π K i))`
  -- is, up to the canonical identification of cones, the image `Q.mapCone` of the
  -- product cone `limit.cone (Discrete.functor K)` (whose apex is `∏ᶜ K` and whose
  -- legs are the `Pi.π K i`).  Since `Q` preserves `I`-products
  -- (`preservesLimitsOfShape_Q`), this mapped cone is a limit
  -- (`isLimitOfPreserves`).
  --
  -- PROOF STRATEGY (Lean).
  -- `have := preservesLimitsOfShape_Q (A := A) (I := I)`.
  -- Take `hL : IsLimit (Q.mapCone (productIsProduct K).cone)` from
  -- `isLimitOfPreserves DerivedCategory.Q (productIsProduct K)` (or
  -- `limit.isLimit (Discrete.functor K)`), then `exact ⟨hL.ofIsoLimit eFan⟩`
  -- where `eFan` is the cone iso identifying `Q.mapCone` of the product cone
  -- with `productFanInDerivedCategory K` (apex `Q.obj (∏ᶜ K)`, legs `Q.map (Pi.π K i)`;
  -- `Fan.mk` legs match `Q.map` of `Pi.π` definitionally / by `Cones.ext (Iso.refl _)`).
  have := preservesLimitsOfShape_Q (A := A) (I := I)
  have hL := isLimitOfPreserves DerivedCategory.Q (productIsProduct K)
  exact ⟨Fan.isLimitMapConeEquiv DerivedCategory.Q K (Fan.mk (∏ᶜ K) (Pi.π K)) hL⟩

omit [Countable I] in
/-- **Statement 3 (Cohomology of the product).**
For every `p ∈ ℤ` and every countable family `X : I → D(A)`, the canonical
comparison morphism
`H^p(∏ X_i) → ∏ H^p(X_i)`
induced by the projections (`piComparison` of the homology functor) is an
isomorphism in `A`.  Equivalently `H^p(∏ X_i) = ∏ H^p(X_i)` (canonical iso). -/
@[stacks 07KC "(3)"]
theorem isIso_piComparison_homologyFunctor
    [HasProductsOfShape I (DerivedCategory A)]
    (X : I → DerivedCategory A) (p : ℤ) :
    IsIso (piComparison (DerivedCategory.homologyFunctor A p) X) := by
  -- SANITY CHECK PASSED
  -- INFORMAL ARGUMENT (sound, sanity-checked).
  -- By `PreservesProduct.of_iso_comparison` it suffices to show
  -- `homologyFunctor A p` preserves the product of `X`, equivalently that the
  -- comparison `Hᵖ(∏ X_i) → ∏ Hᵖ(X_i)` is iso.  Choose representatives:
  -- `K i := Q.objPreimage (X i)` with `eᵢ : Q.obj (K i) ≅ X i`.  By Statement 2
  -- (`isLimit_productFanInDerivedCategory`), `Q.obj (∏ᶜ K)` is the product of the
  -- `Q.obj (K i)`, hence `∏ X_i ≅ Q.obj (∏ᶜ K)` compatibly with projections.
  -- Now `Hᵖ ∘ Q = ` homology of the complex (`DerivedCategory.homologyFunctor`
  -- factors the complex-level `homologyFunctor` through `Q`), and at the complex
  -- level `Hᵖ(∏ᶜ K) ≅ ∏ Hᵖ(K_i)` by the SAME exactness input as the core lemma
  -- (★) — homology commutes with the (termwise) product because
  -- `lim.PreservesHomology` holds.  Chaining the canonical isos and checking they
  -- compose to `piComparison (homologyFunctor A p) X` gives the result.
  --
  -- PROOF STRATEGY (Lean).
  -- Reduce to the complex level: pick reps via `Q.objPreimage`/`objObjPreimageIso`;
  -- transport `piComparison` along these isos (`piComparison` is natural in the
  -- family, so it suffices to treat `X i = Q.obj (K i)`).  Then use:
  --   • `isLimit_productFanInDerivedCategory K` to identify `∏ (Q.obj ∘ K)` with
  --     `Q.obj (∏ᶜ K)` (`IsLimit.conePointUniqueUpToIso`);
  --   • the natural iso `DerivedCategory.homologyFunctor A p` ∘ `Q` ≅ the
  --     complex-level `homologyFunctor _ _ p` (search:
  --     `DerivedCategory.homologyFunctorFactors` / `homologyFunctor_comp_Q`);
  --   • the complex-level commutation `Hᵖ(∏ᶜ K) ≅ ∏ Hᵖ(K_i)` derived from
  --     `(lim : (Discrete I ⥤ CochainComplex A ℤ) ⥤ _).PreservesHomology`
  --     (the same ingredient as ★), or directly
  --     `isIso (piComparison (homologyFunctor _ _ p) K)` at the complex level.
  -- Conclude `IsIso (piComparison (homologyFunctor A p) X)` by
  -- `PreservesProduct.of_iso_comparison` / matching the canonical comparison map.
  set H := DerivedCategory.homologyFunctor A p with hH
  -- It suffices to show `H` preserves `Discrete I`-products.
  suffices hpres : PreservesLimitsOfShape (Discrete I) H by
    infer_instance
  apply preservesLimitsOfShape_discrete_of_isIso_piComparison
  intro Y
  -- representatives
  set Q := DerivedCategory.Q (C := A) with hQ
  set K : I → CochainComplex A ℤ := fun i => Q.objPreimage (Y i) with hK
  -- iso family `e i : Q.obj (K i) ≅ Y i`
  let e : (i : I) → Q.obj (K i) ≅ Y i := fun i => Q.objObjPreimageIso (Y i)
  -- Step A: `IsIso (piComparison H (fun i => Q.obj (K i)))`, the representative case.
  have := preservesLimitsOfShape_Q (A := A) (I := I)
  have hcH := preservesLimitsOfShape_homologyFunctor (A := A) (I := I) p
  -- `Q ⋙ H ≅ Hᵖ` (complex level), which preserves products; hence so does `Q ⋙ H`.
  have : PreservesLimitsOfShape (Discrete I) (Q ⋙ H) :=
    preservesLimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors A p).symm
  have hQH : IsIso (piComparison (Q ⋙ H) K) := inferInstance
  have hpc := piComparison_comp_eq Q H K
  have hQc : IsIso (piComparison Q K) := inferInstance
  have hHm : IsIso (H.map (piComparison Q K)) := inferInstance
  rw [hpc] at hQH
  have hStepA : IsIso (piComparison H (fun i => Q.obj (K i))) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ (H.map (piComparison Q K)) _ hHm hQH
  -- Step B: transport to the original family `Y` along the isos `e`.
  have hnat := piComparison_naturality H (fun i => Q.obj (K i)) Y (fun i => (e i).hom)
  have hPmap : IsIso (Limits.Pi.map (fun i => H.map (e i).hom)) := by
    have : ∀ i, IsIso (H.map (e i).hom) := fun i => inferInstance
    infer_instance
  have hHpi : IsIso (H.map (Limits.Pi.map (fun i => (e i).hom))) := by
    have : IsIso (Limits.Pi.map (fun i => (e i).hom)) := by
      have : ∀ i, IsIso (e i).hom := fun i => inferInstance
      infer_instance
    infer_instance
  have hrw : piComparison H Y
      = inv (H.map (Limits.Pi.map (fun i => (e i).hom)))
        ≫ piComparison H (fun i => Q.obj (K i)) ≫ Limits.Pi.map (fun i => H.map (e i).hom) := by
    rw [hnat, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hrw]
  infer_instance

end Stacks.DerivedProducts
