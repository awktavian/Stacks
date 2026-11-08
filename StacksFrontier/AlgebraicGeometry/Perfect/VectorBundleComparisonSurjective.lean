module

public import StacksFrontier.Algebra.Homology.BrutalTruncation
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Shift
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.CanonicalFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.FiniteLocallyFreeReplacement
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentative
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.LocallyFiniteCohomology
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import StacksCore.Tactic.StacksAttribute

/-!
# Surjectivity of `K₀(Vect(X)) ⟶ K₀(X)`

Let `X` be a scheme.  The comparison homomorphism
`AlgebraicGeometry.comparisonAddHom` sends the class of a finite locally free `𝒪_X`-module to
the class of that module placed in degree zero, and so maps `K₀(Vect(X))` to
`K₀(X) = K₀(D_perf(𝒪_X))`.  This file computes the class of a bounded complex `ℰ^•` of finite
locally free modules as the image of the alternating sum `∑ (-1)^i [ℰ^i]`, and deduces that the
comparison homomorphism is surjective as soon as every perfect object of `D(𝒪_X)` is isomorphic
to the image of such a complex.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.comparisonAddHom_sum_eq_cls`: the identity
  `[ℰ^•] = ∑_i (-1)^i [ℰ^i[0]]` in `K₀(D_perf(𝒪_X))`.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.surjective_comparisonAddHom`: surjectivity of
  `K₀(Vect(X)) ⟶ K₀(X)`.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.exists_isZero_homology_of_lt_of_isPerfect`: the
  cohomology of a perfect object on a quasi-compact scheme vanishes in all low degrees.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.exists_plusQuasicoherent_of_isPerfect`: a perfect
  object represented by a complex of quasi-coherent modules is represented by a bounded below
  one.
* `surjective_comparisonAddHom_of_exists_quasicoherentModel`, in the same namespace:
  surjectivity of `K₀(Vect(X)) ⟶ K₀(X)` with the hypothesis cut down from the `[stacks 0F8F]`
  theorem `exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty` of
  `Perfect/BoundedLocallyFreeComplexes/PerfectRepresentative` to the [Stacks, Tag 08DB] input
  that theorem consumes.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.surjective_comparisonAddHom_of_isNoetherian`:
  **the surjectivity half of [Stacks, Tag 0FDJ]** — surjectivity of `K₀(Vect(X)) ⟶ K₀(X)` on a
  Noetherian, quasi-separated scheme with the resolution property, with no hypothesis beyond
  those instances.

## Implementation notes

The alternating sum identity is proved by induction on the number of degrees in the supporting
range of `ℰ^•`.  The inductive step is the brutal truncation short exact sequence
`ℰ^b[b] ⟶ ℰ^• ⟶ σ_{<b} ℰ^•` of `StacksFrontier.Algebra.Homology.BrutalTruncation`: it is a
distinguished triangle of `D(𝒪_X)` with perfect vertices, so the class of `ℰ^•` is the class of
its top term in degree `b` — which is `(-1)^b` times the class of that term in degree zero — plus
the class of the truncation, to which the inductive hypothesis applies.

Surjectivity takes as a hypothesis that every perfect object of `D(𝒪_X)` is isomorphic to the
image of a bounded complex of finite locally free modules.  That is the statement of the
`[stacks 0F8F]` theorem `exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty` of
`Perfect/BoundedLocallyFreeComplexes/PerfectRepresentative`.  Under the quasi-compact,
quasi-separated and resolution-property instances that theorem discharges the hypothesis, and
`surjective_comparisonAddHom_of_isNoetherian` is surjectivity read that way; the hypothesis stays
a binder of `surjective_comparisonAddHom` because `VectorBundleComparisonBijective` supplies a
representability that need not come from those instances.  Injectivity is not proved here: it
needs the inverse homomorphism
`K₀(X) ⟶ K₀(Vect(X))` of the source, which is
`StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonBijective`.

That hypothesis can be weakened to [Stacks, Tag 08DB] read on complexes, with no boundedness
asked of the quasi-coherent representative: the two steps from there to Tag 0F8F are
`exists_plusQuasicoherent_of_isPerfect`, which truncates the representative below the degree
given by `exists_isZero_homology_of_lt_of_isPerfect`, and
`exists_boundedFiniteLocallyFree_iso_of_exists_plusQuasicoherent`, which is the application of
Tag 0F8E.  The result is `surjective_comparisonAddHom_of_exists_quasicoherentModel`.

On a Noetherian scheme with the resolution property no hypothesis is left:
`exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty`, the `[stacks 0F8F]` theorem
imported from `Perfect/BoundedLocallyFreeComplexes/PerfectRepresentative`, writes every perfect
object of `D(𝒪_X)` as the image of a bounded complex of finite locally free modules — it deduces
the affine diagonal from the resolution property by [Stacks, Tag 0F8C],
`AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal`.  That is
`surjective_comparisonAddHom_of_isNoetherian`, the surjectivity half of [Stacks, Tag 0FDJ] on a
Noetherian scheme.  The whole tag, at the source's hypotheses and with
both halves of the conclusion, is
`Stacks.Perfect.BoundedLocallyFreeComplexes.bijective_comparisonAddHom_of_hasResolutionProperty`
of `StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonBijectiveUnconditional`.

The two spellings of the derived category of the `𝒪_X`-modules — `X.Modules`, which
`PerfectDerivedCategory` is built on, and `Stacks.DerivedTensor.RingedSite.Modules
X.toRingedSpace.sheaf`, on which `AlgebraicGeometry.comparisonAddHom` carries its model — are the
same category, but instances found separately for the two are different terms and identifying
them exhausts the elaborator.  `hasDerivedCategoryStandardRingedSiteModules` names the single
standard instance at the second spelling and is activated in every section below.

The two spellings of `K₀(D_perf(𝒪_X))` — the one in the type of
`AlgebraicGeometry.comparisonAddHom`, with the level of the derived category free, and
`Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory`, which fixes
`HasDerivedCategory.standard` — are the same type, and no transport between them is needed; see
`k0_isPerfect_eq_k0_perfectDerivedCategory`.

## References

* [Stacks Project, Tag 0FDJ](https://stacks.math.columbia.edu/tag/0FDJ)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
-/

@[expose] public noncomputable section

section SchemeGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.PerfectComplexes
open Stacks.FiniteLocallyFree
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The standard derived category of the `𝒪_X`-modules, at the spelling of
`AlgebraicGeometry.comparisonAddHom`.**  The comparison homomorphism takes its derived-category
model on `Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf`, while
`Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory` takes it on `X.Modules`.
The two categories are the same, but an instance found separately for each spelling is a
different term, and identifying the two is beyond the elaborator's budget. This names the one
instance at the spelling the comparison homomorphism asks for, and is activated below wherever
the two meet. -/
@[instance_reducible]
def hasDerivedCategoryStandardRingedSiteModules (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1}
      (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) :=
  HasDerivedCategory.standard (C := X.Modules)

attribute [local instance 20000] hasDerivedCategoryStandardRingedSiteModules

/-- **The isomorphism `ℰ[0]⟦-b⟧ ≅ ℰ[b]` in the derived category.** It is the shift comparison
isomorphism of `DerivedCategory.singleFunctors`. -/
def singleFunctorShiftIso (X : Scheme.{u}) (M : X.Modules) (b : ℤ) :
    ((DerivedCategory.singleFunctor X.Modules 0).obj M)⟦(-b : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor X.Modules b).obj M :=
  ((DerivedCategory.singleFunctors X.Modules).shiftIso (-b) b 0 (by omega)).app M

/-- **A finite locally free module placed in degree `b` is a perfect object of `D(𝒪_X)`.** It is
the shift by `-b` of the same module in degree zero, which is perfect, and perfect objects form a
triangulated subcategory, hence are stable under shift. -/
theorem isPerfect_singleFunctor_shift (X : Scheme.{u}) (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) (b : ℤ) :
    IsPerfect (X := X.toRingedSpace) ((DerivedCategory.singleFunctor X.Modules b).obj M) := by
  let P : ObjectProperty (DerivedCategory X.Modules) :=
    fun K => IsPerfect (X := X.toRingedSpace) K
  exact P.prop_of_iso (singleFunctorShiftIso X M b)
    (P.le_shift (-b) _ (isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM))

/-- Perfect objects of `D(𝒪_X)` with isomorphic underlying objects have the same class in `K₀`. -/
private theorem cls_eq_of_iso_obj (X : Scheme.{u}) {A B : PerfectDerivedCategory X}
    (e : A.obj ≅ B.obj) : K0.cls A = K0.cls B :=
  K0.cls_eq_of_iso (ObjectProperty.isoMk _ e)

/-- **The class of a finite locally free module in degree `b` is `(-1)^b` times its class in
degree zero.** The module in degree `b` is the shift by `-b` of the module in degree zero, and
the shift by `n` multiplies classes in `K₀` by `(-1)^n`. -/
theorem cls_single_eq_negOnePow_smul (X : Scheme.{u}) (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
    (b : ℤ) (hb : IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules b).obj M)) :
    K0.cls (⟨_, hb⟩ : PerfectDerivedCategory X)
      = (b.negOnePow : ℤ) • K0.cls (⟨_, isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM⟩
          : PerfectDerivedCategory X) := by
  let P : ObjectProperty (DerivedCategory X.Modules) :=
    fun K => IsPerfect (X := X.toRingedSpace) K
  let A : P.FullSubcategory := ⟨_, hb⟩
  let B : P.FullSubcategory := ⟨_, isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM⟩
  calc K0.cls A = K0.cls (B⟦(-b : ℤ)⟧) :=
        cls_eq_of_iso_obj X ((singleFunctorShiftIso X M b).symm ≪≫
          ((P.ι.commShiftIso (-b : ℤ)).app B).symm)
    _ = ((-b).negOnePow : ℤ) • K0.cls B := K0.cls_shift B (-b)
    _ = (b.negOnePow : ℤ) • K0.cls B := by rw [Int.negOnePow_neg]

/-- **The class of a finite locally free module in degree `b` is `(-1)^b` times its class in
degree zero**, with the perfectness of the module in degree `b` supplied by
`Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_singleFunctor_shift`. -/
theorem cls_singleFunctor_eq_negOnePow_smul (X : Scheme.{u}) (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) (b : ℤ) :
    K0.cls (⟨(DerivedCategory.singleFunctor X.Modules b).obj M,
        isPerfect_singleFunctor_shift X M hM b⟩ : PerfectDerivedCategory X)
      = (b.negOnePow : ℤ) • K0.cls (⟨(DerivedCategory.singleFunctor X.Modules 0).obj M,
          isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM⟩ : PerfectDerivedCategory X) :=
  cls_single_eq_negOnePow_smul X M hM b (isPerfect_singleFunctor_shift X M hM b)

/-- **The two spellings of `K₀(D_perf(𝒪_X))` are the same type.** The full subcategory of
`Stacks.Cohomology.PerfectComplexes.IsPerfect` at the standard derived-category level is
`Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory`. -/
theorem k0_isPerfect_eq_k0_perfectDerivedCategory (X : Scheme.{u}) :
    K0 (ObjectProperty.FullSubcategory
        (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace)))
      = K0 (PerfectDerivedCategory X) :=
  rfl

/-- **The comparison homomorphism sends the class of a finite locally free module to the class of
that module in degree zero**, with the target read as `K₀(PerfectDerivedCategory X)`. -/
theorem comparisonAddHom_classOf' (X : Scheme.{u}) (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    comparisonAddHom X (VectorBundleKZero.classOf X M)
      = K0.cls (⟨(DerivedCategory.singleFunctor X.Modules 0).obj M,
          isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM⟩ : PerfectDerivedCategory X) :=
  comparisonAddHom_classOf X M hM _

end Stacks.Perfect.BoundedLocallyFreeComplexes

end SchemeGlue

section BoundedLocallyFreeSum

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.PerfectComplexes
open Stacks.FiniteLocallyFree
open Stacks.Perfect.BoundedLocallyFreeComplexes
open scoped ZeroObject

universe u

/-- A homological complex all of whose terms are zero objects is itself a zero object. -/
theorem HomologicalComplex.isZero_of_forall_isZero_X {V : Type*} [Category V]
    [HasZeroMorphisms V] {ι : Type*} {c : ComplexShape ι} (E : HomologicalComplex V c)
    (h : ∀ i, IsZero (E.X i)) : IsZero E := by
  rw [IsZero.iff_id_eq_zero]
  ext i
  exact (h i).eq_of_src _ _

/-- Adjoining the right endpoint to `Finset.Icc a (b - 1)` gives `Finset.Icc a b`. -/
theorem Finset.insert_Icc_sub_one_eq_Icc (a b : ℤ) (h : a ≤ b) :
    insert b (Finset.Icc a (b - 1)) = Finset.Icc a b := by
  ext i
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] hasDerivedCategoryStandardRingedSiteModules

/-- A perfect object of `D(𝒪_X)` which is a zero object there has class zero in
`K₀(D_perf(𝒪_X))`: it is isomorphic, inside the subcategory of perfect objects, to the zero
object of that subcategory. -/
theorem cls_eq_zero_of_isZero (X : Scheme.{u}) (Y : DerivedCategory X.Modules)
    (hP : IsPerfect (X := X.toRingedSpace) Y) (hY : IsZero Y) :
    K0.cls (⟨Y, hP⟩ : PerfectDerivedCategory X) = 0 := by
  have hz0 : IsZero ((0 : PerfectDerivedCategory X).obj) :=
    (ObjectProperty.ι _).map_isZero (isZero_zero _)
  exact (cls_eq_of_iso_obj X (hY.iso hz0)).trans K0.cls_zero

/-- **The alternating sum identity for an empty range of degrees.**  A complex strictly supported
both in degrees `≥ a` and in degrees `≤ b` with `b < a` has every term zero, hence is a zero
object of `D(𝒪_X)` and has class zero, while the indexing set `Finset.Icc a b` is empty, so the
alternating sum is zero as well. -/
theorem comparisonAddHom_sum_eq_cls_of_lt (X : Scheme.{u}) (a b : ℤ) (hba : b < a)
    (E : CochainComplex X.Modules ℤ) (hge : E.IsStrictlyGE a) (hle : E.IsStrictlyLE b)
    (hP : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj E)) :
    comparisonAddHom X (∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) •
        VectorBundleKZero.classOf X (E.X i))
      = K0.cls (⟨DerivedCategory.Q.obj E, hP⟩ : PerfectDerivedCategory X) := by
  have hzE : IsZero E := HomologicalComplex.isZero_of_forall_isZero_X E fun i => by
    by_cases hi : a ≤ i
    · exact E.isZero_of_isStrictlyLE b i (by omega)
    · exact E.isZero_of_isStrictlyGE a i (by omega)
  have h0 : (∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • VectorBundleKZero.classOf X (E.X i))
      = (0 : VectorBundleKZero X) := by
    rw [Finset.Icc_eq_empty (by omega : ¬ a ≤ b), Finset.sum_empty]
  exact ((congrArg (comparisonAddHom X) h0).trans (comparisonAddHom X).map_zero).trans
    (cls_eq_zero_of_isZero X _ hP (DerivedCategory.Q.map_isZero hzE)).symm

/-- **The alternating sum identity, by induction on the length of the supporting range.**  The
bounds are explicit arguments rather than instances so that the inductive hypothesis can be
applied to the brutal truncation, whose supporting range is one degree shorter. -/
@[sga "6 0 3.1" "partial"]
theorem comparisonAddHom_sum_eq_cls_aux (X : Scheme.{u}) (a : ℤ) :
    ∀ (n : ℕ) (b : ℤ), b + 1 - a = (n : ℤ) → ∀ (E : CochainComplex X.Modules ℤ),
      E.IsStrictlyGE a → E.IsStrictlyLE b →
      (∀ i : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (E.X i)) →
      ∀ hP : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj E),
        comparisonAddHom X (∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) •
            VectorBundleKZero.classOf X (E.X i))
          = K0.cls (⟨DerivedCategory.Q.obj E, hP⟩ : PerfectDerivedCategory X) := by
  intro n
  induction n with
  | zero =>
    intro b hb E hge hle _ hP
    exact comparisonAddHom_sum_eq_cls_of_lt X a b (by omega) E hge hle hP
  | succ n ih =>
    intro b hb E hge hle hflf hP
    -- Every term of the brutal truncation is finite locally free: away from degree `b` it is a
    -- term of `E`, and in degree `b` it is a zero object.
    have hE'flf : ∀ i : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        ((CochainComplex.brutalTrunc (V := X.Modules) E b).X i) := by
      intro i
      by_cases hi : i = b
      · rw [hi]
        exact @IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ (0 : X.Modules) _
          ((isZero_zero X.Modules).iso (CochainComplex.isZero_brutalTrunc_X_self E b))
          (VectorBundleKZero.isFiniteLocallyFree_zero X)
      · exact @IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ (E.X i) _
          (CochainComplex.brutalTruncXIso E b i hi).symm (hflf i)
    -- The three vertices of the brutal truncation triangle are perfect.
    have h1 : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) b).obj (E.X b))) :=
      isPerfect_singleFunctor_shift X (E.X b) (hflf b) b
    have h3 : IsPerfect (X := X.toRingedSpace)
        (DerivedCategory.Q.obj (CochainComplex.brutalTrunc (V := X.Modules) E b)) :=
      Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_boundedFiniteLocallyFree X _
        ⟨⟨⟨a, CochainComplex.isStrictlyGE_brutalTrunc E b a⟩,
          ⟨b - 1, CochainComplex.isStrictlyLE_brutalTrunc E b⟩⟩, hE'flf⟩
    -- The brutal truncation short exact sequence is a distinguished triangle, so the classes add.
    have key := K0.cls_eq_add_of_distinguished_of_prop
      (show ObjectProperty (DerivedCategory X.Modules) from
        fun K => IsPerfect (X := X.toRingedSpace) K) h1 hP h3 _ _ _
      (DerivedCategory.triangleOfSES_distinguished
        (CochainComplex.brutalTruncShortComplex_shortExact E b))
    -- The top term contributes its degree-zero class with the sign `(-1)^b`.
    have hsingle : K0.cls (⟨_, h1⟩ : PerfectDerivedCategory X)
        = (b.negOnePow : ℤ) • comparisonAddHom X (VectorBundleKZero.classOf X (E.X b)) :=
      (cls_single_eq_negOnePow_smul X (E.X b) (hflf b) b h1).trans
        (congrArg ((b.negOnePow : ℤ) • ·)
          (comparisonAddHom_classOf' X (E.X b) (hflf b)).symm)
    -- The inductive hypothesis applies to the brutal truncation.
    have hIH := ih (b - 1) (by omega) (CochainComplex.brutalTrunc (V := X.Modules) E b)
      (CochainComplex.isStrictlyGE_brutalTrunc E b a)
      (CochainComplex.isStrictlyLE_brutalTrunc E b) hE'flf h3
    -- In the degrees it keeps, the brutal truncation has the terms of `E`.
    have hsum : (∑ i ∈ Finset.Icc a (b - 1), (i.negOnePow : ℤ) • VectorBundleKZero.classOf X
          ((CochainComplex.brutalTrunc (V := X.Modules) E b).X i))
        = ∑ i ∈ Finset.Icc a (b - 1), (i.negOnePow : ℤ) • VectorBundleKZero.classOf X (E.X i) :=
      Finset.sum_congr rfl fun i hi => by
        have hib : i ≠ b := by
          rw [Finset.mem_Icc] at hi
          omega
        rw [VectorBundleKZero.classOf_eq_of_iso (CochainComplex.brutalTruncXIso E b i hib)
          (hE'flf i)]
    have hIH' := (congrArg (comparisonAddHom X) hsum.symm).trans hIH
    -- Split the degree `b` summand off the alternating sum.
    have hnot : b ∉ Finset.Icc a (b - 1) := by
      rw [Finset.mem_Icc]
      omega
    have hsplit := Finset.sum_insert (f := fun i : ℤ => (i.negOnePow : ℤ) •
      VectorBundleKZero.classOf X (E.X i)) hnot
    rw [Finset.insert_Icc_sub_one_eq_Icc a b (by omega)] at hsplit
    have hL := congrArg (comparisonAddHom X) hsplit
    simp only [map_add, map_zsmul] at hL
    exact hL.trans ((congrArg₂ (fun s t : K0 (PerfectDerivedCategory X) => s + t) hsingle
      hIH'.symm).symm.trans key.symm)

/-- **The class of a bounded complex of finite locally free modules is the alternating sum of the
classes of its terms.**  For a cochain complex `E` of `𝒪_X`-modules strictly supported in the
degrees `a ≤ i ≤ b` with every term finite locally free, the identity
`[E^•] = Σ_{i = a}^{b} (-1)^i [E^i[0]]` holds in `K₀(D_perf(𝒪_X))`, the classes of the terms
being taken through the comparison homomorphism out of `K₀(Vect(X))`. -/
@[sga "6 0 3.1" "partial"]
theorem comparisonAddHom_sum_eq_cls (X : Scheme.{u}) (a b : ℤ)
    (E : CochainComplex X.Modules ℤ) (hge : E.IsStrictlyGE a) (hle : E.IsStrictlyLE b)
    (hflf : ∀ i : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (E.X i))
    (hP : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj E)) :
    comparisonAddHom X (∑ i ∈ Finset.Icc a b,
        (i.negOnePow : ℤ) • VectorBundleKZero.classOf X (E.X i))
      = K0.cls (⟨DerivedCategory.Q.obj E, hP⟩ : PerfectDerivedCategory X) :=
  (lt_or_ge b a).elim
    (fun hba => comparisonAddHom_sum_eq_cls_of_lt X a b hba E hge hle hP)
    (fun hba => comparisonAddHom_sum_eq_cls_aux X a (b + 1 - a).toNat b (by omega) E hge hle
      hflf hP)

end Stacks.Perfect.BoundedLocallyFreeComplexes

end BoundedLocallyFreeSum

section Surjectivity

open CategoryTheory CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.Cohomology.PerfectComplexes
open Stacks.FiniteLocallyFree
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] hasDerivedCategoryStandardRingedSiteModules

/-- **The comparison homomorphism is surjective once the conclusion of the `[stacks 0F8F]`
theorem holds.** The canonical homomorphism `K₀(Vect(X)) ⟶ K₀(X) = K₀(D_perf(𝒪_X))`, which
sends the class of a finite locally free `𝒪_X`-module to the class of that module placed in
degree zero, is surjective once every perfect object of `D(𝒪_X)` is isomorphic to the image of a
bounded complex of finite locally free modules — the conclusion of
`exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty` of
`Perfect/BoundedLocallyFreeComplexes/PerfectRepresentative`, carried here as the binder `hrep`
because `StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonBijective` applies it at
representability that need not come from that theorem's instances.

The classes of perfect objects generate `K₀(D_perf(𝒪_X))`, and the class of such a complex is
the image of the alternating sum of the classes of its terms.

The surjectivity clause of [Stacks, Tag 0FDJ] is this with the hypothesis discharged, by the
registered theorem, in `surjective_comparisonAddHom_of_isNoetherian`. -/
theorem surjective_comparisonAddHom (X : Scheme.{u})
    (hrep : ∀ K : DerivedCategory X.Modules, IsPerfect (X := X.toRingedSpace) K →
      ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
        Nonempty (DerivedCategory.Q.obj E ≅ K)) :
    Function.Surjective (comparisonAddHom X) := by
  refine K0.surjective_of_forall_cls_mem_range (C := PerfectDerivedCategory X) _ fun Y => ?_
  obtain ⟨E, ⟨⟨⟨a, hge⟩, ⟨b, hle⟩⟩, hflf⟩, ⟨e⟩⟩ := hrep Y.obj Y.property
  exact ⟨∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • VectorBundleKZero.classOf X (E.X i),
    (comparisonAddHom_sum_eq_cls X a b E hge hle hflf
      (isPerfect_of_boundedFiniteLocallyFree X E ⟨⟨⟨a, hge⟩, ⟨b, hle⟩⟩, hflf⟩)).trans
    (cls_eq_of_iso_obj X e)⟩

/-- A perfect object of `D(𝒪_X)` on a quasi-compact, quasi-separated scheme with the resolution
property that admits a bounded below representative with quasi-coherent terms is the image of a
bounded complex of finite locally free modules.

This is the step of the `[stacks 0F8F]` theorem
`exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty` that follows the representability
of a perfect object by a bounded below complex of quasi-coherent modules: that representability
is the hypothesis `hmodel` here, while the registered theorem obtains it from
`exists_plus_quasicoherent_representative`, and the conclusion is drawn from it by
`Stacks.Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_quasiIso`, which is
Tag 0F8E. -/
theorem exists_boundedFiniteLocallyFree_iso_of_exists_plusQuasicoherent (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [AlgebraicGeometry.HasResolutionProperty X]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K)
    (hmodel : ∃ F : CochainComplex X.Modules ℤ, CochainComplex.plus X.Modules F ∧
      (∀ i : ℤ, (F.X i).IsQuasicoherent) ∧ Nonempty (DerivedCategory.Q.obj F ≅ K)) :
    ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) := by
  obtain ⟨F, hFplus, hFqc, ⟨eF⟩⟩ := hmodel
  have hFperf : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj F) :=
    isPerfect_of_iso eF.symm hK
  obtain ⟨E, f, hE, hf⟩ := exists_boundedFiniteLocallyFree_quasiIso X F hFplus hFqc hFperf
  exact ⟨E, hE, ⟨asIso (DerivedCategory.Q.map f) ≪≫ eF⟩⟩

/-- Surjectivity of `K₀(Vect(X)) ⟶ K₀(X)` on a quasi-compact, quasi-separated scheme with the
resolution property, for a scheme on which every perfect object of `D(𝒪_X)` has a bounded below
representative with quasi-coherent terms.

The hypothesis is the [Stacks, Tag 08DB] input that the `[stacks 0F8F]` theorem
`exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty` consumes through
`exists_plus_quasicoherent_representative`; the rest of that theorem is
`exists_boundedFiniteLocallyFree_iso_of_exists_plusQuasicoherent`. -/
theorem surjective_comparisonAddHom_of_exists_plusQuasicoherent (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [AlgebraicGeometry.HasResolutionProperty X]
    (hmodel : ∀ K : DerivedCategory X.Modules, IsPerfect (X := X.toRingedSpace) K →
      ∃ F : CochainComplex X.Modules ℤ, CochainComplex.plus X.Modules F ∧
        (∀ i : ℤ, (F.X i).IsQuasicoherent) ∧ Nonempty (DerivedCategory.Q.obj F ≅ K)) :
    Function.Surjective (comparisonAddHom X) :=
  surjective_comparisonAddHom X fun K hK =>
    exists_boundedFiniteLocallyFree_iso_of_exists_plusQuasicoherent X K hK (hmodel K hK)

end Stacks.Perfect.BoundedLocallyFreeComplexes

end Surjectivity

section QuasicoherentRepresentative

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.PerfectComplexes
open Stacks.AlgebraicGeometry.PerfectCohomology
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] hasDerivedCategoryStandardRingedSiteModules

/-- **The canonical truncation of a complex of quasi-coherent modules has quasi-coherent
terms.**  Above the truncation degree the terms are those of the complex, below it they vanish,
and at it the term is the cokernel of the incoming differential. -/
theorem isQuasicoherent_truncGE_X (X : Scheme.{u}) (H : CochainComplex X.Modules ℤ)
    (hHqc : ∀ i : ℤ, (H.X i).IsQuasicoherent) (a i : ℤ) :
    ((H.truncGE a).X i).IsQuasicoherent := by
  rcases lt_trichotomy i a with hi | hi | hi
  · exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
      (R := X.ringCatSheaf) ((H.truncGE a).isZero_of_isStrictlyGE a i hi)
  · subst hi
    have hx1 : ((H.sc i).X₁).IsQuasicoherent := hHqc _
    have hx2 : ((H.sc i).X₂).IsQuasicoherent := hHqc _
    have hcok : (cokernel ((H.sc i).f)).IsQuasicoherent :=
      Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel ((H.sc i).f)
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((CochainComplex.truncGEXIsoOpcycles H i ≪≫ (H.sc i).opcyclesIsoCokernel).symm) hcok
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (CochainComplex.truncGEXIso H a i hi).symm (hHqc i)

/-- **A perfect object represented by a complex of quasi-coherent modules is represented by a
bounded below one.**  The cohomology of a perfect object on a quasi-compact scheme vanishes in
all low degrees, so the canonical truncation of the representative at a degree below which it
vanishes is a quasi-isomorphism, and that truncation again has quasi-coherent terms.

This turns the representability statement of [Stacks, Tag 08DB] — read on complexes, with no
boundedness — into the bounded below representability that [Stacks, Tag 0F8E] consumes. -/
theorem exists_plusQuasicoherent_of_isPerfect (X : Scheme.{u}) [CompactSpace X]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K)
    (hmodel : ∃ H : CochainComplex X.Modules ℤ, (∀ i : ℤ, (H.X i).IsQuasicoherent) ∧
      Nonempty (DerivedCategory.Q.obj H ≅ K)) :
    ∃ F : CochainComplex X.Modules ℤ, CochainComplex.plus X.Modules F ∧
      (∀ i : ℤ, (F.X i).IsQuasicoherent) ∧ Nonempty (DerivedCategory.Q.obj F ≅ K) := by
  obtain ⟨H, hHqc, ⟨eH⟩⟩ := hmodel
  obtain ⟨a, ha⟩ := exists_isZero_homology_of_isPerfect X K hK
  have hQge : (DerivedCategory.Q.obj H).IsGE a :=
    (DerivedCategory.isGE_iff _ a).2 fun i hi =>
      (ha i hi).of_iso ((DerivedCategory.homologyFunctor X.Modules i).mapIso eH)
  have hHge : H.IsGE a := (DerivedCategory.isGE_Q_obj_iff H a).1 hQge
  have _ : QuasiIso (H.πTruncGE a) := inferInstance
  refine ⟨H.truncGE a, ?_, isQuasicoherent_truncGE_X X H hHqc a,
    ⟨(asIso (DerivedCategory.Q.map (H.πTruncGE a))).symm ≪≫ eH⟩⟩
  rw [CochainComplex.plus_iff]
  exact ⟨a, inferInstance⟩

/-- **The `[stacks 0F8F]` conclusion, for a perfect object with a quasi-coherent model.**  On a
quasi-compact, quasi-separated scheme with the resolution property, a perfect object of
`D(𝒪_X)` that is the image of some complex of quasi-coherent modules is the image of a bounded
complex of finite locally free modules.

Under these instances the conclusion is already the `[stacks 0F8F]` theorem
`exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty`; this is that theorem read from a
prescribed quasi-coherent model.  The hypothesis `hmodel` is Tag 08DB read on complexes, with no
boundedness asked of the representative; `exists_plusQuasicoherent_of_isPerfect` supplies the
boundedness and `exists_boundedFiniteLocallyFree_iso_of_exists_plusQuasicoherent` the
replacement of Tag 0F8E. -/
theorem exists_boundedFiniteLocallyFree_iso_of_exists_quasicoherentModel (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [AlgebraicGeometry.HasResolutionProperty X]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K)
    (hmodel : ∃ H : CochainComplex X.Modules ℤ, (∀ i : ℤ, (H.X i).IsQuasicoherent) ∧
      Nonempty (DerivedCategory.Q.obj H ≅ K)) :
    ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) :=
  exists_boundedFiniteLocallyFree_iso_of_exists_plusQuasicoherent X K hK
    (exists_plusQuasicoherent_of_isPerfect X K hK hmodel)

/-- **Surjectivity of `K₀(Vect(X)) ⟶ K₀(X)` for perfect objects with quasi-coherent models.**
On a quasi-compact, quasi-separated scheme with the resolution property the comparison
homomorphism is surjective as soon as every perfect object of `D(𝒪_X)` is the image of some
complex of quasi-coherent modules.

This is `Stacks.Perfect.BoundedLocallyFreeComplexes.surjective_comparisonAddHom` with its
hypothesis replaced by the [Stacks, Tag 08DB] input of the `[stacks 0F8F]` theorem
`exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty`: under the instances above that
input comes from `exists_plus_quasicoherent_representative`, the affine diagonal through
`AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal`, and everything the theorem
deduces from it is assembled by
`exists_boundedFiniteLocallyFree_iso_of_exists_quasicoherentModel`. -/
theorem surjective_comparisonAddHom_of_exists_quasicoherentModel (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [AlgebraicGeometry.HasResolutionProperty X]
    (hmodel : ∀ K : DerivedCategory X.Modules, IsPerfect (X := X.toRingedSpace) K →
      ∃ H : CochainComplex X.Modules ℤ, (∀ i : ℤ, (H.X i).IsQuasicoherent) ∧
        Nonempty (DerivedCategory.Q.obj H ≅ K)) :
    Function.Surjective (comparisonAddHom X) :=
  surjective_comparisonAddHom X fun K hK =>
    exists_boundedFiniteLocallyFree_iso_of_exists_quasicoherentModel X K hK (hmodel K hK)

end Stacks.Perfect.BoundedLocallyFreeComplexes

end QuasicoherentRepresentative

section Noetherian

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.PerfectComplexes
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] hasDerivedCategoryStandardRingedSiteModules

/-- **The surjectivity half of [Stacks, Tag 0FDJ].** On a Noetherian, quasi-separated scheme with
the resolution property the canonical homomorphism `K₀(Vect(X)) ⟶ K₀(X) = K₀(D_perf(𝒪_X))`, which
sends the class of a finite locally free `𝒪_X`-module to the class of that module placed in
degree zero, is surjective.

The `[stacks 0F8F]` theorem `exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty` of
`Perfect/BoundedLocallyFreeComplexes/PerfectRepresentative` — which deduces the affine diagonal
from the resolution property by [Stacks, Tag 0F8C],
`AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal` — writes every perfect object of
`D(𝒪_X)` as the image of a bounded complex of finite locally free modules. That is the
hypothesis of `Stacks.Perfect.BoundedLocallyFreeComplexes.surjective_comparisonAddHom`, which
reads off the class of such a complex as the alternating sum of the classes of its terms.

The whole tag, on a quasi-compact and quasi-separated scheme with the resolution property and
with the comparison homomorphism an isomorphism, is
`Stacks.Perfect.BoundedLocallyFreeComplexes.bijective_comparisonAddHom_of_hasResolutionProperty`
of `StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonBijectiveUnconditional`. -/
@[stacks 0FDJ "surjectivity of `K₀(Vect(X)) ⟶ K₀(X)`, for a Noetherian scheme in place of an \
arbitrary quasi-compact one: the representability that the proof needs is the registered \
`[stacks 0F8F]` theorem exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty", \
sga "6 IV 2.9" "(i)"]
theorem surjective_comparisonAddHom_of_isNoetherian (X : Scheme.{u})
    [AlgebraicGeometry.IsNoetherian X] [QuasiSeparatedSpace X]
    [AlgebraicGeometry.HasResolutionProperty X] :
    Function.Surjective (comparisonAddHom X) :=
  surjective_comparisonAddHom X (exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty X)

end Stacks.Perfect.BoundedLocallyFreeComplexes

end Noetherian

end
