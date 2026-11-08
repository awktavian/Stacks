module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingAmple
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode

/-!
# Ampleness of the dualizing sheaf of a nodal curve (the fibre step of Stacks 0E74)

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, with
at-worst-nodal singularities and of genus at least two. The fibre step of Stacks 0E74 is the
equivalence

  `X` has no rational tail and no rational bridge  ⟺  `ω_X` is invertible and ample,

where `ω_X` is the dualizing sheaf of Stacks 0BS2 (`Stacks.Duality.dualizingSheafOverField`).
The source proves it by citing three lemmas of the chapter on algebraic curves, and this file
assembles it from exactly those statements.

## Main results

* `AlgebraicGeometry.IsRationalTail.isCurve` and `AlgebraicGeometry.IsRationalBridge.isCurve`:
  a rational tail, resp. a rational bridge, of such an `X` is a curve over `k`.
* `AlgebraicGeometry.noRationalTail_noRationalBridge_of_isAmple_dualizingSheafOverField`: the
  implication `ω_X` ample ⟹ no rational tail and no rational bridge, from the degree
  computations of Stacks 0E63 and Stacks 0E64 together with the positivity half of Stacks 0B5Y.
* `AlgebraicGeometry.isAmple_dualizingSheafOverField_iff_noRationalTail_noRationalBridge_of`:
  the equivalence conditional on the three shapes (kept for consumers that pass them as
  hypotheses), the converse being Stacks 0E3P.
* `AlgebraicGeometry.dualizingAmpleOfNoRationalTailsBridges`,
  `AlgebraicGeometry.degreeNegativeOnRationalTails` and
  `AlgebraicGeometry.degreeZeroOnRationalBridges`: the three shapes, discharged from the
  registered theorems of Stacks 0E3P, 0E63 and 0E64.
* `AlgebraicGeometry.isAmple_dualizingSheafOverField_iff_noRationalTail_noRationalBridge`: the
  equivalence proved outright from the three transports.

## Implementation notes

**Discharged in-repo.** The three inputs are the registered theorems
`AlgebraicGeometry.isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities` (Stacks 0E3P,
`Curves/ContractingRationalBridges/DualizingAmple.lean`),
`AlgebraicGeometry.invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail`
(Stacks 0E63, `Curves/ContractingRationalTails/DualizingSheafDegree.lean`) and
`AlgebraicGeometry.invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge`
(Stacks 0E64, `Curves/ContractingRationalBridges/DualizingSheafDegree.lean`). The latter two
statements carry, inside `letI`, proofs of Prop-valued facts — the invertibility of `ω_X` and of its
restriction to a component, the dimension bound of the component — which the degree does not depend
on. In the shapes below those proofs are binders, so each registered statement implies its shape by
proof irrelevance: `dualizingAmpleOfNoRationalTailsBridges`, `degreeNegativeOnRationalTails` and
`degreeZeroOnRationalBridges` are the transports, and the fibre step below is proved outright from
them.

The ampleness criterion is the positivity half of Stacks 0B5Y at an arbitrary closed subcurve,
`AlgebraicGeometry.invertibleCurveDegree_pullback_pos_of_isAmple`: a rational tail or bridge is
an integral irreducible component, of dimension one because `X` is equidimensional of dimension
one (Stacks 0BY5), hence a curve.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
* [Stacks Project, Tag 0E63](https://stacks.math.columbia.edu/tag/0E63)
* [Stacks Project, Tag 0E64](https://stacks.math.columbia.edu/tag/0E64)
* [Stacks Project, Tag 0B5Y](https://stacks.math.columbia.edu/tag/0B5Y)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- An integral closed subscheme of `X` whose support is an irreducible component is a curve
over `k` once `X` is proper of dimension one with `H⁰(X, 𝒪_X) = k`: it is integral, separated
and of finite type over `k`, and its dimension is that of `X` because `X` is equidimensional. -/
theorem isCurve_subschemeι_comp_of_mem_irreducibleComponents [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (C : X.IdealSheafData) [IsIntegral C.subscheme]
    (hC : (C.support : Set X) ∈ irreducibleComponents X) :
    IsCurve k (C.subschemeι ≫ (X ↘ Spec (.of k))) := by
  have heq := equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim
  have hCdim : topologicalKrullDim C.subscheme = 1 := by
    rw [Stacks.Chow.topologicalKrullDim_subscheme C,
      heq.topologicalKrullDim_eq_of_mem_irreducibleComponents hC, hdim]
  exact (isCurve_iff k _).2 ⟨{ }, hCdim⟩

/-- A rational tail of a proper one-dimensional scheme `X` over `k` with `H⁰(X, 𝒪_X) = k` is a
curve over `k`. -/
theorem IsRationalTail.isCurve [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    IsCurve k (C.subschemeι ≫ (X ↘ Spec (.of k))) :=
  have : IsIntegral C.subscheme := hC.1
  isCurve_subschemeι_comp_of_mem_irreducibleComponents hdim C hC.2.1

/-- A rational bridge of a proper one-dimensional scheme `X` over `k` with `H⁰(X, 𝒪_X) = k` is
a curve over `k`. -/
theorem IsRationalBridge.isCurve [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    IsCurve k (C.subschemeι ≫ (X ↘ Spec (.of k))) :=
  have : IsIntegral C.subscheme := hC.isIntegral
  isCurve_subschemeι_comp_of_mem_irreducibleComponents hdim C
    hC.support_mem_irreducibleComponents

/-- The degree of `ω_X|_C` on a rational tail is negative: the shape of Stacks 0E63, with the
Prop-valued proofs its statement fixes (invertibility of `ω_X|_C` and the dimension bound on
`C`) generalized to binders. -/
abbrev DegreeNegativeOnRationalTails : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))], topologicalKrullDim X = 1 →
    ∀ [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)],
    Stacks.Curves.HasAtWorstNodalSingularities k X →
    ∀ (C : X.IdealSheafData), IsRationalTail k X C →
    ∀ (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) < 0

/-- **Stacks 0E63, discharged.** The registered theorem
`AlgebraicGeometry.invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail`
supplies its own dimension bound and invertibility proofs inside its statement; both are
propositions, so the statement specializes to the binderized shape
`DegreeNegativeOnRationalTails` exactly. -/
theorem degreeNegativeOnRationalTails : DegreeNegativeOnRationalTails :=
  fun _ _ _ _ _ hd _ hn C hC _ _ =>
    invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail hd hn C hC

/-- The degree of `ω_X|_C` on a rational bridge is zero: the shape of Stacks 0E64, with the
Prop-valued proofs its statement fixes generalized to binders. -/
abbrev DegreeZeroOnRationalBridges : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))], topologicalKrullDim X = 1 →
    ∀ [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)],
    Stacks.Curves.HasAtWorstNodalSingularities k X →
    ∀ (C : X.IdealSheafData), IsRationalBridge k X C →
    ∀ (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) = 0

/-- **Stacks 0E64, discharged.** The registered theorem
`AlgebraicGeometry.invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge`
supplies its own dimension bound and invertibility proofs inside its statement; both are
propositions, so the statement specializes to the binderized shape
`DegreeZeroOnRationalBridges` exactly. -/
theorem degreeZeroOnRationalBridges : DegreeZeroOnRationalBridges :=
  fun _ _ _ _ _ hd _ hn C hC _ _ =>
    invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge hd hn C hC

/-- The dualizing sheaf of a nodal curve without rational tails and bridges, of genus at least
two, is invertible and ample: the shape of Stacks 0E3P. -/
abbrev DualizingAmpleOfNoRationalTailsBridges : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))], topologicalKrullDim X = 1 →
    ∀ [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)],
    Stacks.Curves.HasAtWorstNodalSingularities k X →
    (∀ C : X.IdealSheafData, ¬ IsRationalTail k X C) →
    (∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C) →
    2 ≤ genus (X ↘ Spec (.of k)) →
    ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))

/-- **Stacks 0E3P, discharged.** The registered theorem
`AlgebraicGeometry.isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities` is the shape
`DualizingAmpleOfNoRationalTailsBridges` with the same binder structure. -/
theorem dualizingAmpleOfNoRationalTailsBridges : DualizingAmpleOfNoRationalTailsBridges :=
  isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities

/-- **`ω_X` ample excludes rational tails and rational bridges** (the implication (2) ⟹ (1) of
Stacks 0E74 on the fibre). If `ω_X` is invertible and ample, its restriction to every closed
subcurve has positive degree (Stacks 0B5Y), while its degree on a rational tail is negative
(`degreeNegativeOnRationalTails`, Stacks 0E63) and on a rational bridge is zero
(`degreeZeroOnRationalBridges`, Stacks 0E64). -/
theorem noRationalTail_noRationalBridge_of_isAmple_dualizingSheafOverField
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    [hω : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))]
    (hamp : Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :
    (∀ C : X.IdealSheafData, ¬ IsRationalTail k X C) ∧
      (∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C) := by
  have hpos : ∀ (C : X.IdealSheafData), IsCurve k (C.subschemeι ≫ (X ↘ Spec (.of k))) →
      ∃ (hCdim : topologicalKrullDim C.subscheme ≤ 1) (_ : SheafOfModules.IsInvertible
        C.subscheme.presheaf C.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))),
      0 < invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) := fun C hC =>
    have hCdim : topologicalKrullDim C.subscheme ≤ 1 :=
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.subschemeι ≫ (X ↘ Spec (.of k)))).le
    ⟨hCdim, SheafOfModules.isInvertible_pullback C.subschemeι _,
      invertibleCurveDegree_pullback_pos_of_isAmple k (X ↘ Spec (.of k)) C.subschemeι hCdim _
        hamp⟩
  refine ⟨fun C hC => ?_, fun C hC => ?_⟩
  · obtain ⟨hCdim, _, hp⟩ := hpos C (hC.isCurve hdim)
    exact absurd (degreeNegativeOnRationalTails k X hdim hnodal C hC hCdim) (not_lt.2 hp.le)
  · obtain ⟨hCdim, _, hp⟩ := hpos C (hC.isCurve hdim)
    exact hp.ne' (degreeZeroOnRationalBridges k X hdim hnodal C hC hCdim)

/-- **The fibre step of Stacks 0E74, from its inputs.** Let `X` be a proper scheme of dimension
one over a field `k` with `H⁰(X, 𝒪_X) = k`, with at-worst-nodal singularities and of genus at
least two. Then `X` has no rational tail and no rational bridge if and only if its dualizing
sheaf `ω_X` is invertible and ample.

The inputs are the shapes of Stacks 0E3P, Stacks 0E63 and Stacks 0E64,
`AlgebraicGeometry.DualizingAmpleOfNoRationalTailsBridges`,
`AlgebraicGeometry.DegreeNegativeOnRationalTails` and
`AlgebraicGeometry.DegreeZeroOnRationalBridges`, now discharged in-repo by
`AlgebraicGeometry.dualizingAmpleOfNoRationalTailsBridges`,
`AlgebraicGeometry.degreeNegativeOnRationalTails` and
`AlgebraicGeometry.degreeZeroOnRationalBridges`; this conditional form is kept only for downstream
consumers that still pass the shapes through as hypotheses — see
`AlgebraicGeometry.isAmple_dualizingSheafOverField_iff_noRationalTail_noRationalBridge` for the
unconditional statement. -/
theorem isAmple_dualizingSheafOverField_iff_noRationalTail_noRationalBridge_of
    (h0E3P : DualizingAmpleOfNoRationalTailsBridges.{u})
    (h0E63 : DegreeNegativeOnRationalTails.{u}) (h0E64 : DegreeZeroOnRationalBridges.{u})
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hg : 2 ≤ genus (X ↘ Spec (.of k))) :
    ((∀ C : X.IdealSheafData, ¬ IsRationalTail k X C) ∧
        ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C) ↔
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) :=
  ⟨fun h => h0E3P k X hdim hnodal h.1 h.2 hg, fun ⟨_, hamp⟩ =>
    noRationalTail_noRationalBridge_of_isAmple_dualizingSheafOverField hdim hnodal hamp⟩

/-- **The fibre step of Stacks 0E74, discharged.** Let `X` be a proper scheme of dimension one
over a field `k` with `H⁰(X, 𝒪_X) = k`, with at-worst-nodal singularities and of genus at least
two. Then `X` has no rational tail and no rational bridge if and only if its dualizing sheaf `ω_X`
is invertible and ample. The three input shapes of the conditional form above are proved here from
the registered theorems of Stacks 0E3P, Stacks 0E63 and Stacks 0E64. -/
theorem isAmple_dualizingSheafOverField_iff_noRationalTail_noRationalBridge
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hg : 2 ≤ genus (X ↘ Spec (.of k))) :
    ((∀ C : X.IdealSheafData, ¬ IsRationalTail k X C) ∧
        ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C) ↔
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) :=
  isAmple_dualizingSheafOverField_iff_noRationalTail_noRationalBridge_of
    dualizingAmpleOfNoRationalTailsBridges degreeNegativeOnRationalTails
    degreeZeroOnRationalBridges hdim hnodal hg

end AlgebraicGeometry

end
