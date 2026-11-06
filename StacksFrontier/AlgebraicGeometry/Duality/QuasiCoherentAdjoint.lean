module

public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentAdjoint.HomologyCoproducts
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel

/-!
# Direct sums in `D_QCoh` of an affine scheme, and the twisted inverse image over an affine base

Let `f : X ⟶ Y` be a morphism of quasi-compact, quasi-separated schemes. [Stacks, Tag 0A9E]
asserts that `Rf_* : D_QCoh(𝒪_X) ⟶ D_QCoh(𝒪_Y)` has a right adjoint, and obtains it from Brown
representability ([Stacks, Tag 0A8G]) once four geometric facts are in place: `D_QCoh(𝒪_X)` is a
triangulated subcategory of `D(𝒪_X)` ([Stacks, Tag 06VT]), it has direct sums
([Stacks, Tag 08DT]), it is compactly generated ([Stacks, Tag 09IS]), and `Rf_*` commutes with
direct sums ([Stacks, Tag 08DZ]). The formal half of that argument is already available as
`Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward`, which carries all four as
hypotheses.

This file discharges the second of them for an affine scheme. The complexes with quasi-coherent
cohomology are closed under direct sums because quasi-coherent modules on `Spec R` are
(`Stacks.Descent.isQuasicoherent_sigmaObj`) and because cohomology commutes with direct sums in a
Grothendieck abelian category (`Stacks.Duality.derivedCategoryB_isClosedUnderCoproducts`); a full
subcategory closed under colimits of a given shape has them. The index universe is the scheme
universe `u`, which is also the morphism universe of the derived category in force, so what comes
out is exactly the `HasCoproducts.{u}` that Brown representability asks for.

Together with `AlgebraicGeometry.derivedQuasicoherent_isTriangulated` — the affine case of
[Stacks, Tag 06VT] — this leaves the adjointness statement over an affine base with three
hypotheses, recorded in `Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward_of_affine`:
that `Rf_*` preserves quasi-coherence of cohomology, that the restricted functor is exact and
commutes with direct sums, and that `D_QCoh(𝒪_X)` is compactly generated.

The first of those three is then discharged as well. For a morphism of affine schemes — which is
an affine morphism — part (1) of [Stacks, Tag 08D5] is available at an arbitrary chosen model of
the derived categories as
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom`,
hence at the locally small model in force here. So the restricted functor can be formed
unconditionally (`Stacks.Duality.affineQuasiCoherentDerivedPushforward`) and
`Stacks.Duality.isLeftAdjoint_affineQuasiCoherentDerivedPushforward` carries only two of the
source's inputs: [Stacks, Tag 08DZ], that `Rf_*` commutes with direct sums, and
[Stacks, Tag 09IS], compact generation of `D_QCoh`.

Those same two inputs, and no others, are what
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward` carries for an
arbitrary quasi-compact quasi-separated morphism with quasi-compact target, where the tag is
registered. Of the two, neither is open any more. 08DZ is formalized at the
locally small model in force here, in the namespace `Stacks.Duality.DerivedPushforward`, as
`LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward`
of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSumsLocallySmall.lean`;
it takes the quasi-coherence proof `hpush` as an argument and so covers the affine restricted
functor below as well. 09IS is formalized in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/PerfectGeneratorInduction.lean`, as
`Stacks.DerivedQCoh.AnyModel.hasPerfectGenerator_of_qcqs` (`@[stacks 09IS]`) and, in the
source's own words, `Stacks.DerivedQCoh.AnyModel.exists_isPerfect_isZero_iff_forall_hom_eq_zero`
(`@[stacks 09IS]`). The two inputs are consumed and discharged together downstream, at the
`@[stacks 0A9E]` `Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs`
(`Duality/CompactGeneration/QcqsCompactGeneration.lean`) and its affine-source case
`isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isAffine`
(`Duality/CompactGeneration/AffineQuasiCoherent.lean`). Those files lie downstream of this one
in the import order, so the hypotheses are still binders here — but they are no longer open.

## Main results

* `Stacks.Duality.isQuasicoherent_isClosedUnderCoproducts` — quasi-coherent `𝒪_{Spec R}`-modules
  are closed under `u`-indexed direct sums, as an `ObjectProperty` closure statement.
* `Stacks.Duality.derivedQuasicoherent_isClosedUnderCoproducts` and
  `Stacks.Duality.hasCoproducts_quasiCoherentDerivedCategory_of_isAffine` — `D_QCoh(𝒪_{Spec R})`
  is closed under `u`-indexed direct sums and therefore has them. This is the affine case of
  [Stacks, Tag 08DT].
* `Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward_of_affine` — the Stacks proof of
  [Stacks, Tag 0A9E] for a morphism of affine schemes, with the triangulated-subcategory and
  direct-sum inputs discharged.
* `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_affine` — part (1) of
  [Stacks, Tag 08D5] for a morphism of affine schemes, at the model in force here.
* `Stacks.Duality.isLeftAdjoint_affineQuasiCoherentDerivedPushforward` — the same statement of
  [Stacks, Tag 0A9E] with the quasi-coherence input discharged too, leaving only
  [Stacks, Tag 08DZ] and [Stacks, Tag 09IS].

## Implementation notes

Everything is stated over `Spec R` rather than over a general scheme because that is the range of
the two inputs: `Stacks.Descent.isQuasicoherent_sigmaObj` is proved from the equivalence
`AlgebraicGeometry.tildeEquiv` between `R`-modules and quasi-coherent `𝒪_{Spec R}`-modules, which
exists only over an affine base, and `AlgebraicGeometry.isQuasicoherent_isWeakSerre` likewise.
No `@[stacks]` attribute is attached for that reason: a tag here would report the general Tags
08DT and 0A9E as formalized when only their affine cases are proved.

The derived category in force is the locally small one, `HasDerivedCategory.{u} X.Modules` from
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, and not
`HasDerivedCategory.standard`. This is not a matter of taste: with the standard model the
morphisms of `D(𝒪_X)` live in `Type (u + 1)` while its direct sums are only `Type u`-indexed, so
the `HasCoproducts` hypothesis of Tag 0A8G is false rather than unavailable and the conclusion
would be vacuous.

The quasi-coherence property is the `ObjectProperty` on `SheafOfModules (Spec R).ringCatSheaf`
applied to objects of the definitionally equal `(Spec R).Modules`, matching the spelling of
`AlgebraicGeometry.derivedQuasicoherent_isTriangulated`; the two views carry separately
declared `Preadditive` instances and instance search does not cross between them, so each
statement below stays in one view.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite

universe u

namespace Stacks.Duality

variable (R : CommRingCat.{u})

/-! ### Direct sums of quasi-coherent modules on an affine scheme -/

/-- **Quasi-coherent modules on an affine scheme are closed under direct sums** indexed by any
type of the scheme universe: `~` is a left adjoint and an equivalence onto the quasi-coherent
modules, so a direct sum of quasi-coherent modules is the image of a direct sum of `R`-modules. -/
instance isQuasicoherent_isClosedUnderCoproducts (J : Type u) :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderColimitsOfShape
      (Discrete J) := by
  refine IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  have (j : Discrete J) : (F.obj j).IsQuasicoherent := hF j
  exact Stacks.Descent.isQuasicoherent_colimit F

/-- The direct sum of a family of quasi-coherent `𝒪_{Spec R}`-modules is quasi-coherent, in the
form that `Stacks.Duality.derivedCategoryB_isClosedUnderCoproducts` consumes. -/
theorem isQuasicoherent_sigmaObj {J : Type u} (M : J → (Spec R).Modules)
    (hM : ∀ j, SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf (M j)) :
    SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf (∐ M) :=
  have (j : J) : (M j).IsQuasicoherent := hM j
  Stacks.Descent.isQuasicoherent_sigmaObj M

/-! ### Direct sums in `D_QCoh` of an affine scheme -/

/-- **`D_QCoh(𝒪_{Spec R})` is closed under direct sums** indexed by any type of the scheme
universe: cohomology commutes with direct sums in a Grothendieck abelian category, and the
quasi-coherent modules are closed under them. This is the affine case of [Stacks, Tag 08DT]. -/
theorem derivedQuasicoherent_isClosedUnderCoproducts (J : Type u) :
    (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).IsClosedUnderColimitsOfShape
      (Discrete J) :=
  derivedCategoryB_isClosedUnderCoproducts _ _ (AlgebraicGeometry.isQuasicoherent_isWeakSerre R)
    (isQuasicoherent_sigmaObj R)

/-- **`D_QCoh(𝒪_{Spec R})` has direct sums** indexed by any type of the scheme universe — which
is also the morphism universe of the derived category in force, so this is the hypothesis Brown
representability ([Stacks, Tag 0A8G]) asks for. Affine case of [Stacks, Tag 08DT]. -/
instance hasColimitsOfShape_discrete_quasiCoherentDerivedCategory (J : Type u) :
    HasColimitsOfShape (Discrete J) (quasiCoherentDerivedCategory (Spec R)) :=
  have := derivedQuasicoherent_isClosedUnderCoproducts R J
  inferInstance

/-- `D_QCoh(𝒪_{Spec R})` has all direct sums indexed by the scheme universe. -/
theorem hasCoproducts_quasiCoherentDerivedCategory_of_isAffine :
    HasCoproducts.{u} (quasiCoherentDerivedCategory (Spec R)) :=
  fun J => hasColimitsOfShape_discrete_quasiCoherentDerivedCategory R J

/-! ### The twisted inverse image over an affine base -/

/-- **The Stacks proof of Tag 0A9E for a morphism of affine schemes.** Let `f : Spec S ⟶ Spec R`
and suppose derived direct image preserves quasi-coherent cohomology. If the restricted derived
direct image is exact and commutes with direct sums, and `D_QCoh(𝒪_{Spec S})` is compactly
generated by a family `E`, then it has a right adjoint — the twisted inverse image `f^×`.

Compared with `Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward` this discharges
three hypotheses: that `D_QCoh` is a triangulated subcategory on either side, which over an
affine base is `AlgebraicGeometry.derivedQuasicoherent_isTriangulated`, and that
`D_QCoh(𝒪_{Spec S})` has direct sums, which is
`Stacks.Duality.hasCoproducts_quasiCoherentDerivedCategory_of_isAffine`. What remains are the
three inputs the source derives from quasi-compactness and quasi-separatedness of `f`: Tags 08D5,
08DZ and 09IS. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_of_affine
    (S : CommRingCat.{u}) (f : Spec S ⟶ Spec R)
    (hpush : ∀ (K : quasiCoherentDerivedCategory (Spec S)) (i : ℤ),
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    [(quasiCoherentDerivedPushforward f hpush).CommShift ℤ]
    [(quasiCoherentDerivedPushforward f hpush).IsTriangulated]
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (quasiCoherentDerivedPushforward f hpush)]
    {ι : Type u} (E : ι → quasiCoherentDerivedCategory (Spec S))
    [∀ (i : ι) (α : Type u),
      PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (hE : ∀ K : quasiCoherentDerivedCategory (Spec S),
      ((ofObj E).shiftClosure ℤ).rightOrthogonal K → IsZero K) :
    (quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint :=
  have := hasCoproducts_quasiCoherentDerivedCategory_of_isAffine S
  isLeftAdjoint_quasiCoherentDerivedPushforward f hpush E hE

/-! ### Discharging the quasi-coherence hypothesis over an affine base -/

/-- **Derived direct image along a morphism of affine schemes preserves quasi-coherent
cohomology.** This is part (1) of [Stacks, Tag 08D5] for an affine morphism, and it is the
hypothesis `hpush` of `Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward_of_affine`.

A morphism between affine schemes is affine, so
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom`
applies; being stated at an arbitrary chosen model of the two derived categories, it is available
at the locally small model in force here, which the `HasDerivedCategory.standard` form
`AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom` would not
be. -/
theorem isQuasicoherent_homology_derivedPushforward_of_affine
    (S : CommRingCat.{u}) (f : Spec S ⟶ Spec R) (K : quasiCoherentDerivedCategory (Spec S))
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent :=
  AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom
    f K.obj K.2 i

/-- **The restriction of `Rf_*` to `D_QCoh` for a morphism of affine schemes**, with no
quasi-coherence hypothesis supplied: it is discharged by
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_affine`. This is the functor
`Rf_* : D_QCoh(𝒪_{Spec S}) ⥤ D_QCoh(𝒪_{Spec R})` whose right adjoint [Stacks, Tag 0A9E]
produces. -/
abbrev affineQuasiCoherentDerivedPushforward (S : CommRingCat.{u}) (f : Spec S ⟶ Spec R) :
    quasiCoherentDerivedCategory (Spec S) ⥤ quasiCoherentDerivedCategory (Spec R) :=
  quasiCoherentDerivedPushforward f (isQuasicoherent_homology_derivedPushforward_of_affine R S f)

/-- **The Stacks proof of Tag 0A9E for a morphism of affine schemes, with the quasi-coherence
input discharged as well.** Let `f : Spec S ⟶ Spec R`. If `Rf_* : D_QCoh(𝒪_{Spec S}) ⥤
D_QCoh(𝒪_{Spec R})` is exact and commutes with direct sums, and `D_QCoh(𝒪_{Spec S})` is compactly
generated by a family `E`, then it has a right adjoint — the twisted inverse image `f^×`.

This strengthens `Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward_of_affine` by
removing its explicit hypothesis `hpush`, which over an affine base is
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_affine`; the functor the conclusion
is about is correspondingly the canonical
`Stacks.Duality.affineQuasiCoherentDerivedPushforward` rather than one depending on a supplied
proof. Of the inputs the source cites, what remains are exactly two: [Stacks, Tag 08DZ], that
`Rf_*` commutes with direct sums, which is the `PreservesColimitsOfShape` instance together with
the exactness instances; and [Stacks, Tag 09IS], compact generation, which is `E`, its
compactness instance and `hE`. Both are formalized in this repository — 08DZ at the locally
small model in force here, by
`DerivedPushforward.LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward`,
and 09IS as `Stacks.DerivedQCoh.AnyModel.hasPerfectGenerator_of_qcqs` (`@[stacks 09IS]`,
`DerivedQCoh/PerfectGeneratorInduction.lean`) — and both are discharged together downstream, in
`DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs` and its affine-source
case `isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isAffine`
(`Duality/CompactGeneration/AffineQuasiCoherent.lean`); those files lie downstream of this one in
the import order, so the inputs still have to be supplied by the caller here. -/
theorem isLeftAdjoint_affineQuasiCoherentDerivedPushforward
    (S : CommRingCat.{u}) (f : Spec S ⟶ Spec R)
    [(affineQuasiCoherentDerivedPushforward R S f).CommShift ℤ]
    [(affineQuasiCoherentDerivedPushforward R S f).IsTriangulated]
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (affineQuasiCoherentDerivedPushforward R S f)]
    {ι : Type u} (E : ι → quasiCoherentDerivedCategory (Spec S))
    [∀ (i : ι) (α : Type u),
      PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (hE : ∀ K : quasiCoherentDerivedCategory (Spec S),
      ((ofObj E).shiftClosure ℤ).rightOrthogonal K → IsZero K) :
    (affineQuasiCoherentDerivedPushforward R S f).IsLeftAdjoint :=
  isLeftAdjoint_quasiCoherentDerivedPushforward_of_affine R S f
    (isQuasicoherent_homology_derivedPushforward_of_affine R S f) E hE

end Stacks.Duality

end
