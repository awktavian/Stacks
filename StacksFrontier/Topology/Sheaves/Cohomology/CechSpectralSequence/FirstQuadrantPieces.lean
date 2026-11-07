module

public import StacksFrontier.Algebra.Homology.SpectralSequence.NatRestrict
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.DoubleComplexSpectralSequences

/-!
# Pieces of the Čech-to-cohomology spectral sequence of Tag 01ES

[Stacks, Tag 01ES] needs a *first quadrant* `E₂` cohomological spectral sequence, functorial in
the sheaf, whose second page is Čech cohomology of the cohomology presheaves. What
`Stacks.Cohomology.CechSpectral.totalE₂SpectralSequence₂Functor` provides is the functorial second
spectral sequence of a double complex, carried on `ℤ × ℤ`; the implementation notes accompanying it
list three things 01ES still needs, of which the third, labelled (c) there, is "a comparison of a
`CohomologicalSpectralSequence` carried on `ℤ × ℤ` with an `E₂CohomologicalSpectralSequenceNat`
carried on `ℕ × ℕ`, which needs the first-quadrant vanishing of the pages and does not follow
from `restrictR₀` alone".

This file supplies that comparison, by applying the general restriction
`CategoryTheory.SpectralSequence.natRestrictComp` of
`StacksFrontier/Algebra/Homology/SpectralSequence/NatRestrict.lean` to
`totalE₂SpectralSequence₂Functor`. Its hypothesis is carried at the level of the ambient
category — first-quadrant vanishing of *every* double complex there — so, as
`Algebra/Homology/SpectralSequence/FirstQuadrantDoubleComplex.lean` records, this is not the
form the module's route to the tag consumes; the objectwise
`CategoryTheory.SpectralSequence.natRestrictE₂Comp` is used there instead. **Tag 01ES itself
is not stated in this file**, and nothing here carries the tag: the tag is registered in
`CechSpectralSequence/Assembled.lean` as `Stacks.Cohomology.CechSpectral.cechSpectralSequence`
(`@[stacks 01ES, sga "4 V 3.2" "ringed space, open cover"]`); the implementation notes name
the ingredients the assembly consumes.

## Main definitions

* `totalE₂SpectralSequenceNat₂Functor`: the second spectral sequence of a double complex,
  presented from its second page and restricted to the first quadrant, as a functor of the
  double complex — item (c) of the implementation notes accompanying
  `Stacks.Cohomology.CechSpectral.totalE₂SpectralSequence₂Functor`.

## Main results

* `isFirstQuadrant_totalE₂SpectralSequence₂Functor_of_isZero_pageTwo`: the vanishing hypothesis
  of `totalE₂SpectralSequenceNat₂Functor` need only be checked on the second page, which is the
  page whose terms [Stacks, Tag 0130] identifies.

## Implementation notes

The first-quadrant vanishing is an input here, not a conclusion: it is a property of the double
complex one starts from (for the Čech double complex of an injective resolution it comes from the
complex being concentrated in the first quadrant), and the identification of the second page which
would let it be read off is item (a) of those same notes. What
this file adds is that the vanishing is the *only* missing input for the index conversion, and
that it suffices to check it on the second page.

The remaining ingredients of 01ES, neither of which is supplied here, are the natural
identification of the second page with `H^p_{II}(H^q_I(K^{•,•}))` and the functorial filtered
abutment; both are registered in the module — the first as `cechPageTwoIso` and the second as
`cechAbutment` along the chain `SequenceAndSecondPage.lean` / `AbutmentIsCohomology.lean`,
which `Assembled.lean` bundles into `cechSpectralSequence` (`@[stacks 01ES]`). The latter needs
the abutment shape of [Stacks, Tag 01F6],
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo`.

## References

* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Cohomology.CechSpectral

variable (C : Type u) [Category.{v} C] [Abelian C]
  [∀ (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)),
    K.HasTotal (ComplexShape.up ℤ)]

/-- For the second spectral sequence of a double complex, presented from its second page,
first-quadrant vanishing need only be checked on that second page. -/
lemma isFirstQuadrant_totalE₂SpectralSequence₂Functor_of_isZero_pageTwo
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (h : ∀ x : ℤ × ℤ, x.1 < 0 ∨ x.2 < 0 →
      IsZero ((((totalE₂SpectralSequence₂Functor C).obj K).page 2 le_rfl).X x)) :
    SpectralSequence.IsFirstQuadrant (u := fun r => (r, 1 - r))
      ((totalE₂SpectralSequence₂Functor C).obj K) :=
  SpectralSequence.isFirstQuadrant_of_isZero_page _ h

/-- **The second spectral sequence of a double complex as a first-quadrant `E₂` cohomological
spectral sequence, functorially in the double complex.** This is item (c) of the implementation
notes accompanying `totalE₂SpectralSequence₂Functor`: the conversion of the index type from
`ℤ × ℤ` to
`ℕ × ℕ`, which 01ES needs and which `restrictR₀` does not give. The hypothesis is that every page
of the spectral sequence of every double complex vanishes outside the first quadrant; by
`isFirstQuadrant_totalE₂SpectralSequence₂Functor_of_isZero_pageTwo` it is enough to check the
second page. -/
def totalE₂SpectralSequenceNat₂Functor
    (hF : ∀ K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      SpectralSequence.IsFirstQuadrant (u := fun r => (r, 1 - r))
        ((totalE₂SpectralSequence₂Functor C).obj K)) :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      E₂CohomologicalSpectralSequenceNat C :=
  SpectralSequence.natRestrictE₂Comp (totalE₂SpectralSequence₂Functor C) hF

/-- The pages of `totalE₂SpectralSequenceNat₂Functor` are the first-quadrant restrictions of the
pages of `totalE₂SpectralSequence₂Functor`. -/
@[simp]
lemma totalE₂SpectralSequenceNat₂Functor_obj_page
    (hF : ∀ K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      SpectralSequence.IsFirstQuadrant (u := fun r => (r, 1 - r))
        ((totalE₂SpectralSequence₂Functor C).obj K))
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (r : ℤ) (hr : 2 ≤ r) :
    ((totalE₂SpectralSequenceNat₂Functor C hF).obj K).page r hr =
      HomologicalComplex.natRestrict (r, 1 - r)
        (((totalE₂SpectralSequence₂Functor C).obj K).page r hr) :=
  rfl

end Stacks.Cohomology.CechSpectral

end
