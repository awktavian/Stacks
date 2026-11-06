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
public import StacksFrontier.Homology.Eta.Reduction.ReductionDirectSum

/-!
# Reducing the Berthelot--Ogus eta complex modulo a nonzerodivisor

Let `f` be a nonzerodivisor in a commutative ring `A` and let `M` be a cochain complex of
`f`-torsion-free `A`-modules. This file describes the reduction `η_f M / f η_f M`: its
terms are the cohomology modules of the reduction `M/fM`, its differential is the
Bockstein operator of the fractional-power filtration of `A[1/f]`, and the canonical
comparison `η_f M ⊗_A A/fA → H^•(M/f)` is a quasi-isomorphism.

## Main definitions

* `Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerIdeal` is the submodule
  `fⁱA ⊆ A[1/f]`, with
  `Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerInclusion` its successive inclusion
  and `Stacks.EtaComplex.FractionalPowerBockstein.fractionalPowerIso` the identification `A ≅ fⁱA`
    by multiplication by `fⁱ`.
* `Stacks.EtaComplex.FractionalPowerBockstein.powerIdealShortComplex` and
  `Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex` are the two rows
    of the power-ideal
  diagram, tensored with `M`; `Stacks.EtaComplex.FractionalPowerBockstein.powerBocksteinOperator`
    is the connecting
  morphism of the lower row.
* `EtaPow.Bockstein.bocksteinOperator` and `EtaPow.Bockstein.bocksteinComplex` are the Bockstein
  differential and the complex denoted `Hᵇ(M/f)` in the source.
* `Stacks.EtaComplex.ModNonzerodivisor.etaTensorMod` is `η_f M ⊗_A A/fA`,
  `Stacks.EtaComplex.ModNonzerodivisor.etaTensorQuotientIso` its
  standard identification with `η_f M / f η_f M`, and
  `Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein` the comparison to the Bockstein
    complex.
* `Stacks.Eta.BocksteinVanishing.literalPowerQuotientShortComplex` is the reduction row
  `M ⊗ A/f → M ⊗ A/f² → M ⊗ A/f`.

## Main results

* `Stacks.Eta.Reduction.exists_boundary_subcomplex_of_etaQuotient` (tag 0F7S): modulo `f` the eta
  complex has an acyclic subcomplex with degree-`i` term `B^(i+1) ⊕ B^i`, and the quotient
  has the cohomology modules of `M/fM` as its terms.
* `powerBocksteinOperator_eq_connectingHom_comp_reduction` (tag 0GSP): the
  Bockstein operator factors through the connecting morphism of the unquotiented row.
* `EtaPow.Bockstein.bockstein_comp_bockstein` and `EtaPow.Bockstein.bocksteinComplex` (tag 0GSQ):
  consecutive Bockstein operators compose to zero, so they are the differential of a
  complex.
* `Stacks.EtaComplex.ModNonzerodivisor.etaTensorMod_to_bockstein_quasiIso` (tag 0F7T): the
  canonical map from
  `η_f M ⊗_A A/fA` to the Bockstein complex of `M/f` is a quasi-isomorphism.
* `Stacks.Eta.BocksteinVanishing.cyclesReduction_epi_iff_powerBocksteinOperator_eq_zero` (tag
  0F7Y): reduction from cycles modulo `f²` to cycles modulo `f` is surjective exactly when the
  Bockstein operator vanishes, and this holds when `f` acts injectively on `Hⁱ⁺¹(M)`.
* `Stacks.Eta.ReductionDirectSum.etaQuotient_range_eq_prod_of_cyclesReduction_surjective` (tag
  0F7Z): under
  that surjectivity the canonical map `(1, dⁱ)` embeds the degree-`i` eta term modulo `f`
  as a product of submodules of the two successive power quotients.

## Implementation notes

The eta complex, its terms and its reduction are those of
`StacksFrontier.Homology.Eta.Complex`. Fractional powers are the submodules
`EtaPow.fpowSub f A i` inside the localization, and the quotients are categorical
cokernels in `ModuleCat`, so tensoring them gives literally the complexes of the source.
Mathlib's monoidal structure on `ModuleCat` requires the ring and module universes to
coincide, which is why tags 0GSP, 0GSQ and 0F7T are stated in a single universe; tag 0F7Y
recovers independent universes by restricting scalars along `ULift.ringEquiv`.

## References

* [The Stacks Project, Tag 0F7S](https://stacks.math.columbia.edu/tag/0F7S)
* [The Stacks Project, Tag 0GSP](https://stacks.math.columbia.edu/tag/0GSP)
* [The Stacks Project, Tag 0GSQ](https://stacks.math.columbia.edu/tag/0GSQ)
* [The Stacks Project, Tag 0F7T](https://stacks.math.columbia.edu/tag/0F7T)
* [The Stacks Project, Tag 0F7Y](https://stacks.math.columbia.edu/tag/0F7Y)
* [The Stacks Project, Tag 0F7Z](https://stacks.math.columbia.edu/tag/0F7Z)
* [Berthelot--Ogus, *Notes on crystalline cohomology*, Section 8][Berthelot-Ogus]
* [Bhatt--Morrow--Scholze, *Integral p-adic Hodge theory*, Section 6][BMS]
-/

@[expose] public section

-- The eta terms and the tensor total complex are unfolded repeatedly below.

universe u v

