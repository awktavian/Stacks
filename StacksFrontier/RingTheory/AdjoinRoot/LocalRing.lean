module

public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Monogenic algebras over a local ring whose defining polynomial has irreducible reduction

Let `A` be a local ring with residue field `κ` and let `p : A[X]` be monic.  If the reduction
`p̄ ∈ κ[X]` is irreducible, then the monogenic algebra `AdjoinRoot p = A[X] ⧸ (p)` is again local,
its maximal ideal is the extension `𝔪 · AdjoinRoot p` of the maximal ideal of `A`, and the
structure map is a local ring map.

These are the elementary facts that make "adjoin a root of a polynomial with irreducible
reduction" an *unramified* step: nothing is added to the maximal ideal, and everything new lands
in the residue field.  They are used in two unrelated places — the construction of a strict
henselization as a colimit of étale local algebras
(`StacksFrontier.RingTheory.Etale.ResidueFieldColimit`) and the unramified extensions of discrete
valuation rings of `StacksFrontier.RingTheory.DiscreteValuationRing.MonicResidueIrreducible` — so
they live here, with no hypothesis beyond locality of `A`.

## Main results

* `AdjoinRoot.isMaximal_map_maximalIdeal`: `𝔪 · AdjoinRoot p` is maximal.
* `AdjoinRoot.isLocalRing_of_irreducible_map_residue`: `AdjoinRoot p` is local.
* `AdjoinRoot.maximalIdeal_eq_map_maximalIdeal`: its maximal ideal is `𝔪 · AdjoinRoot p`.
* `AdjoinRoot.isLocalHom_of_monic`: `A → AdjoinRoot p` is a local ring map.
* `AdjoinRoot.residue_algebraMap_eq_zero_of_mem_maximalIdeal`: the residue of the image of an
  element of `𝔪` vanishes, which is the form in which the identification of the maximal ideal is
  consumed.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace AdjoinRoot

variable {A : Type*} [CommRing A] [IsLocalRing A] {p : A[X]}

/-- **The extension of the maximal ideal to a monogenic algebra with irreducible reduction is
maximal.** If the reduction of `p` in `κ(A)[X]` is irreducible then `𝔪 · AdjoinRoot p` is a maximal
ideal of `AdjoinRoot p`, because `AdjoinRoot p ⧸ 𝔪 · AdjoinRoot p ≃ κ(A)[X] ⧸ (p̄)` is a field. -/
theorem isMaximal_map_maximalIdeal (hirr : Irreducible (p.map (residue A))) :
    ((maximalIdeal A).map (AdjoinRoot.of p)).IsMaximal := by
  have h1 : IsField (Polynomial (ResidueField A) ⧸ Ideal.span {p.map (residue A)}) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
      (PrincipalIdealRing.isMaximal_of_irreducible hirr)
  have hfield : IsField ((AdjoinRoot p) ⧸ (maximalIdeal A).map (AdjoinRoot.of p)) :=
    MulEquiv.isField h1 (AdjoinRoot.quotEquivQuotMap p (maximalIdeal A)).toRingEquiv.toMulEquiv
  exact Ideal.Quotient.maximal_of_isField _ hfield

/-- A maximal ideal of `AdjoinRoot p` for monic `p` contracts to the maximal ideal of `A`. -/
private theorem comap_of_isMaximal_eq_maximalIdeal (hp : p.Monic) (Q : Ideal (AdjoinRoot p))
    [Q.IsMaximal] :
    Q.comap (AdjoinRoot.of p) = maximalIdeal A := by
  have : Module.Finite A (AdjoinRoot p) := hp.finite_adjoinRoot
  have hint : Algebra.IsIntegral A (AdjoinRoot p) := Algebra.IsIntegral.of_finite A (AdjoinRoot p)
  rw [← AdjoinRoot.algebraMap_eq]
  exact (IsLocalRing.isMaximal_iff A).mp
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A (AdjoinRoot p))
      (algebraMap_isIntegral_iff.mpr hint) Q)

/-- **A monogenic algebra with monic irreducible reduction over a local ring is local.** Every
maximal ideal of `AdjoinRoot p` contracts to `𝔪` (the algebra is integral over `A`), hence contains
the maximal ideal `𝔪 · AdjoinRoot p`, hence equals it. -/
theorem isLocalRing_of_irreducible_map_residue (hp : p.Monic)
    (hirr : Irreducible (p.map (residue A))) : IsLocalRing (AdjoinRoot p) := by
  have hmax := isMaximal_map_maximalIdeal hirr
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨(maximalIdeal A).map (AdjoinRoot.of p), hmax, fun Q hQ => ?_⟩
  have hsub : (maximalIdeal A).map (AdjoinRoot.of p) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, comap_of_isMaximal_eq_maximalIdeal hp Q]
  exact (hmax.eq_of_le hQ.ne_top hsub).symm

/-- **The maximal ideal of a monogenic algebra with irreducible reduction is the extension of the
maximal ideal of the base.** -/
theorem maximalIdeal_eq_map_maximalIdeal (hirr : Irreducible (p.map (residue A)))
    [IsLocalRing (AdjoinRoot p)] :
    maximalIdeal (AdjoinRoot p) = (maximalIdeal A).map (AdjoinRoot.of p) :=
  ((IsLocalRing.isMaximal_iff (AdjoinRoot p)).mp (isMaximal_map_maximalIdeal hirr)).symm

/-- **A monogenic algebra of a monic polynomial is a local extension.** For `p` monic with
`AdjoinRoot p` local, `AdjoinRoot.of p` is a local ring map: `AdjoinRoot p` is integral over `A`,
so the contraction of its maximal ideal is maximal, hence is `𝔪`. -/
@[ega "0 10.3.1.4" "algebraic successor"]
theorem isLocalHom_of_monic (hp : p.Monic) [IsLocalRing (AdjoinRoot p)] :
    IsLocalHom (AdjoinRoot.of p) := by
  have h := (IsLocalRing.local_hom_TFAE (AdjoinRoot.of p)).out 1 5
  rw [h]
  exact comap_of_isMaximal_eq_maximalIdeal hp _

/-- The residue of the image of an element of the maximal ideal of `A` vanishes in
`AdjoinRoot p`. -/
theorem residue_algebraMap_eq_zero_of_mem_maximalIdeal
    (hirr : Irreducible (p.map (residue A))) [IsLocalRing (AdjoinRoot p)] {x : A}
    (hx : x ∈ maximalIdeal A) :
    residue (AdjoinRoot p) (algebraMap A (AdjoinRoot p) x) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, maximalIdeal_eq_map_maximalIdeal hirr,
    AdjoinRoot.algebraMap_eq]
  exact Ideal.mem_map_of_mem _ hx

end AdjoinRoot
