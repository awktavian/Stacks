module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.RingHom.Surjective
public import StacksCore.Tactic.StacksAttribute

/-!
# Stalks of a quotient affine scheme

Let `I` be an ideal of a commutative ring `R` contained in a prime ideal `p`. Then `p / I` is a
prime ideal of `R / I`, the closed immersion `Spec (R / I) ⟶ Spec R` carries it to `p`, and the
induced map of local rings is the quotient map `R_p → R_p / I R_p`.

## Main definitions

* `AlgebraicGeometry.quotientPrime`: the prime `p / I` of the quotient ring.

## Main results

* `AlgebraicGeometry.quotientPrime_comap`: the image of `p / I` in `Spec R` is `p`.
* `AlgebraicGeometry.stalkMap_quotient_surjective`: the induced map on stalks is surjective.
* `AlgebraicGeometry.stalkMap_quotient_ker`: its kernel is the extended ideal `I R_p`.

## Implementation notes

That the stalk map is `R_p → R_p / I R_p` is expressed without choosing localization
isomorphisms: the actual map of structure-sheaf stalks is asserted to be surjective, and its
kernel is identified with the image of `I` under the canonical map from `R` to the stalk.
Together these two statements say exactly that the stalk map is the canonical quotient map, and
they compose with any identification of the stalk with `R_p` rather than presupposing one.

This file covers only the stalk clause of Tag 01IG, together with the identification of the
point `x = i(z)` that clause is stated at. The remaining clauses — that the morphism is a
closed immersion of locally ringed spaces in the sense of Definition 01HK, that its base map is
a homeomorphism onto a closed subset, and that it is the closed subspace cut out by `I^~` — are
in `StacksFrontier.AlgebraicGeometry.Scheme.Immersion.QuotientClosedImmersion`, which is not
imported here: those clauses need the sheaf-theoretic development and nothing below uses them.

Both proofs go through `Scheme.localRingHom_comp_stalkIso`, which factors the stalk map as a
localization map `Localization.localRingHom` conjugated by the two stalk isomorphisms
`Spec.stalkIso`; surjectivity and the kernel computation are then
`RingHom.surjective_localRingHom_of_surjective` and `IsLocalization.ker_map`, transported along
those isomorphisms. The private lemma `stalkIso_toStalk_eq_algebraMap` records the one
compatibility needed for the transport, that the stalk isomorphism carries
`StructureSheaf.toStalk` to the localization map.

## References

* [Stacks Project, Tag 01IG](https://stacks.math.columbia.edu/tag/01IG)
-/

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-- The prime ideal `p / I` in `R / I`, for `I ⊆ p`. -/
public def quotientPrime {R : Type u} [CommRing R] (I p : Ideal R) [p.IsPrime]
    (hIp : I ≤ p) : PrimeSpectrum (R ⧸ I) :=
  ⟨p.map (Ideal.Quotient.mk I), Ideal.isPrime_map_quotientMk_of_isPrime hIp⟩

/-- **Stacks Project, Tag 01IG.** The point `p / I` of `Spec(R / I)` maps to
the point `p` of `Spec R`. -/
@[stacks 01IG "quotient_stalk_map"]
public theorem quotientPrime_comap {R : Type u} [CommRing R] (I p : Ideal R) [p.IsPrime]
    (hIp : I ≤ p) :
    PrimeSpectrum.comap (Ideal.Quotient.mk I) (quotientPrime I p hIp) =
      (⟨p, inferInstance⟩ : PrimeSpectrum R) :=
  PrimeSpectrum.ext (Ideal.comap_map_mk hIp)

/-- The stalk isomorphism of an affine scheme carries the canonical map from the ring into the
stalk to the canonical map into the localization. -/
private theorem stalkIso_toStalk_eq_algebraMap {R : Type u} [CommRing R]
    (x : PrimeSpectrum R) :
    (Spec.stalkIso (CommRingCat.of R) x).hom.hom.comp
      (StructureSheaf.toStalk R x).hom = algebraMap R (Localization.AtPrime x.asIdeal) := by
  ext r
  show (StructureSheaf.stalkIso R x).symm (StructureSheaf.toStalk R x r) =
    algebraMap R (Localization.AtPrime x.asIdeal) r
  rw [← StructureSheaf.stalkAlgebra_map]
  exact (StructureSheaf.stalkIso R x).symm.commutes r

/-- The stalk map of `Spec (R / I) → Spec R` is the localization map conjugated by the stalk
isomorphisms. -/
private theorem stalkIso_comp_localRingHom_eq_stalkMap {R : Type u} [CommRing R] (I : Ideal R)
    (q : PrimeSpectrum (R ⧸ I)) :
    (Spec.stalkIso (CommRingCat.of (R ⧸ I)) q).inv.hom.comp
      ((Localization.localRingHom (PrimeSpectrum.comap (Ideal.Quotient.mk I) q).asIdeal
        q.asIdeal (Ideal.Quotient.mk I) rfl).comp
        (Spec.stalkIso (CommRingCat.of R) (PrimeSpectrum.comap (Ideal.Quotient.mk I) q)).hom.hom) =
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).stalkMap q).hom := by
  convert (CommRingCat.hom_ext_iff.mp
    (Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom (Ideal.Quotient.mk I)) q)) using 1

/-- **Stacks Project, Tag 01IG.** The map on stalks induced by
`Spec(R / I) → Spec R` at `p / I` is surjective. -/
@[stacks 01IG "quotient_stalk_map"]
public theorem stalkMap_quotient_surjective {R : Type u} [CommRing R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    Function.Surjective
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).stalkMap
        (quotientPrime I p hIp)).hom := by
  let q := quotientPrime I p hIp
  let x := PrimeSpectrum.comap (Ideal.Quotient.mk I) q
  let e₁ := Spec.stalkIso (CommRingCat.of R) x
  let e₂ := Spec.stalkIso (CommRingCat.of (R ⧸ I)) q
  let g := CommRingCat.ofHom
    (Localization.localRingHom x.asIdeal q.asIdeal (Ideal.Quotient.mk I) rfl)
  have hcomp := stalkIso_comp_localRingHom_eq_stalkMap I q
  rw [← hcomp]
  exact e₂.commRingCatIsoToRingEquiv.symm.bijective.2.comp
    ((RingHom.surjective_localRingHom_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q.asIdeal).comp
      e₁.commRingCatIsoToRingEquiv.bijective.2)

/-- **Stacks Project, Tag 01IG.** The kernel of the map on stalks induced by
`Spec(R / I) → Spec R` at `p / I` is the extended ideal `I R_p`. -/
@[stacks 01IG "quotient_stalk_map"]
public theorem stalkMap_quotient_ker {R : Type u} [CommRing R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    RingHom.ker
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).stalkMap
          (quotientPrime I p hIp)).hom =
      Ideal.map
        (StructureSheaf.toStalk R
          (PrimeSpectrum.comap (Ideal.Quotient.mk I) (quotientPrime I p hIp))).hom I := by
  let q := quotientPrime I p hIp
  let x := PrimeSpectrum.comap (Ideal.Quotient.mk I) q
  let e₁ := Spec.stalkIso (CommRingCat.of R) x
  let e₂ := Spec.stalkIso (CommRingCat.of (R ⧸ I)) q
  let g := CommRingCat.ofHom
    (Localization.localRingHom x.asIdeal q.asIdeal (Ideal.Quotient.mk I) rfl)
  have hcomp := stalkIso_comp_localRingHom_eq_stalkMap I q
  have hT : Submonoid.map (Ideal.Quotient.mk I) x.asIdeal.primeCompl =
      q.asIdeal.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q.asIdeal
  have hker : RingHom.ker g.hom =
      Ideal.map (algebraMap R (Localization.AtPrime x.asIdeal)) I := by
    simpa [g, Localization.localRingHom, Ideal.mk_ker] using
      (IsLocalization.ker_map (Localization.AtPrime q.asIdeal)
        (Ideal.Quotient.mk I) hT)
  rw [← hcomp]
  show RingHom.ker (e₂.inv.hom.comp (g.hom.comp e₁.hom.hom)) =
    Ideal.map (StructureSheaf.toStalk R x).hom I
  rw [RingHom.ker_comp_of_injective (g.hom.comp e₁.hom.hom)
      e₂.commRingCatIsoToRingEquiv.symm.bijective.1,
    ← RingHom.comap_ker g.hom e₁.hom.hom, hker]
  have hmap :
      Ideal.map e₁.hom.hom (Ideal.map (StructureSheaf.toStalk R x).hom I) =
        Ideal.map (algebraMap R (Localization.AtPrime x.asIdeal)) I :=
    (Ideal.map_map (StructureSheaf.toStalk R x).hom e₁.hom.hom).trans
      (congrArg (fun f : R →+* Localization.AtPrime x.asIdeal => Ideal.map f I)
        (stalkIso_toStalk_eq_algebraMap (R := R) x))
  rw [← hmap]
  exact Ideal.comap_map_of_bijective e₁.hom.hom
    e₁.commRingCatIsoToRingEquiv.bijective

end AlgebraicGeometry
