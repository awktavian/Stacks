module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesEtaleLocallyHProjective

/-!
# Étale-local scheme charts of families of curves (the statement of Stacks 0E6F)

Stacks 0E6F says that a family of curves `X ⟶ S` becomes a scheme étale locally on `S`: there is
an étale covering `{Sᵢ ⟶ S}` such that every `X ×_S Sᵢ` is a scheme. This file records that
assertion as a proposition, `AlgebraicGeometry.C1590Private.HasEtaleLocalSchemeCharts`, for use
as an explicit input by results whose proofs in the source pass through Stacks 0E6F.

The proposition is proved here. The registered theorem
`AlgebraicGeometry.CurveFamily.exists_etaleCovering_isPullback_isProjectiveMorphism` (Stacks 0E6F,
`Quot/CurveFamiliesEtaleLocallyHProjective.lean`) supplies an étale covering of the base over which
every base change of the family is even an H-projective scheme; the covering member whose image
contains `s`, together with its chart, is exactly the chart `HasEtaleLocalSchemeCharts` asks for
pointwise, and the transport — `hasEtaleLocalSchemeCharts_of_stacks0E6F` below, which discards the
H-projectivity and uses no mathematics of its own — replaces this paragraph's former claim that the
result was unavailable here. The source's proof of Stacks 0E6F runs through Stacks 0DQ0 (the
morphism `PolarizedCurves ⟶ Curves` is smooth), which needs the openness of the ample locus for
algebraic spaces (Stacks 0D3D) and the smoothness of the Picard stack of a family of curves (Stacks
0DPJ); the registered theorem reaches the same conclusion through smooth-local polarization. The
proposition is assembled independently, without 0E6F, in
`C1590Private/CurveFamilyEtaleSchemeChartsProof.lean`
(`AlgebraicGeometry.C1590Private.hasEtaleLocalSchemeCharts`).

## Main definitions

* `AlgebraicGeometry.C1590Private.HasEtaleLocalSchemeCharts`: the assertion of Stacks 0E6F.
* `AlgebraicGeometry.C1590Private.hasEtaleLocalSchemeCharts_of_stacks0E6F`: the assertion,
  transported from the registered theorem of Stacks 0E6F.

## Implementation notes

The étale covering is stated pointwise: every point `s` of the base is in the image of an étale
morphism `φ : U ⟶ S` of the site over which the family is represented by a scheme `Z` of the site.
The family of all such `φ` is then an étale covering. Representability is a cartesian square of
algebraic spaces whose left column is a morphism of schemes `q : Z ⟶ U`, read as a morphism of
algebraic spaces by `AlgebraicGeometry.schemeSpaceMap`. This is the shape in which a scheme chart
of a family of curves is consumed: the scheme-level properties of `q` (flat, of finite
presentation, proper) are those of the family by base change.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The assertion of Stacks 0E6F.** Every family of curves `X ⟶ S` is a scheme étale locally on
`S`. Every point `s` of `S` lies in the image of an étale morphism `φ : U ⟶ S` of the site such
that the base change `X ×_S U` is represented by a scheme `Z` of the site over `U`. -/
def HasEtaleLocalSchemeCharts : Prop :=
  ∀ (X : CurveFamily B hZ) (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base),
    ∃ (U Z : BigFppfOver B integerBase hZ) (φ : U ⟶ X.base) (q : Z ⟶ U)
      (p : schemeSpace Z ⟶ X.total),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
        s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
        IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ)

variable (B hZ) in
/-- **Stacks 0E6F in the pointwise shape of `HasEtaleLocalSchemeCharts`.** From the registered
theorem `AlgebraicGeometry.CurveFamily.exists_etaleCovering_isPullback_isProjectiveMorphism`: the
étale covering member through `s` carries a scheme chart of `X`. The H-projectivity of the chart
over its covering member is not used. -/
theorem hasEtaleLocalSchemeCharts_of_stacks0E6F : HasEtaleLocalSchemeCharts B hZ := by
  intro X s
  obtain ⟨_, U, φ, het, hcover, hchart⟩ :=
    CurveFamily.exists_etaleCovering_isPullback_isProjectiveMorphism (B := B) (hZ := hZ) X
  obtain ⟨j, hj⟩ := hcover s
  obtain ⟨Z, p, q, hpb, _⟩ := hchart j
  exact ⟨U j, Z, φ j, q, p, het j, hj, hpb⟩

end AlgebraicGeometry.C1590Private

end
