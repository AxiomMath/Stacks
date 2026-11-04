module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies

/-!
# Étale-local scheme charts of families of curves (the statement of Stacks 0E6F)

Stacks 0E6F says that a family of curves `X ⟶ S` becomes a scheme étale locally on `S`: there is
an étale covering `{Sᵢ ⟶ S}` such that every `X ×_S Sᵢ` is a scheme. This file records that
assertion as a proposition, `AlgebraicGeometry.C1590Private.HasEtaleLocalSchemeCharts`, for use
as an explicit input by results whose proofs in the source pass through Stacks 0E6F.

The proposition is not proved here. Its proof in the source runs through Stacks 0DQ0 (the morphism
`PolarizedCurves ⟶ Curves` is smooth), which needs the openness of the ample locus for algebraic
spaces (Stacks 0D3D) and the smoothness of the Picard stack of a family of curves (Stacks 0DPJ).
None of these is available here.

## Main definitions

* `AlgebraicGeometry.C1590Private.HasEtaleLocalSchemeCharts`: the assertion of Stacks 0E6F.

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

end AlgebraicGeometry.C1590Private

end
