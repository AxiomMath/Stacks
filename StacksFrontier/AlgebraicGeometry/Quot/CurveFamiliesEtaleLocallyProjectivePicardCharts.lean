module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsSmoothLocallyPolarized

/-!
# Curve families are étale locally projective, from Picard charts

Assuming the Picard-chart hypothesis `hchart` (Stacks 0D04 with Stacks 09DS, and Stacks 0DPJ),
every family of curves has an étale covering `{S_j ⟶ S}` of its base along which it becomes a
scheme, H-projective over `S_j`: the conclusion of Stacks 0E6F.

## Main results

* `exists_etaleCovering_isPullback_isProjectiveMorphism_of_picardCharts`: given `hchart`, every
  family of curves `X ⟶ S` admits an étale covering `{S_j ⟶ S}` such that each `X ×_S S_j` is a
  scheme, H-projective over `S_j`.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- Given the Picard-chart hypothesis `hchart`, a family of curves `X ⟶ S` has an étale covering
`{S_j ⟶ S}` such that each `X ×_S S_j` is a scheme, H-projective over `S_j`. -/
theorem exists_etaleCovering_isPullback_isProjectiveMorphism_of_picardCharts
    (hchart : ∀ (X : CurveFamily B hZ) (K : Type u) (_ : Field K)
      (hK : B.Contains (Spec (.of K)))
      (x : (schemeOverIntegers B).obj (B.obj hK) ⟶ X.base)
      (A₀ : Space.PicardObject X.picardSituation), A₀.T = X.picardTestScheme x →
        A₀.IsInAmpleLocus →
        ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base),
          Smooth ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
          ∃ (A : Space.PicardObject X.picardSituation) (hA : A.T = X.picardTestScheme π)
            (K' : Type u) (_ : Field K') (hK' : B.Contains (Spec (.of K')))
            (y : (schemeOverIntegers B).obj (B.obj hK') ⟶ T')
            (e : (schemeOverIntegers B).obj (B.obj hK') ⟶ (schemeOverIntegers B).obj (B.obj hK)),
            y ≫ π = e ≫ x ∧
            (Space.PicardSituation.pullbackObject A
              (X.picardTestSchemeMap y π ≫ eqToHom hA.symm)).IsInAmpleLocus)
    (X : CurveFamily B hZ) :
    ∃ (J : Type u) (U : J → BigFppfOver B integerBase hZ) (φ : ∀ j, U j ⟶ X.base),
      (∀ j, Etale ((BigFppfOver.toScheme B integerBase hZ).map (φ j))) ∧
      (∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
        ∃ j, s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map (φ j))) ∧
      ∀ j, ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ X.total) (q : Z ⟶ U j),
        IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap (φ j)) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q) :=
  exists_etaleCovering_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized_one X
    (isSmoothLocallyPolarized hchart X)

end AlgebraicGeometry.CurveFamily

end
