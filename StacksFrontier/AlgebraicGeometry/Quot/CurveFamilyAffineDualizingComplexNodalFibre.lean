module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAffineDualizingComplexFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyNodalFibreDualizing

/-!
# The relative dualizing complex of an at-worst-nodal family on a fibre

Let `f : X → S` be a family of curves over an affine base which is at-worst-nodal of relative
dimension one, `ω^•_{X/S} = a(𝒪_S)` its relative dualizing complex, and `V` a scheme presenting
the fibre over a field-valued point `Spec K → S` through `q : V → X`. By Section 0E6N the
cohomology sheaves of `Lq^* ω^•_{X/S}`, read on the Zariski site of `V`, are those of the
dualizing complex `ω_V^•` of the fibre, which vanish outside degree `-1` because the fibre is a
nodal, hence Gorenstein and Cohen–Macaulay, curve (Algebraic Curves, Lemma 0BS3).

## Main results

* `AlgebraicGeometry.CurveFamily.isZero_homology_derivedPullback_affineDualizingComplex`.

## Implementation notes

Unregistered helper towards Stacks 0E6P for at-worst-nodal families.

## References

* [Stacks Project, Tag 0E6N](https://stacks.math.columbia.edu/tag/0E6N)
* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.CurveFamily

-- The same choice of models as `AlgebraicGeometry.CurveFamily.affineDualizingComplex`.
attribute [local instance low] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The relative dualizing complex of an at-worst-nodal family on a fibre has no cohomology
outside degree `-1`** (Section 0E6N). For an at-worst-nodal family of curves `f : X → S` over an
affine base, a field-valued point `Spec K → S` and a scheme `V` presenting the fibre through
`q : V → X`, the restriction to the Zariski site of `V` of `H^n(Lq^* ω^•_{X/S})` vanishes for
`n ≠ -1`. -/
theorem isZero_homology_derivedPullback_affineDualizingComplex (G : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj G.base))
    (hG : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj)
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ G.total.obj)
    [IsProper ((BigFppfOver.toScheme B integerBase hZ).map v)]
    (h : IsPullback q (yoneda.map v) G.toBase.hom (yonedaEquiv.symm p.value)) (n : ℤ)
    (hn : n ≠ -1) :
    IsZero (Space.restrictToChartScheme B integerBase hZ (yoneda.obj V)
        (isAlgebraicSpace_yoneda B integerBase hZ V)
        ((DerivedCategory.homologyFunctor
          (Space.Modules.{u, u} B integerBase hZ (schemeSpace V).1 (schemeSpace V).2) n).obj
          ((Space.smallEtaleDerivedModulePullback B integerBase hZ
            (ObjectProperty.homMk q : schemeSpace V ⟶ G.total)).obj
              (affineDualizingComplex G hA).obj))
        (Space.idEtaleChart B integerBase hZ V)) := by
  obtain ⟨e⟩ := nonempty_homology_derivedPullback_affineDualizingComplex_iso G hA p V v q h n
  exact (isZero_homology_dualizingComplexOverField_of_isAtWorstNodal hG h n hn).of_iso e

end AlgebraicGeometry.CurveFamily

end
