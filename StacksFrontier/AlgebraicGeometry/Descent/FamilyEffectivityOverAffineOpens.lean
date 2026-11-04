module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseFamilyEffectivity
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyBaseRestriction

/-!
# Effectivity of an affine descent datum over the affine opens of the base

Let `𝒰 = {X i ⟶ S}` be an fpqc covering family of a scheme `S` and let `D` be a descent datum
relative to `𝒰` whose structure morphisms `V i ⟶ X i` are affine. Over an affine open `U` of
`S` the restricted family is again an fpqc covering, of `U`, and the components of the
restricted datum are again affine, so the datum restricted to `U` is effective.

## Main results

* `AlgebraicGeometry.DescentData.isFamilyEffective_restrictBase_of_isAffineHom`: the
  restriction of the datum to an affine open of the base is effective.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.DescentData

/-- Let `𝒰` be an fpqc covering family of `S` and let `D` be a descent datum relative to it whose
structure morphisms are affine. Then the restriction of `D` to any affine open of `S` is
effective. -/
theorem isFamilyEffective_restrictBase_of_isAffineHom {S : Scheme.{u}}
    {𝒰 : PreZeroHypercover.{u} S}
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData 𝒰.f) (hD : ∀ i, IsAffineHom (D.obj i).hom)
    (U : S.Opens) (hU : IsAffineOpen U) :
    ((MorphismOfSchemeFamilies.pullbackFunctor
      (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U)).functor.obj D).IsFamilyEffective :=
  have : IsAffine U.toScheme := hU
  isFamilyEffective_of_isAffineHom_of_affineBase
    (PreZeroHypercover.restrictBase 𝒰 U).f
    (PreZeroHypercover.mem_fpqcPrecoverage_restrictBase 𝒰 U h𝒰) _
    fun i ↦ DescentData.restrictBase_prop_obj 𝒰 U D i (hD i)

end AlgebraicGeometry.DescentData

end
