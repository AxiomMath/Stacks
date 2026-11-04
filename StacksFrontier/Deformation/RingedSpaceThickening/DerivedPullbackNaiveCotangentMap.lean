module

public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentPullbackMap

/-!
# The canonical map `Lg^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`

For morphisms of ringed spaces `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` and `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, the map
`Lg^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}` of the proof of Stacks 0GQ1 is the canonical comparison
`Lg^*𝖭𝖫_{X/S} ⟶ g^*𝖭𝖫_{X/S}` of the derived pullback of Stacks 06YJ, followed by the canonical map
`g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}` of naive cotangent complexes
(`AlgebraicGeometry.RingedSpaceThickening.pullbackNaiveCotangentMap`).

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangentMap`: the map
  `Lg^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}` in `D(𝒪_Y)`.

## References

* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} (g : Y ⟶ X) (f : X ⟶ S)

/-- **The canonical map `Lg^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`** of Stacks 0GQ1: the comparison
`Lg^*𝖭𝖫_{X/S} ⟶ g^*𝖭𝖫_{X/S}` of the derived pullback, followed by the canonical map
`g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`. -/
def derivedPullbackNaiveCotangentMap :
    derivedPullbackNaiveCotangent g f ⟶ relativeNaiveCotangentObj (g ≫ f) :=
  (derivedPullback g).map ((DerivedCategory.quotientCompQhIso _).inv.app
      (show CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ from
        PresentedSquareZeroExtension.relativeComplex f)) ≫
    (derivedPullbackComparison g).app ((HomotopyCategory.quotient _ _).obj
      (show CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ from
        PresentedSquareZeroExtension.relativeComplex f)) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app _ ≫
    DerivedCategory.Q.map (pullbackNaiveCotangentMap g f)

end AlgebraicGeometry.RingedSpaceThickening

end
