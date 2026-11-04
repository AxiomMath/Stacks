module

public import
    StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedC3UnitCompatAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistUnit

/-!
# The unit of the twists of a relative Proj

In Situation 0849 the unit `𝒪_P ⟶ 𝒪_P(0)` of the twists of `P = Proj_X(𝒜)` is descended along
the presentation `P = P_U/P_R` from the unit of the twists on the scheme of `P_U`
(`AlgebraicGeometry.Space.RelativeProjSituation.twistModuleUnit`).  The descent uses the
compatibility of the identification of Stacks 03DX (2) of the structure sheaf with inverse images
along morphisms of the site, which is `AlgebraicGeometry.Space.representedC3UnitCompat`; this file
records the unit, its characterization along the atlas, and its existence and uniqueness with that
compatibility supplied.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraUnit`: **the unit
  `𝒪_P ⟶ 𝒪_P(0)` of the twists of the relative Proj** (Stacks 084D).

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.existsUnique_twistAlgebraUnit`: the unit exists
  and is unique, characterized by its inverse image along the atlas.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraUnit_spec`: the inverse image of the
  unit along the atlas is the unit of the twists of Stacks 01NR on the scheme of `P_U`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The unit of the twists of the relative Proj exists and is unique** (Stacks 084D): there is
exactly one morphism `𝒪_P ⟶ 𝒪_P(0)` whose inverse image along the atlas of the presentation
`P = P_U/P_R` is the unit of the twists of Stacks 01NR on the scheme of `P_U`, through Stacks 03LU
and the chart identification of `𝒪_P(0)`. -/
theorem existsUnique_twistAlgebraUnit :
    type_of% (s.existsUnique_twistModuleUnit Px
      (fun g => representedC3UnitCompat s.site s.base s.containsBase g)) :=
  s.existsUnique_twistModuleUnit Px
    (fun g => representedC3UnitCompat s.site s.base s.containsBase g)

/-- **The unit of the twists of the relative Proj** (Stacks 084D): `𝒪_P ⟶ 𝒪_P(0)`, the descent
along the presentation `P = P_U/P_R` of the unit of the twists of Stacks 01NR on the scheme of
`P_U`. -/
def twistAlgebraUnit :
    SheafOfModules.unit (structureRingSheaf s.site s.base s.containsBase
        ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩) ⟶
      (s.twistModule Px 0).obj :=
  s.twistModuleUnit Px (fun g => representedC3UnitCompat s.site s.base s.containsBase g)

/-- **The inverse image along the atlas of the unit of the twists is the unit of the twists of
Stacks 01NR on the scheme of `P_U`**, through Stacks 03LU and the chart identification of
`𝒪_P(0)`. -/
theorem twistAlgebraUnit_spec :
    type_of% (s.twistModuleUnit_spec Px
      (fun g => representedC3UnitCompat s.site s.base s.containsBase g)) :=
  s.twistModuleUnit_spec Px (fun g => representedC3UnitCompat s.site s.base s.containsBase g)

end RelativeProjSituation

end AlgebraicGeometry.Space

end
