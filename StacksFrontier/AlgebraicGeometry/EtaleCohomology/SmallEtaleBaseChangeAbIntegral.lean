module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbFinite

/-!
# Base change of an abelian direct image along an integral morphism

Let
```
Y' --π'--> Y
|e'        |e
v          v
T' --π---> T
```
be a cartesian square of schemes with `π` integral. The canonical comparison
`e⁻¹ π_* ⟶ π'_* (e')⁻¹` of abelian sheaves on the small étale sites,
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb`, is an isomorphism ([Stacks, Tag 0EYP]).

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIntegralHom`: the comparison
  `smallEtaleBaseChangeAb e π π' e'` is an isomorphism for a cartesian square with `π` integral.

## References

* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **Direct image of abelian sheaves along an integral morphism commutes with base change.** For
a cartesian square
```
Y' --π'--> Y
|e'        |e
v          v
T' --π---> T
```
of schemes with `π` integral, the canonical comparison `e⁻¹ π_* ⟶ π'_* (e')⁻¹` of abelian
sheaves on the small étale sites is an isomorphism. -/
public theorem isIso_smallEtaleBaseChangeAb_of_isIntegralHom {Y Y' T T' : Scheme.{u}}
    (e : Y ⟶ T) (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T') (sq : IsPullback π' e' e π)
    [IsIntegralHom π] :
    IsIso (smallEtaleBaseChangeAb e π π' e' sq.w) :=
  isIso_smallEtaleBaseChangeAb_of_isIso_sets e π π' e' sq
    fun B hT' hT hY hY' hw F ↦
      have : IsIntegralHom (B.inclusion.map
          (ObjectProperty.homMk (X := B.obj T' hT') (Y := B.obj T hT) π)) :=
        inferInstanceAs (IsIntegralHom π)
      isIso_smallEtaleBaseChangeNatTrans_app_of_isIntegralHom B
        (ObjectProperty.homMk (X := B.obj Y' hY') (Y := B.obj T' hT') e')
        (ObjectProperty.homMk (X := B.obj Y' hY') (Y := B.obj Y hY) π')
        (ObjectProperty.homMk (X := B.obj T' hT') (Y := B.obj T hT) π)
        (ObjectProperty.homMk (X := B.obj Y hY) (Y := B.obj T hT) e) sq.flip hw F

end Stacks.EtaleCohomology

end
