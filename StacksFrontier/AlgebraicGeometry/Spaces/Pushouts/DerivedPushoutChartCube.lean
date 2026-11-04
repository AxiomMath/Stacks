module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutGlueingCubeSpaces

/-!
# The base change of a commutative square of algebraic spaces along a morphism to its corner

Let `i ≫ f' = f ≫ j` be a commutative square of algebraic spaces
```
X  --i-->  X'
|f         |f'
v          v
Y  --j-->  Y'
```
and `h : V ⟶ Y'`. Its base change along `h` is the square
`X ×_Y (Y ×_{Y'} V) → X' ×_{Y'} V`, `X ×_Y (Y ×_{Y'} V) → Y ×_{Y'} V`, `X' ×_{Y'} V → V`,
`Y ×_{Y'} V → V`, and the four vertical faces of the resulting cube are cartesian. This is the
cube along which the proof of Stacks 0DL7 restricts the glueing map to an étale chart `V` of `Y'`
(`AlgebraicGeometry.Space.pushoutGlueingMap_restrict`); when `h` is étale, so are the three other
vertical edges, and the base change maps of the four faces are invertible (Stacks 08GE).

## Main definitions

* `AlgebraicGeometry.Space.chartCubeX`: `X ×_Y (Y ×_{Y'} V)`, and `chartCubeI : chartCubeX ⟶
  X' ×_{Y'} V` the base change of `i`.

## Main results

* `AlgebraicGeometry.Space.chartCubeI_snd` and `chartCubeI_fst`: the two faces through the base
  change of `i` commute.
* `AlgebraicGeometry.Space.isPullback_chartCubeI`: the face of `i` is cartesian.
* `AlgebraicGeometry.Space.isEtale_chartCube_fst`: the vertical edges are étale when `h` is.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' Y Y' V : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) (f' : X' ⟶ Y') (j : Y ⟶ Y')
  (w : i ≫ f' = f ≫ j) (h : V ⟶ Y')

/-- The base change `X ×_Y (Y ×_{Y'} V)` of the corner `X` of a square along `h : V ⟶ Y'`. -/
abbrev chartCubeX : AlgebraicSpaces B S hS :=
  pullback f (pullback.fst j h)

/-- The base change `X ×_Y (Y ×_{Y'} V) ⟶ X' ×_{Y'} V` of `i`. -/
def chartCubeI : chartCubeX f j h ⟶ pullback f' h :=
  pullback.lift (pullback.fst f (pullback.fst j h) ≫ i)
    (pullback.snd f (pullback.fst j h) ≫ pullback.snd j h) (by
      rw [Category.assoc, w, ← Category.assoc, pullback.condition, Category.assoc,
        pullback.condition, Category.assoc])

include w in
/-- The top face of the cube commutes. -/
@[reassoc]
theorem chartCubeI_snd :
    chartCubeI i f f' j w h ≫ pullback.snd f' h =
      pullback.snd f (pullback.fst j h) ≫ pullback.snd j h :=
  pullback.lift_snd _ _ _

include w in
/-- The face of the cube through `i` commutes. -/
@[reassoc]
theorem chartCubeI_fst :
    pullback.fst f (pullback.fst j h) ≫ i = chartCubeI i f f' j w h ≫ pullback.fst f' h :=
  (pullback.lift_fst _ _ _).symm

include w in
/-- **The face of the cube through `i` is cartesian**:
`X ×_Y (Y ×_{Y'} V) = X ×_{X'} (X' ×_{Y'} V)`, both being `X ×_{Y'} V`. -/
theorem isPullback_chartCubeI :
    IsPullback (pullback.fst f (pullback.fst j h)) (chartCubeI i f f' j w h) i
      (pullback.fst f' h) := by
  have big := (IsPullback.of_hasPullback f (pullback.fst j h)).paste_vert
    (IsPullback.of_hasPullback j h)
  rw [← chartCubeI_snd i f f' j w h, ← w] at big
  exact IsPullback.of_bot big (chartCubeI_fst i f f' j w h) (IsPullback.of_hasPullback f' h)

/-- The vertical edges of the cube are étale when `h` is. -/
theorem isEtale_chartCube_fst (hh : IsEtale B S hS h.hom) :
    IsEtale B S hS (pullback.fst j h).hom ∧ IsEtale B S hS (pullback.fst f' h).hom ∧
      IsEtale B S hS (pullback.fst f (pullback.fst j h)).hom := by
  have hY : IsEtale B S hS (pullback.fst j h).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ (IsPullback.of_hasPullback j h).flip hh
  exact ⟨hY, isEtale_of_isPullback B S hS _ _ _ _ (IsPullback.of_hasPullback f' h).flip hh,
    isEtale_of_isPullback B S hS _ _ _ _ (IsPullback.of_hasPullback f (pullback.fst j h)).flip hY⟩

end AlgebraicGeometry.Space

end
