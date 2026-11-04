module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus

/-!
# Quasi-finiteness and the points in a fibre of a cartesian diagram

Let `D` be a cartesian square of algebraic spaces over a scheme `S` as in Stacks 0AC1, with
corners `W`, `Z`, `X`, `Y` and right vertical morphism `f : X ⟶ Y`, and let `x` of `|X|` and
`z` of `|Z|` have the same image in `|Y|`. Tag 0AC6 says that the set `F_{x, z}` of Stacks
0AC2 is finite as soon as `f` is of finite type and quasi-finite at `x`.

## Main results

* `AlgebraicGeometry.Space.finite_fibrePoints_of_isFiniteType_of_isQuasiFiniteAt`:
  **Stacks 0AC6**, the finiteness criterion.

## Implementation notes

The left vertical morphism `q : W ⟶ Z` is a base change of `f`, so it is of finite type
(Stacks 03XH, `AlgebraicGeometry.Space.isFiniteType_isStableUnderBaseChange`) and its
quasi-finite locus is the inverse image of that of `f` (Stacks 0ABM, part (2),
`AlgebraicGeometry.Space.setOf_isQuasiFiniteAt_eq_preimage_of_isPullback`). Every point of
`F_{x, z}` maps to `x`, hence lies in that inverse image, so `F_{x, z}` is contained in the
set of points over `z` at which `q` is quasi-finite, which is finite by Stacks 0ABN,
`AlgebraicGeometry.Space.finite_setOf_mapsTo_and_isQuasiFiniteAt`.

## References

* [Stacks Project, Tag 0AC6](https://stacks.math.columbia.edu/tag/0AC6)
* [Stacks Project, Tag 0AC1](https://stacks.math.columbia.edu/tag/0AC1)
* [Stacks Project, Tag 0AC2](https://stacks.math.columbia.edu/tag/0AC2)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 0ABN](https://stacks.math.columbia.edu/tag/0ABN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0AC6.** In a cartesian square of algebraic spaces as in Stacks 0AC1, the set of
points of the upper-left corner lying over prescribed points `x` and `z` of the upper-right
and lower-left corners is finite as soon as the right vertical morphism is of finite type and
quasi-finite at `x`. -/
@[stacks 0AC6]
theorem finite_fibrePoints_of_isFiniteType_of_isQuasiFiniteAt
    (D : PointsFibresDiagram B S hS) (x : points B S hS D.X) (z : points B S hS D.Z)
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    (hf : IsFiniteType B S hS D.f) (hx : IsQuasiFiniteAt B S hS D.f x) :
    (fibrePoints D x z h).Finite := by
  let W : AlgebraicSpaces B S hS := ⟨D.W, D.W_isAlgebraicSpace⟩
  let Z : AlgebraicSpaces B S hS := ⟨D.Z, D.Z_isAlgebraicSpace⟩
  let X : AlgebraicSpaces B S hS := ⟨D.X, D.X_isAlgebraicSpace⟩
  let Y : AlgebraicSpaces B S hS := ⟨D.Y, D.Y_isAlgebraicSpace⟩
  let q : W ⟶ Z := ObjectProperty.homMk D.q
  let p : W ⟶ X := ObjectProperty.homMk D.p
  let f : X ⟶ Y := ObjectProperty.homMk D.f
  let g : Z ⟶ Y := ObjectProperty.homMk D.g
  have hsq : IsPullback p q f g :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) D.isPullback
  refine (finite_setOf_mapsTo_and_isQuasiFiniteAt B S hS D.W_isAlgebraicSpace
    D.Z_isAlgebraicSpace D.q
    ((isFiniteType_isStableUnderBaseChange B S hS).of_isPullback hsq hf) z).subset
    fun w hw ↦ ⟨hw.2, ?_⟩
  show w ∈ {w' : points B S hS W.1 | IsQuasiFiniteAt B S hS q.hom w'}
  rw [setOf_isQuasiFiniteAt_eq_preimage_of_isPullback B S hS hsq hf.1]
  show IsQuasiFiniteAt B S hS D.f (pointsMap B S hS D.W D.p w)
  rw [hw.1]
  exact hx

end AlgebraicGeometry.Space

end
