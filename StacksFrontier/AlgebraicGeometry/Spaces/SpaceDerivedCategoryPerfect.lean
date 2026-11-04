module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects

/-!
# Perfect objects of the derived category of an algebraic space, at the standard model

For an algebraic space `X`, this module defines perfectness of an object of
`AlgebraicGeometry.Space.spaceDerivedCategory X`, the derived category `D(𝒪_X)` of the
`𝒪_X`-modules on the small étale site of `X` at the standard model.

## Main definitions

* `AlgebraicGeometry.Space.spaceIsPerfect X E`: `E` is a perfect object of `D(𝒪_X)`, i.e.
  `AlgebraicGeometry.RingedSite.IsPerfect` on the small étale ringed site of `X`, at the standard
  model `AlgebraicGeometry.Space.spaceHasDerivedCategory X`.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object `E` of `D(𝒪_X)` on the small étale site of an algebraic space `X` is perfect, at the
standard model `spaceHasDerivedCategory X`. -/
abbrev spaceIsPerfect (X : AlgebraicSpaces B S hS) (E : spaceDerivedCategory B S hS X) : Prop :=
  letI := spaceHasDerivedCategory B S hS X
  (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E

end AlgebraicGeometry.Space
