module

public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
public import StacksFrontier.AlgebraicGeometry.RelativeProjFinitePresentation.TwistFinitePresentation

/-!
# Finite presentation of the actual twists of a relative projective spectrum

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra whose structure map is of finite
presentation over every affine open of the base. The twists `𝒪_X(t)` on `X = Proj_S(A)` are the
homogeneous pieces of the twist datum
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` of `A` (Tag 01NR); by
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.gluedTwistAlgebra_piece`, they are the glued twists
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist` of Tag 01NO. Each of them is a module
sheaf of finite presentation, which is the second assertion of Stacks tag 0D4D; the first, that the
structure morphism is of finite presentation, is
`Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.finitePresentation_toBase`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.isFinitePresentation_relativeProjTwist`:
  every twist `𝒪_X(t)` of the relative `Proj` of a quasi-coherent graded algebra of finite
  presentation is a module sheaf of finite presentation.
* `Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.isFinitePresentation_gluedTwist`: the
  same, written for the glued twist of Tag 01NO in the given degree rather than for the piece of
  the twist datum.

## References

* [Stacks Project, Tag 0D4D](https://stacks.math.columbia.edu/tag/0D4D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjFinitePresentation

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

include A in
/-- Every twist `𝒪_X(t)` on the relative projective spectrum `X = Proj_S(A)` of a quasi-coherent
graded algebra whose structure map is of finite presentation over every affine open of the base is
a module sheaf of finite presentation. The twists are the homogeneous pieces of the twist datum
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` of `A`. -/
@[stacks 0D4D "twists_finite_presentation"]
public theorem isFinitePresentation_relativeProjTwist
    (hA : ∀ U : S.Opens, IsAffineOpen U → (A.strHom U).FinitePresentation) (t : ℤ) :
    SheafOfModules.IsFinitePresentation.{u, u, u}
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.piece t) :=
  isFinitePresentation_twist A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) hA t

include A in
/-- The glued twist `𝒪_X(t)` of Tag 01NO on the relative projective spectrum of a quasi-coherent
graded algebra whose structure map is of finite presentation over every affine open of the base is
a module sheaf of finite presentation. -/
public theorem isFinitePresentation_gluedTwist
    (hA : ∀ U : S.Opens, IsAffineOpen U → (A.strHom U).FinitePresentation) (t : ℤ) :
    SheafOfModules.IsFinitePresentation.{u, u, u}
      (ChartTransRelativeProj.gluedTwist A t (ProjTwistCocycle.isNestedCocycle A t)) :=
  isFinitePresentation_relativeProjTwist A hA t

end Stacks.AlgebraicGeometry.RelativeProjFinitePresentation

end
