module

public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Twists

/-!
# Finite type of the actual twists of a relative projective spectrum

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra of finite type. The twists
`𝒪_X(t)` on `X = Proj_S(A)` are the homogeneous pieces of the twist datum
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` of `A` (Tag 01NR), and each
of them is a finite-type module sheaf. This is the second assertion of Stacks tag 07ZY.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjFiniteType.isFiniteType_relativeProjTwist`: every twist
  `𝒪_X(t)` of the relative `Proj` of a finite type quasi-coherent graded algebra is of finite type.

## References

* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjFiniteType

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

include A in
/-- Every twist `𝒪_X(t)` on the relative projective spectrum `X = Proj_S(A)` of a finite type
quasi-coherent graded algebra is a finite-type module sheaf. The twists are the homogeneous pieces
of the twist datum `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` of `A`.
-/
@[stacks 07ZY "relative_proj_twist_finite_type"]
public theorem isFiniteType_relativeProjTwist (hA : IsFiniteType A) (t : ℤ) :
    SheafOfModules.IsFiniteType.{u, u, u}
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.piece t) :=
  isFiniteType_twist A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) hA t

end Stacks.AlgebraicGeometry.RelativeProjFiniteType

end
