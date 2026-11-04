module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCoverRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChangeRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestriction
import all StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition

/-!
# The small étale site of a representable étale morphism of formal algebraic spaces

Strengthened forms, under primed names, of results of
`StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition` on the small étale site of
a representable étale morphism of formal algebraic spaces. A declaration of that module whose
statement is strengthened keeps its original statement there.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### From the relative étale condition to the every-étale-chart condition -/

namespace Reduction

variable {B S hS} {X Y : FppfSheaf B S hS}

/-! ### Stacks 0DED: the induced morphism of reductions is étale -/

/-! ### Stacks 0DED: the functor `j` and the identification of `f_small` -/

end Reduction

end AlgebraicGeometry.FormalSpace

end
