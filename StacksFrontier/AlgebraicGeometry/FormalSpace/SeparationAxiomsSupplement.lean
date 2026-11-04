module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms

/-!
# Further results on `StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms`

Further separation properties of formal algebraic spaces over a base scheme `S` in the big fppf
site `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end AlgebraicGeometry.FormalSpace

end
