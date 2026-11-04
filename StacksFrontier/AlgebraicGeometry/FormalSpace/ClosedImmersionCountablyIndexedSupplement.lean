module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionMcQuillanPresentation

/-!
# Closed immersions into countably indexed affine formal algebraic spaces, continued

Further material on closed immersions into countably indexed affine formal algebraic spaces,
over `StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCountablyIndexed` and
`StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionMcQuillanPresentation`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section CountablyIndexed

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end CountablyIndexed

section Correspondence

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

end Correspondence

section Quotient

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

end Quotient

section Combined

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

end Combined

end AlgebraicGeometry.FormalSpace

end
