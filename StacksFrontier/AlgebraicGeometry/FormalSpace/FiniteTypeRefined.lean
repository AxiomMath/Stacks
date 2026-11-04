module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableCancellation
import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# Finite type morphisms of formal algebraic spaces are locally of finite type

Results on finite type morphisms of formal algebraic spaces that complement
`StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType`: here, that a morphism of finite type is
locally of finite type.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of finite type is locally of finite type: the condition of Stacks 03XF on each
base change along a scheme-valued point of the target is a conjunction whose first half is the
local one. -/
theorem IsFiniteType.isLocallyOfFiniteType {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hf : IsFiniteType B S hS f) : IsLocallyOfFiniteType B S hS f := by
  obtain ⟨hrep, hprop⟩ := hf
  exact ⟨hrep, fun U ξ ↦ (hprop U ξ).1⟩

end AlgebraicGeometry.FormalSpace

end
