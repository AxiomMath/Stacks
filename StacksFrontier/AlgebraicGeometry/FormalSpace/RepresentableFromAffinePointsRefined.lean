module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFromAffinePoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValuedRefined
public import StacksFrontier.CategoryTheory.Limits.CoproductPullback
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive
import all StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFromAffinePoints

/-!
# Representability by algebraic spaces from the affine points of the target: the refined forms

Strengthened forms, under primed names, of the representability criteria of
`StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFromAffinePoints`, which deduce that a
morphism of fppf sheaves is representable by algebraic spaces from its base changes along the
affine points of its target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.FormalSpace

variable (𝔅 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝔅.Contains S)

end AlgebraicGeometry.FormalSpace

end
