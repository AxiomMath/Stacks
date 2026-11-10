module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
import all StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines

/-!
# Affine morphisms of affine formal algebraic spaces: the refined forms

The strengthened and newly added declarations of the 2026-10 chapter-87 round that belong with
`StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines`. A declaration of that
module
whose statement the round strengthened keeps its original statement there; its strengthened form
lives here under a primed name.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end AlgebraicGeometry.FormalSpace

end
