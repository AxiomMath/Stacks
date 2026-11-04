module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalAtlasCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas

/-!
# The set-theoretic condition for a countable atlas (Stacks 0AIS, observation (3)): refined forms

The home of strengthened forms of declarations of
`StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas`: a declaration of that module whose
statement is strengthened keeps its original statement there, and its strengthened form lives
here under a primed name. The module holds no declarations at present.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A family as in Definition 0AIM -/

/-! ### Observation (3), first half: a countable atlas is dominated by one object of the site -/

/-! ### Observation (3), second half: the relation produced by the atlas -/

end AlgebraicGeometry.FormalSpace

end
