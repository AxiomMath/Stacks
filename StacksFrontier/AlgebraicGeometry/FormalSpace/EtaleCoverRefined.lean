module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
import all StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover

/-!
# Étale coverings by formal algebraic spaces: the refined forms

The strengthened and newly added declarations of the 2026-10 chapter-87 round that belong with
`StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover`. A declaration of that module whose
statement the round strengthened keeps its original statement there; its strengthened form lives
here under a primed name.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end AlgebraicGeometry.FormalSpace

end
