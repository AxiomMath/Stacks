module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
import StacksCore.Tactic.StacksAttribute

/-! ## Countable coproducts

The remark after Stacks 012Z says that the total complex of a double complex exists as soon as
countable direct sums do. In Mathlib this is instance search rather than a lemma:
`HomologicalComplex₂.HasTotal` asks for a coproduct over each antidiagonal
`{(p, q) | π (p, q) = n}`, a countable type whenever the index types are, and the instance
attributed below turns `HasCountableCoproducts C` into coproducts of every countable shape. -/

@[expose] public section

add_to_stacks 012Z "Tot exists when countable coproducts do: each antidiagonal is countable"
  CategoryTheory.Limits.instHasCoproductsOfShapeOfHasCountableCoproductsOfCountable
