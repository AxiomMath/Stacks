module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituationSupplement

/-!
# Re-basing a descent situation

`AlgebraicGeometry.Space.DescentSituation` and `AlgebraicGeometry.Space.LimitSituation` carry the
same data — Situation 084R — in two packagings: the first with a chosen limit cone and a
distinguished index, the second attached to a presheaf which the cone exhibits as the limit.
`AlgebraicGeometry.Space.LimitSituation.toDescentSituation` and
`AlgebraicGeometry.Space.DescentSituation.toLimitSituation` translate between them; what is not
there, and is what this file adds, is the change of distinguished index.

The change of index is needed in the proof of Stacks 07SQ, which repeatedly enlarges the index at
which it works: the separated stage of Stacks 084T, the stage over which the polynomial
presentation is defined, and the stage at which the square of Stacks 084U becomes Cartesian are
three different indices, and the statements used at each of them are stated at the distinguished
index of the situation.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.rebase`: the same situation with another
  distinguished index.

## Implementation notes

A change of distinguished index copies every field and replaces one; the `simp` lemmas
`rebase_system`, `rebase_limitCone` and `rebase_base` hold by `rfl`.

## References

* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe v u

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})}

section Rebase

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- A descent situation with another distinguished index. -/
def rebase (i : I) : DescentSituation B S hS hZ I :=
  { D with base := i }

@[simp]
theorem rebase_system (i : I) : (D.rebase i).system = D.system := rfl

@[simp]
theorem rebase_limitCone (i : I) : (D.rebase i).limitCone = D.limitCone := rfl

@[simp]
theorem rebase_base (i : I) : (D.rebase i).base = i := rfl

end Rebase

end DescentSituation

end AlgebraicGeometry.Space

end
