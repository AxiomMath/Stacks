module

public import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# The square of two open subsets covering an open subset

Two open subsets `U` and `V` of a topological space whose union is an open subset `W` form the
commutative square `U ⊓ V, V, U, W` of opens, all four of whose maps are inclusions.  It is the
square along which the Mayer--Vietoris sequence of a sheaf on the space is formed.

## Main definitions

* `Stacks.Cohomology.coverSquare`: the square `U ⊓ V, V, U, W` of two open subsets with union
  `W`, as a `CategoryTheory.Square`.

## References

* [Stacks Project, Tag 08BX](https://stacks.math.columbia.edu/tag/08BX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.Cohomology

/-- The Mayer--Vietoris square `U ⊓ V, V, U, W` of two open subsets `U` and `V` with union
`W`, numbered as `CategoryTheory.Square` numbers its vertices. -/
def coverSquare {T : Type u} [TopologicalSpace T] (U V : Opens T) {W : Opens T}
    (hUV : U ⊔ V = W) : Square (Opens T) where
  X₁ := U ⊓ V
  X₂ := V
  X₃ := U
  X₄ := W
  f₁₂ := homOfLE inf_le_right
  f₁₃ := homOfLE inf_le_left
  f₂₄ := homOfLE (le_sup_right.trans hUV.le)
  f₃₄ := homOfLE (le_sup_left.trans hUV.le)
  fac := Subsingleton.elim _ _

end Stacks.Cohomology

end
