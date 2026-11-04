module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions

/-!
# The standing data of a quotient by a group action (Stacks 04WL)

The quotient stack `[X/G]` of a group algebraic space acting on an algebraic space is built
from a scheme `S` of a big fppf site, an algebraic space `B` over `S`, a group algebraic space
`G` over `B`, an algebraic space `X` over `B` and an action of `G` on `X` over `B`.

## Main definitions

* `AlgebraicGeometry.Space.GroupActionSituation` is that data, bundled.

## Implementation notes

The group algebraic space is an object of
`AlgebraicGeometry.Space.GroupAlgebraicSpace` and the action is the monoidal-category notion
`CategoryTheory.ModObj` in the slice over `B`, whose tensor product is the fibre product over
`B`, so that the action morphism of the bundled data is literally a morphism `G ×_B X ⟶ X`
over `B`.  Both are the forms in which the acted-on objects of **Stacks 043H** and
**Stacks 043Q** already appear in the library, and
`AlgebraicGeometry.Space.actionSpace` and `AlgebraicGeometry.Space.action` read the fibre
product and the action morphism of a situation as an algebraic space over `S` and a morphism
of algebraic spaces.

## References

* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 043Q](https://stacks.math.columbia.edu/tag/043Q)
* [Stacks Project, Tag 04WL](https://stacks.math.columbia.edu/tag/04WL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks Project, Tag 04WL.** The data a quotient by a group action is formed from: a
scheme `S` of a big fppf site, an algebraic space `B` over `S`, a group algebraic space `G`
over `B`, an algebraic space `X` over `B`, and an action of `G` on `X` over `B`. -/
@[stacks 04WL]
structure GroupActionSituation where
  /-- The big fppf site. -/
  site : BigFppfSite.{u}
  /-- The scheme `S` the whole situation lives over. -/
  S : Scheme.{u}
  /-- `S` is contained in the big fppf site. -/
  containsS : site.Contains S
  /-- The presheaf underlying the algebraic space `B` over `S`. -/
  B : (BigFppfOver site S containsS)ᵒᵖ ⥤ Type u
  /-- `B` is an algebraic space. -/
  isAlgebraicSpaceB : IsAlgebraicSpace site S containsS B
  /-- The group algebraic space `(G, m)` over `B`. -/
  G : GroupAlgebraicSpace site S containsS B isAlgebraicSpaceB
  /-- The algebraic space `X` over `B`, together with its structure morphism `π : X ⟶ B`. -/
  X : Over B
  /-- `X` is an algebraic space. -/
  isAlgebraicSpaceX : IsAlgebraicSpace site S containsS X.left
  /-- The action `a : G ×_B X ⟶ X` of `G` on `X` over `B`. -/
  a : ModObj G.obj.X X

end AlgebraicGeometry.Space

end
