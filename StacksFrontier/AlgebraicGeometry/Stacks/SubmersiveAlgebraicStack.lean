module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Submersive and universally submersive 1-morphisms of algebraic stacks (Stacks 06U6)

Following Stacks 06U6, a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is submersive* when
the induced continuous map `|𝒳| → |𝒴|` of topological spaces of points is submersive in the sense
of Stacks 0406 — a surjective map inducing the topology of the target as the coinduced one — and
*is universally submersive* when for every 1-morphism `g : 𝒴' ⟶ 𝒴` of algebraic stacks the base
change `𝒴' ×_{g, 𝒴, f} 𝒳 ⟶ 𝒴'` is submersive in that sense.

Both notions are about *arbitrary* 1-morphisms of algebraic stacks, not only about those
representable by algebraic spaces: the topological space of points is available for every
algebraic stack, by Stacks 04XG and 04XL.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsSubmersive`: **Stacks 06U6**, part (1), the
  quotient-map condition on points.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsUniversallySubmersive`: **Stacks 06U6**, part (2),
  submersiveness of every base change along a 1-morphism of algebraic stacks.

## Implementation notes

This is the submersive member of the family whose closed member is
`AlgebraicGeometry.Stack.AlgebraicStacks.IsClosed` / `...UniversallyClosed` (**Stacks 0513**) and
whose open member is `...IsOpen` / `...UniversallyOpen` (**Stacks 06U2**), and it is stated at the
same spelling: the points of an algebraic stack are `AlgebraicGeometry.Stack.points`
(**Stacks 04XG**), their topology is `AlgebraicGeometry.Stack.pointTopology` (**Stacks 04XL**),
supplied by `letI` at the source and the target, and the map on points is
`AlgebraicGeometry.Stack.pointsMap`. The topology is constructed for an arbitrary category fibred
in groupoids and so takes no algebraicity hypothesis; `IsSubmersive` therefore mentions only the
fibred-in-groupoids clause `𝒳.val.property` of its arguments, the algebraicity clause
`𝒳.property` being needed nowhere.

Submersiveness of a continuous map is `Topology.IsQuotientMap`, which is **Stacks 0406**
part (2); the source's Definition 06U6 refers to Topology, Definition 0406 for exactly that
notion.

The base change in the universal condition is the first projection of the canonical
2-commutative square `AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`
(**Stacks 04T2**) of the cospan `(g, f)`, which is a 2-fibre product in the 2-category of
algebraic stacks; quantifying over the test stack `𝒴'` and the 1-morphism `g` rather than over all
2-fibre-product squares makes the condition independent of a choice of fibre product, since any
two are equivalent and `AlgebraicGeometry.Stack.pointsMap` is invariant under 2-isomorphism.

## References

* [Stacks Project, Tag 0406](https://stacks.math.columbia.edu/tag/0406)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 06U2](https://stacks.math.columbia.edu/tag/06U2)
* [Stacks Project, Tag 06U6](https://stacks.math.columbia.edu/tag/06U6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06U6, part (1).** A 1-morphism of algebraic stacks over `S` *is submersive* when the
map `|𝒳| → |𝒴|` it induces on the topological spaces of points of Stacks 04XG and 04XL is a
quotient map, which is submersiveness in the sense of Stacks 0406. -/
@[stacks 06U6 "part (1)", sga "1 IX 2.1" "submersive"]
abbrev IsSubmersive {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  letI := Stack.pointTopology B S hS 𝒳.val
  letI := Stack.pointTopology B S hS 𝒴.val
  Topology.IsQuotientMap
    (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom)

/-- **Stacks 06U6, part (2).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is
universally submersive* when, for every 1-morphism `g : 𝒴' ⟶ 𝒴` of algebraic stacks over `S`, the
base change `𝒴' ×_{g, 𝒴, f} 𝒳 ⟶ 𝒴'` of `f` by `g` is submersive in the sense of
`AlgebraicGeometry.Stack.AlgebraicStacks.IsSubmersive`. -/
@[stacks 06U6 "part (2)", sga "1 IX 2.1" "univ. submersive"]
abbrev IsUniversallySubmersive {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (𝒴' : Stack.AlgebraicStacks.{u, w} B S hS) (g : 𝒴' ⟶ 𝒴),
    IsSubmersive B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst

end AlgebraicGeometry.Stack.AlgebraicStacks

end
