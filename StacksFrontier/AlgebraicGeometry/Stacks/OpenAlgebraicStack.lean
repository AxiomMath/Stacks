module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Open and universally open 1-morphisms of algebraic stacks (Stacks 06U2)

Following Stacks 06U2, a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is open* when the
induced map `|𝒳| → |𝒴|` of topological spaces of points is open, and *is universally open* when
for every 1-morphism `g : 𝒵 ⟶ 𝒴` of algebraic stacks the base change `𝒵 ×_{g, 𝒴, f} 𝒳 ⟶ 𝒵` is
open in that sense. The base change is the first projection of the canonical 2-fibre product
square `AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` of the cospan `(g, f)`.

Both notions are about *arbitrary* 1-morphisms of algebraic stacks, not only about those
representable by algebraic spaces: the topological space of points is available for every
algebraic stack, by Stacks 04XG and 04XL.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsOpen`: a 1-morphism of algebraic stacks is open on
  points.
* `AlgebraicGeometry.Stack.AlgebraicStacks.UniversallyOpen`: every base change of a 1-morphism of
  algebraic stacks along a 1-morphism of algebraic stacks is open on points.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 06U2](https://stacks.math.columbia.edu/tag/06U2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is open* when the map `|𝒳| → |𝒴|` it
induces on the topological spaces of points is an open map. -/
@[stacks 06U2 "part (1): open"]
abbrev IsOpen {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  letI := Stack.pointTopology B S hS 𝒳.val
  letI := Stack.pointTopology B S hS 𝒴.val
  IsOpenMap (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom)

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is universally open* when, for every
1-morphism `g : 𝒵 ⟶ 𝒴` of algebraic stacks over `S`, the base change `𝒵 ×_{g, 𝒴, f} 𝒳 ⟶ 𝒵` of `f`
by `g` is open in the sense of `AlgebraicGeometry.Stack.AlgebraicStacks.IsOpen`. -/
@[stacks 06U2 "part (2): universally open"]
abbrev UniversallyOpen {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴),
    IsOpen B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst

end AlgebraicGeometry.Stack.AlgebraicStacks

end
