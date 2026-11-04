module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedQuasiSeparatedAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Closed, universally closed and proper 1-morphisms of algebraic stacks (Stacks 0513, 0CL5)

Following Stacks 0513, a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is closed* when the
induced map `|𝒳| → |𝒴|` of topological spaces of points is closed, and *is universally closed*
when for every 1-morphism `g : 𝒵 ⟶ 𝒴` of algebraic stacks the base change
`𝒵 ×_{g, 𝒴, f} 𝒳 ⟶ 𝒵` is closed in that sense. Stacks 0CL5 then calls `f` *proper* when it is
separated, of finite type and universally closed.

Both notions are about *arbitrary* 1-morphisms of algebraic stacks, not only about those
representable by algebraic spaces: the topological space of points is available for every
algebraic stack, by Stacks 04XG and 04XL.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsClosed`: **Stacks 0513**, part (1), closedness on
  points.
* `AlgebraicGeometry.Stack.AlgebraicStacks.UniversallyClosed`: **Stacks 0513**, part (2),
  closedness of every base change along a 1-morphism of algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsProper`: **Stacks 0CL5**, properness.

## Implementation notes

The three conditions are stated in the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks`
(**Stacks 03YP**), so all three are predicates on one and the same kind of 1-morphism as the
separatedness condition `AlgebraicGeometry.Stack.AlgebraicStacks.IsSeparated` (**Stacks 04YW**)
and the finite type condition `AlgebraicGeometry.Stack.AlgebraicStacks.IsFiniteType`
(**Stacks 06FS**, part (2)) that Stacks 0CL5 conjoins them with.

The points of an algebraic stack are `AlgebraicGeometry.Stack.points` (**Stacks 04XG**) and their
topology is `AlgebraicGeometry.Stack.pointTopology` (**Stacks 04XL**), supplied by `letI` at the
source and the target; the map on points is `AlgebraicGeometry.Stack.pointsMap`. The topology is
constructed for an arbitrary category fibred in groupoids and so takes no algebraicity
hypothesis; `IsClosed` therefore mentions only the fibred-in-groupoids clause `𝒳.val.property`
of its arguments, the algebraicity clause `𝒳.property` being needed nowhere.

The base change in the universal condition is the first projection of the canonical
2-commutative square `AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`
(**Stacks 04T2**) of the cospan `(g, f)`, which is a 2-fibre product in the 2-category of
algebraic stacks by
`AlgebraicGeometry.Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks`;
quantifying over the test stack `𝒵` and the 1-morphism `g` rather than over all 2-fibre-product
squares makes the condition independent of a choice of fibre product, since any two are
equivalent and `AlgebraicGeometry.Stack.pointsMap` is invariant under 2-isomorphism.

**These are not the Stacks 04XB relative properties of the same names.**
`AlgebraicGeometry.Stack.UniversallyClosed` and `AlgebraicGeometry.Stack.IsProper`
(`AlgebraicGeometry.Stack.SeparatedMorphism`) are the relative notions for a 1-morphism
*representable by algebraic spaces*, quantified over represented base changes along
scheme-valued points, and they are different propositions about a different kind of 1-morphism —
they are not even comparable by type. The same distinction already holds between
`AlgebraicGeometry.Stack.IsSeparated` and
`AlgebraicGeometry.Stack.AlgebraicStacks.IsSeparated`.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 0CL5](https://stacks.math.columbia.edu/tag/0CL5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0513, part (1).** A 1-morphism of algebraic stacks over `S` *is closed* when the
map `|𝒳| → |𝒴|` it induces on the topological spaces of points of Stacks 04XG and 04XL is a
closed map. -/
@[stacks 0513 "closed"]
abbrev IsClosed {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  letI := Stack.pointTopology B S hS 𝒳.val
  letI := Stack.pointTopology B S hS 𝒴.val
  IsClosedMap (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom)

/-- **Stacks 0513, part (2).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is
universally closed* when, for every 1-morphism `g : 𝒵 ⟶ 𝒴` of algebraic stacks over `S`, the
base change `𝒵 ×_{g, 𝒴, f} 𝒳 ⟶ 𝒵` of `f` by `g` is closed in the sense of
`AlgebraicGeometry.Stack.AlgebraicStacks.IsClosed`. -/
@[stacks 0513 "universally closed"]
abbrev UniversallyClosed {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴),
    IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst

/-- **Stacks 0CL5.** A 1-morphism of algebraic stacks over `S` *is proper* when it is separated
(**Stacks 04YW**), of finite type (**Stacks 06FS**, part (2)) and universally closed
(**Stacks 0513**, part (2)).

This is properness for an *arbitrary* 1-morphism of algebraic stacks; the Stacks 04XB relative
notion for a 1-morphism representable by algebraic spaces is
`AlgebraicGeometry.Stack.IsProper`. -/
@[stacks 0CL5]
abbrev IsProper {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsSeparated B S hS f ∧ IsFiniteType B S hS f ∧ UniversallyClosed B S hS f

end AlgebraicGeometry.Stack.AlgebraicStacks

end
