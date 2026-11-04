module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Locally quasi-finite 1-morphisms of algebraic stacks (Stacks 06PU)

Following Stacks 06PU, a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is locally
quasi-finite* when three conditions hold: it is quasi-DM, it is locally of finite type, and for
every field-valued point `Spec(k) → 𝒴` of the target the fibre `𝒳_k` has discrete space of
points.

The first two conjuncts are
`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiDMWithRepresentableDiagonal` (**Stacks 04YW**, the
quasi-DM condition) and `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFiniteType`
(**Stacks 06FS**, part (1)).

A field-valued point of `𝒴` is rendered as the data it consists of over `S`: a field `k` whose
spectrum lies in the chosen big fppf site, a structure morphism `Spec(k) ⟶ S` making that
spectrum an object of the big fppf category over `S`, and a 1-morphism from the algebraic stack
that object represents to `𝒴`. The algebraic stack representing it is
`AlgebraicGeometry.Stack.schemeStack` (**Stacks 04X5**, the canonical 2-categorical
correspondence), and the fibre is the apex of the canonical 2-fibre-product square
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` (**Stacks 04T2**). Its space of
points is `AlgebraicGeometry.Stack.points` (**Stacks 04XG**) carrying the topology
`AlgebraicGeometry.Stack.pointTopology` (**Stacks 04XL**), supplied by `letI` exactly as
`AlgebraicGeometry.Stack.AlgebraicStacks.IsClosed` does.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyQuasiFinite`: **Stacks 06PU**.

## Implementation notes

This is local quasi-finiteness of an *arbitrary* 1-morphism of algebraic stacks. The Stacks 04XB
relative notion, for a 1-morphism representable by algebraic spaces, is the different predicate
`AlgebraicGeometry.Stack.IsLocallyQuasiFinite`, which quantifies over the algebraic spaces
representing the base changes of `f` along scheme-valued points and asks each to have locally
quasi-finite structural morphism. The two share a leaf name and are not the same notion, so they
live in different namespaces, as do `AlgebraicGeometry.Stack.IsQuasiSeparated` and
`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiSeparated`, and
`AlgebraicGeometry.Stack.UniversallyClosed` and
`AlgebraicGeometry.Stack.AlgebraicStacks.UniversallyClosed`.

The predicate is an `abbrev`, so a consumer may project the three defining clauses and reach the
topology on every field-valued fibre directly. That is the shape of the sibling definitions of
this chapter — `AlgebraicGeometry.Stack.AlgebraicStacks.IsProper` (**Stacks 0CL5**) and
`...IsFiniteType` (**Stacks 06FS**, part (2)).

## References

* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06PU.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is locally
quasi-finite* when it is quasi-DM (**Stacks 04YW**), locally of finite type (**Stacks 06FS**,
part (1)), and for every field-valued point of `𝒴` the fibre of `f` over it has discrete space of
points.

A field-valued point is a field `k` contained in the site together with a structure morphism
`Spec(k) ⟶ S` and a 1-morphism from the algebraic stack `Spec(k)` represents to `𝒴`; the fibre is
the apex of the canonical 2-fibre-product square of that 1-morphism with `f`, and its points
carry the topology of **Stacks 04XL**. -/
@[stacks 06PU]
abbrev IsLocallyQuasiFinite {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsQuasiDMWithRepresentableDiagonal B S hS f ∧ IsLocallyOfFiniteType B S hS f ∧
    ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
      (toBase : Spec (.of k) ⟶ S)
      (g : Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒴),
      letI := Stack.pointTopology B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val
      DiscreteTopology
        (Stack.points B S hS
          (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.val
          (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.property)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
