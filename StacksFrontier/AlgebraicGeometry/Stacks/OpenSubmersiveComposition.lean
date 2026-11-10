module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SubmersiveAlgebraicStack

/-!
# Composition of open and of submersive 1-morphisms of algebraic stacks (Stacks 06U4, 0CHZ)

**Stacks 06U4** asserts that the composite of two open 1-morphisms of algebraic stacks over `S`
is open, and **Stacks 0CHZ** that the composite of two submersive ones is submersive. The source
proves neither (both read "Omitted."): each is the corresponding topological fact about the
induced maps on points, which compose.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_comp'`: the map on points of a composite of
  1-morphisms of algebraic stacks is the composite of the maps on points.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isOpen_comp`: **Stacks 06U4**, the non-universal half.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSubmersive_comp`: **Stacks 0CHZ**, the non-universal
  half.

## Implementation notes

Openness (**Stacks 06U2** part (1)) and submersiveness (**Stacks 06U6** part (1)) are conditions
on `AlgebraicGeometry.Stack.pointsMap` for the topology of **Stacks 04XL**, so both statements
reduce to one identity — that `AlgebraicGeometry.Stack.pointsMap` turns composition of
1-morphisms into composition of maps — followed by `IsOpenMap.comp` and
`Topology.IsQuotientMap.comp`. That identity is
`AlgebraicGeometry.Stack.pointsMap_comp` read in the 2-category of algebraic stacks
(**Stacks 03YP**), where composition of 1-morphisms is composition of the underlying based
functors on the nose, so no transport appears.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06U2](https://stacks.math.columbia.edu/tag/06U2)
* [Stacks Project, Tag 06U4](https://stacks.math.columbia.edu/tag/06U4)
* [Stacks Project, Tag 06U6](https://stacks.math.columbia.edu/tag/06U6)
* [Stacks Project, Tag 0CHZ](https://stacks.math.columbia.edu/tag/0CHZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map on points of a composite of 1-morphisms of algebraic stacks over `S` is the
composite of the maps on points: `AlgebraicGeometry.Stack.pointsMap_comp` read in the 2-category
of algebraic stacks, where composition of 1-morphisms is composition of the underlying based
functors. -/
theorem pointsMap_comp' {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒵.val.property (f ≫ g).hom.hom =
      Stack.pointsMap B S hS 𝒴.val.val 𝒴.val.property 𝒵.val.property g.hom.hom ∘
        Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom :=
  funext fun z => (Stack.pointsMap_comp B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property
    𝒵.val.property f.hom.hom g.hom.hom z).symm

/-- **Stacks 06U4.** The composite of two open 1-morphisms of algebraic stacks over `S` is
open. -/
@[stacks 06U4 "composition_open"]
theorem isOpen_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hf : IsOpen B S hS f) (hg : IsOpen B S hS g) :
    IsOpen B S hS (f ≫ g) := by
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  let _ := Stack.pointTopology B S hS 𝒵.val
  change IsOpenMap
    (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒵.val.property (f ≫ g).hom.hom)
  rw [pointsMap_comp' B S hS f g]
  exact hg.comp hf

/-- **Stacks 0CHZ.** The composite of two submersive 1-morphisms of algebraic stacks over `S` is
submersive. -/
@[stacks 0CHZ "composition_submersive"]
theorem isSubmersive_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hf : IsSubmersive B S hS f) (hg : IsSubmersive B S hS g) :
    IsSubmersive B S hS (f ≫ g) := by
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  let _ := Stack.pointTopology B S hS 𝒵.val
  change Topology.IsQuotientMap
    (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒵.val.property (f ≫ g).hom.hom)
  rw [pointsMap_comp' B S hS f g]
  exact hg.comp hf

end AlgebraicGeometry.Stack.AlgebraicStacks

end
