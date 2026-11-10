module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubmersiveComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedBaseChange

/-!
# Composition of closed and of universally closed 1-morphisms of algebraic stacks

The composite of two closed 1-morphisms of algebraic stacks over `S` is closed, and the composite
of two universally closed 1-morphisms of algebraic stacks over `S` is universally closed.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_comp`: the composite of two closed
  1-morphisms of algebraic stacks is closed.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_comp`: the composite of two
  universally closed 1-morphisms of algebraic stacks is universally closed.

## Implementation notes

The leaf names agree with those of `AlgebraicGeometry.Space.universallyClosed_comp` for
morphisms of algebraic spaces; the two are distinguished by namespace.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 0514](https://stacks.math.columbia.edu/tag/0514)
* [Stacks Project, Tag 0515](https://stacks.math.columbia.edu/tag/0515)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The composite of two closed 1-morphisms of algebraic stacks over `S` is closed. -/
@[stacks 0515 "closed"]
theorem isClosed_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hf : IsClosed B S hS f) (hg : IsClosed B S hS g) :
    IsClosed B S hS (f ≫ g) := by
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  let _ := Stack.pointTopology B S hS 𝒵.val
  change IsClosedMap
    (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒵.val.property (f ≫ g).hom.hom)
  rw [pointsMap_comp' B S hS f g]
  exact hg.comp hf

/-- The composite of two universally closed 1-morphisms of algebraic stacks over `S` is
universally closed. -/
@[stacks 0515 "universally closed"]
theorem universallyClosed_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : UniversallyClosed B S hS f) (hg : UniversallyClosed B S hS g) :
    UniversallyClosed B S hS (f ≫ g) := by
  intro 𝒲 k
  have hA := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k g
  set A := Stack.twoFibreProductSquareAlgebraicStacks B S hS k g with hAdef
  have hC := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS A.snd f
  set C := Stack.twoFibreProductSquareAlgebraicStacks B S hS A.snd f with hCdef
  exact Stack.isClosedMap_pointsMap_fst_congr B S hS
    (A.paste C).underlying
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS k (f ≫ g)).underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (Bicategory.isTwoFibreProduct_paste hA hC))
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k (f ≫ g)))
    (isClosed_comp B S hS C.fst A.fst (hf A.pt A.snd) (hg 𝒲 k))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
