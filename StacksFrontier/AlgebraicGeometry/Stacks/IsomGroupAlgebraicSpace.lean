module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomGroupSpace

/-!
# `Isom_𝒳(y, y)` is a group algebraic space (Stacks 04YP, part (1))

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site `B`, let `T` be a
scheme of that site and let `y` be an object of the fibre category of `𝒳` over `T`. Part (1) of
**Stacks 04YP** says that `Isom_𝒳(y, y)` is a group algebraic space over `T`.

The statement below is about the canonical object `AlgebraicGeometry.Stack.isomSpaceOver` with
`x = y`, whose underlying presheaf is `Isom_𝒳(y, y)` by definition, together with its group
structure `AlgebraicGeometry.Stack.isomSpaceOverGrpObj`. It asserts that

* this group object over the base `AlgebraicGeometry.Stack.siteTerminalSpace` (which is `T`
  read on its own site) is an object of the category of group algebraic spaces over `T` of
  Stacks 043H, i.e. its underlying presheaf `Isom_𝒳(y, y)` is an algebraic space, and
* its multiplication is composition of local automorphisms.

## Main results

* `AlgebraicGeometry.Stack.isomSpaceOver_isGroupAlgebraicSpace`: **Stacks 04YP**, part (1).

## References

* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj

universe u w

namespace AlgebraicGeometry.Stack

/-- **Stacks 04YP, part (1).** For an object `y` of the fibre category of an algebraic stack `𝒳`
over a scheme `T` of the big fppf site of `S`, `Isom_𝒳(y, y)` is a group algebraic space over
`T`: the group object `Isom_𝒳(y, y)` over the base `AlgebraicGeometry.Stack.siteTerminalSpace`,
with the group structure `AlgebraicGeometry.Stack.isomSpaceOverGrpObj`, is (on the nose) an
object of the category `AlgebraicGeometry.Space.GroupAlgebraicSpace` of group algebraic spaces
over `T`, and its multiplication is composition of local automorphisms
(`AlgebraicGeometry.Stack.isomSpaceComp`). -/
@[stacks 04YP "part (1): Isom(y, y) is a group algebraic space over T"]
theorem isomSpaceOver_isGroupAlgebraicSpace (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (U : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber U) :
    letI : GrpObj (isomSpaceOver B S hS 𝒳 U y y) := isomSpaceOverGrpObj B S hS 𝒳 U y
    (∃ G : Space.GroupAlgebraicSpace B U.left.1 U.left.2 (siteTerminalSpace B S hS U)
        (isAlgebraicSpace_yoneda B U.left.1 U.left.2
          (⊤_ (BigFppfOver B U.left.1 U.left.2))),
        G.obj = Grp.mk (isomSpaceOver B S hS 𝒳 U y y)) ∧
      ∀ (Q : Over (siteTerminalSpace B S hS U)) (a b : Q ⟶ isomSpaceOver B S hS 𝒳 U y y)
        (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (t : Q.left.obj V),
        ((CartesianMonoidalCategory.lift a b ≫
          MonObj.mul (X := isomSpaceOver B S hS 𝒳 U y y)).left.app V) t =
          isomSpaceComp B S hS 𝒳 U y V ((a.left.app V) t) ((b.left.app V) t) := by
  let : GrpObj (isomSpaceOver B S hS 𝒳 U y y) := isomSpaceOverGrpObj B S hS 𝒳 U y
  refine ⟨⟨⟨Grp.mk (isomSpaceOver B S hS 𝒳 U y y), ?_⟩, rfl⟩, ?_⟩
  · show IsAlgebraicSpace B U.left.1 U.left.2 (isomSpace B S hS 𝒳 U y y)
    exact isAlgebraicSpace_isomSpace B S hS 𝒳 h𝒳 U y y
  · intro Q a b V t
    exact isomSpaceOverGrpObj_mul B S hS 𝒳 U y Q a b V t

end AlgebraicGeometry.Stack

end
