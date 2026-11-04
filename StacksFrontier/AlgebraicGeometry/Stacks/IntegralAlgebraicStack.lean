module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStack
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBasedCategory

/-!
# Integral algebraic stacks

An algebraic stack `𝒳` over a scheme `S` contained in a big fppf site is *integral* when four
conditions hold: it is reduced, it is decent, its inertia projection `I_𝒳 ⟶ 𝒳` is quasi-compact,
and its space of points `|𝒳|` is irreducible.

## Main definitions

* `AlgebraicGeometry.Stack.inertiaAlgebraicStack`: the inertia `I_𝒳` of an algebraic stack, as an
  object of the 2-category of algebraic stacks over `S`.
* `AlgebraicGeometry.Stack.inertiaProjectionAlgebraicStacks`: the forgetful 1-morphism
  `π : I_𝒳 ⟶ 𝒳`, read in that 2-category.
* `AlgebraicGeometry.Stack.IsIntegral`: integrality of an algebraic stack.

## Implementation notes

Irreducibility of `|𝒳|` is `IrreducibleSpace` for the points of `𝒳` with their topology, and so
includes nonemptiness.

## References

* [Stacks Project, Tag 0GWB](https://stacks.math.columbia.edu/tag/0GWB)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 04Y8](https://stacks.math.columbia.edu/tag/04Y8)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inertia `I_𝒳` of an algebraic stack `𝒳` over `S`, as an object of the 2-category of
algebraic stacks over `S`: the inertia of the underlying category fibred in groupoids. -/
abbrev inertiaAlgebraicStack (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.{u, w} B S hS :=
  ⟨inertia B S hS 𝒳.val, isAlgebraicStack_inertia.{u, w} B S hS 𝒳.val 𝒳.property⟩

/-- The forgetful 1-morphism `π : I_𝒳 ⟶ 𝒳` of the inertia of an algebraic stack `𝒳` over `S`,
`(x, α) ↦ x`, read in the 2-category of algebraic stacks over `S` rather than in the ambient
2-category of categories fibred in groupoids. -/
def inertiaProjectionAlgebraicStacks (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    inertiaAlgebraicStack B S hS 𝒳 ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom
      (RelativeInertia.basedProjection
        (𝒴 := BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
        ⟨𝒳.val.val.p, Functor.comp_id 𝒳.val.val.p⟩))

/-- An algebraic stack `𝒳` over `S` is *integral* when it is reduced, it is
decent, its inertia projection `I_𝒳 ⟶ 𝒳` is quasi-compact, and its space of points `|𝒳|` is
irreducible. -/
@[stacks 0GWB]
abbrev IsIntegral (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  IsReducedStack B S hS 𝒳 ∧ IsDecent B S hS 𝒳.val ∧
    IsQuasiCompactMorphism B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳) ∧
      @IrreducibleSpace (points B S hS 𝒳.val.val 𝒳.val.property)
        (pointTopology B S hS 𝒳.val)

end AlgebraicGeometry.Stack

end
