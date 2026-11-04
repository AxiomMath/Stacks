module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids

/-!
# An algebraic stack is a stack for the fppf topology (Stacks 04SZ, parts (1) and (2))

`AlgebraicGeometry.Stack.IsAlgebraicStack` carries the stack condition as a conjunction of the
two renderings of Stacks 02ZJ: the sieve-indexed `CategoryTheory.Functor.IsStack` of Stacks 026F,
which is universe-free, and the family-indexed `CategoryTheory.Functor.IsStackInGroupoids` of
Stacks 02ZI at the descent universe `w`. The notions that consume the stack condition — among
them `CategoryTheory.Functor.IsStackInSetoids` — contain the sieve-indexed one, so for an
algebraic stack it is available by projection, at every descent universe.

This file records that projection and the consequence for Stacks 04SZ: the equivalence (1) ⟺ (2)
of that tag for an algebraic stack, at a free descent universe.

## Main results

In the namespace `AlgebraicGeometry.Stack`:

* `isStack_of_isAlgebraicStack`: an algebraic stack is a stack in the sense of Stacks 026F.
* `isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isAlgebraicStack`: an algebraic stack
  is a stack in setoids if and only if the projection from its inertia is an equivalence.

## References

* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 02ZJ](https://stacks.math.columbia.edu/tag/02ZJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack over the big fppf site of `S` is a stack, in the sieve-indexed sense
`CategoryTheory.Functor.IsStack`. -/
theorem isStack_of_isAlgebraicStack {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳) :
    𝒳.p.IsStack (BigFppfOver.topology B S hS) :=
  h𝒳.2.1.1

/-- An algebraic stack over the big fppf site of `S` is a stack in setoids if and only if the
canonical projection from its inertia category is an equivalence. -/
@[stacks 04SZ "parts (1) and (2)"]
theorem isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isAlgebraicStack
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) ↔
      (RelativeInertia.π 𝒳.val.p :
        AbsoluteInertia 𝒳.val.p ⥤ 𝒳.val.obj).IsEquivalence :=
  isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isStack B S hS 𝒳
    (isStack_of_isAlgebraicStack B S hS h𝒳)

end AlgebraicGeometry.Stack

end
