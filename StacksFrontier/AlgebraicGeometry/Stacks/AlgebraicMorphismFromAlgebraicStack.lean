module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct

/-!
# A 1-morphism out of an algebraic stack is algebraic (Stacks 06CG)

Let `S` be a scheme contained in a big fppf site `B` and let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of
stacks in groupoids over the big fppf site of `S`. If `𝒳` is an algebraic stack and the diagonal
`Δ : 𝒴 ⟶ 𝒴 × 𝒴` is representable by algebraic spaces, then `F` is *algebraic* in the sense of
Stacks 06CF: its 2-fibre product with every scheme-valued point of `𝒴` is an algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicMorphism_of_isAlgebraicStack`: **Stacks 06CG**.

## Implementation notes

The 2-fibre product that Stacks 06CF asks about is the one over the cospan formed by the point
and by `F`, so Stacks 04TF
(`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct`) applies to it directly, with base
`𝒴`: its hypotheses on the base are exactly the stack clause of `𝒴` and the hypothesis on the
diagonal of `𝒴`, and its two other factors are `𝒳` and the category over which the point is
taken. That category is `CategoryTheory.BasedCategory.ofFunctor (CategoryTheory.Over.map U.hom)`,
the relocalization of the site at the scheme `U` carrying the point; it is equivalent over the
site to `AlgebraicGeometry.Stack.schemeFibredCategory`, which is an algebraic stack, by the
iterated-slice equivalence, so
`AlgebraicGeometry.Stack.isAlgebraicStack_iff_of_isEquivalence` makes it one too.

The source's own proof instead builds a smooth surjective presentation of the 2-fibre product
and invokes Stacks 05UL, which in this library carries the unproved bootstrap theorem
Stacks 04S6 as a hypothesis; the route through Stacks 04TF needs no such input.

The hypothesis `h𝒴` is the sieve-indexed rendering `CategoryTheory.Functor.IsStack` of
Stacks 026F of the source's hypothesis that `𝒴` is a stack in groupoids, whose family-indexed
rendering of Stacks 02ZI is already carried by `CategoryTheory.StackInGroupoids`. The two are
the conditions (1) and (3) of Stacks 02ZJ and either may be assumed, but only the implication
from the sieve-indexed one to the family-indexed one is available in this library — see the
implementation notes of `StacksFrontier/AlgebraicGeometry/Stacks/AlgebraicStack.lean` — and
Stacks 04TF consumes the sieve-indexed one.

## References

* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 06CF](https://stacks.math.columbia.edu/tag/06CF)
* [Stacks Project, Tag 06CG](https://stacks.math.columbia.edu/tag/06CG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- **The relocalization of the big fppf site of `S` at an object `U` is an algebraic stack.**
It is equivalent over the site, by the iterated-slice equivalence, to the category represented
by `U`, which is an algebraic stack. -/
theorem isAlgebraicStack_overMap (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) :
    IsAlgebraicStack.{u, w} B S hS
      (BasedCategory.ofFunctor.{u, u + 1, u, u + 1} (Over.map U.hom)) :=
  (isAlgebraicStack_iff_of_isEquivalence.{u, u, u + 1, w} B S hS
      (𝒳 := BasedCategory.ofFunctor.{u, u + 1, u, u + 1} (Over.map U.hom))
      (𝒴 := (schemeFibredCategory B S hS U).val)
      ⟨Over.iteratedSliceBackward U, rfl⟩
      (Functor.IsFiberedInGroupoids.over_map U.hom)
      (schemeFibredCategory B S hS U).isFiberedInGroupoids
      (inferInstanceAs (Functor.IsEquivalence (Over.iteratedSliceEquiv U).inverse))).mpr
    (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS U)

/-- **Stacks 06CG.** Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf
site of `S`. If `𝒳` is an algebraic stack and the diagonal of `𝒴` is representable by algebraic
spaces, then `F` is algebraic in the sense of Stacks 06CF. -/
@[stacks 06CG]
theorem isAlgebraicMorphism_of_isAlgebraicStack
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1}
      (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : 𝒴.toBasedCategory.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.toBasedCategory)
    (hΔ : HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk 𝒴.toBasedCategory
        𝒴.isStackInGroupoids.isFiberedInGroupoids)) :
    IsAlgebraicMorphism.{u, w, w, w} B S hS (𝒳 := 𝒳) (𝒴 := 𝒴) f.hom := by
  intro U y hy
  exact isAlgebraicStack_twoFibreProduct.{u, w} B S hS
    (BasedCategory.ofFunctor.{u, u + 1, u, u + 1} (Over.map U.hom))
    𝒳.toBasedCategory 𝒴.toBasedCategory ⟨y, hy⟩ f.hom
    ⟨h𝒴, 𝒴.isStackInGroupoids⟩ hΔ (isAlgebraicStack_overMap.{u, w} B S hS U) h𝒳

end AlgebraicGeometry.Stack

end
