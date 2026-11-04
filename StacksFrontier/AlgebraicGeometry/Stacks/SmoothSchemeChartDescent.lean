module

public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# Checking smoothness of a 1-morphism of algebraic stacks on a scheme chart of its target

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is smooth as soon as its base change along
a single smooth surjective 1-morphism from the stack of a scheme of the site is smooth
(**Stacks 0DN7**, with flatness and local finite presentation of the chart following from its
smoothness). Since every algebraic stack has such a chart (**Stacks 026O**), it suffices that the
base change along every such chart be smooth.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_isSmooth_baseChange_schemeStack`:
  smoothness from one smooth surjective scheme chart of the target.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_forall_isSmooth_baseChange_schemeStack`:
  the same with the chart quantified away.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 04TA](https://stacks.math.columbia.edu/tag/04TA)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0DN7](https://stacks.math.columbia.edu/tag/0DN7)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Smoothness of a 1-morphism of algebraic stacks from one smooth surjective scheme chart of
its target.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let
`g : (Sch/U) ⟶ 𝒴` be smooth and surjective. If the base change `(Sch/U) ×_𝒴 𝒳 ⟶ (Sch/U)` of `f`
along `g` is smooth, then `f` is smooth. -/
theorem isSmooth_of_isSmooth_baseChange_schemeStack
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (U : BigFppfOver B S hS) (g : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴)
    (hgsm : IsSmooth B S hS g) (hgs : Stack.IsSurjective B S hS g)
    (hbase : IsSmooth B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst) :
    IsSmooth B S hS f :=
  isSmooth_of_baseChange B S hS f g hgs (isFlat_of_isSmooth B S hS g hgsm)
    (isLocallyOfFinitePresentation_of_isSmooth B S hS g hgsm) hbase

/-- **Smoothness of a 1-morphism of algebraic stacks is a condition on its base changes to the
scheme charts of its target.** If the base change of `f : 𝒳 ⟶ 𝒴` along every smooth surjective
1-morphism from the stack of a scheme of the site to `𝒴` is smooth, then `f` is smooth. -/
theorem isSmooth_of_forall_isSmooth_baseChange_schemeStack
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hbase : ∀ (U : BigFppfOver B S hS) (g : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴),
      IsSmooth B S hS g → Stack.IsSurjective B S hS g →
        IsSmooth B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst) :
    IsSmooth B S hS f := by
  obtain ⟨U, g, hgsm, hgs⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒴
  exact isSmooth_of_isSmooth_baseChange_schemeStack B S hS f U g hgsm hgs (hbase U g hgsm hgs)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
