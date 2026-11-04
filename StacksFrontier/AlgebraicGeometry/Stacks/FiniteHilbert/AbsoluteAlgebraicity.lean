module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.AbsoluteOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.FiniteCoverAlgebraicStack

/-!
# Algebraicity of the absolute finite Hilbert category

Let `S` be a scheme contained in a big fppf site, let `𝒳` be a stack in groupoids over that site
which is representable by an algebraic space over `S`, and let `d ≥ 1` be an integer. Then the
absolute finite Hilbert category `ℋ_d(𝒳)` is an algebraic stack over `S`.

The category `ℋ_d` of degree-`d` finite locally free covers is an algebraic stack by the second
assertion of Stacks 05YQ (`AlgebraicGeometry.Stack.isAlgebraicStack_finiteCoverFibered`), and
the forgetful 1-morphism `ℋ_d(𝒳) ⟶ ℋ_d` of Stacks 05WD is representable by algebraic spaces, so
Stacks 05UM applies: the source of a 1-morphism representable by algebraic spaces into an
algebraic stack is itself an algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_absoluteHilbertCategory`: the statement above, which
  is Stacks 05YS.

## References

* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 05YJ](https://stacks.math.columbia.edu/tag/05YJ)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
* [Stacks Project, Tag 05YS](https://stacks.math.columbia.edu/tag/05YS)
* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable (𝒳 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)) (d : ℕ)

/-- **Stacks 05YS.** For `𝒳` representable by an algebraic space over `S` and `d ≥ 1`, the
absolute finite Hilbert category `ℋ_d(𝒳)` is an algebraic stack. The hypothesis `d ≥ 1`, as
`[NeZero d]`, is the domain of the statement: the source defines `ℋ_d` only for `d ≥ 1`.

`ℋ_d` is an algebraic stack by the second assertion of Stacks 05YQ
(`AlgebraicGeometry.Stack.isAlgebraicStack_finiteCoverFibered`), the forgetful 1-morphism
`ℋ_d(𝒳) ⟶ ℋ_d` is representable by algebraic spaces by Stacks 05YJ, and Stacks 05UM applies. -/
theorem isAlgebraicStack_absoluteHilbertCategory [NeZero d]
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.mk 𝒳.toBasedCategory
        𝒳.isStackInGroupoids.isFiberedInGroupoids)) :
    IsAlgebraicStack.{u, w} B S hS (absoluteHilbertFibered 𝒳 d).val :=
  isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS
    (forgetAbsoluteStructureFibered 𝒳 d)
    (isRepresentableByAlgebraicSpaces_forgetAbsoluteStructure_of_space 𝒳 d h𝒳)
    (isAlgebraicStack_finiteCoverFibered.{u, w} B S hS d)

end AlgebraicGeometry.Stack

end
