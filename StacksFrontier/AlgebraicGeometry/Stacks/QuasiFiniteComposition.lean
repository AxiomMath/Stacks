module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiFiniteAlgebraicStack

/-!
# Composition of quasi-finite 1-morphisms of algebraic stacks (Stacks 0G2N)

A composite of quasi-finite 1-morphisms of algebraic stacks over `S` is quasi-finite.
Quasi-finiteness (**Stacks 0G2M**) is the conjunction of local quasi-finiteness
(**Stacks 06PU**) and quasi-compactness (**Stacks 050U**), and each conjunct composes on its
own: the first by **Stacks 06UD** and the second by **Stacks 050W**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiFinite_comp`: **Stacks 0G2N**.

## Implementation notes

No hypothesis beyond those of the source is carried: the local quasi-finiteness conjunct is
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_comp` (**Stacks 06UD**) and the
quasi-compactness conjunct is `AlgebraicGeometry.Stack.isQuasiCompactMorphism_comp`
(**Stacks 050W**), both unconditional.

Quasi-finiteness is an `abbrev` for a conjunction, so the two conjuncts of the hypotheses are
projected and the conclusion is built as a pair; there is nothing else to the proof, which is why
the covering set is the one declaration.

## References

* [Stacks Project, Tag 050W](https://stacks.math.columbia.edu/tag/050W)
* [Stacks Project, Tag 06UD](https://stacks.math.columbia.edu/tag/06UD)
* [Stacks Project, Tag 0G2M](https://stacks.math.columbia.edu/tag/0G2M)
* [Stacks Project, Tag 0G2N](https://stacks.math.columbia.edu/tag/0G2N)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0G2N.** A composite of quasi-finite 1-morphisms of algebraic stacks over `S` is
quasi-finite: local quasi-finiteness composes by **Stacks 06UD** and quasi-compactness by
**Stacks 050W**. -/
@[stacks 0G2N]
theorem isQuasiFinite_comp
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsQuasiFinite B S hS f) (hg : IsQuasiFinite B S hS g) :
    IsQuasiFinite B S hS (f ≫ g) :=
  ⟨isLocallyQuasiFinite_comp B S hS f g hf.1 hg.1,
    Stack.isQuasiCompactMorphism_comp B S hS f g hf.2 hg.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
