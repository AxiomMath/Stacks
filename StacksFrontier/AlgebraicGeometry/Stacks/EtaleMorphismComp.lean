module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismCompUnconditional

/-!
# The composite of étale 1-morphisms of algebraic stacks is étale (Stacks 0CIM)

**Stacks 0CIM** asserts that the composite of two étale 1-morphisms of algebraic stacks is
étale, étaleness being that of **Stacks 0CIL**: `AlgebraicGeometry.Stack.IsEtale`, the
Deligne–Mumford condition together with the universal étale-smooth diagram test at étaleness of
morphisms of algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isEtale_comp`: **Stacks 0CIM**, both conjuncts of
  `AlgebraicGeometry.Stack.IsEtale` for the composite.

## Implementation notes

The proof is the source's: combine **Stacks 0CIH** with **Stacks 0465**. The étaleness of
Stacks 0CIL is, by definition, the property of Deligne–Mumford 1-morphisms of algebraic stacks
which **Stacks 0CIG** induces from `AlgebraicGeometry.Space.IsEtale`, and both abbreviations
unfold to the same proposition, so Stacks 0CIH applies to it verbatim. Its two hypotheses on the
property are that étaleness of morphisms of algebraic spaces is étale-smooth local on the
source-and-target, which is the étale entry of **Stacks 0CG3**,
`AlgebraicGeometry.Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget`, and that it is stable
under composition, which is **Stacks 0465** (= **Stacks 03FT**),
`AlgebraicGeometry.Space.isEtale_comp`. Stacks 0CIH is
`AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_comp_of_isEtaleSmoothLocal`, which takes
**Stacks 0CIA** and **Stacks 06N3** from the library, so nothing is carried.

The weaker `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_comp_of_isEtale` of
`StacksFrontier.AlgebraicGeometry.Stacks.EtaleMorphismPermanence` is the first conjunct of the
result here.

## References

* [Stacks Project, Tag 0465](https://stacks.math.columbia.edu/tag/0465)
* [Stacks Project, Tag 0CG3](https://stacks.math.columbia.edu/tag/0CG3)
* [Stacks Project, Tag 0CIG](https://stacks.math.columbia.edu/tag/0CIG)
* [Stacks Project, Tag 0CIH](https://stacks.math.columbia.edu/tag/0CIH)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIM](https://stacks.math.columbia.edu/tag/0CIM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CIM.** The composite of two étale 1-morphisms of algebraic stacks over `S` is
étale, in the sense of **Stacks 0CIL**: it is Deligne–Mumford and passes the universal
étale-smooth diagram test at étaleness of morphisms of algebraic spaces.

This is **Stacks 0CIH** for the property `AlgebraicGeometry.Space.IsEtale`, which is
étale-smooth local on the source-and-target (**Stacks 0CG3**) and stable under composition
(**Stacks 0465**). -/
@[stacks 0CIM]
theorem isEtale_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} {g : 𝒴 ⟶ 𝒵}
    (hf : Stack.IsEtale B S hS f) (hg : Stack.IsEtale B S hS g) :
    Stack.IsEtale B S hS (f ≫ g) :=
  hasEtaleSmoothLocalProperty_comp_of_isEtaleSmoothLocal B S hS _
    (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS)
    (fun _ _ hp hq => Space.isEtale_comp B S hS hp hq) f g hf hg

end AlgebraicGeometry.Stack.AlgebraicStacks

end
