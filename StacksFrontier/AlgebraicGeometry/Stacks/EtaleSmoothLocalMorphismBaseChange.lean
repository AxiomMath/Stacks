module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismBaseChangeStable
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEquivalence

/-!
# Base change of an étale-smooth local property of Deligne–Mumford morphisms (Stacks 0CII)

Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on
the source-and-target (**Stacks 0CFZ**) and stable under base change. **Stacks 0CII** says that
the property of Deligne–Mumford 1-morphisms of algebraic stacks which **Stacks 0CIG** induces
from `P` is stable under arbitrary base change.

## Main results

* `AlgebraicGeometry.Stack`
  `.hasEtaleSmoothLocalProperty_snd_of_isTwoFibreProduct_of_isStableUnderBaseChange`:
  **Stacks 0CII**, for every 2-fibre product.

## Implementation notes

The source's argument is
`AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_baseChange`, in
`StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismBaseChangeStable`, which takes the
one surjective étale presentation it chooses — that of `𝒳 ×_𝒴 V` for a smooth chart `V ⟶ 𝒴`,
supplied by **Stacks 0CIA** — through the substantial direction of **Stacks 06N3** as a
hypothesis. Here that direction is the proved theorem
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`, read at the terminal scheme,
which every big fppf site contains (`AlgebraicGeometry.BigFppfSite.contains_terminal`); so the
statement has exactly the source's hypotheses.

The base change is the second projection of an arbitrary 2-fibre product square. The source's
argument produces it for the canonical square, and
`AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_snd_of_isTwoFibreProduct` moves it to every
other one along the comparison equivalence.

## References

* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIG](https://stacks.math.columbia.edu/tag/0CIG)
* [Stacks Project, Tag 0CII](https://stacks.math.columbia.edu/tag/0CII)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CII.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
étale-smooth local on the source-and-target and stable under base change. If a Deligne–Mumford
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` has the property of Stacks 0CIG induced by
`P`, then so does its base change `𝒳 ×_𝒴 𝒵 ⟶ 𝒵` along any 1-morphism `g : 𝒵 ⟶ 𝒴`, the second
projection of any 2-fibre product square of `(f, g)`. -/
@[stacks 0CII]
theorem hasEtaleSmoothLocalProperty_snd_of_isTwoFibreProduct_of_isStableUnderBaseChange
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    [P.IsStableUnderBaseChange]
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (R : Bicategory.TwoCommSq f g) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : HasEtaleSmoothLocalProperty B S hS P f) :
    HasEtaleSmoothLocalProperty B S hS P R.snd :=
  hasEtaleSmoothLocalProperty_snd_of_isTwoFibreProduct B S hS P f g R hR
    (hasEtaleSmoothLocalProperty_baseChange B S hS P hP B.contains_terminal
      (existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f g hf)

end AlgebraicGeometry.Stack

end
