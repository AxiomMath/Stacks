module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Permanence of étaleness for 1-morphisms of algebraic stacks (Stacks 0CIM, 0CIN)

**Stacks 0CIM** asserts that a composite of étale 1-morphisms of algebraic stacks over `S` is
étale, and **Stacks 0CIN** that an étale 1-morphism stays étale after an arbitrary base change.
Étaleness of a 1-morphism of algebraic stacks, `AlgebraicGeometry.Stack.IsEtale` of
**Stacks 0CIL**, is a conjunction of two conditions: the Deligne–Mumford condition of
**Stacks 04YW** and the universal étale-smooth diagram test of **Stacks 0CIF** at étaleness of
morphisms of algebraic spaces. This file proves the Deligne–Mumford conjunct of each of the two
conclusions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_comp_of_isEtale`: the Deligne–Mumford conjunct
  of **Stacks 0CIM** — a composite of étale 1-morphisms of algebraic stacks is Deligne–Mumford.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_baseChange_of_isEtale`: the Deligne–Mumford
  conjunct of **Stacks 0CIN** — the projection to `𝒴'` of any 2-fibre product of a cospan
  `(g : 𝒴' ⟶ 𝒴, f : 𝒳 ⟶ 𝒴)` with `f` étale is Deligne–Mumford.

Each conclusion is the Deligne–Mumford condition alone, and each attribute is keyed with that
conjunct rather than left bare.

## Implementation notes

Both proofs are the corresponding clause of **Stacks 050M**'s companions applied to the
Deligne–Mumford conjunct of the hypothesis: composition is **Stacks 050K**,
`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_comp`, and base change is **Stacks 050F**,
`AlgebraicGeometry.Stack.isDM_baseChange_of_isTwoFibreProduct`, at the exchanged square — a
2-fibre product of `(g, f)` is one of `(f, g)` with its legs permuted, by **Stacks 003Q**.

The second conjunct — the universal étale-smooth diagram test — is proved in neither case, and
the obstruction is the same for both. It is the content of **Stacks 0CIH**, respectively
**Stacks 0CII**, for the property `AlgebraicGeometry.Space.IsEtale`, and the argument for each
interpolates an algebraic space `V₀` carrying a *surjective étale* 1-morphism onto the base
change of a Deligne–Mumford 1-morphism by an algebraic space, which is **Stacks 0CIA** and is
not available in the library. Concretely:

* For composition, a diagram of algebraic spaces over `f ≫ g` with smooth right-hand vertical
  1-morphism `b : V ⟶ 𝒵` factors the test through `𝒴 ×_𝒵 V`. The test for `f` can be fed by any
  algebraic space smooth over `𝒴 ×_𝒵 V` — a smooth chart suffices — but the test for `g` asks
  the comparison `V₀ ⟶ 𝒴 ×_𝒵 V` to be *étale*, and only Stacks 0CIA produces such a `V₀`.
  Étaleness of the resulting top horizontal morphism of `V` then comes from
  `AlgebraicGeometry.Space.isEtale_comp` and from étale locality on the source, both of which
  are part of `AlgebraicGeometry.Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget`
  (**Stacks 0CG3**).
* For base change, the universal test for `f` cannot be applied to a diagram over the projection
  `Q.fst` directly: composing the diagram's right-hand vertical 1-morphism `b : V ⟶ 𝒴'` with `g`
  gives a 1-morphism `V ⟶ 𝒴` which need not be smooth, as `g` is arbitrary. The test must
  therefore be reached through the *existential* test of Stacks 0CIF, whose implication from the
  universal one is the half of that tag recorded as unavailable in
  `StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEveryConverse`, again for want of
  Stacks 0CIA.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 0CG3](https://stacks.math.columbia.edu/tag/0CG3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIH](https://stacks.math.columbia.edu/tag/0CIH)
* [Stacks Project, Tag 0CII](https://stacks.math.columbia.edu/tag/0CII)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIM](https://stacks.math.columbia.edu/tag/0CIM)
* [Stacks Project, Tag 0CIN](https://stacks.math.columbia.edu/tag/0CIN)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The Deligne–Mumford conjunct of Stacks 0CIM.** A composite of two étale 1-morphisms of
algebraic stacks over `S` is Deligne–Mumford.

Étaleness of Stacks 0CIL contains the Deligne–Mumford condition of Stacks 04YW, and that
condition is stable under composition by **Stacks 050K**. -/
@[stacks 0CIM "the Deligne–Mumford conjunct of the conclusion"]
theorem isDM_comp_of_isEtale {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : Stack.IsEtale B S hS f) (hg : Stack.IsEtale B S hS g) :
    Stack.IsDM B S hS (f ≫ g) :=
  isDM_comp B S hS f g hf.1 hg.1

/-- **The Deligne–Mumford conjunct of Stacks 0CIN.** The projection to `𝒴'` of any 2-fibre
product of a cospan `(g : 𝒴' ⟶ 𝒴, f : 𝒳 ⟶ 𝒴)` of 1-morphisms of algebraic stacks over `S` is
Deligne–Mumford as soon as `f` is étale.

Étaleness of Stacks 0CIL contains the Deligne–Mumford condition of Stacks 04YW, and that
condition is inherited by base changes by **Stacks 050F**; a 2-fibre product of `(g, f)` is one
of `(f, g)` with its two legs exchanged (**Stacks 003Q**), which turns the projection `Q.fst`
into the second projection that Stacks 050F speaks about. -/
@[stacks 0CIN "the Deligne–Mumford conjunct of the conclusion"]
theorem isDM_baseChange_of_isEtale {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hf : Stack.IsEtale B S hS f) :
    Stack.IsDM B S hS Q.fst :=
  Stack.isDM_baseChange_of_isTwoFibreProduct B S hS f g Q.swap
    (Bicategory.isTwoFibreProduct_swap hQ) hf.1

end AlgebraicGeometry.Stack.AlgebraicStacks

end
