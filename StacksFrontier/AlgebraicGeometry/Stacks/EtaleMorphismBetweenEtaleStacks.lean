module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordFibreProductPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleMorphismOverBase

/-!
# A morphism between two stacks étale over a base is étale (Stacks 0CIR)

Let `𝒳` and `𝒴` be algebraic stacks étale over an algebraic stack `𝒵`. **Stacks 0CIR** says that
every 1-morphism `𝒳 ⟶ 𝒴` over `𝒵` is étale in the sense of **Stacks 0CIL**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isEtale_of_isEtale_over_base`: **Stacks 0CIR**, under
  exactly the source's hypotheses.

## Implementation notes

`StacksFrontier.AlgebraicGeometry.Stacks.EtaleMorphismOverBase` carries out the source's argument
with the étale charts of **Stacks 0CIA**, part (2), as its one input `hchart`. Here `hchart` is
`Stack.AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_of_isDM_algebraicSpace`,
the library's Stacks 0CIA, part (2), which rests on the structure theorem **Stacks 06N3**.

## References

* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIR](https://stacks.math.columbia.edu/tag/0CIR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CIR.** Let `𝒳` and `𝒴` be algebraic stacks étale over an algebraic stack `𝒵`, with
structure 1-morphisms `p : 𝒳 ⟶ 𝒵` and `q : 𝒴 ⟶ 𝒵`. Any 1-morphism `f : 𝒳 ⟶ 𝒴` over `𝒵`, i.e.
with a 2-isomorphism `η : p ≅ f ≫ q`, is étale in the sense of Stacks 0CIL: Deligne–Mumford, and
étale on every diagram of its universal étale-smooth test.

This is
`AlgebraicGeometry.Stack.isEtale_of_isEtale_over_base_of_isDeligneMumfordStack_twoFibreProduct`
with its étale charts supplied by **Stacks 0CIA**, part (2),
`Stack.AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_of_isDM_algebraicSpace`. -/
@[stacks 0CIR]
theorem isEtale_of_isEtale_over_base {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒵) (q : 𝒴 ⟶ 𝒵) (η : p ≅ f ≫ q)
    (hp : Stack.IsEtale B S hS p) (hq : Stack.IsEtale B S hS q) : Stack.IsEtale B S hS f :=
  isEtale_of_isEtale_over_base_of_isDeligneMumfordStack_twoFibreProduct B S hS
    (fun f hf V hV b =>
      isDeligneMumfordStack_twoFibreProduct_of_isDM_algebraicSpace B S hS f hf V hV b)
    f p q η hp hq

end AlgebraicGeometry.Stack.AlgebraicStacks

end
