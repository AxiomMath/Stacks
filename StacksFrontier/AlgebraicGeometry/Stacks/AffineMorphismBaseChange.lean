module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability

/-!
# Base change of affine 1-morphisms of algebraic stacks (Stacks 0CHR)

Stacks 0CHQ calls a 1-morphism of algebraic stacks *affine* when it is representable by
algebraic spaces and affine in the sense of Stacks 04XB. This file states **Stacks 0CHR** with
both halves of that notion written out separately, in hypothesis and conclusion: if `g : 𝒵 ⟶ 𝒴`
is representable by algebraic spaces and affine in the sense of Stacks 04XB, and `P` is a
2-fibre product of the cospan `(g, f)` for an arbitrary 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks, then the base change `P.snd : 𝒵 ×_𝒴 𝒳 ⟶ 𝒳` is again representable by algebraic spaces
and affine in the sense of Stacks 04XB.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_and_isAffineHom_snd`:
  **Stacks 0CHR**.

## Implementation notes

The representability half is the base change of representability by algebraic spaces (Stacks
0302, at a 2-fibre product square of algebraic stacks), the affineness half is Stacks 045C at
affineness. Neither uses any hypothesis on the property: the algebraic space tested at a
scheme-valued point of `𝒵 ×_𝒴 𝒳` is one of those tested at the transported point of `𝒴`. The
square `P` is arbitrary, so the statement applies to any square already exhibited as a 2-fibre
product, and in particular to the canonical one of Stacks 04T2.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
* [Stacks Project, Tag 0CHR](https://stacks.math.columbia.edu/tag/0CHR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒵 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}

/-- **Stacks 0CHR.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let
`g : 𝒵 ⟶ 𝒴` be an affine 1-morphism of algebraic stacks, that is (Stacks 0CHQ) one which is
representable by algebraic spaces and affine in the sense of Stacks 04XB. If `P` is a 2-fibre
product of the cospan `(g, f)`, then the base change `P.snd : 𝒵 ×_𝒴 𝒳 ⟶ 𝒳` is an affine
1-morphism of algebraic stacks: it is representable by algebraic spaces, and it is affine in the
sense of Stacks 04XB. -/
@[stacks 0CHR]
theorem isRepresentableByAlgebraicSpaces_and_isAffineHom_snd
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg_rep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (hg_aff : Stack.IsAffineHom B S hS g.hom) :
    IsRepresentableByAlgebraicSpaces B S hS P.snd.hom.hom ∧
      Stack.IsAffineHom B S hS P.snd.hom :=
  ⟨isRepresentableByAlgebraicSpaces_snd_of_isTwoFibreProduct B S hS P hP hg_rep,
    Stack.isAffineHom_snd_of_isTwoFibreProduct B S hS P hP hg_aff⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
