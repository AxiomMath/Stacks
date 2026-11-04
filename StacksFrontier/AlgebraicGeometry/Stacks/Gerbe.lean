module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Basic

/-!
# Gerbes of algebraic stacks (Stacks 06QC)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` makes `𝒳` a *gerbe over* `𝒴` when it does
so as a 1-morphism of stacks in groupoids over the big fppf site of `S`, in the sense of
**Stacks 06P2**. An algebraic stack `𝒳` *is a gerbe* when there is a 1-morphism `𝒳 ⟶ X` with `X`
representable by an algebraic space which makes `𝒳` a gerbe over `X`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsGerbeOver`: the relative notion, **Stacks 06QC**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsGerbe`: the absolute notion, **Stacks 06QC**.

## Implementation notes

The two definitions of Stacks 06QC together form the covering set of the tag, so both carry it.

The relative notion needs nothing new: `CategoryTheory.IsGerbeOver`, which is Stacks 06P2, is
stated for a 1-morphism of categories fibred in groupoids over an arbitrary site, and the
underlying functor of a 1-morphism of algebraic stacks over the big fppf site of `S` is one.
Every algebraic stack is a stack in groupoids (Stacks 026O), so the hypothesis under which
Stacks 06P2 is read in the source is met; `CategoryTheory.IsGerbeOver` records the fibred-in-
groupoids half of it as its own first two fields rather than as a side condition, and the
implementation notes of `StacksFrontier.CategoryTheory.Sites.Gerbe.Basic` explain why that is the
hypothesis available.

An algebraic-space target is expressed as an algebraic *stack* which is representable by an
algebraic space (**Stacks 04SV**) rather than as an algebraic space on the nose, so that `f` is
an ordinary 1-morphism of algebraic stacks and no comparison of 2-categories is needed. Both the
target and the 1-morphism are kept in the existential, since the base-change and descent
arguments for gerbes consume them.

Both are abbreviations, so a consumer gets the fields of `CategoryTheory.IsGerbeOver` and the
witnesses of the existential directly.

## References

* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 06P2](https://stacks.math.columbia.edu/tag/06P2)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06QC.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` makes `𝒳` a *gerbe
over* `𝒴` when its underlying functor makes `𝒳` a gerbe over `𝒴` in the sense of Stacks 06P2,
for the fppf topology on the big fppf site of `S`. -/
@[stacks 06QC "gerbe over an algebraic stack"]
abbrev IsGerbeOver {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  _root_.CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS) 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom)

/-- **Stacks 06QC.** An algebraic stack `𝒳` over `S` *is a gerbe* when there is an algebraic
stack `𝒴` representable by an algebraic space over `S` and a 1-morphism `𝒳 ⟶ 𝒴` making `𝒳` a
gerbe over `𝒴`. -/
@[stacks 06QC "gerbe"]
abbrev IsGerbe (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS,
    IsRepresentableByAlgebraicSpace B S hS 𝒴.val ∧ ∃ f : 𝒳 ⟶ 𝒴, IsGerbeOver B S hS f

end AlgebraicGeometry.Stack.AlgebraicStacks

end
