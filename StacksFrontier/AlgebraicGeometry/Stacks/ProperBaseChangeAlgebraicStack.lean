module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Base change of properness for 1-morphisms of algebraic stacks (Stacks 0CL6)

A 1-morphism of algebraic stacks over `S` is *proper* (**Stacks 0CL5**) when it is separated, of
finite type and universally closed. This file proves **Stacks 0CL6**: a base change of a proper
1-morphism is proper.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_baseChange`: **Stacks 0CL6**.

## Implementation notes

Properness is a conjunction of three conditions, each of which is already known to be stable
under base change, and the source's proof is the list of those three facts and nothing else —
*"see Lemmas 050F, 06FU, and 0514"*. So the theorem is the conjunction of
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_baseChange_of_isTwoFibreProduct`
(**Stacks 050F**, the separated case),
`AlgebraicGeometry.Stack.AlgebraicStacks.isFiniteType_baseChange` (**Stacks 06FU**, the global
assertion) and
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_baseChange_of_isTwoFibreProduct`
(**Stacks 0514**), introduced in that order.

The separated case is stated over `CategoryTheory.Bicategory.TwoCommSq f g` and concludes about
the *second* projection, where the finite type and universal closedness statements are stated
over `CategoryTheory.Bicategory.TwoCommSq g f` and conclude about the *first*. The two readings
of one square differ by `CategoryTheory.Bicategory.TwoCommSq.swap`, which exchanges the legs on
the nose, so the separated conjunct is supplied at `P.swap` together with
`CategoryTheory.Bicategory.isTwoFibreProduct_swap`. That is the same bridge
`AlgebraicGeometry.Stack.AlgebraicStacks.isFinitePresentation_baseChange` (**Stacks 06Q4**) uses
for its quasi-separated conjunct, and the reason it costs nothing is that `swap` keeps the apex
and merely permutes the projections, so `P.swap.snd` *is* `P.fst`.

The statement is made at an **arbitrary** 2-fibre product square rather than at the canonical one
of Stacks 04T2, as all three ingredients are: the canonical form is the one-term instantiation
`P := AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks B S hS g f`.

The `@[stacks 0CL6]` attribute sits on the single theorem below, which is that tag's whole
covering set — the source asserts exactly one proposition. Stacks 0CL5 is the *definition* of
properness and keeps its own key on
`AlgebraicGeometry.Stack.AlgebraicStacks.IsProper`.

## References

* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 0514](https://stacks.math.columbia.edu/tag/0514)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
* [Stacks Project, Tag 0CL5](https://stacks.math.columbia.edu/tag/0CL5)
* [Stacks Project, Tag 0CL6](https://stacks.math.columbia.edu/tag/0CL6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CL6.** A base change of a proper 1-morphism of algebraic stacks over `S` is proper:
if `f : 𝒳 ⟶ 𝒴` is proper and `P` is any 2-fibre product square of the cospan `(g, f)` for some
`g : 𝒴' ⟶ 𝒴`, then the projection `P.fst` — the base change of `f` along `g` — is proper.

Properness is separatedness, finite type and universal closedness (Stacks 0CL5), and the three
conjuncts base change by **Stacks 050F**, **Stacks 06FU** and **Stacks 0514** respectively, which
is the source's own proof. -/
@[stacks 0CL6]
theorem isProper_baseChange {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsProper B S hS f) :
    IsProper B S hS P.fst :=
  ⟨isSeparated_baseChange_of_isTwoFibreProduct B S hS f g P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hf.1,
    isFiniteType_baseChange B S hS f g P hP hf.2.1,
    universallyClosed_baseChange_of_isTwoFibreProduct B S hS P hP hf.2.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
