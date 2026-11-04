module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceSources
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal

/-!
# A 1-morphism out of an algebraic space into an algebraic stack is representable

Let `S` be a scheme contained in a big fppf site `B`. The conventions paragraph of Properties of
Stacks, Section 04XB uses a basic consequence of Stacks 045G without further mention: *every
morphism from an algebraic space to an algebraic stack is representable by algebraic spaces.* It
is the step that makes the covering hypotheses of Properties of Stacks, Lemma 04XD say anything
at all — those hypotheses are implications whose antecedent is an algebraic space representing a
base change of the covering 1-morphism — and the reason the algebraicity of the source and target
appear as hypotheses of that lemma, which otherwise never uses them.

This module records the consequence. It is the composite of three formalized parts of Stacks 045G:
representability of the diagonal is the condition that every isomorphism sheaf of a fibre is an
algebraic space (parts (1) and (2)), that is the condition that every scheme-valued point is
representable by algebraic spaces (parts (2) and (3)), and that implies the same for a
1-morphism out of a category fibred in groupoids representable by an algebraic space
(the implication (3) ⇒ (7)).

## Main results

* `isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace_source`:
  the statement for a target with representable diagonal.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`: the same for an
  algebraic stack, whose third clause is that condition.

## Implementation notes

Neither declaration carries a `@[stacks]` attribute. Both are instances of the chain of
equivalences of Stacks 045G, whose eight conditions are already covered by seven tagged sites —
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf` and its
companions — and
  `AlgebraicGeometry.Stack.isRepresentableFromAlgebraicSpaces_of_isRepresentableFromSchemes`
is the (3) ⇒ (7) half of one of them. The statements below add no condition of 045G; they are the
form in which the source quotes it, with the source of the 1-morphism given as a category fibred
in groupoids representable by an algebraic space rather than as condition (7) applied by hand.

Only representability of the diagonal of the target is used, not the full algebraicity: the first
statement is therefore available for a target which is merely a category fibred in groupoids with
representable diagonal, and the second is its instance at the third clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack`.

The universes are pinned to `CatFiberedInGroupoids.{u, u, u + 1, u + 1}` for both categories.
Condition (7) quantifies its source over `CatFiberedInGroupoids.{u, max u v₁, u + 1,
max (u + 1) w₁}`, which is that assignment exactly at `v₁ = u` and `w₁ = u + 1`; the target is
taken at the same universes because that is where its consumers — the relative-property results
of Properties of Stacks, Section 04XB — live.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒴 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **A 1-morphism into a category fibred in groupoids with representable diagonal, out of one
representable by an algebraic space, is representable by algebraic spaces.** This is the basic
consequence of Stacks 045G that the conventions paragraph of Properties of Stacks,
Section 04XB uses without further mention. -/
theorem isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace_source
    (h𝒴 : HasRepresentableDiagonal B S hS 𝒴)
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲) (g : 𝒲 ⟶ 𝒴) :
    IsRepresentableByAlgebraicSpaces B S hS g.hom :=
  isRepresentableFromAlgebraicSpaces_of_isRepresentableFromSchemes.{u, u, u + 1, u, u + 1}
    B S hS 𝒴
    ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒴).1
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).1 h𝒴))
    𝒲 h𝒲 g.hom

/-- **Every 1-morphism from an algebraic space to an algebraic stack is representable by
algebraic spaces.** The third clause of algebraicity of the target is representability of its
diagonal, which is all that
`Stack.isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace_source`
asks for. -/
theorem isRepresentableByAlgebraicSpaces_of_isAlgebraicStack
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲) (g : 𝒲 ⟶ 𝒴) :
    IsRepresentableByAlgebraicSpaces B S hS g.hom := by
  obtain ⟨_, -, h𝒴diag, -⟩ := h𝒴
  exact isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace_source
    B S hS h𝒴diag h𝒲 g

end AlgebraicGeometry.Stack

end
