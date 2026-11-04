module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionUniqueness
public import StacksFrontier.CategoryTheory.DottedArrows.Faithful

/-!
# The uniqueness criterion for a representable morphism of algebraic stacks

The uniqueness part of the valuative criterion for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
(**Stacks 0CLG**, `AlgebraicGeometry.Stack.ValuativeCriterion.Uniqueness`) is a *conjunction*:
for every valuative diagram, the category of dotted arrows is a setoid (Stacks 02XZ) *and* any
two dotted arrows are isomorphic. This file records that the first conjunct is automatic as soon
as `f` is representable by algebraic spaces, so that against such an `f` the criterion is the
second conjunct alone.

## Main results

* `AlgebraicGeometry.Stack.valuativeCriterionUniqueness_iff_forall_nonempty_iso`: for `f`
  representable by algebraic spaces, the uniqueness part of the valuative criterion holds exactly
  when any two dotted arrows of any valuative diagram for `f` are isomorphic.

## Implementation notes

Two inputs, both already in the library. A 1-morphism representable by algebraic spaces has
faithful underlying functor by **Stacks 04Y5**
(`AlgebraicGeometry.Stack.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces`), and the
category of dotted arrows along a faithful 1-morphism is a setoid by
`CategoryTheory.isSetoidCategory_dottedArrow_of_faithful`.

This is worth a name rather than a `have` at each use because it removes a conjunct from every
later statement about Stacks 0CLG for a representable morphism — which is every case the Stacks
project treats — and because the setoid conjunct is the half whose proof has nothing to do with
valuation rings.

## References

* [Stacks Project, Tag 0CLG](https://stacks.math.columbia.edu/tag/0CLG)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 02XZ](https://stacks.math.columbia.edu/tag/02XZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The uniqueness part of the valuative criterion for a representable morphism is its second
conjunct.** For a 1-morphism `f` of algebraic stacks representable by algebraic spaces,
`AlgebraicGeometry.Stack.ValuativeCriterion.Uniqueness` holds exactly when any two dotted arrows
of any valuative diagram for `f` are isomorphic.

The setoid conjunct of Stacks 0CLG is automatic: `f` is faithful on underlying functors by
Stacks 04Y5, and a category of dotted arrows along a faithful 1-morphism is thin. -/
theorem valuativeCriterionUniqueness_iff_forall_nonempty_iso (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    ValuativeCriterion.Uniqueness B S hS f ↔
      ∀ (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
        (a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ), Nonempty (a ≅ b) := by
  have hfaith : (CatFiberedInGroupoids.homFunctor f.hom).Faithful :=
    faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f.hom hf
  exact ⟨fun h D => (h D).2,
    fun h D => ⟨isSetoidCategory_dottedArrow_of_faithful, h D⟩⟩

end AlgebraicGeometry.Stack

end
