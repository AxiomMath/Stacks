module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedDiagonalCriterionUnconditional

/-!
# Unramified 1-morphisms of algebraic stacks are those of locally finite type with étale diagonal

**Stacks 0CJ0**: a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks is unramified (**Stacks 0CIT**) if
and only if it is locally of finite type (**Stacks 06FS**) and its relative diagonal
`Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is étale (**Stacks 0CIL**).

## Main results

* `isUnramified_iff_isLocallyOfFiniteType_isEtale_relativeDiagonal`: **Stacks 0CJ0**, with no
  hypothesis beyond the 1-morphism `f`.

## Implementation notes

`StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedDiagonalCriterionUnconditional` proves the
equivalence with the substantial direction of **Stacks 06N3** as an explicit argument, through
which **Stacks 0CIA** reaches the forward implication. That direction is the theorem
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`, applied here at the terminal
scheme of the site.

## References

* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CJ0](https://stacks.math.columbia.edu/tag/0CJ0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CJ0.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is unramified if and
only if it is locally of finite type and its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is étale.

The implication (2) ⇒ (1) is
`isUnramified_of_isLocallyOfFiniteType_of_isEtale_relativeDiagonal`;
(1) ⇒ (2) is
`isLocallyOfFiniteType_and_isEtale_relativeDiagonal_of_isUnramified_of_etalePresentation`
at the structure theorem of Stacks 06N3,
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`, through which Stacks 0CIA is
available. -/
@[stacks 0CJ0]
theorem isUnramified_iff_isLocallyOfFiniteType_isEtale_relativeDiagonal
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    Stack.IsUnramified B S hS f ↔
      (IsLocallyOfFiniteType B S hS f ∧ Stack.IsEtale B S hS (relativeDiagonal B S hS f)) :=
  isUnramified_iff_isLocallyOfFiniteType_isEtale_relativeDiagonal_of_etalePresentation B S hS
    (Stack.existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f

end AlgebraicGeometry.Stack.AlgebraicStacks

end
