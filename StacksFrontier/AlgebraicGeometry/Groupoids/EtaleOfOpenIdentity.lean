module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.SheafOfDifferentials
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# A groupoid scheme with open identity section has étale source and target

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with identity section `e : U ⟶ R`, and
suppose `s` is flat and locally of finite presentation.  If `e` is an open immersion then `s`
and `t` are étale.

This is the last step of the proof of [Stacks Project, Tag 04S6]: after the groupoid has been
refined ([Stacks Project, Tag 0489]), localized to a quasi-split situation
([Stacks Project, Tag 04S0]) and divided by a finite locally free subgroupoid
([Stacks Project, Tag 04S4]), what one knows about the resulting groupoid is that its identity
section is an open immersion, and what is needed to form the quotient as an algebraic space —
by [Stacks Project, Tag 02WW] or, for a relation of algebraic spaces,
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isAlgebraicSpace` — is that `s` and
`t` be étale.

The argument is the one of [Stacks Project, Tag 04R9]: the relative differentials `Ω_{R/U}` of
`s` are a quotient of `t^* 𝒞_{U/R}`, and `𝒞_{U/R}` vanishes when `e` is an open immersion, so
`Ω_{R/U} = 0` and `s` is unramified.  Formally the vanishing is routed through the cartesian
square
```
R --Δ_s--→ R ×_{s, U, s} R
|                |
t                γ
↓                ↓
U ---e---------→ R
```
of `Stacks.Groupoids.GroupoidScheme.isPullback_diagonal_divide`: the diagonal of `s` is a base
change of `e`, hence an open immersion, which is Mathlib's criterion for `s` to be formally
unramified.  A flat, locally finitely presented, formally unramified morphism is étale.

## Main definitions

This file introduces no definitions.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isOpenImmersion_diagonal_source_of_isOpenImmersion_identity`:
  the diagonal of the source morphism is an open immersion.
* `Stacks.Groupoids.GroupoidScheme.etale_source_of_isOpenImmersion_identity` and
  `Stacks.Groupoids.GroupoidScheme.etale_target_of_isOpenImmersion_identity`: the source and
  target morphisms are étale.

## Implementation notes

Flatness and local finite presentation are assumed of `s` only.  The target morphism inherits
both from the source morphism through the inverse, which is an isomorphism of the underlying
schemes by `AlgebraicGeometry.groupoidInverse_left_isIso`; so assuming them of `t` as well
would be redundant, and the étaleness of `t` is obtained by composing the isomorphism `i` with
the étale `s`, using `t = i ≫ s`.

No monomorphism or jointly-monic hypothesis is needed.  The cartesian square above is proved
from the groupoid axioms alone in
`StacksFrontier/AlgebraicGeometry/Groupoids/SheafOfDifferentials.lean`, where it is the square
whose conormal comparison is the canonical surjection of [Stacks Project, Tag 04R9].

## References

* [Stacks Project, Tag 04R9](https://stacks.math.columbia.edu/tag/04R9)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The diagonal of the source morphism of a groupoid scheme whose identity section is an open
immersion is an open immersion.

It is a base change of the identity section along division of arrows with a common source, by
`Stacks.Groupoids.GroupoidScheme.isPullback_diagonal_divide`. -/
theorem isOpenImmersion_diagonal_source_of_isOpenImmersion_identity
    [IsOpenImmersion G.identity.left] :
    IsOpenImmersion (pullback.diagonal G.source.left) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsOpenImmersion) G.isPullback_diagonal_divide.flip inferInstance

/-- The source morphism of a groupoid scheme whose identity section is an open immersion and
whose source morphism is flat and locally of finite presentation is étale.

This is the final step of the proof of [Stacks Project, Tag 04S6]; see the module docstring. -/
theorem etale_source_of_isOpenImmersion_identity [IsOpenImmersion G.identity.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left] :
    Etale G.source.left :=
  have := G.isOpenImmersion_diagonal_source_of_isOpenImmersion_identity
  Etale.of_formallyUnramified_of_flat _

/-- The target morphism of a groupoid scheme whose identity section is an open immersion and
whose source morphism is flat and locally of finite presentation is étale.

The target morphism is the composite of the inverse, an isomorphism of the underlying schemes,
with the source morphism. -/
theorem etale_target_of_isOpenImmersion_identity [IsOpenImmersion G.identity.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left] :
    Etale G.target.left := by
  have := G.etale_source_of_isOpenImmersion_identity
  have : IsIso G.inverse.left := AlgebraicGeometry.groupoidInverse_left_isIso G
  have h : G.target.left = G.inverse.left ≫ G.source.left :=
    congrArg Over.Hom.left G.source_inverse.symm
  rw [h]
  exact Etale.etale_comp _ _

end Stacks.Groupoids.GroupoidScheme

end
