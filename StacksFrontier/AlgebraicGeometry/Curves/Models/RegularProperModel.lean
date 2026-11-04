module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularModel
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic

/-!
# A regular proper model of a smooth projective curve

The geometry of a regular model is studied in one standing context, refining the context of
`Stacks.Models.RegularModelSituation`: the discrete valuation ring comes with a chosen
uniformizer `π`, the curve `C` is projective over `K` and satisfies `H⁰(C, 𝒪_C) = K`, and the
model `X ⟶ Spec(R)` is proper. The irreducible components `C₁, …, Cₙ` of the special fibre
`X_k` and their multiplicities are then the ones produced by Tag 0C5Z.

## Main definitions

* `Stacks.Models.RegularProperModelSituation` — the standing data of the situation.

## Main results

There are no propositional results beyond the bundled situation: this file fixes the context in
which the intersection theory on a regular model is developed.

## Implementation notes

Projectivity of `C ⟶ Spec(K)` is `Stacks.HProjective.IsHProjective`: the existence of some `n`
and a closed immersion `C ⟶ ℙⁿ_{Spec K}` over the base, with the relative projective space
`AlgebraicGeometry.projectiveSpaceOver` (Tag 01NF); no separate projectivity class is assumed.
The condition `H⁰(C, 𝒪_C) = K` is the assertion that the canonical ring map
`K ⟶ Γ(C, 𝒪_C)`, namely `(Scheme.ΓSpecIso (.of K)).inv ≫ C_to_K.appTop`, is an isomorphism.

The components of the special fibre are *not* enumerated here: they are indexed canonically by
`irreducibleComponents S.specialFiber`, so no ordering of `C₁, …, Cₙ` is fixed, and their
multiplicities `mᵢ` are the values of the coefficient family of Tag 0C5Z applied to the
underlying regular-model situation.

## References

* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Models

universe u

/-- **Stacks Project, Tag 0C61.** The standing situation of the geometry of a regular model: a
discrete valuation ring with a chosen uniformizer, a smooth projective curve over its fraction
field whose only global functions are the constants, and a regular proper model of that
curve. -/
@[stacks 0C61]
public structure RegularProperModelSituation extends RegularModelSituation.{u} where
  /-- A chosen uniformizer of the discrete valuation ring. -/
  π : R
  /-- In a discrete valuation ring, an irreducible element is a uniformizer. -/
  uniformizer : Irreducible π
  /-- The smooth curve is projective over its ground field. -/
  curveProjective : Stacks.HProjective.IsHProjective C_to_K
  /-- The regular model is proper over the discrete valuation ring. -/
  [modelProper : IsProper X_to_R]
  /-- The canonical homomorphism from the fraction field to the global functions
  of the curve is an isomorphism. -/
  [isIso_globalSections : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ C_to_K.appTop)]

attribute [instance] RegularProperModelSituation.modelProper
  RegularProperModelSituation.isIso_globalSections

end Stacks.Models

end
