module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change preserves the hypotheses for a canonical weighting

A morphism of schemes that is flat, locally quasi-finite and locally of finite presentation
keeps all three properties after any base change, which is what makes the canonical
weighting of such a morphism available over an arbitrary base.

## Main results

Each of the four constituent properties is stable under base change, by the existing
instances for `AlgebraicGeometry.Flat`, `AlgebraicGeometry.LocallyOfFiniteType`,
`AlgebraicGeometry.LocallyQuasiFinite` and
`AlgebraicGeometry.LocallyOfFinitePresentation`.

## Implementation notes

Local quasi-finiteness is the conjunction of local finite type with the fibre-isolation
condition `AlgebraicGeometry.LocallyQuasiFinite`, so two of the four instances together
cover that conclusion; flatness and local finite presentation are each covered by one.
Every one of them applies to an arbitrary cartesian square, not only to a chosen fibre
product.

## References

* [Stacks Project, Tag 0GKI](https://stacks.math.columbia.edu/tag/0GKI)
-/

@[expose] public section

add_to_stacks 0GKI "base_change_preserves_hypotheses" AlgebraicGeometry.Flat.isStableUnderBaseChange

add_to_stacks 0GKI "base_change_preserves_hypotheses"
  AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange

add_to_stacks 0GKI "base_change_preserves_hypotheses"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite

add_to_stacks 0GKI "base_change_preserves_hypotheses"
  AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange

end
