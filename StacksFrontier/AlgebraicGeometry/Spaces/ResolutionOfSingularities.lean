module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Regular
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralModification
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces

/-!
# Resolutions of singularities of an algebraic space

A *resolution of singularities* of a Noetherian integral algebraic space `Y` over a scheme `S`
is a modification `f : X ⟶ Y` whose source `X` is regular.

## Main definitions

* `AlgebraicGeometry.Space.IsResolutionOfSingularities` is the property of a morphism of
  algebraic spaces of being a resolution of singularities of its target.

## Main results

* `AlgebraicGeometry.Space.IsResolutionOfSingularities.isIntegralModification` and
  `AlgebraicGeometry.Space.IsResolutionOfSingularities.hasEtaleLocalProperty_isRegular` are
  the two defining conditions.

## Implementation notes

Noetherianity and integrality of the target are context rather than part of the predicate,
exactly as in the source; integrality is used, since a modification is only defined for an
integral target, while Noetherianity is carried for faithfulness and is not consumed.

A modification is `AlgebraicGeometry.Space.IsIntegralModification`, the predicate of
Stacks 0AD8. It asks for decency at source and target, as birationality of a morphism of
algebraic spaces does, so decency is carried here too.

Regularity of the source is the étale-local scheme property `AlgebraicGeometry.IsRegular`,
through `AlgebraicGeometry.Space.HasEtaleLocalProperty`: an algebraic space is regular when it
admits a surjective étale atlas by a regular scheme. Regularity is local for the étale
precoverage, so by Stacks 03E8 this is equivalent to regularity of every étale chart.

The predicate is an abbreviation, so a downstream existence statement can use the two defining
conditions directly.

## References

* [Stacks Project, Tag 0BHW](https://stacks.math.columbia.edu/tag/0BHW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A *resolution of singularities* of a Noetherian integral algebraic space `Y` over `S` is a
modification `f : X ⟶ Y` whose source `X` is regular. -/
@[stacks 0BHW]
abbrev IsResolutionOfSingularities {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (_hYnoeth : IsNoetherian B S hS hZ Y) (hYint : IsIntegralSpace B S hS Y)
    (_hdecentX : IsDecentSpace B S hS X)
    (_hdecentY : IsDecentSpace B S hS Y) (f : X ⟶ Y) : Prop :=
  IsIntegralModification B S hS hX hY hYint f ∧
    HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T)

variable {B S hS hZ} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {hY : IsAlgebraicSpace B S hS Y}
    {hYnoeth : IsNoetherian B S hS hZ Y} {hYint : IsIntegralSpace B S hS Y}
    {hdecentX : IsDecentSpace B S hS X}
    {hdecentY : IsDecentSpace B S hS Y} {f : X ⟶ Y}

/-- A resolution of singularities is a modification. -/
theorem IsResolutionOfSingularities.isIntegralModification
    (hf : IsResolutionOfSingularities B S hS hZ hX hY hYnoeth hYint hdecentX hdecentY f) :
    IsIntegralModification B S hS hX hY hYint f := hf.1

/-- The source of a resolution of singularities is a regular algebraic space, in the sense
that it admits a surjective étale atlas by a regular scheme. -/
theorem IsResolutionOfSingularities.hasEtaleLocalProperty_isRegular
    (hf : IsResolutionOfSingularities B S hS hZ hX hY hYnoeth hYint hdecentX hdecentY f) :
    HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T) := hf.2

end AlgebraicGeometry.Space

end
