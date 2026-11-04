module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionOfSingularities

/-!
# A resolution of singularities of an algebraic space is a regular alteration

Let `S` be a scheme and let `Y` be a Noetherian integral algebraic space over `S`. A resolution
of singularities `f : X ⟶ Y` of `Y` in the sense of Stacks 0BHW is an alteration of `Y` in the
sense of Stacks 0ADA, and its source is regular.

This is the implication (2) `⇒` (1) of Stacks 0BHY.

## Main results

* `AlgebraicGeometry.Space.IsResolutionOfSingularities.isAlteration`: a resolution of
  singularities is an alteration.
* `AlgebraicGeometry.Space.exists_regular_alteration_of_exists_resolutionOfSingularities`: the
  implication (2) `⇒` (1) of Stacks 0BHY.

## Implementation notes

A modification is proper with integral source and it is birational, hence dominant by
`AlgebraicGeometry.Space.isDominant_of_isBirational`; by Stacks 0AD9 it is an isomorphism, so in
particular finite, over a nonempty open subspace of its target.

The implication holds without the two-dimensionality that Stacks 0BHY assumes throughout, and it
is stated without it. Decency of `Y`, which Stacks 0BHW asks for in order to speak of
birationality, is a consequence of integrality (Stacks 0AD4), so condition (2) is stated with the
decency witness `AlgebraicGeometry.Space.IsIntegralSpace.isDecentSpace`; decency of the source is
quantified together with the resolution, a modification having integral, hence decent, source.

## References

* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
* [Stacks Project, Tag 0BHW](https://stacks.math.columbia.edu/tag/0BHW)
* [Stacks Project, Tag 0ADA](https://stacks.math.columbia.edu/tag/0ADA)
* [Stacks Project, Tag 0AD9](https://stacks.math.columbia.edu/tag/0AD9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {hY : IsAlgebraicSpace B S hS Y}
    {hYnoeth : IsNoetherian B S hS hZ Y} {hYint : IsIntegralSpace B S hS Y}
    {hdecentX : IsDecentSpace B S hS X} {hdecentY : IsDecentSpace B S hS Y} {f : X ⟶ Y}

/-- A resolution of singularities of a Noetherian integral algebraic space `Y` over `S` is an
alteration of `Y`: a modification is proper with integral source, dominant because birational,
and an isomorphism, in particular finite, over a nonempty open subspace of `Y` by Stacks 0AD9. -/
theorem IsResolutionOfSingularities.isAlteration
    (hf : IsResolutionOfSingularities B S hS hZ hX hY hYnoeth hYint hdecentX hdecentY f) :
    IsAlteration B S hS f := by
  have hmod : IsIntegralModification B S hS hX hY hYint f := hf.1
  have hXint : IsIntegralSpace B S hS X := hmod.isIntegralSpace B S hS
  have hdom : IsDominant B S hS f :=
    isDominant_of_isBirational B S hS hX hY hXint.isDecentSpace hYint.isDecentSpace
      (hXint.finite_irreducibleComponents B S hS X)
      (hYint.finite_irreducibleComponents B S hS Y) (hmod.isBirational B S hS)
  obtain ⟨U, hU, hUne, hiso⟩ := hmod.exists_isIso_fromPreimage B S hS
  exact ⟨hY, hYint, hX, hXint, hmod.isProper B S hS, hdom, U, hU, hUne,
    isFinite_of_isIso B S hS (U.fromPreimage f)⟩

/-- **Stacks 0BHY, (2) `⇒` (1).** If a Noetherian integral algebraic space `Y` over `S` has a
resolution of singularities, then there is an alteration `X ⟶ Y` with `X` regular.

The two-dimensionality of `Y` that the source assumes is not used. -/
theorem exists_regular_alteration_of_exists_resolutionOfSingularities
    (hY : IsAlgebraicSpace B S hS Y) (hYnoeth : IsNoetherian B S hS hZ Y)
    (hYint : IsIntegralSpace B S hS Y)
    (h : ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
      (hdecentX : IsDecentSpace B S hS X) (f : X ⟶ Y),
      IsResolutionOfSingularities B S hS hZ hX hY hYnoeth hYint hdecentX
        (hYint.isDecentSpace B S hS Y) f) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : X ⟶ Y), IsAlteration B S hS f ∧
      HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T) := by
  obtain ⟨X, hX, hdecentX, f, hf⟩ := h
  exact ⟨X, f, hf.isAlteration, hf.2⟩

end AlgebraicGeometry.Space

end
