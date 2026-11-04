module

public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionFromNormalizedBlowUps
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionSurfaceAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceRegularAlterationCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.SurfaceResolutionFromCriterion

/-!
# Resolution of two-dimensional algebraic spaces (Stacks 0BHY)

Let `S` be a scheme and `Y` a two-dimensional integral Noetherian algebraic space over `S`. The
following are equivalent:

1. there exists an alteration `X ⟶ Y` with `X` regular;
2. there exists a resolution of singularities of `Y`;
3. `Y` has a resolution of singularities by normalized blowups;
4. the normalization `Y^ν ⟶ Y` is finite, `Y^ν` has finitely many singular points, and the
   completion of the henselian local ring of `Y^ν` at each of them is normal.

## Main results

* `AlgebraicGeometry.Space.tfae_resolution_of_dimension_eq_two`: **Stacks 0BHY**.

## Implementation notes

The four implications closing the cycle are
`Space.NormalizationData.isSurfaceResolutionCriterion_of_exists_regular_alteration`
((1) `⇒` (4)),
`AlgebraicGeometry.Space.hasResolutionByNormalizedBlowUps_of_isSurfaceResolutionCriterion`
((4) `⇒` (3)), applied to the constructed normalization
`AlgebraicGeometry.Space.normalizationData`,
`AlgebraicGeometry.Space.exists_resolutionOfSingularities_of_hasResolutionByNormalizedBlowUps`
((3) `⇒` (2)) and
`AlgebraicGeometry.Space.exists_regular_alteration_of_exists_resolutionOfSingularities`
((2) `⇒` (1)).

Condition (4) is asserted of every normalization of `Y`; normalizations exist and are unique up
to unique isomorphism over `Y`. Decency of `Y`, needed to speak of henselian local rings and of
birationality, is the decency of an integral space (Stacks 0AD4).

## References

* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0BHY.** For a two-dimensional integral Noetherian algebraic space `Y` over `S`, the
following are equivalent: (1) there is an alteration `X ⟶ Y` with `X` regular; (2) `Y` has a
resolution of singularities; (3) `Y` has a resolution of singularities by normalized blowups;
(4) the normalization `Y^ν ⟶ Y` is finite, `Y^ν` has finitely many singular points, and the
completion of the henselian local ring of `Y^ν` at each of them is normal. -/
@[stacks 0BHY]
theorem tfae_resolution_of_dimension_eq_two (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : AlgebraicSpaces B S hS) (hYdim : dimension B S hS Y.obj Y.property = 2)
    (hYnoeth : IsNoetherian B S hS hZ Y.obj) (hYint : IsIntegralSpace B S hS Y.obj) :
    List.TFAE
      [∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : X ⟶ Y.obj), IsAlteration B S hS f ∧
          HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T),
        ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
          (hdecentX : IsDecentSpace B S hS X) (f : X ⟶ Y.obj),
          IsResolutionOfSingularities B S hS hZ hX Y.property hYnoeth hYint hdecentX
            (hYint.isDecentSpace B S hS Y.obj) f,
        HasResolutionByNormalizedBlowUps B S hS hZ Y hYdim hYnoeth hYint,
        ∀ D : NormalizationData B S hS Y.obj,
          D.IsSurfaceResolutionCriterion Y.property (hYint.isDecentSpace B S hS Y.obj)] := by
  tfae_have 1 → 4 := fun h D =>
    NormalizationData.isSurfaceResolutionCriterion_of_exists_regular_alteration hZ Y hYdim
      hYnoeth hYint h D
  tfae_have 4 → 3 := fun h =>
    hasResolutionByNormalizedBlowUps_of_isSurfaceResolutionCriterion hZ Y hYdim hYnoeth hYint _
      (h (normalizationData B S hS Y.property
        (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Y.obj Y.property
          hYnoeth.2.2)))
  tfae_have 3 → 2 :=
    exists_resolutionOfSingularities_of_hasResolutionByNormalizedBlowUps hZ Y hYdim hYnoeth hYint
  tfae_have 2 → 1 :=
    exists_regular_alteration_of_exists_resolutionOfSingularities Y.property hYnoeth hYint
  tfae_finish

end AlgebraicGeometry.Space

end
