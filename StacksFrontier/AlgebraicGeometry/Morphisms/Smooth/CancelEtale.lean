module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cancelling an étale morphism out of a smooth composition

If `X → Z` is a smooth morphism of schemes which factors through an étale morphism `Y → Z`,
then the induced morphism `X → Y` is again smooth.

## Main results

* `AlgebraicGeometry.smooth_isMultiplicative`: smoothness is stable under composition and
  contains the identities.
* `AlgebraicGeometry.smooth_hasOfPostcompProperty_etale`: smoothness has the of-postcomposition
  property with respect to étaleness.
* `AlgebraicGeometry.Smooth.of_comp_of_etale`: if `f ≫ g` is smooth and `g` is étale, then `f`
  is smooth.

## References

* [Stacks Project, Tag 0G80](https://stacks.math.columbia.edu/tag/0G80)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Smoothness of morphisms of schemes is multiplicative: it is stable under composition and
every identity morphism is smooth. -/
@[sga "1 II 1.3" "more general"]
public instance smooth_isMultiplicative : MorphismProperty.IsMultiplicative @Smooth.{u} :=
  HasRingHomProperty.isMultiplicative RingHom.Smooth.stableUnderComposition
    RingHom.Smooth.holdsForLocalizationAway.containsIdentities

/-- Smoothness has the of-postcomposition property with respect to étaleness: if `f ≫ g` is
smooth and `g` is étale, then `f` is smooth. -/
public instance smooth_hasOfPostcompProperty_etale :
    MorphismProperty.HasOfPostcompProperty @Smooth.{u} @Etale.{u} :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ g _hg => inferInstanceAs <| Smooth (pullback.diagonal g)

/-- Let `X → Y → Z` be morphisms of schemes. If `X → Z` is smooth and `Y → Z` is étale, then
`X → Y` is smooth. -/
@[stacks 0G80]
public theorem Smooth.of_comp_of_etale {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Smooth (f ≫ g)] [Etale g] : Smooth f :=
  MorphismProperty.of_postcomp (W := @Smooth) f g ‹Etale g› ‹Smooth (f ≫ g)›

end AlgebraicGeometry
