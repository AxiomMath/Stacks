module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentIntegralSurjective

/-!
# Effective descent for small étale sheaves along a proper surjection

A proper surjection of schemes is the second class of morphisms for which descent of small étale
sheaves is effective, the first being the integral surjections. The two dévissage inputs are the
same for both classes and are already available: the projections `X ×_Y X ⟶ X` and
`X ×_Y (X ×_Y X) ⟶ X ×_Y X` are split, by the diagonal and by the graph of the first projection
respectively, whatever the morphism `f : X ⟶ Y`. Surjectivity and properness are preserved by
base change in the underlying category of a big étale site, so the conclusion propagates to every
base change of a proper surjection.

## Main results

* `AlgebraicGeometry.surjective_inclusion_map_pullback_snd` and
  `AlgebraicGeometry.isProper_inclusion_map_pullback_snd`: surjectivity and properness of a
  morphism of a big étale site pass to its base changes.
* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_proper_of_section`:
  the split case, which is already [Stacks, Tag 0GEY].
* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_proper`: descent
  along a proper surjection is effective, given the dévissage of [Stacks, Tag 0GF1] as a
  hypothesis.

## Implementation notes

The source proves this lemma by rerunning the proof of [Stacks, Tag 0GEZ] with the base-change
theorem for integral morphisms replaced by the proper base-change theorem [Stacks, Tag 0A3U].
That argument, which needs no dévissage hypothesis, is
`AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_isProper_of_surjective` in the
module `SheafDescentProperSurjectiveUnconditional` beside this one.
The results of this file reduce the general case to the dévissage of [Stacks, Tag 0GF1] instead;
that dévissage is proved in the source from the present lemma together with [Stacks, Tag 0GEZ],
so it is taken here as an explicit hypothesis, stated for the proper branch of the criterion only.

## References

* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Surjectivity of a morphism of a big étale site passes to its base changes. -/
public theorem surjective_inclusion_map_pullback_snd (B : BigEtaleSite.{u})
    {X Y Z : B.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective (B.inclusion.map f)] :
    Surjective (B.inclusion.map (pullback.snd f g)) := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  exact MorphismProperty.of_isPullback (P := @Surjective)
    (B.inclusion.map_isPullback (IsPullback.of_hasPullback f g)) ‹_›

/-- Properness of a morphism of a big étale site passes to its base changes. -/
public theorem isProper_inclusion_map_pullback_snd (B : BigEtaleSite.{u})
    {X Y Z : B.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [IsProper (B.inclusion.map f)] :
    IsProper (B.inclusion.map (pullback.snd f g)) := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  exact MorphismProperty.of_isPullback (P := @IsProper)
    (B.inclusion.map_isPullback (IsPullback.of_hasPullback f g)) ‹_›

/-- A proper surjection admitting a section is an effective descent morphism for small étale
sheaves. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_proper_of_section
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [Surjective (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence :=
  smallEtaleSheafDescentFunctor_isEquivalence_of_section B f s hs

/-- A proper surjection is an effective descent morphism for small étale sheaves. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_proper
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [Surjective (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
    (devissage : ∀ {X' Y' Z' : B.Scheme} (f' : X' ⟶ Y') (g' : Z' ⟶ Y'),
      Surjective (B.inclusion.map g') → IsProper (B.inclusion.map g') →
      (smallEtaleSheafDescentFunctor B (pullback.snd f' g')).IsEquivalence →
      (smallEtaleSheafDescentFunctor B
        (pullback.snd f' (pullback.fst g' g' ≫ g'))).IsEquivalence →
      (smallEtaleSheafDescentFunctor B f').IsEquivalence) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence :=
  devissage f f ‹Surjective (B.inclusion.map f)› ‹IsProper (B.inclusion.map f)›
    (smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_self B f)
    (smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_fst_comp B f)

/-- Every base change of a proper surjection is again an effective descent morphism for small
étale sheaves, surjectivity and properness being preserved by base change. -/
public theorem smallEtaleSheafDescentFunctor_isEquivalence_pullback_snd_of_surjective_proper
    (B : BigEtaleSite.{u}) {X Y W : B.Scheme} (f : X ⟶ Y) (g : W ⟶ Y)
    [Surjective (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
    (devissage : ∀ {X' Y' Z' : B.Scheme} (f' : X' ⟶ Y') (g' : Z' ⟶ Y'),
      Surjective (B.inclusion.map g') → IsProper (B.inclusion.map g') →
      (smallEtaleSheafDescentFunctor B (pullback.snd f' g')).IsEquivalence →
      (smallEtaleSheafDescentFunctor B
        (pullback.snd f' (pullback.fst g' g' ≫ g'))).IsEquivalence →
      (smallEtaleSheafDescentFunctor B f').IsEquivalence) :
    (smallEtaleSheafDescentFunctor B (pullback.snd f g)).IsEquivalence := by
  have : Surjective (B.inclusion.map (pullback.snd f g)) :=
    surjective_inclusion_map_pullback_snd B f g
  have : IsProper (B.inclusion.map (pullback.snd f g)) :=
    isProper_inclusion_map_pullback_snd B f g
  exact smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_proper B
    (pullback.snd f g) devissage

end AlgebraicGeometry

end
