module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance

/-!
# Topological invariance of the small étale site: the fully faithful half, bundled

Base change along a universal homeomorphism `f : X ⟶ Y` is a fully faithful functor from the
small étale site of `Y` to the small étale site of `X`. Fullness and faithfulness are available
separately as `Stacks.Etale.etalePullback_full_of_universalHomeomorphism` and
`Stacks.Etale.etalePullback_faithful_of_universalHomeomorphism`; this file bundles them into a
single `CategoryTheory.Functor.FullyFaithful` term, which is the form a consumer wanting the
inverse on morphisms actually needs.

Topological invariance of the étale site, Stacks Project, Tag 04DZ, asserts that this functor is
an *equivalence*. That statement is **not** proved here and this file must not be read as
proving it: an equivalence is fullness, faithfulness and essential surjectivity, and only the
first two are established. Essential surjectivity is effectivity of étale descent along a
surjective integral morphism, Stacks Project, Tag 0BTP, which is not available in this library.

## Main results

* `Stacks.Etale.etalePullbackFullyFaithful_of_universalHomeomorphism` — the base-change functor
  between small étale sites along a universal homeomorphism is fully faithful.

## References

* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace Stacks.Etale

open AlgebraicGeometry

/-- Base change along a universal homeomorphism `f : X ⟶ Y` is a fully faithful functor from
the small étale site of `Y` to the small étale site of `X`.

This is the fully faithful half of the topological invariance of the small étale site. It is
*not* the full statement of Stacks Project, Tag 04DZ, which additionally asserts essential
surjectivity. -/
def etalePullbackFullyFaithful_of_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f] :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ f).FullyFaithful := by
  have : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  have := etalePullback_full_of_universalHomeomorphism f
  have := etalePullback_faithful_of_universalHomeomorphism f
  exact Functor.FullyFaithful.ofFullyFaithful _

end Stacks.Etale

end

end
