module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Thickening
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.UniversalHomeomorphism

/-!
# Base change of finite étale covers along a universal homeomorphism is fully faithful

Let `f : X ⟶ Y` be a universal homeomorphism. Base change along `f` of finite étale covers is
faithful (`AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_universalHomeomorphism`). It is
moreover full, hence fully faithful: a morphism of finite étale covers is a morphism of the
schemes étale over the base, and base change is full on the étale site by Stacks Project,
Tag 0BTY.

## Main results

* `AlgebraicGeometry.full_finiteEtaleBaseChange_of_universalHomeomorphism` and
  `AlgebraicGeometry.fullyFaithfulFiniteEtaleBaseChangeOfUniversalHomeomorphism` — base change of
  finite étale covers along a universal homeomorphism is full, hence fully faithful.

## Implementation notes

Fullness is transported from the étale site exactly as in
`AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_isThickening`: the inclusion
`AlgebraicGeometry.finiteEtaleToEtale` of the finite étale covers into the étale site is fully
faithful, and base change on finite étale covers is, after that inclusion, base change on the
étale site on the nose.

## References

* [Stacks Project, Tag 0BQN](https://stacks.math.columbia.edu/tag/0BQN)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Base change of finite étale covers along a universal homeomorphism is full.** Let
`f : X ⟶ Y` be a universal homeomorphism and let `V₁`, `V₂` be finite étale covers of `Y`. Every
morphism `V₁ ×_Y X ⟶ V₂ ×_Y X` of finite étale covers of `X` is the base change of a morphism
`V₁ ⟶ V₂` over `Y`.

A morphism of finite étale covers is nothing but a morphism of the schemes étale over the base,
and base change along a universal homeomorphism is full on the étale site by Stacks Project,
Tag 0BTY (`Stacks.Etale.etalePullback_full_of_universalHomeomorphism`). -/
theorem full_finiteEtaleBaseChange_of_universalHomeomorphism (f : X ⟶ Y)
    [UniversalHomeomorphism f] : (finiteEtaleBaseChange f).Full := by
  have hpb : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
  have hbc : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let E : Y.Etale ⥤ X.Etale := MorphismProperty.Over.pullback (@Etale) ⊤ f
  have _ : E.Full := Stacks.Etale.etalePullback_full_of_universalHomeomorphism f
  let F := finiteEtaleBaseChange f
  let G := finiteEtaleToEtale X
  let G' := finiteEtaleToEtale Y
  have hmap : ∀ {A B : FiniteEtaleOver Y} (φ : A ⟶ B),
      G.map (F.map φ) = E.map (G'.map φ) := fun _ ↦ rfl
  have hG'ff := finiteEtaleToEtaleFullyFaithful Y
  refine ⟨fun {A B} φ ↦ ⟨hG'ff.preimage (E.preimage (G.map φ)),
    (finiteEtaleToEtaleFullyFaithful X).map_injective ?_⟩⟩
  rw [hmap, hG'ff.map_preimage]
  exact E.map_preimage _

/-- **Base change of finite étale covers along a universal homeomorphism is fully faithful.**
This bundles `AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_universalHomeomorphism` with
`AlgebraicGeometry.full_finiteEtaleBaseChange_of_universalHomeomorphism`. -/
def fullyFaithfulFiniteEtaleBaseChangeOfUniversalHomeomorphism (f : X ⟶ Y)
    [UniversalHomeomorphism f] : (finiteEtaleBaseChange f).FullyFaithful :=
  have _ := faithful_finiteEtaleBaseChange_of_universalHomeomorphism f
  have _ := full_finiteEtaleBaseChange_of_universalHomeomorphism f
  Functor.FullyFaithful.ofFullyFaithful _

end AlgebraicGeometry

end
