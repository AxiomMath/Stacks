module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceAffine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective
public import StacksFrontier.AlgebraicGeometry.PartTwoResidue.Complete
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Topological invariance of the étale site on affine objects, unconditionally

Let `f : X ⟶ Y` be a universal homeomorphism. Base change `V ↦ X ×_Y V` along `f` restricts to
an equivalence between the affine schemes étale over `Y` and the affine schemes étale over `X`.

## Main results

* `Stacks.Etale.affineEtalePullback_isEquivalence_of_universalHomeomorphism` — base change along
  a universal homeomorphism restricts to an equivalence on the full subcategories of affine
  objects of the two small étale sites.

## References

* [Stacks Project, Tag 05YX](https://stacks.math.columbia.edu/tag/05YX)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 05YU](https://stacks.math.columbia.edu/tag/05YU)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

/-- **Topological invariance of the étale site on affine objects.** Let `f : X ⟶ Y` be a universal
homeomorphism. Base change `V ↦ X ×_Y V` along `f` carries an affine scheme étale over `Y` to an
affine scheme étale over `X`, and the induced functor from the full subcategory of affine objects
of the small étale site of `Y` to the full subcategory of affine objects of the small étale site
of `X` is an equivalence. -/
@[stacks 05YX "base change along a universal homeomorphism restricts to an equivalence between
the affine schemes etale over the target and the affine schemes etale over the source",
  sga "4½ Th_finitude 2.7" "partial"]
theorem affineEtalePullback_isEquivalence_of_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f] :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦
        MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    let F : Y.Etale ⥤ X.Etale :=
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ f
    let PY : ObjectProperty Y.Etale := fun V ↦ IsAffine V.left
    let PX : ObjectProperty X.Etale := fun U ↦ IsAffine U.left
    ∃ (h : ∀ V : PY.FullSubcategory, PX (F.obj V.obj)),
      (PX.lift (PY.ι ⋙ F) h).IsEquivalence := by
  obtain ⟨_, _, _⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp ‹_›
  refine affineEtalePullback_isEquivalence_of_essSurj_of_h09YZ f ?_ ?_
  · have := etalePullback_isEquivalence f
    infer_instance
  · intro X' S g _ _ _
    exact Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation g

end Stacks.Etale

end
