module

public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationInitial.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Initial
public import StacksFrontier.AlgebraicGeometry.SeminormalizationGluing.Basic

/-!
# Seminormalization and absolute weak normalization of a scheme

The seminormalization and the absolute weak normalization of a scheme `X` are the sources of
the initial objects of the two categories of universal homeomorphisms over `X`, together with
their structure morphisms to `X`. Every morphism of schemes lifts uniquely to a morphism
between the absolute weak normalizations.

## Main definitions

* `AlgebraicGeometry.Scheme.absoluteWeakNormalization` is the source of the chosen initial
  universal homeomorphism over a scheme, and
  `AlgebraicGeometry.Scheme.absoluteWeakNormalizationHom` its structure morphism.
* `AlgebraicGeometry.Scheme.seminormalization` is the source of the chosen initial
  seminormalization candidate over a scheme, and
  `AlgebraicGeometry.Scheme.seminormalizationHom` its structure morphism.

## Main results

* `AlgebraicGeometry.existsUnique_absoluteWeakNormalization_lift` gives the unique lift of a
  morphism of schemes to their absolute weak normalizations.

## References

* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
* [Stacks Project, Tag 0EUT](https://stacks.math.columbia.edu/tag/0EUT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The absolute weak normalization of `X`, chosen as the source of the initial universal
homeomorphism over `X`. -/
abbrev Scheme.absoluteWeakNormalization (X : Scheme.{u}) : Scheme.{u} :=
  (initial (UniversalHomeomorphismOver X)).obj.left

/-- The canonical universal homeomorphism from the absolute weak normalization to `X`. -/
abbrev Scheme.absoluteWeakNormalizationHom (X : Scheme.{u}) :
    X.absoluteWeakNormalization ⟶ X :=
  (initial (UniversalHomeomorphismOver X)).obj.hom

/-- Every morphism of schemes has a unique compatible lift to the absolute weak normalizations. -/
@[stacks 0EUS "absolute_weak_normalization_functorial"]
theorem existsUnique_absoluteWeakNormalization_lift {X' X : Scheme.{u}} (h : X' ⟶ X) :
    ∃! hawn : X'.absoluteWeakNormalization ⟶ X.absoluteWeakNormalization,
      hawn ≫ X.absoluteWeakNormalizationHom =
        X'.absoluteWeakNormalizationHom ≫ h := by
  let target : UniversalHomeomorphismOver X' :=
    UniversalHomeomorphismOver.pullback h (initial (UniversalHomeomorphismOver X))
  let m := initial.to target
  refine ⟨m.hom.left ≫ Limits.pullback.snd h X.absoluteWeakNormalizationHom, ?_, ?_⟩
  · simpa [Category.assoc, Limits.pullback.condition, target,
      UniversalHomeomorphismOver.pullback] using
      congrArg (fun q => q ≫ h) m.hom.w
  · intro g hg
    let lift := Limits.pullback.lift X'.absoluteWeakNormalizationHom g (by
      simpa [Category.assoc] using hg.symm)
    let n : initial (UniversalHomeomorphismOver X') ⟶ target :=
      ObjectProperty.homMk (Over.homMk lift (Limits.pullback.lift_fst _ _ _))
    have heq : lift ≫ Limits.pullback.snd h X.absoluteWeakNormalizationHom =
        m.hom.left ≫ Limits.pullback.snd h X.absoluteWeakNormalizationHom :=
      congrArg (fun q : initial (UniversalHomeomorphismOver X') ⟶ target =>
        q.hom.left ≫ Limits.pullback.snd h X.absoluteWeakNormalizationHom)
        (initial.hom_ext n m)
    simpa only [lift, Limits.pullback.lift_snd] using heq

/-- The seminormalization of `X`, as the source of the chosen initial seminormalization candidate
over `X`. -/
abbrev Scheme.seminormalization (X : Scheme.{u}) : Scheme.{u} :=
  (initial (SeminormalizationCategory X)).obj.left

/-- The canonical morphism from the seminormalization of `X` to `X`. -/
@[stacks 0EUT "part (1): the seminormalization morphism of an arbitrary scheme, no hypotheses"]
abbrev Scheme.seminormalizationHom (X : Scheme.{u}) : X.seminormalization ⟶ X :=
  (initial (SeminormalizationCategory X)).obj.hom

add_to_stacks 0EUT
  "part (2): the absolute weak normalization morphism of an arbitrary scheme, no hypotheses"
  Scheme.absoluteWeakNormalizationHom

end AlgebraicGeometry

end
