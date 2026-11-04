module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidPullbackDiagram
public import StacksCore.Tactic.StacksAttribute

/-!
# Openness of composition in a groupoid scheme over a field

When the object scheme of a groupoid scheme is the spectrum of a field, the target map is
universally open, hence so is the projection from the scheme of pairs of arrows with a common
target.  The comparison between that scheme and the scheme of composable pairs identifies
composition with that projection up to an isomorphism, so composition is an open map.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isOpenMap_comp_of_objects_isFieldSpectrum` states the
  openness of composition.

## Implementation notes

The hypothesis that the object scheme is a field spectrum is expressed by a scheme
isomorphism. The composition morphism is a morphism in `Over S`; its underlying scheme
morphism is `G.comp.left`.

## References

* [Stacks Project, Tag 04LM](https://stacks.math.columbia.edu/tag/04LM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Composition in a groupoid scheme is an open map when the scheme of objects is the
spectrum of a field. -/
@[stacks 04LM]
public theorem isOpenMap_comp_of_objects_isFieldSpectrum
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (k : Type u) [Field k] (e : G.objects.left ≅ Spec (.of k)) :
    IsOpenMap G.comp.left := by
  have hu : UniversallyOpen G.target.left :=
    (MorphismProperty.cancel_right_of_respectsIso
      (P := @UniversallyOpen) G.target.left e.hom).mp inferInstance
  have hp : IsOpenMap (pullback.snd G.target G.target).left :=
    hu.universally_isOpenMap (pullback.fst G.target G.target).left G.target.left
      (pullback.snd G.target G.target).left (by
        simpa only [Over.forget_map] using
          (IsPullback.map (Over.forget S)
            (IsPullback.of_hasPullback G.target G.target)).flip)
  let d := targetPullbackToComposable G
  have : IsIso d := targetPullbackToComposable_isIso G
  rw [congrArg (fun f => f.left) ((cancel_epi d).mp (by
    rw [targetPullbackToComposable_comp]
    simp) : G.comp = inv d ≫ pullback.snd G.target G.target)]
  exact hp.comp ((Over.forget S).mapIso (asIso d)).inv.homeomorph.isOpenMap

end AlgebraicGeometry.GroupoidScheme
