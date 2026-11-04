module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceEquivalence
public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromSurjectiveUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral

/-!
# Topological invariance of the étale site on affine objects

Let `f : X ⟶ Y` be a universal homeomorphism. Base change along `f` carries a scheme étale over
`Y` to a scheme étale over `X`, and it matches up the *affine* objects of the two small étale
sites: the base change of an affine étale scheme is affine because `f` is an affine morphism,
and conversely a scheme étale over `Y` whose base change is affine is itself affine because the
projection from that base change is surjective and universally closed.

Consequently base change restricts to an equivalence between the full subcategory of affine
objects of the small étale site of `Y` and that of `X`. This is Stacks Project, Tag 05YX.

## Main results

* `Stacks.Etale.affineEtalePullback_isEquivalence_of_essSurj_of_h09YZ` — base change along a
  universal homeomorphism restricts to an equivalence on the full subcategories of affine étale
  objects.

## Implementation notes

The small étale site is Mathlib's `AlgebraicGeometry.Scheme.Etale` and the functor is
`CategoryTheory.MorphismProperty.Over.pullback` for the morphism property
`AlgebraicGeometry.Etale`, with the two instance arguments it needs supplied inline in the
statement exactly as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceEquivalence`.

The affine objects are cut out by an `CategoryTheory.ObjectProperty`, and the restricted functor
is its `CategoryTheory.ObjectProperty.lift`, so that it is literally the functor induced by base
change rather than an arbitrary functor isomorphic to it. The witness that base change preserves
affineness is produced alongside the equivalence, since the lift cannot be formed without it;
pinning the functor this way means the existential statement is not weaker than the assertion it
formalizes.

Two results cited by the source occur as explicit hypotheses.

* Essential surjectivity of base change on the whole small étale site, part of Stacks Project,
  Tag 04DZ; its full and faithful halves are proved in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance`, and the assembly of the
  three into the equivalence is
  `Stacks.Etale.etalePullback_isEquivalence_of_universalHomeomorphism_of_essSurj`.
* `AlgebraicGeometry.IntegralHasFinitePresentationLimit`, which is Stacks Project, Tag 09YZ over
  a quasi-compact quasi-separated base. It is the input of Stacks Project, Tag 05YU,
  affineness of the target of a surjective universally closed morphism out of an affine scheme;
  the rest of Tag 05YU is
  `Stacks.AffineFromUniversallyClosed.isAffine_of_surjective_universallyClosed_of_h09YZ`.

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

/-- **Topological invariance of the étale site on affine objects.** Base change along a universal
homeomorphism `f : X ⟶ Y` restricts to an equivalence between the full subcategory of affine
objects of the small étale site of `Y` and the full subcategory of affine objects of the small
étale site of `X`.

The hypothesis `hessSurj` is essential surjectivity of base change on the whole small étale
site, part of Stacks Project, Tag 04DZ, and `h09YZ` is Stacks Project, Tag 09YZ over a
quasi-compact quasi-separated base, the input of Stacks Project, Tag 05YU. -/
@[stacks 05YX "assuming essential surjectivity of etale pullback (the content of Stacks 04DZ)
and Stacks 09YZ over a qcqs base"]
theorem affineEtalePullback_isEquivalence_of_essSurj_of_h09YZ
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f]
    (hessSurj :
      letI : MorphismProperty.HasPullbacksAlong
          (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
      letI : MorphismProperty.IsStableUnderBaseChangeAlong
          (@Etale : MorphismProperty Scheme.{u}) f :=
        ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
      (show Y.Etale ⥤ X.Etale from
        MorphismProperty.Over.pullback
          (@Etale : MorphismProperty Scheme.{u}) ⊤ f).EssSurj)
    (h09YZ : IntegralHasFinitePresentationLimit.{u}) :
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
  classical
  intro F PY PX
  rcases (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp
    ‹_› with ⟨hInt, _, hSurj⟩
  have : IsAffineHom f :=
    (IsIntegralHom.iff_universallyClosed_and_isAffineHom).mp hInt |>.2
  have hAff (V : Y.Etale) (hV : IsAffine V.left) : IsAffine (F.obj V).left := by
    change IsAffine (pullback V.hom f)
    exact isAffine_of_isAffineHom (f := pullback.fst V.hom f) (Y := V.left)
  have hAffReflect (V : Y.Etale) (hV : IsAffine (F.obj V).left) : IsAffine V.left := by
    have : IsAffine (pullback V.hom f) := hV
    exact AffineFromUniversallyClosed.isAffine_of_surjective_universallyClosed_of_h09YZ
      (pullback.fst V.hom f) h09YZ
  have : F.IsEquivalence :=
    etalePullback_isEquivalence_of_universalHomeomorphism_of_essSurj f hessSurj
  let e : Y.Etale ≌ X.Etale := F.asEquivalence
  have hProp : PX.inverseImage e.functor = PY := by
    ext V
    exact ⟨hAffReflect V, hAff V⟩
  have : PX.IsClosedUnderIsomorphisms := by
    refine ⟨fun {U V} i hU ↦ ?_⟩
    have : IsAffine U.left := hU
    let d : U.left ≅ V.left := (Scheme.Etale.forget X ⋙ Over.forget X).mapIso i
    exact IsAffine.of_isIso d.inv
  refine ⟨fun V ↦ hAff V.obj V.property, ?_⟩
  change (e.congrFullSubcategory hProp).functor.IsEquivalence
  infer_instance

end Stacks.Etale

end
