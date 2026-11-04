module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.Sites.Precoverage
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.DoubleRestriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent of a property of the source map along a double restriction

Let `G` be a groupoid scheme restricted successively along `g : U' ⟶ U` and `g' : U'' ⟶ U'`.
The two cartesian squares of `AlgebraicGeometry.doubleRestrictionDiagram` make the source map
of the second restriction a base change of the source map over the composite restriction, so a
property which is stable under base change and local on the target descends in both directions:
upwards to the second restriction, when the original target map is a covering, and downwards to
the open image of the first source map, when that image is covered.

## Main results

* `AlgebraicGeometry.restrictionSource_mem_of_composite` gives the property for the second
  restriction.
* `AlgebraicGeometry.descent_to_open_image` gives the factorization of the composite-restriction
  source map through the open image and its morphism property.

## Implementation notes

The source and target maps of the first restriction are the canonical maps
`AlgebraicGeometry.restrictionSource` and `AlgebraicGeometry.restrictionTarget`.  The statements
use an arbitrary base-change-stable precoverage, which specializes to each of the six topologies
in the source.  Pullbacks are taken in `Over S`, and morphism properties are asserted of the
underlying scheme maps.

The first source map's open image is represented by an open subscheme `V` together with the
covering morphism into `V`; its equality with the image is explicit.  The conclusion supplies
the factorization of the composite source map, rather than assuming this factorization.

## References

* [Stacks Project, Tag 04MX](https://stacks.math.columbia.edu/tag/04MX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- A property respecting isomorphisms holds for `pullback.snd` once it holds for the second
projection of any other pullback square on the same cospan. -/
private theorem mem_pullback_snd_of_isPullback {C : Type*} [Category C]
    (P : MorphismProperty C) [P.RespectsIso] {A X Y Z : C} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : IsPullback fst snd f g) (hs : P snd) :
    P (pullback.snd f g) := by
  have hcanon := IsPullback.of_hasPullback f g
  apply (P.cancel_left_of_respectsIso (h.isoIsPullback _ _ hcanon).hom _).mp
  rwa [h.isoIsPullback_hom_snd _ _ hcanon]

/-- A property of the source map over a composite restriction descends to the
source map over the second restriction when the original target map covers. -/
@[stacks 04MX "pullback_to_second_restriction"]
public theorem restrictionSource_mem_of_composite {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U')
    (K : Precoverage Scheme.{u}) [K.IsStableUnderBaseChange]
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget K]
    (ht : Presieve.singleton G.target.left ∈ K G.objects.left)
    (hP : P ((pullback.snd (g' ≫ g) G.target ≫ G.source).left)) :
    P ((pullback.snd g' (restrictionTarget G g) ≫ restrictionSource G g).left) := by
  let D := doubleRestrictionDiagram G g g'
  let F := Over.forget S
  let β := F.map (pullback.fst g G.target)
  let α := F.map (pullback.fst (firstSourceMap G g) (compositeSourceMap G g g'))
  have hcover : Presieve.singleton β ∈ K U'.left := by
    change Presieve.singleton (F.map G.target) ∈ K (F.obj G.objects) at ht
    show Presieve.singleton β ∈ K (F.obj U')
    have hcov : Presieve.ofArrows
        (fun _ : PUnit => F.obj (pullback g G.target))
        (fun _ => β) ∈ K (F.obj U') := by
      apply Precoverage.IsStableUnderBaseChange.mem_coverings_of_isPullback
        (J := K) (f := fun _ : PUnit => F.map G.target)
      · rwa [Presieve.ofArrows_of_unique]
      · exact fun _ => (IsPullback.of_hasPullback g G.target).map F
    simpa only [Presieve.ofArrows_of_unique] using hcov
  have hmiddle : P α := by
    apply MorphismProperty.of_isPullback
      (by simpa only [α, Over.forget_obj] using D.right_isPullback.map F)
    exact hP
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (K := K) (P := P) hcover
  rintro _ _ _ ⟨⟩
  exact mem_pullback_snd_of_isPullback P (D.left_isPullback.map F) hmiddle

/-- A morphism property local on the target descends from the source map of a
restriction to the source map after a further restriction, viewed over the
open image of the first source map. -/
@[stacks 04MX "descent_to_open_image"]
public theorem descent_to_open_image {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U')
    (K : Precoverage Scheme.{u}) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget K]
    (V : G.objects.left.Opens)
    (hV : (firstArrowSource G g).left ⟶ V.toScheme)
    (hV_fac : hV ≫ V.ι = (firstSourceMap G g).left)
    (_hV_range : Set.range (firstSourceMap G g).left = (V : Set G.objects.left))
    (hV_cover : Presieve.singleton hV ∈ K V.toScheme)
    (hP : P (secondSourceMap G g g').left) :
    ∃ hV' : (compositeArrowSource G g g').left ⟶ V.toScheme,
      hV' ≫ V.ι = (compositeSourceMap G g g').left ∧ P hV' := by
  let j : compositeArrowSource G g g' ⟶ firstArrowSource G g :=
    pullback.lift
      (pullback.fst (g' ≫ g) G.target ≫ g')
      (pullback.snd (g' ≫ g) G.target)
      ((Category.assoc _ _ _).trans pullback.condition)
  have hj : j ≫ firstSourceMap G g = compositeSourceMap G g g' := by
    dsimp [j, firstSourceMap, compositeSourceMap, firstArrowSource, compositeArrowSource]
    exact congrArg (fun f : compositeArrowSource G g g' ⟶ G.arrows => f ≫ G.source)
      (pullback.lift_snd _ _ _)
  let hV' : (compositeArrowSource G g g').left ⟶ V.toScheme := j.left ≫ hV
  have hV'_fac : hV' ≫ V.ι = (compositeSourceMap G g g').left := by
    dsimp [hV']
    rw [Category.assoc, hV_fac]
    simpa only [Over.comp_left] using
      congrArg (fun f : compositeArrowSource G g g' ⟶ G.objects => f.left) hj
  let D := doubleRestrictionDiagram G g g'
  have hPx : P ((Over.forget S).map
      (pullback.fst (firstSourceMap G g) (compositeSourceMap G g g'))) :=
    MorphismProperty.of_isPullback (D.left_isPullback.map (Over.forget S))
      (by simpa only [Over.forget_map] using hP)
  have hright : IsPullback
      ((Over.forget S).map (pullback.snd (firstSourceMap G g) (compositeSourceMap G g g')))
      ((Over.forget S).map (pullback.fst (firstSourceMap G g) (compositeSourceMap G g g')))
      hV' hV :=
    IsPullback.of_isLimit (PullbackCone.isLimitOfFactors _ _ V.ι hV' hV
      hV'_fac hV_fac _ (D.right_isPullback.map (Over.forget S)).isLimit)
  refine ⟨hV', hV'_fac, ?_⟩
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hV_cover
  rintro _ _ _ ⟨⟩
  exact mem_pullback_snd_of_isPullback P hright hPx

end AlgebraicGeometry
