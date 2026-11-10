module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphism properties of a restricted groupoid scheme

The arrow scheme of the restriction of a groupoid scheme `G` along `g : U' ⟶ U` is an iterated
fibre product of the source and target maps of `G` with `g`, and its source map is a composite
of two projections of those fibre products.  So every property of morphisms of schemes which
is stable under base change — and, for the hypotheses phrased on `G` itself rather than on the
composite, also under composition — passes from the data of `G` and `g` to the source and
target maps of the restriction.  Local finite type, local finite presentation and flatness are
the three instances the source records.

## Main results

* `AlgebraicGeometry.restriction_source_mem` and `AlgebraicGeometry.restriction_target_mem`
  give an arbitrary base-change-stable property for the source and target maps of a
  restriction.
* `AlgebraicGeometry.restrictionSource_locallyOfFiniteType` and
  `AlgebraicGeometry.restrictionTarget_locallyOfFiniteType` treat local finite type.
* `AlgebraicGeometry.restrictionSource_locallyOfFinitePresentation` and
  `AlgebraicGeometry.restrictionTarget_locallyOfFinitePresentation` treat local finite
  presentation.
* `AlgebraicGeometry.restrictionSource_flat` and `AlgebraicGeometry.restrictionTarget_flat`
  treat flatness.

## Implementation notes

The source's assertions each concern both structure maps, so the conclusions for the source and
the target are stated separately.  A restriction is represented by
`AlgebraicGeometry.GroupoidScheme.Restriction`, so the results apply to any groupoid equipped
with the specified identifications with the canonical fibre products, and in particular to
`AlgebraicGeometry.GroupoidScheme.restrict`.  A morphism to the object scheme canonically gives
its domain a scheme structure over the base; the three named instances use this to form
`AlgebraicGeometry.GroupoidScheme.restrict`.

## References

* [Stacks Project, Tag 04MP](https://stacks.math.columbia.edu/tag/04MP)
* [Stacks Project, Tag 04MV](https://stacks.math.columbia.edu/tag/04MV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- Pre- and postcomposing with isomorphisms preserves a property respecting isomorphisms. -/
private lemma property_iso_comp {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {A B C D : Scheme.{u}} (i : A ⟶ B) (f : B ⟶ C) (j : C ⟶ D)
    [IsIso i] [IsIso j] (hf : P f) : P (i ≫ f ≫ j) := by
  have hif : P (i ≫ f) := (P.cancel_left_of_respectsIso i f).mpr hf
  exact (P.cancel_right_of_respectsIso (i ≫ f) j).mpr hif

/-- The source map of the canonical arrow scheme of a restriction has every property which is
stable under base change and holds for the source map composed with the projection. -/
private lemma restrictionSource_mem {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (P : MorphismProperty Scheme) [P.IsStableUnderBaseChange]
    (hP : P ((pullback.snd g G.target ≫ G.source).left)) :
    P (restrictionSource G g).left :=
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (((IsPullback.of_hasPullback
    (pullback.snd g G.target) (pullback.fst G.source g)).paste_vert
      (IsPullback.of_hasPullback G.source g)).map (Over.forget S)) hP

/-- The source map of a restriction inherits a property from the source map of the groupoid and
the restricting morphism, provided the property is stable under base change and composition. -/
private lemma restrictionSource_property {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (hs : P G.source.left) (hg : P g.left) :
    P (restrictionSource G g).left :=
  restrictionSource_mem G g P
    (overFibreProduct_comp (pullback.snd g G.target) G.source
      (overFibreProduct_snd g G.target hg) hs)

/-- The companion of `restrictionSource_property` for the target map. -/
private lemma restrictionTarget_property {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (ht : P G.target.left) (hg : P g.left) :
    P (restrictionTarget G g).left := by
  have hOuter : P (pullback.fst (pullback.snd g G.target) (pullback.fst G.source g)).left :=
    overFibreProduct_fst _ _ (overFibreProduct_fst G.source g hg)
  have hInner : P (pullback.fst g G.target).left := overFibreProduct_fst g G.target ht
  dsimp [restrictionTarget, restrictionArrows]
  exact P.comp_mem _ _ hOuter hInner

/-- Transport of a property from the source map of the canonical arrow scheme of a restriction
to the source map of any groupoid scheme realizing that restriction. -/
private lemma restriction_source_eq_property {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (R : GroupoidScheme.Restriction G g)
    (h : P (restrictionSource G g).left) : P R.groupoid.source.left := by
  have : IsIso (eqToHom R.arrows_eq).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom R.arrows_eq)))
  have : IsIso (eqToHom R.objects_eq.symm).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom R.objects_eq.symm)))
  rw [R.source_eq]
  dsimp only [Over.comp_left, Over.Hom.left]
  exact property_iso_comp _ _ _ h

/-- The companion of `restriction_source_eq_property` for the target map. -/
private lemma restriction_target_eq_property {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (R : GroupoidScheme.Restriction G g)
    (h : P (restrictionTarget G g).left) : P R.groupoid.target.left := by
  have : IsIso (eqToHom R.arrows_eq).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom R.arrows_eq)))
  have : IsIso (eqToHom R.objects_eq.symm).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom R.objects_eq.symm)))
  rw [R.target_eq]
  dsimp only [Over.comp_left, Over.Hom.left]
  exact property_iso_comp _ _ _ h

/-- The source map of the restriction along `g : U' ⟶ G.objects.left` has every property
stable under base change and composition which holds for the source map of `G` and for `g`. -/
private lemma restrict_source_property {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Scheme.{u}} (g : U' ⟶ G.objects.left)
    (hs : P G.source.left) (hg : P g) :
    P (GroupoidScheme.restrict G (Over.homMk g : Over.mk (g ≫ G.objects.hom) ⟶ G.objects)
      ).groupoid.source.left :=
  restriction_source_eq_property G _ _ (restrictionSource_property G _ hs hg)

/-- The target map of the restriction along `g : U' ⟶ G.objects.left` has every property
stable under base change and composition which holds for the target map of `G` and for `g`. -/
private lemma restrict_target_property {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Scheme.{u}} (g : U' ⟶ G.objects.left)
    (ht : P G.target.left) (hg : P g) :
    P (GroupoidScheme.restrict G (Over.homMk g : Over.mk (g ≫ G.objects.hom) ⟶ G.objects)
      ).groupoid.target.left :=
  restriction_target_eq_property G _ _ (restrictionTarget_property G _ ht hg)

/-- The source map of a restriction has every morphism property which is stable under base
change and holds for the source map after pulling back the target. -/
@[stacks 04MV "source map"]
public theorem restriction_source_mem {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (R : GroupoidScheme.Restriction G g)
    (P : MorphismProperty Scheme) [P.IsStableUnderBaseChange]
    (hP : P ((pullback.snd g G.target ≫ G.source).left)) :
    P R.groupoid.source.left :=
  restriction_source_eq_property G g R (restrictionSource_mem G g P hP)

/-- The target map of a restriction has every morphism property which is stable under base
change and holds for the source map after pulling back the target. -/
@[stacks 04MV "target map"]
public theorem restriction_target_mem {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (R : GroupoidScheme.Restriction G g)
    (P : MorphismProperty Scheme) [P.IsStableUnderBaseChange]
    (hP : P ((pullback.snd g G.target ≫ G.source).left)) :
    P R.groupoid.target.left := by
  rw [← R.groupoid.source_inverse]
  have : IsIso R.groupoid.inverse.left := groupoidInverse_left_isIso R.groupoid
  change P (R.groupoid.inverse.left ≫ R.groupoid.source.left)
  rw [P.cancel_left_of_respectsIso]
  exact restriction_source_mem G g R P hP

/-- The source map of a restriction is locally of finite type if the original source map
and the restricting morphism are locally of finite type. -/
@[stacks 04MP "part (1), source map"]
public theorem restrictionSource_locallyOfFiniteType {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Scheme.{u}} (g : U' ⟶ G.objects.left)
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType g] :
    let U'_S : Over S := Over.mk (g ≫ G.objects.hom)
    let g' : U'_S ⟶ G.objects := Over.homMk g
    LocallyOfFiniteType (GroupoidScheme.restrict G g').groupoid.source.left := by
  dsimp only
  exact restrict_source_property (P := @LocallyOfFiniteType) G g inferInstance inferInstance

/-- The target map of a restriction is locally of finite type if the original target map
and the restricting morphism are locally of finite type. -/
@[stacks 04MP "part (1), target map"]
public theorem restrictionTarget_locallyOfFiniteType {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Scheme.{u}} (g : U' ⟶ G.objects.left)
    [LocallyOfFiniteType G.target.left] [LocallyOfFiniteType g] :
    let U'_S : Over S := Over.mk (g ≫ G.objects.hom)
    let g' : U'_S ⟶ G.objects := Over.homMk g
    LocallyOfFiniteType (GroupoidScheme.restrict G g').groupoid.target.left := by
  dsimp only
  exact restrict_target_property (P := @LocallyOfFiniteType) G g inferInstance inferInstance

/-- The source map of a restriction is locally of finite presentation if the original source map
and the restricting morphism are locally of finite presentation. -/
@[stacks 04MP "part (2), source map"]
public theorem restrictionSource_locallyOfFinitePresentation {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Scheme.{u}} (g : U' ⟶ G.objects.left)
    [LocallyOfFinitePresentation G.source.left] [LocallyOfFinitePresentation g] :
    let U'_S : Over S := Over.mk (g ≫ G.objects.hom)
    let g' : U'_S ⟶ G.objects := Over.homMk g
    LocallyOfFinitePresentation
      (GroupoidScheme.restrict G g').groupoid.source.left := by
  dsimp only
  exact restrict_source_property (P := @LocallyOfFinitePresentation) G g inferInstance inferInstance

/-- The target map of a restriction is locally of finite presentation if the original target map
and the restricting morphism are locally of finite presentation. -/
@[stacks 04MP "part (2), target map"]
public theorem restrictionTarget_locallyOfFinitePresentation {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Scheme.{u}} (g : U' ⟶ G.objects.left)
    [LocallyOfFinitePresentation G.target.left] [LocallyOfFinitePresentation g] :
    let U'_S : Over S := Over.mk (g ≫ G.objects.hom)
    let g' : U'_S ⟶ G.objects := Over.homMk g
    LocallyOfFinitePresentation
      (GroupoidScheme.restrict G g').groupoid.target.left := by
  dsimp only
  exact restrict_target_property (P := @LocallyOfFinitePresentation) G g inferInstance inferInstance

/-- The source map of a restriction is flat if the original source map and the restricting
morphism are flat. -/
@[stacks 04MP "part (3), source map"]
public theorem restrictionSource_flat {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Scheme.{u}} (g : U' ⟶ G.objects.left) [Flat G.source.left] [Flat g] :
    let U'_S : Over S := Over.mk (g ≫ G.objects.hom)
    let g' : U'_S ⟶ G.objects := Over.homMk g
    Flat (GroupoidScheme.restrict G g').groupoid.source.left := by
  dsimp only
  exact restrict_source_property (P := @Flat) G g inferInstance inferInstance

/-- The target map of a restriction is flat if the original target map and the restricting
morphism are flat. -/
@[stacks 04MP "part (3), target map"]
public theorem restrictionTarget_flat {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Scheme.{u}} (g : U' ⟶ G.objects.left) [Flat G.target.left] [Flat g] :
    let U'_S : Over S := Over.mk (g ≫ G.objects.hom)
    let g' : U'_S ⟶ G.objects := Over.homMk g
    Flat (GroupoidScheme.restrict G g').groupoid.target.left := by
  dsimp only
  exact restrict_target_property (P := @Flat) G g inferInstance inferInstance

end AlgebraicGeometry
