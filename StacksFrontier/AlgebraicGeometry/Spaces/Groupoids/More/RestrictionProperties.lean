module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Restriction

/-!
# Properties of the source and target inherited by a restricted groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces over `B` with object space `U`, arrow space `R`,
source `s` and target `t`, and let `g : U' ⟶ U` be a morphism of algebraic spaces. In the
defining diagram of the restriction of `G` along `g` every square is cartesian, so the source
of the restriction is a composite of a base change of `g` and a base change of `s`, and its
target is a composite of a base change of `g` and a base change of `t`. Consequently any
property of morphisms of algebraic spaces which is stable under base change and under
composition passes from `s` and `g` to the restricted source, and from `t` and `g` to the
restricted target. This file records the three cases of Stacks 04RP: being locally of finite
type, being locally of finite presentation, and being flat.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallyOfFiniteType_restrict_source` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallyOfFiniteType_restrict_target`: part (1)
  of Stacks 04RP, for a restricting morphism locally of finite type.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallyOfFinitePresentation_restrict_source`
  and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallyOfFinitePresentation_restrict_target`:
  part (2) of Stacks 04RP, for a restricting morphism locally of finite presentation.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFlat_restrict_source` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFlat_restrict_target`: part (3) of Stacks
  04RP, for a flat restricting morphism.

## Implementation notes

The six statements are all read off one lemma about an abstract property `Q` of morphisms of
algebraic spaces over `S` which is stable under base change and under composition. Writing
`R ×_{s, U} U'` and `U' ×_{U, t} R` for the two fibre products out of which the arrow space
`R'` of the restriction is built, the restricted source is the composite of the projection
`R' ⟶ R ×_{s, U} U'`, a base change of `g`, with the projection `R ×_{s, U} U' ⟶ U'`, a base
change of `s`; the restricted target is the composite of `R' ⟶ U' ×_{U, t} R`, again a base
change of `g`, with `U' ×_{U, t} R ⟶ U'`, a base change of `t`.

The structure morphisms of the restricted groupoid produced by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrict` are these two composites conjugated by
the `eqToHom` of the identifications of its object and arrow spaces. A property stable under
base change respects isomorphisms, so those two isomorphisms simply cancel.

Being locally of finite type and being locally of finite presentation are stable under
composition as properties of morphisms of algebraic spaces, but only their unbundled forms
`AlgebraicGeometry.Space.isLocallyOfFiniteType_comp` and
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_comp` are available; the two instances
are assembled here, the algebraicity hypotheses being supplied by the objects themselves, as
`AlgebraicGeometry.Space.isFlat_isStableUnderComposition` does for flatness.

## References

* [Stacks Project, Tag 03MN](https://stacks.math.columbia.edu/tag/03MN)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 03XQ](https://stacks.math.columbia.edu/tag/03XQ)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 04RP](https://stacks.math.columbia.edu/tag/04RP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being locally of finite type, as a property of morphisms of the category of algebraic
spaces over `S`, is stable under composition. This is
`AlgebraicGeometry.Space.isLocallyOfFiniteType_comp` with the algebraicity of the three objects
supplied by the objects themselves. -/
private instance isLocallyOfFiniteType_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsLocallyOfFiniteType B S hS f.hom) where
  comp_mem {X Y Z} f g hf hg :=
    isLocallyOfFiniteType_comp B S hS X.property Y.property Z.property f.hom g.hom hf hg

/-- Being locally of finite presentation, as a property of morphisms of the category of
algebraic spaces over `S`, is stable under composition. This is
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_comp` with the algebraicity of the three
objects supplied by the objects themselves. -/
private instance isLocallyOfFinitePresentation_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocallyOfFinitePresentation B S hS f.hom) where
  comp_mem {X Y Z} f g hf hg :=
    isLocallyOfFinitePresentation_comp B S hS X.property Y.property Z.property f.hom g.hom hf hg

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (Q : MorphismProperty (AlgebraicSpaces C S hS))
  [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition]
  (G : GroupoidInAlgebraicSpaces C S hS B) {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)

/-- The chosen lift of the source on the arrow space of a restriction lies in a class of
morphisms of algebraic spaces stable under base change and under composition as soon as the
source of the original groupoid and the restricting morphism do. -/
private theorem restrictionSource_mem (hs : Q G.source) (hg : Q g) :
    Q (restrictionSource G g) :=
  Q.comp_mem _ _
    (Q.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct C S hS
        (fiberProductSnd g G.target) (fiberProductFst G.source g))
      (Q.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct C S hS g G.target) hg))
    (Q.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source g) hs)

/-- The chosen lift of the target on the arrow space of a restriction lies in a class of
morphisms of algebraic spaces stable under base change and under composition as soon as the
target of the original groupoid and the restricting morphism do. -/
private theorem restrictionTarget_mem (ht : Q G.target) (hg : Q g) :
    Q (restrictionTarget G g) :=
  Q.comp_mem _ _
    (Q.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct C S hS
        (fiberProductSnd g G.target) (fiberProductFst G.source g)).flip
      (Q.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source g).flip hg))
    (Q.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct C S hS g G.target).flip ht)

/-- The source of the restriction of a groupoid in algebraic spaces lies in a class of
morphisms stable under base change and under composition as soon as the source of the original
groupoid and the restricting morphism do. -/
private theorem restrict_source_mem (hs : Q G.source) (hg : Q g) :
    Q (restrict G g).groupoid.source := by
  rw [(restrict G g).source_eq]
  exact MorphismProperty.RespectsIso.precomp Q _ _
    (MorphismProperty.RespectsIso.postcomp Q _ _ (restrictionSource_mem Q G g hs hg))

/-- The target of the restriction of a groupoid in algebraic spaces lies in a class of
morphisms stable under base change and under composition as soon as the target of the original
groupoid and the restricting morphism do. -/
private theorem restrict_target_mem (ht : Q G.target) (hg : Q g) :
    Q (restrict G g).groupoid.target := by
  rw [(restrict G g).target_eq]
  exact MorphismProperty.RespectsIso.precomp Q _ _
    (MorphismProperty.RespectsIso.postcomp Q _ _ (restrictionTarget_mem Q G g ht hg))

/-- **Stacks 04RP.** If the source of a groupoid in algebraic spaces over `B` and the morphism
`g` along which it is restricted are locally of finite type, then so is the source of the
restriction. -/
@[stacks 04RP "part (1): the restricted source is locally of finite type"]
theorem isLocallyOfFiniteType_restrict_source
    (hs : Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (hg : Space.IsLocallyOfFiniteType C S hS g.hom) :
    Space.IsLocallyOfFiniteType C S hS (restrict G g).groupoid.source.hom :=
  have := Space.isLocallyOfFiniteType_isStableUnderBaseChange C S hS
  restrict_source_mem
    (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) =>
      Space.IsLocallyOfFiniteType C S hS f.hom) G g hs hg

/-- **Stacks 04RP.** If the target of a groupoid in algebraic spaces over `B` and the morphism
`g` along which it is restricted are locally of finite type, then so is the target of the
restriction. -/
@[stacks 04RP "part (1): the restricted target is locally of finite type"]
theorem isLocallyOfFiniteType_restrict_target
    (ht : Space.IsLocallyOfFiniteType C S hS G.target.hom)
    (hg : Space.IsLocallyOfFiniteType C S hS g.hom) :
    Space.IsLocallyOfFiniteType C S hS (restrict G g).groupoid.target.hom :=
  have := Space.isLocallyOfFiniteType_isStableUnderBaseChange C S hS
  restrict_target_mem
    (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) =>
      Space.IsLocallyOfFiniteType C S hS f.hom) G g ht hg

/-- **Stacks 04RP.** If the source of a groupoid in algebraic spaces over `B` and the morphism
`g` along which it is restricted are locally of finite presentation, then so is the source of
the restriction. -/
@[stacks 04RP "part (2): the restricted source is locally of finite presentation"]
theorem isLocallyOfFinitePresentation_restrict_source
    (hs : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (hg : Space.IsLocallyOfFinitePresentation C S hS g.hom) :
    Space.IsLocallyOfFinitePresentation C S hS (restrict G g).groupoid.source.hom :=
  have := Space.isLocallyOfFinitePresentation_isStableUnderBaseChange C S hS
  restrict_source_mem
    (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) =>
      Space.IsLocallyOfFinitePresentation C S hS f.hom) G g hs hg

/-- **Stacks 04RP.** If the target of a groupoid in algebraic spaces over `B` and the morphism
`g` along which it is restricted are locally of finite presentation, then so is the target of
the restriction. -/
@[stacks 04RP "part (2): the restricted target is locally of finite presentation"]
theorem isLocallyOfFinitePresentation_restrict_target
    (ht : Space.IsLocallyOfFinitePresentation C S hS G.target.hom)
    (hg : Space.IsLocallyOfFinitePresentation C S hS g.hom) :
    Space.IsLocallyOfFinitePresentation C S hS (restrict G g).groupoid.target.hom :=
  have := Space.isLocallyOfFinitePresentation_isStableUnderBaseChange C S hS
  restrict_target_mem
    (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) =>
      Space.IsLocallyOfFinitePresentation C S hS f.hom) G g ht hg

/-- **Stacks 04RP.** If the source of a groupoid in algebraic spaces over `B` and the morphism
`g` along which it is restricted are flat, then so is the source of the restriction. -/
@[stacks 04RP "part (3): the restricted source is flat"]
theorem isFlat_restrict_source (hs : Space.IsFlat C S hS G.source.hom)
    (hg : Space.IsFlat C S hS g.hom) :
    Space.IsFlat C S hS (restrict G g).groupoid.source.hom :=
  have := Space.isFlat_isStableUnderBaseChange C S hS
  restrict_source_mem
    (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) => Space.IsFlat C S hS f.hom) G g hs hg

/-- **Stacks 04RP.** If the target of a groupoid in algebraic spaces over `B` and the morphism
`g` along which it is restricted are flat, then so is the target of the restriction. -/
@[stacks 04RP "part (3): the restricted target is flat"]
theorem isFlat_restrict_target (ht : Space.IsFlat C S hS G.target.hom)
    (hg : Space.IsFlat C S hS g.hom) :
    Space.IsFlat C S hS (restrict G g).groupoid.target.hom :=
  have := Space.isFlat_isStableUnderBaseChange C S hS
  restrict_target_mem
    (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) => Space.IsFlat C S hS f.hom) G g ht hg

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
