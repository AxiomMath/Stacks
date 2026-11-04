module

public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationAtlasSmallUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentablePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationExistence

/-!
# The base change of a presentation along a morphism representable by algebraic spaces

Let `S` be a scheme of a big fppf site, let `g : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks over
`S` representable by algebraic spaces and let `P = ((U, R, s, t, c), [U/R] ≃ 𝒳)` be a presentation
of `𝒳`. This module constructs a groupoid in algebraic spaces whose object space is
`U' = U ×_𝒳 𝒳'`, and a presentation `[U'/R'] ⟶ 𝒳'` built on it.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidPresentation.baseChangedAtlasSquare`: the canonical square
  presenting `U' = U ×_𝒳 𝒳'`, with both legs at the morphism universe of `𝒳`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.baseChangedAtlas`: its projection `U' ⟶ 𝒳'`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.baseChangedPresentation`: the groupoid and the
  presentation of `𝒳'`, on chosen representing spaces of `U'` and of `U' ×_{𝒳'} U'`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidPresentation.isRepresentableByAlgebraicSpace_baseChangedAtlas`:
  `U'` is an algebraic space.
* `AlgebraicGeometry.Stack.GroupoidPresentation.isRelativelySmooth_baseChangedAtlas` and
  `...isRelativelySurjective_baseChangedAtlas`: it is smooth and surjective over `𝒳'`.
* `Stack.GroupoidPresentation.isRepresentableByAlgebraicSpace_baseChangedRelation`:
  `U' ×_{𝒳'} U'` is an algebraic space.
* `AlgebraicGeometry.Stack.GroupoidPresentation.baseChangedPresentation_objects` and
  `...baseChangedPresentation_arrows`: the object and arrow spaces of that groupoid are the two
  chosen representing spaces, on the nose.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
* [Stacks Project, Tag 04X0](https://stacks.math.columbia.edu/tag/04X0)
* [Stacks Project, Tag 04Y6](https://stacks.math.columbia.edu/tag/04Y6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.GroupoidPresentation

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 𝒳' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The canonical square presenting `U' = U ×_𝒳 𝒳'`: the 2-fibre product of the atlas of a
presentation with `g`, both read at the morphism universe of `𝒳`. -/
noncomputable abbrev baseChangedAtlasSquare (P : GroupoidPresentation B S hS 𝒳.val)
    (g : 𝒳' ⟶ 𝒳) : Bicategory.TwoCommSq (atlasMap P) g :=
  CatFiberedInGroupoids.RepresentablePresentation.atlasBaseChangeSquare (atlasMap P) g

/-- The base-changed atlas `U' ⟶ 𝒳'`, the projection of that square to `𝒳'`. -/
noncomputable abbrev baseChangedAtlas (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳' ⟶ 𝒳) :
    (baseChangedAtlasSquare P g).pt ⟶ 𝒳' :=
  (baseChangedAtlasSquare P g).snd

/-- The canonical square is a 2-fibre product. -/
noncomputable def isTwoFibreProduct_baseChangedAtlasSquare
    (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳' ⟶ 𝒳) :
    Bicategory.IsTwoFibreProduct (baseChangedAtlasSquare P g) :=
  CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    (atlasMap P) g

/-- For `g` representable by algebraic spaces, `U' = U ×_𝒳 𝒳'` is represented by an algebraic
space. -/
theorem isRepresentableByAlgebraicSpace_baseChangedAtlas
    (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳' ⟶ 𝒳)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom) :
    IsRepresentableByAlgebraicSpace B S hS (baseChangedAtlasSquare P g).pt :=
  isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳 (objectStack P) 𝒳'
    (atlasMap P).hom g.hom hg
    ⟨P.groupoid.objects.obj, P.groupoid.objects.property,
      ⟨StacksRepresentableCFG.EquivalenceOver.refl _⟩⟩

/-- The base-changed atlas `U' ⟶ 𝒳'` is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_baseChangedAtlas
    (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳' ⟶ 𝒳)
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsRepresentableByAlgebraicSpaces B S hS (baseChangedAtlas P g).hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, u, u} B S hS (objectStack P) 𝒳 𝒳'
    (atlasMap P) g (baseChangedAtlasSquare P g).swap
    (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_baseChangedAtlasSquare P g))
    (isRepresentableByAlgebraicSpaces_atlasMap P h𝒳)

/-- The base-changed atlas `U' ⟶ 𝒳'` is smooth. -/
theorem isRelativelySmooth_baseChangedAtlas
    (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳' ⟶ 𝒳)
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsRelativelySmooth B S hS (baseChangedAtlas P g) :=
  ⟨isRepresentableByAlgebraicSpaces_baseChangedAtlas P g h𝒳,
    hasRelativeProperty_baseChange.{u, u, u, u} B S hS
      (Space.smoothMorphismProperty B S hS) (objectStack P) 𝒳 𝒳'
      (atlasMap P) g (baseChangedAtlasSquare P g).swap
      (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_baseChangedAtlasSquare P g))
      (isRepresentableByAlgebraicSpaces_atlasMap P h𝒳)
      (isRelativelySmooth_atlasMap P h𝒳).2⟩

/-- The base-changed atlas `U' ⟶ 𝒳'` is surjective. -/
theorem isRelativelySurjective_baseChangedAtlas
    (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳' ⟶ 𝒳)
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) (baseChangedAtlas P g)
      (isRepresentableByAlgebraicSpaces_baseChangedAtlas P g h𝒳) :=
  hasRelativeProperty_baseChange.{u, u, u, u} B S hS
    (Space.surjectiveMorphismProperty B S hS) (objectStack P) 𝒳 𝒳'
    (atlasMap P) g (baseChangedAtlasSquare P g).swap
    (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_baseChangedAtlasSquare P g))
    (isRepresentableByAlgebraicSpaces_atlasMap P h𝒳)
    (isRelativelySurjective_atlasMap P h𝒳)

/-- For `g` representable by algebraic spaces and `𝒳'` algebraic, the self-intersection
`U' ×_{𝒳'} U'` of the base-changed atlas is represented by an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_baseChangedRelation
    (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳' ⟶ 𝒳)
    (h𝒳' : IsAlgebraicStack.{u, w} B S hS 𝒳'.val)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom) :
    IsRepresentableByAlgebraicSpace B S hS
      (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
        (baseChangedAtlas P g).hom) :=
  SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack B S hS
    (baseChangedAtlasSquare P g).pt 𝒳' (baseChangedAtlas P g).hom h𝒳'
    (isRepresentableByAlgebraicSpace_baseChangedAtlas P g hg)

section Construction

variable {U' R' : AlgebraicSpaces B S hS}
variable (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳' ⟶ 𝒳)
variable (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
variable (h𝒳' : IsAlgebraicStack.{u, w} B S hS 𝒳'.val)
variable
  (eU' : StacksRepresentableCFG.EquivalenceOver
    (baseChangedAtlasSquare P g).pt.val.p (presheafOfCategories (U'.obj ⋙ typeToCat)).p)
  (eR' : StacksRepresentableCFG.EquivalenceOver
    (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
      (baseChangedAtlas P g).hom).val.p
    (presheafOfCategories (R'.obj ⋙ typeToCat)).p)

/-- Given chosen representing spaces `U'` of `U ×_𝒳 𝒳'` and `R'` of `U' ×_{𝒳'} U'`, the
presentation of `𝒳'` by the groupoid in algebraic spaces on `U'` and `R'` together with the
equivalence `[U'/R'] ≃ 𝒳'`. -/
noncomputable def baseChangedPresentation : GroupoidPresentation B S hS 𝒳'.val where
  groupoid := GroupoidInAlgebraicSpaces.changeBase
    ((isTerminal_baseSpace B S hS).from
      (SelfIntersection.selfIntersectionPresentation eU' eR' h𝒳').base)
    (SelfIntersection.selfIntersectionPresentation eU' eR' h𝒳').groupoid
  smooth :=
    ⟨SelfIntersection.isSmooth_selfIntersectionPresentation_source
        (𝒰 := (baseChangedAtlasSquare P g).pt) (𝒳 := 𝒳') (F := baseChangedAtlas P g)
        (U := U') (R := R') eU' eR'
        (isRepresentableByAlgebraicSpaces_baseChangedAtlas P g h𝒳)
        (isRelativelySmooth_baseChangedAtlas P g h𝒳).2 h𝒳',
      SelfIntersection.isSmooth_selfIntersectionPresentation_target
        (𝒰 := (baseChangedAtlasSquare P g).pt) (𝒳 := 𝒳') (F := baseChangedAtlas P g)
        (U := U') (R := R') eU' eR'
        (isRepresentableByAlgebraicSpaces_baseChangedAtlas P g h𝒳)
        (isRelativelySmooth_baseChangedAtlas P g h𝒳).2 h𝒳'⟩
  equivalence :=
    (SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth
      (𝒰 := (baseChangedAtlasSquare P g).pt) (𝒳 := 𝒳') (f := baseChangedAtlas P g)
      (U := U') (R := R') eU' eR' h𝒳'
      (isRelativelySmooth_baseChangedAtlas P g h𝒳).2
      (isRelativelySurjective_baseChangedAtlas P g h𝒳)).choose

/-- The object space of the base-changed presentation is the chosen representing space of
`U ×_𝒳 𝒳'`. -/
@[simp] theorem baseChangedPresentation_objects :
    (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid.objects = U' := rfl

/-- The arrow space of the base-changed presentation is the chosen representing space of
`U' ×_{𝒳'} U'`. -/
@[simp] theorem baseChangedPresentation_arrows :
    (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid.arrows = R' := rfl

end Construction

end AlgebraicGeometry.Stack.GroupoidPresentation

end
