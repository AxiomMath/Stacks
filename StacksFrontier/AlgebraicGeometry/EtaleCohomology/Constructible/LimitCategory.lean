module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality

/-!
# The category of constructible module sheaves on a limit of schemes

Let `X = lim X_i` be a limit of a directed inverse system of quasi-compact, quasi-separated
schemes with affine transition morphisms. Stacks Tag 09YU asserts that the category of
constructible sheaves of `Λ`-modules on `X_étale` is the colimit of the categories of
constructible sheaves of `Λ`-modules on the `(X_i)_étale`, with the inverse-image functors as the
transition functors. This file sets up the vocabulary that assertion is stated in: the category
itself, the inverse-image functor on module sheaves, the comparison identifying an iterated
inverse image with the inverse image along a cone projection, and the structure recording a
colimit presentation of the category.

## Main definitions

* `AlgebraicGeometry.ConstructibleModuleSheaves` — the full subcategory of constructible module
  sheaves on a small étale site, and `AlgebraicGeometry.constructibleModuleSheafInclusion` its
  inclusion into all module sheaves.
* `AlgebraicGeometry.smallEtaleModulePullback` — inverse image of module sheaves between small
  étale sites.
* `AlgebraicGeometry.smallEtaleSheafPullbackStageComparison` — for a cone over a diagram in the
  big étale site, the comparison between inverse image along one projection followed by a
  transition map and inverse image along the other projection.
* `AlgebraicGeometry.ConstructibleModuleSheafColimit` — a colimit presentation of the category of
  constructible module sheaves on the cone point, with every transition and projection functor
  identified with étale inverse image.

## Implementation notes

The stage comparison is not chosen arbitrarily: it is the composition isomorphism
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso` of Tag 021J, transported along the equation
`c.π.app j ≫ D.map e = c.π.app i` satisfied by a cone. That is what makes the fullness assertion
of Tag 09YU a statement about a canonical map rather than about some isomorphism. It is stated for
an arbitrary coefficient category, since the set-valued and abelian-group-valued parts of Tag 09YU
need the same comparison.

In `ConstructibleModuleSheafColimit` the diagram of categories is taken in one fixed
`CategoryTheory.Cat`, so its stages are the small models `CategoryTheory.AsSmall` of the
categories of constructible sheaves rather than those categories themselves; the fields
`stageEquiv` and `limitEquiv` record the identifications, and `transitionSpec` and
`projectionSpec` pin the transition and projection functors to étale inverse image. Nothing in the
structure is a property of the colimit alone: a term of it is a presentation.

**No `@[stacks 09YU]` attribute appears in this file.** Tag 09YU's covering set consists of the
four assertions — essential surjectivity, fullness, faithfulness and the colimit — none of which is
proved here; this file is the vocabulary they are stated in.

## References

* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w r v z t

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- **Stacks 021I, base-change continuity**, in the spelling in which the source of the morphism is
an unbundled scheme contained in the site.

`AlgebraicGeometry.smallEtaleBaseChange_isContinuous` is stated for `T : B.Scheme`, so its
conclusion mentions the site `SmallEtale B T.obj T.property`; a statement about a scheme presented
as `S` together with `hS : B.Contains S` mentions `SmallEtale B S hS` instead, and instance search
cannot match the two, since that would require solving `?T.obj ≡ S` for a metavariable `?T`. This
restatement is what instance search finds for the second spelling, which is the one a cone over a
diagram in the site forces: the vertex comes with a membership proof, not as an object. -/
public instance smallEtaleBaseChange_isContinuous_of_contains {S : Scheme.{u}}
    (hS : B.Contains S) {T : B.Scheme} (f : B.obj S hS ⟶ T) :
    Functor.IsContinuous (smallEtaleBaseChange B f)
      (SmallEtale.topology B T.obj T.property) (SmallEtale.topology B S hS) :=
  smallEtaleBaseChange_isContinuous B f

section Pullback

variable (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **Stacks 09YU.** For a cone `c` over a diagram `D` of schemes in a big étale site whose vertex
the site contains, and a map `e : j ⟶ i` in the index category, the canonical comparison between
inverse image along the projection to `D.obj j` of inverse image along `D.map e`, and inverse image
along the projection to `D.obj i`.

It is the composition isomorphism of Tag 021J transported along the cone equation
`c.π.app j ≫ D.map e = c.π.app i`. -/
public def smallEtaleSheafPullbackStageComparison
    {I : Type w} [Category.{z} I] (Dg : I ⥤ B.Scheme)
    (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)
    {i j : I} (e : j ⟶ i)
    (F : Sheaf (SmallEtale.topology B (Dg.obj i).obj (Dg.obj i).property) A) :
    ((smallEtaleBaseChange B
          (ObjectProperty.homMk (c.π.app j) : B.obj c.pt hX ⟶ Dg.obj j)).sheafPullback A
        (SmallEtale.topology B (Dg.obj j).obj (Dg.obj j).property)
        (SmallEtale.topology B c.pt hX)).obj
        (((smallEtaleBaseChange B (Dg.map e)).sheafPullback A
          (SmallEtale.topology B (Dg.obj i).obj (Dg.obj i).property)
          (SmallEtale.topology B (Dg.obj j).obj (Dg.obj j).property)).obj F) ≅
      ((smallEtaleBaseChange B
        (ObjectProperty.homMk (c.π.app i) : B.obj c.pt hX ⟶ Dg.obj i)).sheafPullback A
        (SmallEtale.topology B (Dg.obj i).obj (Dg.obj i).property)
        (SmallEtale.topology B c.pt hX)).obj F := by
  have hp : (ObjectProperty.homMk (c.π.app j) : B.obj c.pt hX ⟶ Dg.obj j) ≫ Dg.map e =
      (ObjectProperty.homMk (c.π.app i) : B.obj c.pt hX ⟶ Dg.obj i) :=
    B.inclusion.map_injective (c.w e)
  exact (smallEtaleSheafPullbackCompIso B (B.obj c.pt hX) (Dg.obj j) (Dg.obj i)
      (ObjectProperty.homMk (c.π.app j)) (Dg.map e) A).app F ≪≫
    eqToIso (congrArg (fun f : B.obj c.pt hX ⟶ Dg.obj i =>
      ((smallEtaleBaseChange B f).sheafPullback A
        (SmallEtale.topology B (Dg.obj i).obj (Dg.obj i).property)
        (SmallEtale.topology B c.pt hX)).obj F) hp)

end Pullback

section Modules

variable (R : Type r) [CommRing R] [IsNoetherianRing R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]

/-- The category of constructible sheaves of `R`-modules on the small étale site of `X`, as a full
subcategory of all sheaves of `R`-modules on it. -/
public abbrev ConstructibleModuleSheaves (X : B.Scheme) :=
  (show ObjectProperty
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R))
    from IsConstructibleModuleSheaf B X R).FullSubcategory

/-- The inclusion of constructible module sheaves into all module sheaves. -/
public abbrev constructibleModuleSheafInclusion (X : B.Scheme) :
    ConstructibleModuleSheaves B R X ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R) :=
  (show ObjectProperty
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R))
    from IsConstructibleModuleSheaf B X R).ι

/-- Inverse image of sheaves of `R`-modules along a morphism of a big étale site. -/
public abbrev smallEtaleModulePullback {X Y : B.Scheme} (f : X ⟶ Y) :=
  (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{w} R)
    (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)

/-- **Stacks 09YU, constructible modules.** A colimit presentation of the category of constructible
module sheaves on the vertex of a cone over a directed inverse system, with every transition and
projection functor identified with étale inverse image.

The diagram of categories lands in one `CategoryTheory.Cat`, so its values are the small models of
the categories of constructible sheaves; `stageEquiv` and `limitEquiv` are the identifications, and
`transitionSpec`, `transitionIso`, `projectionSpec`, `projectionIso` say that the diagram's
transition maps and the cocone's legs are the inverse-image functors. -/
public structure ConstructibleModuleSheafColimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt) where
  /-- The diagram of categories of constructible module sheaves at the finite stages. -/
  diagram : I ⥤ Cat.{max (u + 1) (w + 1) r + 1, max (u + 1) (w + 1) r + 1}
  /-- Each value of the diagram is the small model of the category at that stage. -/
  stageEquiv : ∀ i : I,
    diagram.obj i ≌ AsSmall.{max (u + 1) w,
      max (u + 1) w, max (u + 1) (w + 1) r}
      (ConstructibleModuleSheaves B R (Dg.obj (op i)))
  /-- The cocone presenting the colimit. -/
  cocone : Cocone diagram
  /-- The vertex of the cocone is the small model of the category at the cone point. -/
  limitEquiv : cocone.pt ≌
    AsSmall.{max (u + 1) w,
      max (u + 1) w, max (u + 1) (w + 1) r}
      (ConstructibleModuleSheaves B R (B.obj c.pt hX))
  /-- The transition functor between two stages. -/
  transitionPullback : ∀ (i j : I) (_h : i ≤ j),
    ConstructibleModuleSheaves B R (Dg.obj (op i)) ⥤
      ConstructibleModuleSheaves B R (Dg.obj (op j))
  /-- The transition functor is étale inverse image. -/
  transitionSpec : ∀ (i j : I) (h : i ≤ j),
    transitionPullback i j h ⋙ constructibleModuleSheafInclusion B R (Dg.obj (op j)) ≅
      constructibleModuleSheafInclusion B R (Dg.obj (op i)) ⋙
        smallEtaleModulePullback B R (Dg.map (homOfLE h).op)
  /-- The diagram's transition map is the transition functor. -/
  transitionIso : ∀ (i j : I) (h : i ≤ j),
    (diagram.map (homOfLE h)).toFunctor ⋙ (stageEquiv j).functor ⋙ AsSmall.down ≅
      (stageEquiv i).functor ⋙ AsSmall.down ⋙ transitionPullback i j h
  /-- The projection functor from a stage to the cone point. -/
  projectionPullback : ∀ i : I,
    ConstructibleModuleSheaves B R (Dg.obj (op i)) ⥤
      ConstructibleModuleSheaves B R (B.obj c.pt hX)
  /-- The projection functor is étale inverse image along the cone projection. -/
  projectionSpec : ∀ i : I,
    projectionPullback i ⋙ constructibleModuleSheafInclusion B R (B.obj c.pt hX) ≅
      constructibleModuleSheafInclusion B R (Dg.obj (op i)) ⋙
        smallEtaleModulePullback B R
          (ObjectProperty.homMk (c.π.app (op i)) : B.obj c.pt hX ⟶ Dg.obj (op i))
  /-- The cocone's leg at a stage is the projection functor. -/
  projectionIso : ∀ i : I,
    (cocone.ι.app i).toFunctor ⋙ limitEquiv.functor ⋙ AsSmall.down ≅
      (stageEquiv i).functor ⋙ AsSmall.down ⋙ projectionPullback i
  /-- The cocone is a colimit. -/
  isColimit : IsColimit cocone

end Modules

end AlgebraicGeometry

end
