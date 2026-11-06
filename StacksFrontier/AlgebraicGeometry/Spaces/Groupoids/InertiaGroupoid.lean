module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.LoopGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.InvariantStabilizerLocus
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# The inertia groupoid of a groupoid in algebraic spaces

Let `B → S` and let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B` (Stacks 044Q
(1)), with identity `e` and inverse `i`, and let `G/U` be its stabilizer group algebraic space
(Stacks 0448). **Stacks 06PB** constructs out of this a second groupoid in algebraic spaces over
`B`, with object space `G` and arrow space

```
R' = R ×_{s, U} G,
```

the structure morphisms being

```
s' : R' → G,   (r, g) ↦ g
t' : R' → G,   (r, g) ↦ c(r, c(g, i(r)))
c' : R' ×_{s', G, t'} R' → R',   ((r₁, g₁), (r₂, g₂)) ↦ (c(r₁, r₂), g₂).
```

This file builds that groupoid, `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaGroupoid`,
and identifies each of its three structure morphisms on generalized points.

The second coordinate of `c'` is `g₂`, not the `g₁` displayed in the Stacks text: a point of the
domain of `c'` has `g₁ = t'(r₂, g₂)`, which lies over `t(r₂)`, while the stabilizer coordinate of
a point of `R' = R ×_{s, U} G` lies over the source of its arrow coordinate, here
`s(c(r₁, r₂)) = s(r₂)`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaArrows`: the arrow space `R'`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaSourceMap`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaTargetMap` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaCompositionMap`: the morphisms `s'`, `t'`
  and `c'`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaGroupoid`: the groupoid
  `(G, R', s', t', c')`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaForgetful`: the morphism of groupoids
  `(G, R', s', t', c') ⟶ (U, R, s, t, c)` given by the structure morphism `G → U` on objects and
  by `(r, g) ↦ r` on arrows.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaSourceMap_app`: `s'(r, g) = g`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaTargetMap_conjugate_formula`: the arrow
  underlying `t'(r, g)` is `c(r, c(g, i(r)))`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaCompose_original` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaCompose_source`: the two coordinates of
  `c'`, namely `c(r₁, r₂)` and `g₂`.

## References

* [Stacks Project, Tag 06PB](https://stacks.math.columbia.edu/tag/06PB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

attribute [local implicit_reducible] toGroupoidInFunctors AlgebraicSpaces.fiberProduct

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this). -/
local instance hasPullbacks_presheaf_inertiaGroupoid :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasLimit_cospan_types_inertiaGroupoid
    {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

local instance (priority := high) hasPullback_presheaf_inertiaGroupoid
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- An arrow of the inertia presentation is an arrow of the original groupoid together with a
loop at its source: the space `R' = R ×_{s, U} G`. -/
noncomputable abbrev inertiaArrows (G : GroupoidInAlgebraicSpaces C S hS B) :
    AlgebraicSpaces C S hS :=
  AlgebraicSpaces.fiberProduct C S hS G.source (stabilizerToObjects G)

/-- The projection `R' ⟶ R`, `(r, g) ↦ r`, onto the arrow coordinate. -/
noncomputable def inertiaOriginalArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaArrows G).obj ⟶ G.arrows.obj :=
  pullback.fst G.source.hom (stabilizerToObjects G).hom

/-- The morphism `R' ⟶ R`, `(r, g) ↦ g`, sending a point to its stabilizer loop viewed as an
arrow of the groupoid. -/
noncomputable def inertiaLoopArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaArrows G).obj ⟶ G.arrows.obj :=
  pullback.snd G.source.hom (stabilizerToObjects G).hom ≫
    stabilizerArrow G

/-- On generalized points, the source of the arrow coordinate is the image in `U` of the
stabilizer coordinate. -/
private lemma inertiaOriginalArrow_source_app_eq
    (G : GroupoidInAlgebraicSpaces C S hS B) (V : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj V) :
    G.toGroupoidInFunctors.source.app V ((inertiaOriginalArrow G).app V q) =
      (stabilizerToObjects G).hom.app V
        ((pullback.snd G.source.hom (stabilizerToObjects G).hom).app V q) :=
  congrArg (fun f => (f.app V) q)
    (pullback.condition (f := G.source.hom) (g := (stabilizerToObjects G).hom))

/-- For `(r, g)` in `R'`, the source of `r` is the target of the loop `g`. -/
lemma inertiaArrows_composable
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaOriginalArrow G ≫ G.source.hom = inertiaLoopArrow G ≫ G.target.hom := by
  ext V q
  exact (inertiaOriginalArrow_source_app_eq G V q).trans
    (stabilizerArrow_target_app G V _).symm

/-- For `(r, g)` in `R'`, the loop `g` and the arrow `r` have the same source. -/
lemma inertiaLoopArrow_source
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaLoopArrow G ≫ G.source.hom = inertiaOriginalArrow G ≫ G.source.hom := by
  ext V q
  exact (stabilizerArrow_source_app G V _).trans
    (inertiaOriginalArrow_source_app_eq G V q).symm

/-- The morphism `R' ⟶ R`, `(r, g) ↦ i(r)`. -/
noncomputable def inertiaInverseArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaArrows G).obj ⟶ G.arrows.obj :=
  inertiaOriginalArrow G ≫ groupoidInverse G

/-- On generalized points, `inertiaInverseArrow` is the inverse of the arrow coordinate. -/
lemma inertiaInverseArrow_app
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj T) :
    (inertiaInverseArrow G).app T q =
      Deformation.inverseArrow G.toGroupoidInFunctors T
        ((inertiaOriginalArrow G).app T q) := by
  show (groupoidInverse G).app T ((inertiaOriginalArrow G).app T q) = _
  rw [groupoidInverse_app]

/-- The source of `i(r)` is the target of `r`. -/
lemma inertiaInverseArrow_source
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaInverseArrow G ≫ G.source.hom = inertiaOriginalArrow G ≫ G.target.hom := by
  show (inertiaOriginalArrow G ≫ groupoidInverse G) ≫ G.source.hom = _
  rw [Category.assoc, groupoidInverse_source]

/-- The target of `i(r)` is the source of `r`. -/
lemma inertiaInverseArrow_target
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaInverseArrow G ≫ G.target.hom = inertiaOriginalArrow G ≫ G.source.hom := by
  show (inertiaOriginalArrow G ≫ groupoidInverse G) ≫ G.target.hom = _
  rw [Category.assoc, groupoidInverse_target]

/-- For `(r, g)` in `R'`, the loop `g` and the arrow `i(r)` are composable. -/
lemma inertiaLoopArrow_inv_composable
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaLoopArrow G ≫ G.source.hom = inertiaInverseArrow G ≫ G.target.hom := by
  rw [inertiaLoopArrow_source, inertiaInverseArrow_target]

/-- The morphism `R' ⟶ R`, `(r, g) ↦ c(r, c(g, i(r)))`. -/
noncomputable def inertiaConjugateArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaArrows G).obj ⟶ G.arrows.obj :=
  groupoidCompose G (inertiaOriginalArrow G)
    (groupoidCompose G (inertiaLoopArrow G) (inertiaInverseArrow G)
      (inertiaLoopArrow_inv_composable G))
    (by
      rw [inertiaArrows_composable]
      exact (groupoidCompose_target G (inertiaLoopArrow G) (inertiaInverseArrow G)
        (inertiaLoopArrow_inv_composable G)).symm)

/-- The source of `c(r, c(g, i(r)))` is the target of `r`. -/
lemma inertiaConjugateArrow_source
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaConjugateArrow G ≫ G.source.hom =
      inertiaOriginalArrow G ≫ G.target.hom := by
  unfold inertiaConjugateArrow
  rw [groupoidCompose_source, groupoidCompose_source, inertiaInverseArrow_source]

/-- The target of `c(r, c(g, i(r)))` is the target of `r`. -/
lemma inertiaConjugateArrow_target
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaConjugateArrow G ≫ G.target.hom =
      inertiaOriginalArrow G ≫ G.target.hom := by
  unfold inertiaConjugateArrow
  rw [groupoidCompose_target]

/-- The arrow space `R'` as an object over `U` through the target of the arrow coordinate. -/
@[implicit_reducible]
noncomputable def inertiaTargetLoopOver
    (G : GroupoidInAlgebraicSpaces C S hS B) : Over G.objects.obj :=
  Over.mk (inertiaOriginalArrow G ≫ G.target.hom)

/-- The conjugate loop `c(r, c(g, i(r)))` as a morphism over `U` to the stabilizer. -/
noncomputable def inertiaTargetStabilizer
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaTargetLoopOver G ⟶ stabilizer G :=
  stabilizerFromLoop G (inertiaConjugateArrow G)
    (inertiaConjugateArrow_source G) (inertiaConjugateArrow_target G)

/-- The target morphism `t' : R' ⟶ G`, `(r, g) ↦ c(r, c(g, i(r)))`. -/
noncomputable def inertiaTargetMap
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaArrows G ⟶ stabilizerOverBase G :=
  ObjectProperty.homMk (inertiaTargetStabilizer G).left

/-- The arrow underlying `inertiaTargetStabilizer G` is `inertiaConjugateArrow G`. -/
lemma inertiaTargetStabilizer_arrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaTargetStabilizer G).left ≫ stabilizerArrow G =
      inertiaConjugateArrow G := by
  simp only [inertiaTargetStabilizer, stabilizerFromLoop, Over.homMk_left]
  show pullback.lift (inertiaConjugateArrow G)
      (inertiaOriginalArrow G ≫ G.target.hom) _ ≫
      pullback.fst (sourceTarget G).hom (diagonal G).hom = _
  exact pullback.lift_fst _ _ _

/-- On generalized points, the arrow underlying `inertiaTargetStabilizer G` is
`inertiaConjugateArrow G`. -/
lemma inertiaTargetStabilizer_arrow_app
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj T) :
    (stabilizerArrow G).app T
      ((inertiaTargetStabilizer G).left.app T q) =
        (inertiaConjugateArrow G).app T q := by
  simpa only [NatTrans.comp_app, CategoryTheory.comp_apply] using
    congrArg (fun f => (f.app T) q) (inertiaTargetStabilizer_arrow G)

/-- On generalized points, `inertiaConjugateArrow G` at `(r, g)` is the composite
`c(r, c(g, i(r)))`. -/
lemma inertiaTargetStabilizer_conjugate_formula
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj T) :
    let K := G.toGroupoidInFunctors
    let r : K.arrows.obj T := (inertiaOriginalArrow G).app T q
    let g := (inertiaLoopArrow G).app T q
    let h := (inertiaConjugateArrow G).app T q
    let i := Deformation.inverseArrow K T r
    ∃ (w₁ : K.source.app T g = K.target.app T i),
      ∃ (w₂ : K.source.app T r = K.target.app T (K.compose T g i w₁)),
        h = K.compose T r (K.compose T g i w₁) w₂ := by
  dsimp
  let K := G.toGroupoidInFunctors
  let r : K.arrows.obj T := (inertiaOriginalArrow G).app T q
  let g := (inertiaLoopArrow G).app T q
  let i := Deformation.inverseArrow K T r
  have w₁ : K.source.app T g = K.target.app T i :=
    (congrArg (fun f => (f.app T) q) (inertiaLoopArrow_source G)).trans
      (Deformation.inverseArrow_target G.toGroupoidInFunctors T r).symm
  have hrg : K.source.app T r = K.target.app T g :=
    congrArg (fun f => (f.app T) q) (inertiaArrows_composable G)
  let inner := groupoidCompose G (inertiaLoopArrow G) (inertiaInverseArrow G)
    (inertiaLoopArrow_inv_composable G)
  have hinnerVal : inner.app T q = K.compose T g i w₁ := by
    simpa only [inertiaInverseArrow_app] using groupoidCompose_eval G (inertiaLoopArrow G)
      (inertiaInverseArrow G) (inertiaLoopArrow_inv_composable G) T q
  have hinner : K.target.app T (K.compose T g i w₁) = K.target.app T g := by
    rw [← hinnerVal]
    exact congrArg (fun f => (f.app T) q) (groupoidCompose_target G (inertiaLoopArrow G)
      (inertiaInverseArrow G) (inertiaLoopArrow_inv_composable G))
  have w₂ : K.source.app T r = K.target.app T (K.compose T g i w₁) := hrg.trans hinner.symm
  refine ⟨w₁, w₂, ?_⟩
  have houter : (inertiaConjugateArrow G).app T q = K.compose T r (inner.app T q) _ :=
    groupoidCompose_eval G _ _ _ T q
  simp only [hinnerVal, K] at houter
  exact houter

/-- On generalized points, `t'` is given by `inertiaTargetStabilizer G`. -/
lemma inertiaTargetMap_app
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj T) :
    (inertiaTargetMap G).hom.app T q = (inertiaTargetStabilizer G).left.app T q := rfl

/-- The source morphism `s' : R' ⟶ G`, `(r, g) ↦ g`. -/
noncomputable def inertiaSourceMap
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaArrows G ⟶ stabilizerOverBase G :=
  ObjectProperty.homMk (pullback.snd G.source.hom (stabilizerToObjects G).hom)

/-- On generalized points, `s'(r, g) = g`. -/
lemma inertiaSourceMap_app
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj T) :
    (inertiaSourceMap G).hom.app T q =
      (pullback.snd G.source.hom (stabilizerToObjects G).hom).app T q := rfl

/-- The image of `s'(r, g)` in `U` is the source of `r`. -/
lemma inertiaSourceMap_toObjects
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaSourceMap G).hom ≫ (stabilizerToObjects G).hom =
      inertiaOriginalArrow G ≫ G.source.hom := by
  ext T q
  exact (inertiaOriginalArrow_source_app_eq G T q).symm

/-- The image of `t'(r, g)` in `U` is the target of `r`. -/
lemma inertiaTargetMap_toObjects
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaTargetMap G).hom ≫ (stabilizerToObjects G).hom =
      inertiaOriginalArrow G ≫ G.target.hom := by
  show (inertiaTargetStabilizer G).left ≫ (stabilizer G).hom =
    inertiaOriginalArrow G ≫ G.target.hom
  simpa only [inertiaTargetLoopOver, Over.mk_hom] using
    (inertiaTargetStabilizer G).w

/-- The structure morphism `G ⟶ B` of the stabilizer. -/
noncomputable def inertiaObjectsToBase
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    stabilizerOverBase G ⟶ B :=
  stabilizerToObjects G ≫ G.objectsToBase

/-- The structure morphism `R' ⟶ B`, through the arrow coordinate. -/
noncomputable def inertiaArrowsToBase
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaArrows G ⟶ B :=
  ObjectProperty.homMk (inertiaOriginalArrow G ≫ G.arrowsToBase.hom)

/-- The functor of composable pairs `R' ×_{s', G, t'} R'` of the inertia groupoid. -/
noncomputable abbrev inertiaComposablePairs
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  (AlgebraicSpaces.fiberProduct C S hS (inertiaSourceMap G) (inertiaTargetMap G)).obj

/-- The arrow coordinate `r₁` of a composable pair `((r₁, g₁), (r₂, g₂))`. -/
noncomputable def inertiaCompLeft
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaComposablePairs G ⟶ G.arrows.obj :=
  pullback.fst (inertiaSourceMap G).hom (inertiaTargetMap G).hom ≫ inertiaOriginalArrow G

/-- The arrow coordinate `r₂` of a composable pair `((r₁, g₁), (r₂, g₂))`. -/
noncomputable def inertiaCompRight
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaComposablePairs G ⟶ G.arrows.obj :=
  pullback.snd (inertiaSourceMap G).hom (inertiaTargetMap G).hom ≫ inertiaOriginalArrow G

/-- The stabilizer coordinate `g₂` of a composable pair `((r₁, g₁), (r₂, g₂))`. -/
noncomputable def inertiaCompSource
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaComposablePairs G ⟶
      (stabilizerOverBase G).obj :=
  pullback.snd (inertiaSourceMap G).hom (inertiaTargetMap G).hom ≫
    (inertiaSourceMap G).hom

/-- For a composable pair `((r₁, g₁), (r₂, g₂))`, the arrows `r₁` and `r₂` are composable. -/
lemma inertiaCompLeftComposable
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaCompLeft G ≫ G.source.hom = inertiaCompRight G ≫ G.target.hom := by
  let p := pullback.fst (inertiaSourceMap G).hom (inertiaTargetMap G).hom
  let q := pullback.snd (inertiaSourceMap G).hom (inertiaTargetMap G).hom
  let f := p ≫ inertiaOriginalArrow G
  let g := q ≫ inertiaOriginalArrow G
  have hw : f ≫ G.source.hom = g ≫ G.target.hom := by
    have hsource := inertiaSourceMap_toObjects G
    have htarget := inertiaTargetMap_toObjects G
    have hfg := congrArg (fun k => k ≫ (stabilizerToObjects G).hom)
      (pullback.condition (f := (inertiaSourceMap G).hom)
        (g := (inertiaTargetMap G).hom))
    calc
      f ≫ G.source.hom = p ≫ (inertiaOriginalArrow G ≫ G.source.hom) := by
        simp [f, Category.assoc]
      _ = p ≫ ((inertiaSourceMap G).hom ≫ (stabilizerToObjects G).hom) :=
        congrArg (fun k => p ≫ k) hsource.symm
      _ = q ≫ ((inertiaTargetMap G).hom ≫ (stabilizerToObjects G).hom) := by
        simpa only [Category.assoc] using hfg
      _ = q ≫ (inertiaOriginalArrow G ≫ G.target.hom) :=
        congrArg (fun k => q ≫ k) htarget
      _ = g ≫ G.target.hom := by simp [g, Category.assoc]
  show (pullback.fst (inertiaSourceMap G).hom (inertiaTargetMap G).hom ≫
      inertiaOriginalArrow G) ≫ G.source.hom =
    (pullback.snd (inertiaSourceMap G).hom (inertiaTargetMap G).hom ≫
      inertiaOriginalArrow G) ≫ G.target.hom
  exact hw

/-- The composite `c(r₁, r₂)` of a composable pair `((r₁, g₁), (r₂, g₂))`. -/
noncomputable def inertiaCompResult
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaComposablePairs G ⟶ G.arrows.obj :=
  groupoidCompose G (inertiaCompLeft G) (inertiaCompRight G)
    (inertiaCompLeftComposable G)

/-- The source of `c(r₁, r₂)` is the image of `g₂` in `U`. -/
lemma inertiaCompResult_source
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    inertiaCompResult G ≫ G.source.hom =
      inertiaCompSource G ≫ (stabilizerToObjects G).hom := by
  rw [inertiaCompResult, groupoidCompose_source]
  show (pullback.snd (inertiaSourceMap G).hom (inertiaTargetMap G).hom ≫
      inertiaOriginalArrow G) ≫ G.source.hom =
    (pullback.snd (inertiaSourceMap G).hom (inertiaTargetMap G).hom ≫
      (inertiaSourceMap G).hom) ≫ (stabilizerToObjects G).hom
  rw [Category.assoc, ← inertiaSourceMap_toObjects, ← Category.assoc]

/-- The composition `c' : R' ×_{s', G, t'} R' ⟶ R'`,
`((r₁, g₁), (r₂, g₂)) ↦ (c(r₁, r₂), g₂)`. -/
noncomputable def inertiaCompositionMap
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    AlgebraicSpaces.fiberProduct C S hS (inertiaSourceMap G) (inertiaTargetMap G) ⟶
      inertiaArrows G :=
  ObjectProperty.homMk (pullback.lift (inertiaCompResult G) (inertiaCompSource G)
    (inertiaCompResult_source G))

/-- The arrow coordinate of `c'` is `c(r₁, r₂)`. -/
lemma inertiaCompositionMap_originalArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaCompositionMap G).hom ≫ inertiaOriginalArrow G = inertiaCompResult G := by
  show pullback.lift (inertiaCompResult G) (inertiaCompSource G)
      (inertiaCompResult_source G) ≫
      pullback.fst G.source.hom (stabilizerToObjects G).hom = inertiaCompResult G
  exact pullback.lift_fst _ _ _

/-- The stabilizer coordinate of `c'` is `g₂`. -/
lemma inertiaCompositionMap_sourceStabilizer
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaCompositionMap G).hom ≫
        pullback.snd G.source.hom (stabilizerToObjects G).hom = inertiaCompSource G := by
  show pullback.lift (inertiaCompResult G) (inertiaCompSource G)
      (inertiaCompResult_source G) ≫
      pullback.snd G.source.hom (stabilizerToObjects G).hom = inertiaCompSource G
  exact pullback.lift_snd _ _ _

/-- The value of `R'` at `T` as the pullback of types of the values at `T` of `s` and of
`G ⟶ U`. -/
noncomputable def inertiaArrowObjIso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    (inertiaArrows G).obj.obj T ≅
      CategoryTheory.Limits.Types.PullbackObj
        (G.source.hom.app T) ((stabilizerToObjects G).hom.app T) :=
  CategoryTheory.Limits.pullbackObjIso G.source.hom
    (stabilizerToObjects G).hom T ≪≫
      CategoryTheory.Limits.Types.pullbackIsoPullback
        (G.source.hom.app T) ((stabilizerToObjects G).hom.app T)

/-- The second component of `inertiaArrowObjIso G T` is the stabilizer coordinate. -/
lemma inertiaArrowObjIso_hom_snd
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj T) :
    ((inertiaArrowObjIso G T).hom q).1.2 =
      (pullback.snd G.source.hom (stabilizerToObjects G).hom).app T q := by
  show ((pullbackObjIso G.source.hom (stabilizerToObjects G).hom T).hom ≫
      pullback.snd (G.source.hom.app T) ((stabilizerToObjects G).hom.app T)) q =
        (pullback.snd G.source.hom (stabilizerToObjects G).hom).app T q
  rw [CategoryTheory.Limits.pullbackObjIso_hom_comp_snd]

/-- The first component of `inertiaArrowObjIso G T` is the arrow coordinate. -/
lemma inertiaArrowObjIso_hom_fst
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj T) :
    ((inertiaArrowObjIso G T).hom q).1.1 =
      (pullback.fst G.source.hom (stabilizerToObjects G).hom).app T q := by
  show ((pullbackObjIso G.source.hom (stabilizerToObjects G).hom T).hom ≫
      pullback.fst (G.source.hom.app T) ((stabilizerToObjects G).hom.app T)) q =
        (pullback.fst G.source.hom (stabilizerToObjects G).hom).app T q
  rw [CategoryTheory.Limits.pullbackObjIso_hom_comp_fst]

/-- The stabilizer coordinate of the inverse of `inertiaArrowObjIso G T` is the second
component. -/
lemma inertiaArrowObjIso_snd
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : CategoryTheory.Limits.Types.PullbackObj
      (G.source.hom.app T) ((stabilizerToObjects G).hom.app T)) :
    (pullback.snd G.source.hom (stabilizerToObjects G).hom).app T
        ((inertiaArrowObjIso G T).inv q) = q.1.2 := by
  have h₁ := congrArg (fun f => f ((CategoryTheory.Limits.Types.pullbackIsoPullback
      (G.source.hom.app T) ((stabilizerToObjects G).hom.app T)).inv q))
    (CategoryTheory.Limits.pullbackObjIso_inv_comp_snd
      G.source.hom (stabilizerToObjects G).hom T)
  have h₂ := congrArg (fun f => f q)
    (CategoryTheory.Limits.Types.pullbackIsoPullback_inv_snd
      (G.source.hom.app T) ((stabilizerToObjects G).hom.app T))
  show (pullback.snd G.source.hom (stabilizerToObjects G).hom).app T
      ((inertiaArrowObjIso G T).inv q) = q.1.2
  exact h₁.trans h₂

/-- The arrow coordinate of the inverse of `inertiaArrowObjIso G T` is the first component. -/
lemma inertiaArrowObjIso_fst
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : CategoryTheory.Limits.Types.PullbackObj
      (G.source.hom.app T) ((stabilizerToObjects G).hom.app T)) :
    (pullback.fst G.source.hom (stabilizerToObjects G).hom).app T
        ((inertiaArrowObjIso G T).inv q) = q.1.1 := by
  have h₁ := congrArg (fun f => f ((CategoryTheory.Limits.Types.pullbackIsoPullback
      (G.source.hom.app T) ((stabilizerToObjects G).hom.app T)).inv q))
    (CategoryTheory.Limits.pullbackObjIso_inv_comp_fst
      G.source.hom (stabilizerToObjects G).hom T)
  have h₂ := congrArg (fun f => f q)
    (CategoryTheory.Limits.Types.pullbackIsoPullback_inv_fst
      (G.source.hom.app T) ((stabilizerToObjects G).hom.app T))
  show (pullback.fst G.source.hom (stabilizerToObjects G).hom).app T
      ((inertiaArrowObjIso G T).inv q) = q.1.1
  exact h₁.trans h₂

/-- On generalized points, the source of `r` is the image in `U` of `s'(r, g)`. -/
lemma inertiaOriginalArrow_source_at
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj T) :
    G.toGroupoidInFunctors.source.app T ((inertiaOriginalArrow G).app T q) =
      (stabilizerToObjects G).hom.app T ((inertiaSourceMap G).hom.app T q) := by
  exact inertiaOriginalArrow_source_app_eq G T q

/-- On generalized points, the target of `r` is the image in `U` of `t'(r, g)`. -/
lemma inertiaOriginalArrow_target_at
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj T) :
    G.toGroupoidInFunctors.target.app T ((inertiaOriginalArrow G).app T q) =
      (stabilizerToObjects G).hom.app T ((inertiaTargetMap G).hom.app T q) := by
  have h := congrArg (fun f => (f.app T) q) (inertiaTargetMap_toObjects G)
  rw [NatTrans.comp_app, CategoryTheory.comp_apply] at h
  exact h.symm

/-- On generalized points, the arrow underlying `t'(r, g)` is `c(r, c(g, i(r)))`. -/
lemma inertiaTargetLoopArrow_at
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj T) :
    (stabilizerArrow G).app T ((inertiaTargetMap G).hom.app T q) =
      (inertiaConjugateArrow G).app T q := by
  rw [inertiaTargetMap_app]
  exact inertiaTargetStabilizer_arrow_app G T q

/-- The arrow underlying the inverse, in the evaluated groupoid at `T`, of the morphism given by
`r` is `Deformation.inverseArrow K T r`. -/
lemma inverseArrow_transport
    (K : Deformation.GroupoidInFunctors
      ((BigFppfOver C S hS)ᵒᵖ))
    (T : (BigFppfOver C S hS)ᵒᵖ)
    {x y : K.Evaluation T} (r : K.arrows.obj T)
    (hx : K.source.app T r = x) (hy : K.target.app T r = y) :
    (K.evaluationArrowEquiv T y x
      (Groupoid.inv ((K.evaluationArrowEquiv T x y).symm ⟨r, hx, hy⟩))).1 =
      Deformation.inverseArrow K T r := by
  cases hx
  cases hy
  unfold Deformation.inverseArrow
  rfl

/-- The morphism `x ⟶ y` of the pointwise inertia groupoid at `T` given by an arrow `r` from the
image of `x` to the image of `y` whose conjugation carries the loop `x` to the loop `y`. -/
noncomputable def inertiaMorphismFromArrow
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (x y : (stabilizerOverBase G).obj.obj T)
    (r : G.toGroupoidInFunctors.arrows.obj T)
    (hs : G.toGroupoidInFunctors.source.app T r =
      (stabilizerToObjects G).hom.app T x)
    (ht : G.toGroupoidInFunctors.target.app T r =
      (stabilizerToObjects G).hom.app T y)
    (hloop : (G.toGroupoidInFunctors.loopConjugationFunctor T).map
      ((G.toGroupoidInFunctors.evaluationArrowEquiv T
        ((stabilizerToObjects G).hom.app T x)
        ((stabilizerToObjects G).hom.app T y)).symm ⟨r, hs, ht⟩)
      (stabilizerToElements G T x).2 = (stabilizerToElements G T y).2) :
    @Quiver.Hom _ (pointwiseInertiaGroupoid G T).toCategory.toQuiver x y := by
  letI := pointwiseInertiaGroupoid G T
  change @InducedCategory.Hom
    ((stabilizerOverBase G).obj.obj T)
    (Functor.Elements (G.toGroupoidInFunctors.loopConjugationFunctor T))
    inferInstance (stabilizerElementsEquiv G T) x y
  refine ⟨Functor.Elements.homMk
    ((G.toGroupoidInFunctors.evaluationArrowEquiv T
      ((stabilizerToObjects G).hom.app T x)
      ((stabilizerToObjects G).hom.app T y)).symm ⟨r, hs, ht⟩) hloop⟩

/-- On generalized points, conjugation by the arrow coordinate `r` carries the loop `s'(r, g)` to
the loop `t'(r, g)`. -/
lemma inertiaConjugationMap_at
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (inertiaArrows G).obj.obj T) :
    (G.toGroupoidInFunctors.loopConjugationFunctor T).map
      ((G.toGroupoidInFunctors.evaluationArrowEquiv T
        ((stabilizerToObjects G).hom.app T
          ((inertiaSourceMap G).hom.app T q))
        ((stabilizerToObjects G).hom.app T
          ((inertiaTargetMap G).hom.app T q))).symm
        ⟨(inertiaOriginalArrow G).app T q,
          inertiaOriginalArrow_source_at G T q,
          inertiaOriginalArrow_target_at G T q⟩)
      (stabilizerToElements G T ((inertiaSourceMap G).hom.app T q)).2 =
      (stabilizerToElements G T ((inertiaTargetMap G).hom.app T q)).2 := by
  let K := G.toGroupoidInFunctors
  let x := (inertiaSourceMap G).hom.app T q
  let y := (inertiaTargetMap G).hom.app T q
  let r : K.arrows.obj T := (inertiaOriginalArrow G).app T q
  let g : K.arrows.obj T := (stabilizerArrow G).app T x
  let h : K.arrows.obj T := (stabilizerArrow G).app T y
  let _ := K.evaluationGroupoid T
  let x₀ : K.Evaluation T := (stabilizerToObjects G).hom.app T x
  let y₀ : K.Evaluation T := (stabilizerToObjects G).hom.app T y
  let f := (K.evaluationArrowEquiv T x₀ y₀).symm
      ⟨r, inertiaOriginalArrow_source_at G T q,
        inertiaOriginalArrow_target_at G T q⟩
  let a := (stabilizerToElements G T x).2
  let α := (K.evaluationArrowEquiv T x₀ x₀).symm a
  let i := Deformation.inverseArrow K T r
  obtain ⟨w₁, w₂, hformula⟩ := inertiaTargetStabilizer_conjugate_formula G T q
  have hsrc := inertiaOriginalArrow_source_at G T q
  have htgt := inertiaOriginalArrow_target_at G T q
  have hα : (K.evaluationArrowEquiv T x₀ x₀ α).1 = g := by
    show (K.evaluationArrowEquiv T x₀ x₀
      ((K.evaluationArrowEquiv T x₀ x₀).symm a)).1 = g
    calc
      _ = a.1 := congrArg Subtype.val
        (Equiv.apply_symm_apply (K.evaluationArrowEquiv T x₀ x₀) a)
      _ = g := by
        show (stabilizerArrow G).app T x =
          (stabilizerArrow G).app T x
        rfl
  have hi : (K.evaluationArrowEquiv T y₀ x₀ (Groupoid.inv f)).1 = i := by
    simpa [i, f, x₀, y₀] using inverseArrow_transport K T r hsrc htgt
  have hr : (K.evaluationArrowEquiv T x₀ y₀ f).1 = r := by
    show (K.evaluationArrowEquiv T x₀ y₀
      ((K.evaluationArrowEquiv T x₀ y₀).symm
        ⟨r, hsrc, htgt⟩)).1 = r
    exact congrArg Subtype.val
      (Equiv.apply_symm_apply (K.evaluationArrowEquiv T x₀ y₀) _)
  have hinner :
      (K.evaluationArrowEquiv T y₀ x₀ (Groupoid.inv f ≫ α)).1 =
        K.compose T g i w₁ := by
    have hcomp := K.evaluationArrowEquiv_comp T (Groupoid.inv f) α
    simpa only [hα, hi] using hcomp
  have houter :
      (K.evaluationArrowEquiv T y₀ y₀ (Groupoid.inv f ≫ α ≫ f)).1 =
        K.compose T r (K.compose T g i w₁) w₂ := by
    have hc := K.evaluationArrowEquiv_comp T (Groupoid.inv f ≫ α) f
    have hcomp : K.compose T
        (K.evaluationArrowEquiv T x₀ y₀ f).1
        (K.evaluationArrowEquiv T y₀ x₀ (Groupoid.inv f ≫ α)).1
        ((K.evaluationArrowEquiv T x₀ y₀ f).2.1.trans
          (K.evaluationArrowEquiv T y₀ x₀ (Groupoid.inv f ≫ α)).2.2.symm) =
          K.compose T r (K.compose T g i w₁) w₂ := by
      apply congrArg (K.comp.app T)
      apply Subtype.ext
      exact Prod.ext hr hinner
    simpa only [Category.assoc] using hc.trans hcomp
  apply Subtype.ext
  show (K.evaluationArrowEquiv T y₀ y₀
      (Groupoid.inv f ≫ α ≫ f)).1 = h
  rw [houter]
  have htarget := inertiaTargetLoopArrow_at G T q
  dsimp [h]
  exact (htarget.trans hformula).symm

/-- Conjugating a loop by two morphisms with the same underlying arrow and equal targets gives the
same element. -/
lemma conjugateElements_eq
    (K : Deformation.GroupoidInFunctors ((BigFppfOver C S hS)ᵒᵖ))
    (T : (BigFppfOver C S hS)ᵒᵖ)
    {x y z : K.Evaluation T} (a : K.pointwiseLoops T x)
    (f : x ⟶ y) (g : x ⟶ z) (h : y = z)
    (hr : (K.evaluationArrowEquiv T x y f).1 =
      (K.evaluationArrowEquiv T x z g).1) :
    (K.loopConjugationFunctor T).elementsMk y (K.conjugateLoopMap T f a) =
      (K.loopConjugationFunctor T).elementsMk z (K.conjugateLoopMap T g a) := by
  subst z
  have : f = g := (K.evaluationArrowEquiv T x y).injective (Subtype.ext hr)
  subst g
  rfl

/-- If `q` has stabilizer coordinate `x` and arrow coordinate the arrow underlying a morphism
`f : x ⟶ y` of the pointwise inertia groupoid, then `t'(q) = y`. -/
lemma inertiaTarget_eq_of_hom
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    {x y : (stabilizerOverBase G).obj.obj T}
    (f : @Quiver.Hom _ (pointwiseInertiaGroupoid G T).toCategory.toQuiver x y)
    (q : (inertiaArrows G).obj.obj T)
    (hs : (inertiaSourceMap G).hom.app T q = x)
    (hr : (inertiaOriginalArrow G).app T q =
      (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ f.hom.hom).1) :
    (inertiaTargetMap G).hom.app T q = y := by
  subst x
  let K := G.toGroupoidInFunctors
  let z := (inertiaTargetMap G).hom.app T q
  let a := (stabilizerToElements G T ((inertiaSourceMap G).hom.app T q)).2
  let f₀ : (stabilizerToElements G T ((inertiaSourceMap G).hom.app T q)).1 ⟶
      (stabilizerToElements G T z).1 := (K.evaluationArrowEquiv T _ _).symm
    ⟨(inertiaOriginalArrow G).app T q,
      inertiaOriginalArrow_source_at G T q, inertiaOriginalArrow_target_at G T q⟩
  have hb : (stabilizerToObjects G).hom.app T z =
      (stabilizerToObjects G).hom.app T y := by
    rw [← inertiaOriginalArrow_target_at, hr]
    exact (K.evaluationArrowEquiv T _ _ f.hom.hom).2.2
  apply (stabilizerElementsEquiv G T).injective
  show stabilizerToElements G T z = stabilizerToElements G T y
  calc
    _ = (K.loopConjugationFunctor T).elementsMk (stabilizerToElements G T z).1
        (K.conjugateLoopMap T f₀ a) :=
      congrArg Functor.Elements.mk (inertiaConjugationMap_at G T q).symm
    _ = (K.loopConjugationFunctor T).elementsMk (stabilizerToElements G T y).1
        (K.conjugateLoopMap T f.hom.hom a) :=
      conjugateElements_eq K T a f₀ f.hom.hom hb ((congrArg Subtype.val
        (Equiv.apply_symm_apply (K.evaluationArrowEquiv T _ _) _)).trans hr)
    _ = stabilizerToElements G T y := congrArg Functor.Elements.mk f.hom.map_val

/-- The point of `R'` given by a morphism `f : x ⟶ y` of the pointwise inertia groupoid: the arrow
underlying `f` together with the loop `x`. -/
noncomputable def inertiaHomArrow
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    {x y : (stabilizerOverBase G).obj.obj T}
    (f : @Quiver.Hom _ (pointwiseInertiaGroupoid G T).toCategory.toQuiver x y) :
    (inertiaArrows G).obj.obj T :=
  (inertiaArrowObjIso G T).inv
    ⟨((G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ f.hom.hom).1, x),
      (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ f.hom.hom).2.1⟩

/-- The stabilizer coordinate of `inertiaHomArrow G T f` is the source of `f`. -/
lemma inertiaHomArrow_source
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    {x y : (stabilizerOverBase G).obj.obj T}
    (f : @Quiver.Hom _ (pointwiseInertiaGroupoid G T).toCategory.toQuiver x y) :
    (inertiaSourceMap G).hom.app T (inertiaHomArrow G T f) = x :=
  inertiaArrowObjIso_snd G T _

/-- The arrow coordinate of `inertiaHomArrow G T f` is the arrow underlying `f`. -/
lemma inertiaHomArrow_original
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    {x y : (stabilizerOverBase G).obj.obj T}
    (f : @Quiver.Hom _ (pointwiseInertiaGroupoid G T).toCategory.toQuiver x y) :
    (inertiaOriginalArrow G).app T (inertiaHomArrow G T f) =
      (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ f.hom.hom).1 :=
  inertiaArrowObjIso_fst G T _

/-- Two points of `R'` with the same arrow coordinate and the same stabilizer coordinate are
equal. -/
lemma inertiaArrow_ext
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    {a b : (inertiaArrows G).obj.obj T}
    (hr : (inertiaOriginalArrow G).app T a = (inertiaOriginalArrow G).app T b)
    (hs : (inertiaSourceMap G).hom.app T a = (inertiaSourceMap G).hom.app T b) : a = b := by
  apply (show Function.Injective ((inertiaArrowObjIso G T).hom) from
    fun a b h => by simpa using congrArg ((inertiaArrowObjIso G T).inv) h)
  apply Subtype.ext
  apply Prod.ext
  · rw [inertiaArrowObjIso_hom_fst, inertiaArrowObjIso_hom_fst]
    exact hr
  · rw [inertiaArrowObjIso_hom_snd, inertiaArrowObjIso_hom_snd]
    exact hs

/-- Morphisms `x ⟶ y` of the pointwise inertia groupoid at `T` correspond to the points of `R'` at
`T` with `s'` equal to `x` and `t'` equal to `y`. -/
noncomputable def inertiaHomEquiv
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (x y : (stabilizerOverBase G).obj.obj T) :
    (@Quiver.Hom _ (pointwiseInertiaGroupoid G T).toCategory.toQuiver x y) ≃
      {q : (inertiaArrows G).obj.obj T //
        (inertiaSourceMap G).hom.app T q = x ∧
        (inertiaTargetMap G).hom.app T q = y} where
  toFun f := ⟨inertiaHomArrow G T f, inertiaHomArrow_source G T f,
    inertiaTarget_eq_of_hom G T f _ (inertiaHomArrow_source G T f)
      (inertiaHomArrow_original G T f)⟩
  invFun q := inertiaMorphismFromArrow G T x y ((inertiaOriginalArrow G).app T q.1)
    (by rw [inertiaOriginalArrow_source_at, q.2.1])
    (by rw [inertiaOriginalArrow_target_at, q.2.2])
    (by
      rcases q with ⟨q, hx, hy⟩
      cases hx
      cases hy
      exact inertiaConjugationMap_at G T q)
  left_inv f := by
    apply InducedCategory.hom_ext
    apply Functor.Elements.hom_ext
    apply (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _).injective
    apply Subtype.ext
    exact (G.toGroupoidInFunctors.evaluationArrowEquiv_symm_val T _).trans
      (inertiaHomArrow_original G T f)
  right_inv q := by
    apply Subtype.ext
    apply inertiaArrow_ext G T
    · rw [inertiaHomArrow_original]
      exact G.toGroupoidInFunctors.evaluationArrowEquiv_symm_val T _
    · exact (inertiaHomArrow_source G T _).trans q.2.1.symm

/-- The composite `c'(a, b)` of two composable points `a`, `b` of `R'` at `T`. -/
noncomputable abbrev inertiaCompose
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (inertiaArrows G).obj.obj T)
    (w : (inertiaSourceMap G).hom.app T a = (inertiaTargetMap G).hom.app T b) :=
  ((composableToPullback (inertiaSourceMap G).hom (inertiaTargetMap G).hom) ≫
    (inertiaCompositionMap G).hom).app T ⟨(a, b), w⟩

/-- The stabilizer coordinate of `c'(a, b)` is that of `b`. -/
lemma inertiaCompose_source
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (inertiaArrows G).obj.obj T)
    (w : (inertiaSourceMap G).hom.app T a = (inertiaTargetMap G).hom.app T b) :
    (inertiaSourceMap G).hom.app T (inertiaCompose G T a b w) =
      (inertiaSourceMap G).hom.app T b := by
  have h := congrArg (fun f => f.app T ⟨(a, b), w⟩)
    (congrArg (fun f => composableToPullback
      (inertiaSourceMap G).hom (inertiaTargetMap G).hom ≫ f)
      (inertiaCompositionMap_sourceStabilizer G))
  simp only [inertiaCompSource, ← Category.assoc, composableToPullback,
    pullback.lift_snd, NatTrans.comp_app, CategoryTheory.comp_apply] at h
  exact h

/-- The arrow coordinate of `c'(a, b)` is the composite of the arrow coordinates of `a` and `b`. -/
lemma inertiaCompose_original
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (inertiaArrows G).obj.obj T)
    (w : (inertiaSourceMap G).hom.app T a = (inertiaTargetMap G).hom.app T b) :
    (inertiaOriginalArrow G).app T (inertiaCompose G T a b w) =
      G.toGroupoidInFunctors.compose T
        ((inertiaOriginalArrow G).app T a) ((inertiaOriginalArrow G).app T b)
        ((inertiaOriginalArrow_source_at G T a).trans
          ((congrArg ((stabilizerToObjects G).hom.app T) w).trans
            (inertiaOriginalArrow_target_at G T b).symm)) := by
  let p := (composableToPullback (inertiaSourceMap G).hom
    (inertiaTargetMap G).hom).app T ⟨(a, b), w⟩
  have h := congrArg (fun f => f.app T p) (inertiaCompositionMap_originalArrow G)
  change (inertiaOriginalArrow G).app T (inertiaCompose G T a b w) =
    (inertiaCompResult G).app T p at h
  rw [h, inertiaCompResult, groupoidCompose_eval]
  have hfst : (inertiaCompLeft G).app T p = (inertiaOriginalArrow G).app T a := by
    show ((composableToPullback (inertiaSourceMap G).hom
      (inertiaTargetMap G).hom ≫ inertiaCompLeft G).app T ⟨(a, b), w⟩) = _
    simp only [inertiaCompLeft, ← Category.assoc, composableToPullback,
      pullback.lift_fst, NatTrans.comp_app, CategoryTheory.comp_apply]
    rfl
  have hsnd : (inertiaCompRight G).app T p = (inertiaOriginalArrow G).app T b := by
    show ((composableToPullback (inertiaSourceMap G).hom
      (inertiaTargetMap G).hom ≫ inertiaCompRight G).app T ⟨(a, b), w⟩) = _
    simp only [inertiaCompRight, ← Category.assoc, composableToPullback,
      pullback.lift_snd, NatTrans.comp_app, CategoryTheory.comp_apply]
    rfl
  congr 1

/-- The groupoid structure at `T` of the inertia groupoid: the pointwise inertia groupoid, with
its morphisms identified with points of `R'` by `inertiaHomEquiv`. -/
noncomputable def inertiaPointwiseData
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    Deformation.PointwiseGroupoid ((inertiaSourceMap G).hom.app T)
      ((inertiaTargetMap G).hom.app T)
      (fun p => inertiaCompose G T p.1.1 p.1.2 p.2) where
  groupoid := pointwiseInertiaGroupoid G T
  arrowEquiv := inertiaHomEquiv G T
  comp_eq g f := by
    let _ := pointwiseInertiaGroupoid G T
    apply inertiaArrow_ext G T
    · change (inertiaOriginalArrow G).app T (inertiaHomArrow G T (g ≫ f)) = _
      rw [inertiaHomArrow_original, inertiaCompose_original]
      change (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _
        (g.hom.hom ≫ f.hom.hom)).1 = _
      rw [G.toGroupoidInFunctors.evaluationArrowEquiv_comp]
      apply congrArg (G.toGroupoidInFunctors.comp.app T)
      apply Subtype.ext
      exact Prod.ext (inertiaHomArrow_original G T f).symm
        (inertiaHomArrow_original G T g).symm
    · change (inertiaSourceMap G).hom.app T (inertiaHomArrow G T (g ≫ f)) = _
      rw [inertiaHomArrow_source, inertiaCompose_source]
      exact (inertiaHomArrow_source G T g).symm

/-- The groupoid `(G, R', s', t', c')` in algebraic spaces over `B` built from a groupoid
`(U, R, s, t, c)` in algebraic spaces over `B`: its object space is the stabilizer `G/U`, its
arrow space is `R' = R ×_{s, U} G`, and its source, target and composition are the morphisms
`s'`, `t'` and `c'`. -/
@[stacks 06PB "the groupoid (G, R', s', t', c')"]
noncomputable def inertiaGroupoid
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    GroupoidInAlgebraicSpaces C S hS B where
  objects := stabilizerOverBase G
  arrows := inertiaArrows G
  objectsToBase := inertiaObjectsToBase G
  arrowsToBase := inertiaArrowsToBase G
  source := inertiaSourceMap G
  target := inertiaTargetMap G
  source_over := by
    apply ObjectProperty.hom_ext
    change ((inertiaSourceMap G).hom ≫ (stabilizerToObjects G).hom) ≫
      G.objectsToBase.hom = inertiaOriginalArrow G ≫ G.arrowsToBase.hom
    rw [inertiaSourceMap_toObjects, Category.assoc]
    exact congrArg (fun f => inertiaOriginalArrow G ≫ f.hom) G.source_over
  target_over := by
    apply ObjectProperty.hom_ext
    change ((inertiaTargetMap G).hom ≫ (stabilizerToObjects G).hom) ≫
      G.objectsToBase.hom = inertiaOriginalArrow G ≫ G.arrowsToBase.hom
    rw [inertiaTargetMap_toObjects, Category.assoc]
    exact congrArg (fun f => inertiaOriginalArrow G ≫ f.hom) G.target_over
  comp := inertiaCompositionMap G
  comp_over := by
    apply ObjectProperty.hom_ext
    change (inertiaCompositionMap G).hom ≫ (inertiaOriginalArrow G ≫ G.arrowsToBase.hom) = _
    rw [← Category.assoc, inertiaCompositionMap_originalArrow]
    change (pullback.lift _ _ _ ≫ G.comp.hom) ≫ G.arrowsToBase.hom = _
    rw [Category.assoc]
    have h := congrArg (fun f => f.hom) G.comp_over
    change G.comp.hom ≫ G.arrowsToBase.hom =
      pullback.fst G.source.hom G.target.hom ≫ G.arrowsToBase.hom at h
    rw [h, ← Category.assoc, pullback.lift_fst]
    rfl
  pointwiseGroupoid T := ⟨inertiaPointwiseData G T⟩

/-- The arrow of the groupoid underlying the stabilizer coordinate of `t'(r, g)` is
`c(r, c(g, i(r)))`. -/
theorem inertiaTargetMap_conjugate_formula (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (q : (inertiaArrows G).obj.obj T) :
    let K := G.toGroupoidInFunctors
    let r : K.arrows.obj T := (inertiaOriginalArrow G).app T q
    let g := (inertiaLoopArrow G).app T q
    let h := (stabilizerArrow G).app T ((inertiaTargetMap G).hom.app T q)
    let i := Deformation.inverseArrow K T r
    ∃ (w₁ : K.source.app T g = K.target.app T i),
      ∃ (w₂ : K.source.app T r = K.target.app T (K.compose T g i w₁)),
        h = K.compose T r (K.compose T g i w₁) w₂ := by
  obtain ⟨w₁, w₂, h⟩ := inertiaTargetStabilizer_conjugate_formula G T q
  exact ⟨w₁, w₂, (inertiaTargetLoopArrow_at G T q).trans h⟩

/-- The morphism of groupoids `(G, R', s', t', c') ⟶ (U, R, s, t, c)` given by `G ⟶ U` on objects
and by `(r, g) ↦ r` on arrows. -/
noncomputable def inertiaForgetful
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    GroupoidInAlgebraicSpaces.Hom (inertiaGroupoid G) G where
  toGroupoidHom := {
    mapObjects := (stabilizerToObjects G).hom
    mapArrows := inertiaOriginalArrow G
    map_source := inertiaOriginalArrow_source_at G
    map_target := inertiaOriginalArrow_target_at G
    map_comp := fun T a b w => (inertiaCompose_original G T a b w).symm
    map_id := Space.mapIdentityOfMapComp
      (G := (inertiaGroupoid G).toGroupoidInFunctors) (H := G.toGroupoidInFunctors)
      (stabilizerToObjects G).hom (inertiaOriginalArrow G)
      (inertiaOriginalArrow_source_at G) (inertiaOriginalArrow_target_at G)
      (fun T a b w => (inertiaCompose_original G T a b w).symm) }
  mapObjects_over := rfl
  mapArrows_over := rfl

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
