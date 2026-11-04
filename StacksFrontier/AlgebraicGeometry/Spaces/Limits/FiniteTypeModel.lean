module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage

/-!
# Finite type models over a limit of Noetherian algebraic spaces

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces
over a scheme `S` with affine transition morphisms, which is
`AlgebraicGeometry.Space.NoetherianLimitSystem` of Stacks 0CP6, and let `X ⟶ B` be a
quasi-separated morphism of finite type. The Stacks project attaches to this situation a
diagram

```
X ⟶ W
↓    ↓
B ⟶ B_i
```

in which `W ⟶ B_i` is of finite type and the induced morphism `X ⟶ B ×_{B_i} W` is a closed
immersion. For each later stage `i' ≥ i` the scheme-theoretic image `X_{i'}` of
`X ⟶ B_{i'} ×_{B_i} W` is then defined, and these form an inverse system over the stages above
`i` carrying a canonical cone with vertex `X`.

This file introduces the diagram as a bundled structure and builds that inverse system and its
cone. It is the algebraic-space analogue of
`StacksFrontier/AlgebraicGeometry/Limits/DescendingMorphisms/FiniteTypeModel.lean` together with
the system half of `StacksFrontier/AlgebraicGeometry/Limits/FiniteTypeSystem.lean`, and it
provides exactly the objects in which Stacks 0CP9 — that the cone is a limit cone — is stated.

## Main definitions

* `AlgebraicGeometry.Space.GoodDiagram` is the diagram above, bundling the stage `i`, the model
  `W ⟶ B_i`, the morphism `X ⟶ W`, the commutativity of the square, the finite-type property of
  the model and the closed-immersion property of the induced morphism. This is the diagram of
  Stacks 0CP8; Stacks 0CP7 asserts that one exists for every quasi-separated `X ⟶ B` of finite
  type.
* `AlgebraicGeometry.Space.GoodDiagram.induced` is the induced morphism `X ⟶ B ×_{B_i} W`.
* `AlgebraicGeometry.Space.GoodDiagram.stageMap` is the morphism from `X` to the base change
  `B_{i'} ×_{B_i} W` of the model at a later stage, and
  `AlgebraicGeometry.Space.GoodDiagram.stageTargetMap` the transition morphism between two such
  base changes.
* `AlgebraicGeometry.Space.GoodDiagram.stageImage` is the scheme-theoretic image `X_{i'}` of the
  stage map, and `AlgebraicGeometry.Space.GoodDiagram.imageTransition` the transition morphism
  between two of them.
* `AlgebraicGeometry.Space.GoodDiagram.imageSystem` and
  `AlgebraicGeometry.Space.GoodDiagram.imageCone` are the inverse system of scheme-theoretic
  images and its canonical cone with vertex `X`.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.isAlgebraicSpace_stageTarget`: the base change of the
  model to a later stage is an algebraic space over `S`, so its scheme-theoretic subspaces are
  available.
* `AlgebraicGeometry.Space.GoodDiagram.stageMap_comp_stageTargetMap`: the stage maps are
  compatible with the transition morphisms of the base-changed models.
* `AlgebraicGeometry.Space.GoodDiagram.imageTransition_ι`: the transition morphism of the image
  system is compatible with the inclusions of the images into the base-changed models.

## Implementation notes

Algebraic spaces over `S` are presheaves on the big fppf site over `S`, so the transition
morphism `B_{i'} ⟶ B_i` for `i ≤ i'` is the image of a morphism of `Iᵒᵖ` and the stage attached
to a good diagram enters the types through `Opposite.op`. The stages above `i` form the slice
`Over (op i)` of `Iᵒᵖ`. Algebraicity of a presheaf is not automatic, so it is a field of the
structure for the model and a theorem for each base change of it.

The fibre products are the canonical ones of the presheaf category and the induced morphism is
`CategoryTheory.Limits.pullback.lift` applied to the commuting square. Finite type for a
morphism of algebraic spaces is `AlgebraicGeometry.Space.IsFiniteType`, which by Stacks 03XF,
part (3), is locally of finite type together with quasi-compact.

The scheme-theoretic image of Stacks 082X is a subfunctor of the target rather than a space with
a chosen closed immersion into it, so `AlgebraicGeometry.Space.GoodDiagram.stageImage` is a
`CategoryTheory.Subfunctor` and the objects of the image system are the presheaves it
underlies. Its transition morphisms are the induced morphisms of scheme-theoretic images of
Stacks 0CP2, and functoriality is checked by composing with the inclusions into the
base-changed models, which are monomorphisms.

The structure `GoodDiagram` carries no hypothesis on the index type, and nothing in this file
needs the index type to be small for the site: the limiting cone of the system is data of
`AlgebraicGeometry.Space.NoetherianLimitSystem` and no limit is constructed here.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP7](https://stacks.math.columbia.edu/tag/0CP7)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 0CP2](https://stacks.math.columbia.edu/tag/0CP2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

section Definition

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The diagram of Stacks 0CP8.** For a morphism `f : X ⟶ B` into the limit of a directed
inverse system of Noetherian algebraic spaces with affine transition morphisms, a diagram
`X ⟶ W ⟶ B_i` over `B ⟶ B_i` in which `W ⟶ B_i` is of finite type and the induced morphism
`X ⟶ B ×_{B_i} W` is a closed immersion. Stacks 0CP7 asserts that such a diagram exists for
every quasi-separated `f` of finite type. -/
structure GoodDiagram {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : NoetherianLimitSystem B S hS hZ I)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ D.limitCone.pt) where
  /-- The stage `i` over which the model is defined. -/
  index : I
  /-- The model `W`, a presheaf on the big fppf site over `S`. -/
  model : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The model is an algebraic space over `S`. -/
  model_isAlgebraicSpace : IsAlgebraicSpace B S hS model
  /-- The structure morphism `W ⟶ B_i`. -/
  modelMap : model ⟶ D.system.obj (op index)
  /-- The horizontal morphism `X ⟶ W`. -/
  toModel : X ⟶ model
  /-- The square with vertical maps `f` and `modelMap` commutes. -/
  commutes : f ≫ D.limitCone.π.app (op index) = toModel ≫ modelMap
  /-- The model is of finite type over `B_i`. -/
  isFiniteType : IsFiniteType B S hS modelMap
  /-- The induced morphism from `X` to the base change of the model is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion B S hS (pullback.lift f toModel commutes)

end Definition

namespace GoodDiagram

section System

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {D : NoetherianLimitSystem B S hS hZ I}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ D.limitCone.pt}

/-- The morphism `X ⟶ B ×_{B_i} W` induced by a good diagram. -/
noncomputable abbrev induced (G : GoodDiagram B S hS hZ D f) :
    X ⟶ pullback (D.limitCone.π.app (op G.index)) G.modelMap :=
  pullback.lift f G.toModel G.commutes

/-- The map from `X` to the base change `B_{i'} ×_{B_i} W` of the model to a stage above the
index of a good diagram. -/
noncomputable def stageMap (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    X ⟶ pullback (D.system.map j.hom) G.modelMap :=
  pullback.lift (f ≫ D.limitCone.π.app j.left) G.toModel (by
    rw [Category.assoc, D.limitCone.w j.hom, G.commutes])

/-- The first component of the stage map is `f` followed by the limit projection to the stage. -/
@[reassoc (attr := simp)]
lemma stageMap_fst (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    stageMap G j ≫ pullback.fst _ _ = f ≫ D.limitCone.π.app j.left :=
  pullback.lift_fst _ _ _

/-- The second component of the stage map is the map `G.toModel` from `X` to the model. -/
@[reassoc (attr := simp)]
lemma stageMap_snd (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    stageMap G j ≫ pullback.snd _ _ = G.toModel :=
  pullback.lift_snd _ _ _

/-- The canonical transition morphism between two base changes of the model. -/
noncomputable def stageTargetMap (G : GoodDiagram B S hS hZ D f) {j k : Over (op G.index)}
    (a : j ⟶ k) :
    pullback (D.system.map j.hom) G.modelMap ⟶ pullback (D.system.map k.hom) G.modelMap :=
  pullback.lift
    (pullback.fst (D.system.map j.hom) G.modelMap ≫ D.system.map a.left)
    (pullback.snd (D.system.map j.hom) G.modelMap) (by
      rw [Category.assoc, ← D.system.map_comp, Over.w a]
      exact pullback.condition)

/-- The first component of the transition morphism is the first projection followed by the
transition map of the system along `a`. -/
@[reassoc (attr := simp)]
lemma stageTargetMap_fst (G : GoodDiagram B S hS hZ D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    stageTargetMap G a ≫ pullback.fst _ _ = pullback.fst _ _ ≫ D.system.map a.left :=
  pullback.lift_fst _ _ _

/-- The transition morphism commutes with the second projections onto the model. -/
@[reassoc (attr := simp)]
lemma stageTargetMap_snd (G : GoodDiagram B S hS hZ D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    stageTargetMap G a ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The stage map is compatible with the transition morphisms of the base-changed models. -/
@[reassoc (attr := simp)]
lemma stageMap_comp_stageTargetMap (G : GoodDiagram B S hS hZ D f) {j k : Over (op G.index)}
    (a : j ⟶ k) : stageMap G j ≫ stageTargetMap G a = stageMap G k := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageTargetMap_fst, stageMap_fst_assoc, stageMap_fst,
      D.limitCone.w a.left]
  · rw [Category.assoc, stageTargetMap_snd, stageMap_snd, stageMap_snd]

/-- The transition morphisms of the base-changed models respect composition. -/
lemma stageTargetMap_comp (G : GoodDiagram B S hS hZ D f) {j k l : Over (op G.index)}
    (a : j ⟶ k) (b : k ⟶ l) :
    stageTargetMap G a ≫ stageTargetMap G b = stageTargetMap G (a ≫ b) := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageTargetMap_fst, stageTargetMap_fst_assoc, stageTargetMap_fst,
      ← D.system.map_comp]
    rfl
  · rw [Category.assoc, stageTargetMap_snd, stageTargetMap_snd, stageTargetMap_snd]

/-- The transition morphism of the base-changed models at an identity is the identity. -/
@[simp]
lemma stageTargetMap_id (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    stageTargetMap G (𝟙 j) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · simp

/-- The base change `B_{i'} ×_{B_i} W` of the model to a later stage is an algebraic space
over `S`, being a fibre product of algebraic spaces. -/
theorem isAlgebraicSpace_stageTarget (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    IsAlgebraicSpace B S hS (pullback (D.system.map j.hom) G.modelMap) :=
  isAlgebraicSpace_pullback B S hS _ _ (D.system_isAlgebraicSpace j.left.unop)
    G.model_isAlgebraicSpace (D.system_isAlgebraicSpace G.index)

/-- The space `X_{i'}` of Stacks 0CP9: the scheme-theoretic image of the stage map
`X ⟶ B_{i'} ×_{B_i} W`, as a closed subspace of the base-changed model. -/
noncomputable abbrev stageImage (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    Subfunctor (pullback (D.system.map j.hom) G.modelMap) :=
  schemeTheoreticImageSubfunctor B S hS (stageMap G j)

/-- The scheme-theoretic images of the stage maps are closed subspaces of the base-changed
models. -/
theorem isClosedSubspace_stageImage (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    IsClosedSubspace B S hS (stageImage G j) :=
  isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (stageMap G j)
    (isAlgebraicSpace_stageTarget G j)

/-- The transition morphism `X_{i'} ⟶ X_{i''}` between the scheme-theoretic images at two
stages. This is the induced morphism of scheme-theoretic images of Stacks 0CP2, applied to the
square whose horizontal morphisms are the stage maps and whose right-hand morphism is the
transition morphism of the base-changed models. -/
noncomputable def imageTransition (G : GoodDiagram B S hS hZ D f) {j k : Over (op G.index)}
    (a : j ⟶ k) : (stageImage G j).toFunctor ⟶ (stageImage G k).toFunctor :=
  schemeTheoreticImageMap B S hS (isAlgebraicSpace_stageTarget G j)
    (isAlgebraicSpace_stageTarget G k)
    (show stageMap G j ≫ stageTargetMap G a = 𝟙 X ≫ stageMap G k by
      rw [Category.id_comp, stageMap_comp_stageTargetMap])

/-- The transition morphism of the image system is compatible with the inclusions of the
scheme-theoretic images into the base-changed models. -/
@[reassoc (attr := simp)]
lemma imageTransition_ι (G : GoodDiagram B S hS hZ D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    imageTransition G a ≫ (stageImage G k).ι = (stageImage G j).ι ≫ stageTargetMap G a :=
  schemeTheoreticImageMap_ι B S hS _ _ _

/-- The inverse system of scheme-theoretic images of the stage maps of a good diagram, indexed
by the stages above the index of the diagram. -/
@[reducible] noncomputable def imageSystem (G : GoodDiagram B S hS hZ D f) :
    Over (op G.index) ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  obj j := (stageImage G j).toFunctor
  map a := imageTransition G a
  map_id j := by
    refine (cancel_mono (stageImage G j).ι).1 ?_
    rw [imageTransition_ι, stageTargetMap_id, Category.comp_id, Category.id_comp]
  map_comp a b := by
    refine (cancel_mono (stageImage G _).ι).1 ?_
    simp only [Category.assoc, imageTransition_ι]
    rw [← Category.assoc, imageTransition_ι, Category.assoc, stageTargetMap_comp]

/-- The cone from `X` to its scheme-theoretic images at all later stages, whose legs are the
factorizations of the stage maps through their images. Stacks 0CP9 asserts that it is a limit
cone. -/
@[reducible] noncomputable def imageCone (G : GoodDiagram B S hS hZ D f) :
    Cone (imageSystem G) where
  pt := X
  π :=
    { app j := toSchemeTheoreticImage B S hS (stageMap G j)
      naturality j k a :=
        (toSchemeTheoreticImage_comp_schemeTheoreticImageMap B S hS
          (show stageMap G j ≫ stageTargetMap G a = 𝟙 X ≫ stageMap G k by
            rw [Category.id_comp, stageMap_comp_stageTargetMap])
          (imageTransition G a) (imageTransition_ι G a)).symm }

/-- The cone point of `imageCone G` is `X`. -/
@[simp]
lemma imageCone_pt (G : GoodDiagram B S hS hZ D f) : (imageCone G).pt = X := rfl

/-- The leg of `imageCone G` at a stage is the factorization of the stage map through its
scheme-theoretic image. -/
@[simp]
lemma imageCone_π_app (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    (imageCone G).π.app j = toSchemeTheoreticImage B S hS (stageMap G j) := rfl

end System

end GoodDiagram

end AlgebraicGeometry.Space

end
