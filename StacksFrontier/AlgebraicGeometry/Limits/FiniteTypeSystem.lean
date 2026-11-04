module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Filtered.Final
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.SmallDominantIndex
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteTypeModel

/-!
# Morphisms of the systems of finite type models over a limit of Noetherian schemes

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms and let `X ⟶ S` be quasi-separated and of finite type. A good diagram
`G` for `X ⟶ S` (Tag 0CNN, `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram`) consists of
a stage `i`, a finite-type model `W ⟶ S_i` and a closed immersion `X ⟶ S ×_{S_i} W`. For each
later stage `i' ≥ i` the scheme-theoretic image `X_{i'}` of `X ⟶ S_{i'} ×_{S_i} W` is defined,
and these form an inverse system over the stages above `i` with a canonical cone from `X`
(Tag 0CNQ).

This file builds that system and shows that a morphism `f : X ⟶ Y` over `S` is realized by a
morphism of the two systems on a sufficiently late common tail, uniquely at sufficiently late
stages. This is Stacks Tag 0CNR.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.stageMap`: the morphism from `X` to
  the base change `S_{i'} ×_{S_i} W` of the model at a later stage.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.stageTargetMap`: the transition
  morphism between two base changes of the model.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageSystem` and
  `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageCone`: the inverse system of
  scheme-theoretic images and its canonical cone with vertex `X`.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt`: a morphism of the systems attached to
  two good diagrams, starting at a common stage, over the base system and inducing a given
  morphism on the limits.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.exists_morphismAt_of_isLimit`: existence of such a
  morphism of systems on a sufficiently late common tail.
* `AlgebraicGeometry.LimitNoetherianSituation.eventually_eq_morphismAt_of_isLimit`: two such
  morphisms inducing the same morphism on the limits agree at every sufficiently late stage.
* `AlgebraicGeometry.Scheme.Hom.ker_toImage`: the canonical morphism to the scheme-theoretic
  image has trivial kernel, i.e. its image is scheme-theoretically dense.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.quasiCompact_toLimit`,
  `locallyOfFiniteType_toLimit` and `quasiSeparated_toLimit`: a morphism admitting a good diagram
  has those three properties, so they need not be assumed alongside a good diagram.

## Implementation notes

The stages above an index `i` form the slice `Over (op i)` of the opposite preorder, and
restriction to a later tail is `CategoryTheory.Over.map`. That functor is initial, because the
opposite of a directed preorder is cofiltered and its slices are thin, so the cone of
scheme-theoretic images restricts to a limit cone over the later tail; this is what lets the two
systems be compared on a common tail.

Both halves of the proof are the two halves of Tag 01ZC, which is available with the index
universes independent of the scheme universe in
`StacksFrontier/AlgebraicGeometry/LimitUniverse/AffineTransitionLimit.lean`. The model
`V ⟶ S_{i₂}` of `Y` is of finite type over a Noetherian scheme, hence of finite presentation, so
the surjectivity half produces a morphism `X_{i₀} ⟶ V` at some stage; the stage morphisms
`X_{i'} ⟶ Y_{i'}` are then obtained by the universal property of the closed immersion
`Y_{i'} ⟶ S_{i'} ×_{S_{i₂}} V`, whose kernel is contained in that of `X_{i'} ⟶ S_{i'} ×_{S_{i₂}} V`
because `X ⟶ X_{i'}` has scheme-theoretically dense image. Uniqueness does not follow the Stacks
proof, which runs through equalizers and constructibility: since `Y_{i'} ⟶ S_{i'} ×_{S_{i₂}} V`
is a monomorphism, two stage morphisms agree as soon as their `V`-components do, and the
injectivity half of Tag 01ZC makes those agree at a late enough stage.

## The index universe, and why no smallness hypothesis is needed

Tag 0CNR inherits Situation 0CNM, "the limit of a directed system of Noetherian schemes". The
index universe here is independent of the universe of the schemes and carries **no** condition
relating the two — in particular no cofinality hypothesis such as
`CategoryTheory.FinallySmall.{u} I`.

That is not automatic. The two halves of Tag 01ZC are available at a free index universe only
under `CategoryTheory.InitiallySmall.{u}` of the index of the system they descend along
(`StacksFrontier/AlgebraicGeometry/LimitUniverse/AffineTransitionLimit.lean`), and that
restriction is genuine: over `Ordinal.{u}` there is a system of nonempty affine schemes with
affine transitions whose limit is empty
(`StacksFrontier/AlgebraicGeometry/SmallnessNecessary/Basic.lean`). What makes it unnecessary
here is special to this situation: the projections `X ⟶ X_{i'}` out of the limit of the image
system are scheme-theoretically dominant (`AlgebraicGeometry.Scheme.Hom.ker_toImage`), so the
system stays a limit after restriction to a `u`-small subsystem and the two halves of Tag 01ZC
hold for it with no condition on the index, by
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant_slice`
and
`AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant_slice`
in `StacksFrontier/AlgebraicGeometry/Limits/SmallDominantIndex.lean`.

Nor is smallness needed for the stage maps: that the projections out of the limit are affine, and
hence that the stage maps are quasi-compact, holds with no smallness hypothesis at all, by
`AlgebraicGeometry.EventualLimit.isAffineHom_π_app`.

The two main results take `IsLimit (GoodDiagram.imageCone GX)` — Tag 0CNQ for the source good
diagram — as an explicit hypothesis, because Tag 0CNQ is proved in
`StacksFrontier/AlgebraicGeometry/Limits/ImageSystemLimit.lean`, which imports this file. The
unconditional forms carrying the Tag 0CNR attribute are in
`StacksFrontier/AlgebraicGeometry/Limits/FiniteTypeSystemMorphism.lean`, above that module.
Only the source good diagram needs the limit description; the Stacks statement assumes it for
both `X` and `Y`.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNQ](https://stacks.math.columbia.edu/tag/0CNQ)
* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Scheme

/-- The morphism to the scheme-theoretic image has trivial kernel: the image is the smallest
closed subscheme through which the morphism factors. -/
lemma Hom.ker_toImage {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    f.toImage.ker = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun V : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ V.1, (V.2 : IsAffineOpen V.1).preimage f.imageι⟩)
    ?_ ?_
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
    simp
  · intro V
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
    show RingHom.ker _ = ⊥
    rw [← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective V

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

namespace GoodDiagram

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I} {X : Scheme.{u}} {f : X ⟶ D.limitScheme}

/-! ### Properties of the morphism a good diagram is for

A morphism admitting a good diagram is quasi-compact, locally of finite type and quasi-separated:
it factors as the closed immersion into the base change of the model followed by that base
change, which inherits the three properties from the model morphism. Nothing has to be assumed
about it.
-/

/-- The base change of the model of a good diagram to the limit is quasi-compact. -/
theorem quasiCompact_pullback_fst (G : GoodDiagram D f) :
    QuasiCompact (pullback.fst (D.limitCone.π.app (op G.index)) G.modelMap) :=
  have _ : QuasiCompact G.modelMap := G.quasiCompact
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (D.limitCone.π.app (op G.index)) G.modelMap).flip inferInstance

/-- The base change of the model of a good diagram to the limit is locally of finite type. -/
theorem locallyOfFiniteType_pullback_fst (G : GoodDiagram D f) :
    LocallyOfFiniteType (pullback.fst (D.limitCone.π.app (op G.index)) G.modelMap) :=
  have _ : LocallyOfFiniteType G.modelMap := G.locallyOfFiniteType
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (D.limitCone.π.app (op G.index)) G.modelMap).flip inferInstance

/-- The base change of the model of a good diagram to the limit is quasi-separated: the model is
of finite type over a Noetherian scheme, hence Noetherian. -/
theorem quasiSeparated_pullback_fst (G : GoodDiagram D f) :
    QuasiSeparated (pullback.fst (D.limitCone.π.app (op G.index)) G.modelMap) :=
  have _ : LocallyOfFiniteType G.modelMap := G.locallyOfFiniteType
  have _ : QuasiCompact G.modelMap := G.quasiCompact
  have _ : IsNoetherian (D.system.obj (op G.index)) := D.noetherian G.index
  have _ : IsNoetherian G.W := isNoetherian_of_locallyOfFiniteType G.modelMap
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (D.limitCone.π.app (op G.index)) G.modelMap).flip inferInstance

/-- The closed immersion of a good diagram, followed by the base change of the model, is `f`. -/
private theorem induced_comp_fst (G : GoodDiagram D f) :
    G.induced ≫ pullback.fst (D.limitCone.π.app (op G.index)) G.modelMap = f :=
  pullback.lift_fst _ _ _

/-- A morphism admitting a good diagram is quasi-compact. -/
theorem quasiCompact_toLimit (G : GoodDiagram D f) : QuasiCompact f := by
  have _ : IsClosedImmersion G.induced := G.isClosedImmersion
  have _ := G.quasiCompact_pullback_fst
  rw [← G.induced_comp_fst]
  infer_instance

/-- A morphism admitting a good diagram is locally of finite type. -/
theorem locallyOfFiniteType_toLimit (G : GoodDiagram D f) : LocallyOfFiniteType f := by
  have _ : IsClosedImmersion G.induced := G.isClosedImmersion
  have _ := G.locallyOfFiniteType_pullback_fst
  rw [← G.induced_comp_fst]
  infer_instance

/-- A morphism admitting a good diagram is quasi-separated. -/
theorem quasiSeparated_toLimit (G : GoodDiagram D f) : QuasiSeparated f := by
  have _ : IsClosedImmersion G.induced := G.isClosedImmersion
  have _ := G.quasiSeparated_pullback_fst
  rw [← G.induced_comp_fst]
  infer_instance

/-- The map from `X` to the base change of the model to a stage above the index of a
good diagram. -/
noncomputable def stageMap (G : GoodDiagram D f) (j : Over (op G.index)) :
    X ⟶ pullback (D.system.map j.hom) G.modelMap :=
  pullback.lift (f ≫ D.limitCone.π.app j.left) G.toModel (by
    rw [Category.assoc, D.limitCone.w j.hom, G.commutes])

/-- The first projection of the stage map is `f` followed by the projection of the limit. -/
@[reassoc (attr := simp)]
lemma stageMap_fst (G : GoodDiagram D f) (j : Over (op G.index)) :
    stageMap G j ≫ pullback.fst _ _ = f ≫ D.limitCone.π.app j.left :=
  pullback.lift_fst _ _ _

/-- The second projection of the stage map is the map to the model. -/
@[reassoc (attr := simp)]
lemma stageMap_snd (G : GoodDiagram D f) (j : Over (op G.index)) :
    stageMap G j ≫ pullback.snd _ _ = G.toModel :=
  pullback.lift_snd _ _ _

/-- The canonical transition map between two base changes of the model. -/
noncomputable def stageTargetMap (G : GoodDiagram D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    pullback (D.system.map j.hom) G.modelMap ⟶ pullback (D.system.map k.hom) G.modelMap :=
  pullback.lift
    (pullback.fst (D.system.map j.hom) G.modelMap ≫ D.system.map a.left)
    (pullback.snd (D.system.map j.hom) G.modelMap) (by
      rw [Category.assoc, ← D.system.map_comp, Over.w a]
      exact pullback.condition)

/-- The first projection of the transition map is the projection followed by the system's
transition morphism. -/
@[reassoc (attr := simp)]
lemma stageTargetMap_fst (G : GoodDiagram D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    stageTargetMap G a ≫ pullback.fst _ _ = pullback.fst _ _ ≫ D.system.map a.left :=
  pullback.lift_fst _ _ _

/-- The transition map commutes with the second projections to the model. -/
@[reassoc (attr := simp)]
lemma stageTargetMap_snd (G : GoodDiagram D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    stageTargetMap G a ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The stage map is compatible with transition of base-changed models. -/
@[reassoc (attr := simp)]
lemma stageMap_comp_stageTargetMap (G : GoodDiagram D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    stageMap G j ≫ stageTargetMap G a = stageMap G k := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageTargetMap_fst, stageMap_fst_assoc, stageMap_fst,
      D.limitCone.w a.left]
  · rw [Category.assoc, stageTargetMap_snd, stageMap_snd, stageMap_snd]

/-- Base-changed model transition maps respect composition. -/
lemma stageTargetMap_comp (G : GoodDiagram D f) {j k l : Over (op G.index)} (a : j ⟶ k)
    (b : k ⟶ l) : stageTargetMap G a ≫ stageTargetMap G b = stageTargetMap G (a ≫ b) := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageTargetMap_fst, stageTargetMap_fst_assoc, stageTargetMap_fst,
      ← D.system.map_comp]
    rfl
  · rw [Category.assoc, stageTargetMap_snd, stageTargetMap_snd, stageTargetMap_snd]

/-- Base-changed model transition at the identity is the identity. -/
@[simp]
lemma stageTargetMap_id (G : GoodDiagram D f) (j : Over (op G.index)) :
    stageTargetMap G (𝟙 j) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · simp

/-- The base change of the model to a later stage is Noetherian, being of finite type over the
Noetherian stage scheme. -/
instance isNoetherian_stageTarget (G : GoodDiagram D f) (j : Over (op G.index)) :
    IsNoetherian (pullback (D.system.map j.hom) G.modelMap) :=
  have : LocallyOfFiniteType G.modelMap := G.locallyOfFiniteType
  have : QuasiCompact G.modelMap := G.quasiCompact
  isNoetherian_of_locallyOfFiniteType (pullback.fst (D.system.map j.hom) G.modelMap)

/-- The canonical transition between the scheme-theoretic images at two stages. This is the
functoriality `AlgebraicGeometry.Scheme.Hom.imageMap` of the scheme-theoretic image, applied to
the square whose horizontal maps are the stage maps and whose right-hand map is
`stageTargetMap`. -/
noncomputable def imageTransition (G : GoodDiagram D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    (stageMap G j).image ⟶ (stageMap G k).image :=
  Scheme.Hom.imageMap (stageMap G j) (stageMap G k) (𝟙 X) (stageTargetMap G a)
    (by rw [Category.id_comp, stageMap_comp_stageTargetMap])

/-- The image transition commutes with the closed embeddings into the base-changed models. -/
@[reassoc (attr := simp)]
lemma imageTransition_imageι (G : GoodDiagram D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    imageTransition G a ≫ (stageMap G k).imageι =
      (stageMap G j).imageι ≫ stageTargetMap G a :=
  Scheme.Hom.imageMap_imageι _ _ _ _ _

/-- The functor of scheme-theoretic images of the stage maps of a good diagram.

This is `@[reducible]` so that the objects and morphisms of a restriction
`Over.map g ⋙ imageSystem G` are visible to `rw` and to instance search; without it the
module system hides the definition at `instances` transparency and no rewrite about a
restricted system elaborates. -/
@[reducible] noncomputable def imageSystem (G : GoodDiagram D f) :
    Over (op G.index) ⥤ Scheme.{u} where
  obj j := (stageMap G j).image
  map a := imageTransition G a
  map_id j := by
    apply (cancel_mono (stageMap G j).imageι).mp
    simp
  map_comp a b := by
    apply (cancel_mono (stageMap G _).imageι).mp
    simp only [Category.assoc, imageTransition_imageι]
    rw [← Category.assoc, imageTransition_imageι, Category.assoc, stageTargetMap_comp]

/-- The object of the image system at a stage is the scheme-theoretic image of the stage map. -/
@[simp]
lemma imageSystem_obj (G : GoodDiagram D f) (j : Over (op G.index)) :
    (imageSystem G).obj j = (stageMap G j).image := rfl

/-- The morphism of the image system along `a` is `imageTransition G a`. -/
@[simp]
lemma imageSystem_map (G : GoodDiagram D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    (imageSystem G).map a = imageTransition G a := rfl

/-- The cone from `X` to its scheme-theoretic images at all later stages. Reducible for the
same reason as `imageSystem`. -/
@[reducible] noncomputable def imageCone (G : GoodDiagram D f) : Cone (imageSystem G) where
  pt := X
  π := {
    app j := (stageMap G j).toImage
    naturality := by
      intro j k a
      change (stageMap G k).toImage = (stageMap G j).toImage ≫ imageTransition G a
      apply (cancel_mono (stageMap G k).imageι).mp
      simp only [Category.assoc, imageTransition_imageι, Scheme.Hom.toImage_imageι]
      rw [← Category.assoc, Scheme.Hom.toImage_imageι]
      exact (stageMap_comp_stageTargetMap G a).symm
  }

/-- The cone point of the image cone is `X`. -/
@[simp]
lemma imageCone_pt (G : GoodDiagram D f) : (imageCone G).pt = X := rfl

/-- The component of the image cone at a stage is the map from `X` to the image of the stage
map. -/
@[simp]
lemma imageCone_π_app (G : GoodDiagram D f) (j : Over (op G.index)) :
    (imageCone G).π.app j = (stageMap G j).toImage := rfl

/-- The base-changed model transitions are affine, being base changes of the transition
morphisms of the system. -/
instance isAffineHom_stageTargetMap (G : GoodDiagram D f) {j k : Over (op G.index)}
    (a : j ⟶ k) : IsAffineHom (stageTargetMap G a) := by
  have hpb : IsPullback (stageTargetMap G a) (pullback.fst (D.system.map j.hom) G.modelMap)
      (pullback.fst (D.system.map k.hom) G.modelMap) (D.system.map a.left) := by
    refine IsPullback.of_right ?_ (stageTargetMap_fst G a)
      ((IsPullback.of_hasPullback (D.system.map k.hom) G.modelMap).flip)
    rw [stageTargetMap_snd]
    have he : D.system.map j.hom = D.system.map a.left ≫ D.system.map k.hom := by
      rw [← D.system.map_comp, Over.w a]
    rw! [he]
    exact (IsPullback.of_hasPullback _ G.modelMap).flip
  exact MorphismProperty.of_isPullback hpb.flip (D.transition_affine a.left)

/-- The transition morphisms of the image system are affine. -/
instance isAffineHom_imageTransition (G : GoodDiagram D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    IsAffineHom (imageTransition G a) :=
  Scheme.Hom.isAffineHom_imageMap _ _ _ _ _

end GoodDiagram

end LimitNoetherianSituation

end AlgebraicGeometry

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

open GoodDiagram

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- The projections out of the limit of a limit-Noetherian situation are affine. This is
`AlgebraicGeometry.LimitNoetherianSituation.isAffineHom_π` with the weaker hypothesis
`CategoryTheory.FinallySmall` in place of `CategoryTheory.EssentiallySmall`. -/
theorem isAffineHom_π_of_finallySmall [FinallySmall.{u} I]
    (D : LimitNoetherianSituation.{v, u} I) (i : Iᵒᵖ) : IsAffineHom (D.limitCone.π.app i) :=
  isAffineHom_π_app_of_initiallySmall D.system D.limitCone D.isLimit i

section Tail

variable {D : LimitNoetherianSituation.{v, u} I} {X : Scheme.{u}} {p : X ⟶ D.limitScheme}

/-- A stage map of a good diagram is quasi-compact: it is so after composition with the
projection to the base-changed model, which is quasi-separated. -/
theorem GoodDiagram.quasiCompact_stageMap [QuasiCompact p]
    (G : GoodDiagram D p) (j : Over (op G.index)) : QuasiCompact (stageMap G j) := by
  have htr : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.system.map g) := D.transition_affine
  have h₁ : IsAffineHom (D.limitCone.π.app j.left) :=
    EventualLimit.isAffineHom_π_app D.system D.limitCone D.isLimit j.left
  have h₂ : QuasiCompact (stageMap G j ≫ pullback.fst (D.system.map j.hom) G.modelMap) := by
    rw [stageMap_fst]; infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst (D.system.map j.hom) G.modelMap)

/-- The transition of the image system, followed by the projection to the stage scheme and any
morphism of the system out of it, is the projection at the earlier stage: the index category is
thin, so there is nothing to choose. -/
theorem GoodDiagram.imageTransition_imageι_fst_map (G : GoodDiagram D p)
    {j k : Over (op G.index)} (a : j ⟶ k) {i₁ : I} (gk : k.left ⟶ op i₁)
    (gj : j.left ⟶ op i₁) :
    imageTransition G a ≫ (stageMap G k).imageι ≫ pullback.fst _ _ ≫ D.system.map gk =
      (stageMap G j).imageι ≫ pullback.fst _ _ ≫ D.system.map gj := by
  have he : a.left ≫ gk = gj := Subsingleton.elim _ _
  rw [imageTransition_imageι_assoc, stageTargetMap_fst_assoc, ← D.system.map_comp, he]

/-- The canonical map from `X` to its image at a stage, followed by the transition to an earlier
stage, is the canonical map at that earlier stage. -/
@[reassoc (attr := simp)]
lemma GoodDiagram.toImage_comp_imageTransition (G : GoodDiagram D p) {j k : Over (op G.index)}
    (a : j ⟶ k) : (stageMap G j).toImage ≫ imageTransition G a = (stageMap G k).toImage := by
  refine (cancel_mono (stageMap G k).imageι).mp ?_
  rw [Category.assoc, imageTransition_imageι, Scheme.Hom.toImage_imageι,
    Scheme.Hom.toImage_imageι_assoc, stageMap_comp_stageTargetMap]

/-- The transitions of the image system compose. -/
@[reassoc]
lemma GoodDiagram.imageTransition_comp (G : GoodDiagram D p) {j k l : Over (op G.index)}
    (a : j ⟶ k) (b : k ⟶ l) :
    imageTransition G a ≫ imageTransition G b = imageTransition G (a ≫ b) := by
  refine (cancel_mono (stageMap G l).imageι).mp ?_
  rw [Category.assoc, imageTransition_imageι, imageTransition_imageι_assoc,
    imageTransition_imageι, stageTargetMap_comp]

/-- The image system of a good diagram, restricted to the stages above an index `i₀` above its
own index, viewed as a diagram of schemes over `S_{i₁}` for any `i₁ ≤ i₀`. -/
noncomputable def GoodDiagram.imageSystemToBase (G : GoodDiagram D p) {i₀ : I}
    (h : G.index ≤ i₀) {i₁ : I} (h₁ : i₁ ≤ i₀) :
    (Over.map ((homOfLE h).op) ⋙ imageSystem G) ⟶
      (Functor.const (Over (op i₀))).obj (D.system.obj (op i₁)) where
  app j := (stageMap G ((Over.map ((homOfLE h).op)).obj j)).imageι ≫
    pullback.fst _ _ ≫ D.system.map (j.hom ≫ (homOfLE h₁).op)
  naturality j k a := by
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact imageTransition_imageι_fst_map G ((Over.map ((homOfLE h).op)).map a) _ _

/-- The component of `imageSystemToBase` at a stage is the closed embedding into the
base-changed model, followed by the projection and the transition to `S_{i₁}`. -/
@[simp]
lemma GoodDiagram.imageSystemToBase_app (G : GoodDiagram D p) {i₀ : I} (h : G.index ≤ i₀)
    {i₁ : I} (h₁ : i₁ ≤ i₀) (j : Over (op i₀)) :
    (imageSystemToBase G h h₁).app j =
      (stageMap G ((Over.map ((homOfLE h).op)).obj j)).imageι ≫
        pullback.fst _ _ ≫ D.system.map (j.hom ≫ (homOfLE h₁).op) := rfl

/-- The image cone of a good diagram, restricted to the stages above a later index, is still a
limit cone: restriction between slices of a cofiltered thin category is an initial functor. -/
noncomputable def GoodDiagram.isLimitImageConeWhisker (G : GoodDiagram D p)
    (hG : IsLimit (imageCone G)) {i₀ : I} (h : G.index ≤ i₀) :
    IsLimit ((imageCone G).whisker (Over.map ((homOfLE h).op))) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.map ((homOfLE h).op)) (imageCone G)).symm hG

/-- Every stage of a restricted image system is quasi-compact. -/
theorem GoodDiagram.compactSpace_imageSystem (G : GoodDiagram D p) {i₀ : I}
    (h : G.index ≤ i₀) :
    ∀ j, CompactSpace ((Over.map ((homOfLE h).op) ⋙ imageSystem G).obj j) :=
  fun j ↦ inferInstanceAs
    (CompactSpace (stageMap G ((Over.map ((homOfLE h).op)).obj j)).image)

/-- Every stage of a restricted image system is quasi-separated. -/
theorem GoodDiagram.quasiSeparatedSpace_imageSystem (G : GoodDiagram D p) {i₀ : I}
    (h : G.index ≤ i₀) :
    ∀ j, QuasiSeparatedSpace ((Over.map ((homOfLE h).op) ⋙ imageSystem G).obj j) :=
  fun j ↦ inferInstanceAs
    (QuasiSeparatedSpace (stageMap G ((Over.map ((homOfLE h).op)).obj j)).image)

/-- The transition morphisms of a restricted image system are affine. -/
theorem GoodDiagram.isAffineHom_imageSystem (G : GoodDiagram D p) {i₀ : I}
    (h : G.index ≤ i₀) :
    ∀ {j k : Over (op i₀)} (a : j ⟶ k),
      IsAffineHom ((Over.map ((homOfLE h).op) ⋙ imageSystem G).map a) :=
  fun {_ _} a ↦ inferInstanceAs
    (IsAffineHom (imageTransition G ((Over.map ((homOfLE h).op)).map a)))

/-- The projections from `X` to the stages of the restricted image system are scheme-theoretically
dominant. -/
private theorem GoodDiagram.isSchemeTheoreticallyDominant_whisker [QuasiCompact p]
    (G : GoodDiagram D p) {i₀ : I} (h : G.index ≤ i₀) :
    ∀ j, IsSchemeTheoreticallyDominant
      (((imageCone G).whisker (Over.map ((homOfLE h).op))).π.app j) := fun j ↦ by
  have := G.quasiCompact_stageMap ((Over.map ((homOfLE h).op)).obj j)
  exact ⟨Scheme.Hom.ker_toImage (stageMap G ((Over.map ((homOfLE h).op)).obj j))⟩

/-- The unique morphism, in the slice over `G.index`, from a stage above `i₀` to the stage
`i₀` itself. -/
def GoodDiagram.toBaseStage (G : GoodDiagram D p) {i₀ : I} (h : G.index ≤ i₀)
    (j : Over (op i₀)) :
    (Over.map ((homOfLE h).op)).obj j ⟶ Over.mk ((homOfLE h).op) :=
  Over.homMk j.hom (Subsingleton.elim _ _)

end Tail

end LimitNoetherianSituation

end AlgebraicGeometry

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

open GoodDiagram

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- A morphism between the systems attached to two good diagrams, starting at a common
stage, over the base system and inducing the specified morphism on their limits. -/
structure MorphismAt (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀) where
  /-- The compatible morphisms at all stages above `i₀`. -/
  maps :
    (Over.map ((homOfLE hX).op) ⋙ GoodDiagram.imageSystem GX) ⟶
      (Over.map ((homOfLE hY).op) ⋙ GoodDiagram.imageSystem GY)
  /-- Each stage morphism lies over the corresponding base scheme. -/
  over_base : ∀ j : Over (op i₀),
    maps.app j ≫
        (GoodDiagram.stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).imageι ≫
        pullback.fst _ _ =
      (GoodDiagram.stageMap GX ((Over.map ((homOfLE hX).op)).obj j)).imageι ≫
        pullback.fst _ _
  /-- The induced map on the limits is `f`. -/
  induces : ∀ j : Over (op i₀),
    (GoodDiagram.imageCone GX).π.app ((Over.map ((homOfLE hX).op)).obj j) ≫ maps.app j =
      f ≫ (GoodDiagram.imageCone GY).π.app ((Over.map ((homOfLE hY).op)).obj j)

section Construction

variable {D : LimitNoetherianSituation.{v, u} I}
  {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
  {f : X ⟶ Y} {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
  {i₀ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}
  {h : (GoodDiagram.stageMap GX (Over.mk ((homOfLE hX).op))).image ⟶ GY.W}
  (hf : f ≫ pY = pX)
  (hh₁ : (GoodDiagram.stageMap GX (Over.mk ((homOfLE hX).op))).toImage ≫ h = f ≫ GY.toModel)
  (hh₂ : h ≫ GY.modelMap = (GoodDiagram.stageMap GX (Over.mk ((homOfLE hX).op))).imageι ≫
      pullback.fst _ _ ≫ D.system.map ((homOfLE hY).op))

/-- The morphism from a stage of the image system of `GX` to the base-changed model of `GY`,
assembled from the projection to the stage scheme and a morphism `X_{i₀} ⟶ V`. -/
noncomputable def stageHomAux (j : Over (op i₀)) :
    (stageMap GX ((Over.map ((homOfLE hX).op)).obj j)).image ⟶
      pullback (D.system.map ((Over.map ((homOfLE hY).op)).obj j).hom) GY.modelMap :=
  pullback.lift
    ((stageMap GX ((Over.map ((homOfLE hX).op)).obj j)).imageι ≫ pullback.fst _ _)
    (imageTransition GX (GX.toBaseStage hX j) ≫ h)
    (by
      rw [Category.assoc, Category.assoc, hh₂]
      exact (imageTransition_imageι_fst_map GX (GX.toBaseStage hX j) ((homOfLE hY).op)
        ((Over.map ((homOfLE hY).op)).obj j).hom).symm)

/-- The first projection of `stageHomAux` is the projection of the image to the stage scheme. -/
@[reassoc (attr := simp)]
lemma stageHomAux_fst (j : Over (op i₀)) :
    stageHomAux hh₂ j ≫ pullback.fst _ _ =
      (stageMap GX ((Over.map ((homOfLE hX).op)).obj j)).imageι ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The second projection of `stageHomAux` is the transition to the stage `i₀` followed by `h`. -/
@[reassoc (attr := simp)]
lemma stageHomAux_snd (j : Over (op i₀)) :
    stageHomAux hh₂ j ≫ pullback.snd _ _ =
      imageTransition GX (GX.toBaseStage hX j) ≫ h :=
  pullback.lift_snd _ _ _

include hf hh₁ in
/-- The composite `X ⟶ X_j ⟶ S_j ×_{S_{i₂}} V` is the stage map of `GY`. -/
lemma toImage_comp_stageHomAux (j : Over (op i₀)) :
    (stageMap GX ((Over.map ((homOfLE hX).op)).obj j)).toImage ≫ stageHomAux hh₂ j =
      f ≫ stageMap GY ((Over.map ((homOfLE hY).op)).obj j) := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageHomAux_fst, Scheme.Hom.toImage_imageι_assoc, stageMap_fst,
      Category.assoc, stageMap_fst, ← Category.assoc, hf]
    rfl
  · rw [Category.assoc, stageHomAux_snd, Category.assoc, stageMap_snd, ← Category.assoc,
      toImage_comp_imageTransition, hh₁]

include hf hh₁ in
/-- The kernel condition letting the stage morphism factor through the image of `GY`. -/
lemma ker_le_ker_stageHomAux [QuasiCompact pX] (j : Over (op i₀)) :
    (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).imageι.ker ≤
      (stageHomAux hh₂ j).ker := by
  have hqc : QuasiCompact (stageMap GX ((Over.map ((homOfLE hX).op)).obj j)) :=
    GX.quasiCompact_stageMap _
  have hbot : (stageMap GX ((Over.map ((homOfLE hX).op)).obj j)).toImage.ker = ⊥ :=
    Scheme.Hom.ker_toImage _
  have key : (stageHomAux hh₂ j).ker =
      (f ≫ stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).ker := by
    rw [← toImage_comp_stageHomAux hf hh₁ hh₂ j, Scheme.Hom.ker_comp, hbot,
      Scheme.IdealSheafData.map_bot]
  refine le_trans (le_of_eq (Scheme.IdealSheafData.ker_subschemeι _)) ?_
  exact le_trans (Scheme.Hom.le_ker_comp f
    (stageMap GY ((Over.map ((homOfLE hY).op)).obj j))) (le_of_eq key.symm)

/-- The stage morphism of image systems produced by a morphism `X_{i₀} ⟶ V`. -/
noncomputable def stageMorphismAux [QuasiCompact pX] (j : Over (op i₀)) :
    (stageMap GX ((Over.map ((homOfLE hX).op)).obj j)).image ⟶
      (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).image :=
  IsClosedImmersion.lift (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).imageι
    (stageHomAux hh₂ j) (ker_le_ker_stageHomAux hf hh₁ hh₂ j)

/-- The stage morphism followed by the closed embedding of the image of `GY` is
`stageHomAux`. -/
@[reassoc (attr := simp)]
lemma stageMorphismAux_imageι [QuasiCompact pX] (j : Over (op i₀)) :
    stageMorphismAux hf hh₁ hh₂ j ≫
        (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).imageι = stageHomAux hh₂ j :=
  IsClosedImmersion.lift_fac _ _ _

/-- The morphism of restricted image systems produced by a morphism `X_{i₀} ⟶ V`. -/
noncomputable def systemMorphismAux [QuasiCompact pX] :
    (Over.map ((homOfLE hX).op) ⋙ imageSystem GX) ⟶
      (Over.map ((homOfLE hY).op) ⋙ imageSystem GY) where
  app := stageMorphismAux hf hh₁ hh₂
  naturality j k a := by
    refine (cancel_mono (stageMap GY ((Over.map ((homOfLE hY).op)).obj k)).imageι).mp ?_
    change (imageTransition GX ((Over.map ((homOfLE hX).op)).map a) ≫
          stageMorphismAux hf hh₁ hh₂ k) ≫ _ =
        (stageMorphismAux hf hh₁ hh₂ j ≫
          imageTransition GY ((Over.map ((homOfLE hY).op)).map a)) ≫ _
    rw [Category.assoc, stageMorphismAux_imageι, Category.assoc, imageTransition_imageι,
      ← Category.assoc, stageMorphismAux_imageι]
    apply pullback.hom_ext
    · rw [Category.assoc, stageHomAux_fst, imageTransition_imageι_assoc, stageTargetMap_fst,
        Category.assoc, stageTargetMap_fst, stageHomAux_fst_assoc]
      rfl
    · have he : ((Over.map ((homOfLE hX).op)).map a) ≫ GX.toBaseStage hX k =
          GX.toBaseStage hX j := Subsingleton.elim _ _
      rw [Category.assoc, stageHomAux_snd, Category.assoc, stageTargetMap_snd,
        stageHomAux_snd, ← Category.assoc, imageTransition_comp, he]

include h hf hh₁ hh₂ in
/-- **Stacks Project, Tag 0CNR, existence**, reduced to its one external input: a morphism
`X_{i₀} ⟶ V` over `S_{i₂}` inducing `X ⟶ Y ⟶ V`. -/
theorem nonempty_morphismAt_of_hom_model [QuasiCompact pX] :
    Nonempty (MorphismAt D f GX GY i₀ hX hY) := by
  refine ⟨systemMorphismAux hf hh₁ hh₂, fun j ↦ ?_, fun j ↦ ?_⟩
  · show stageMorphismAux hf hh₁ hh₂ j ≫ _ ≫ _ = _
    rw [stageMorphismAux_imageι_assoc, stageHomAux_fst]
  · refine (cancel_mono (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).imageι).mp ?_
    show ((stageMap GX ((Over.map ((homOfLE hX).op)).obj j)).toImage ≫
        stageMorphismAux hf hh₁ hh₂ j) ≫ _ =
      (f ≫ (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).toImage) ≫ _
    rw [Category.assoc, stageMorphismAux_imageι, Category.assoc, Scheme.Hom.toImage_imageι]
    exact toImage_comp_stageHomAux hf hh₁ hh₂ j

end Construction

end LimitNoetherianSituation

end AlgebraicGeometry

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

open GoodDiagram

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}
  {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
  {f : X ⟶ Y} {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
  {i₀ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}

namespace MorphismAt

/-- The component of a system morphism at a stage, read inside the base-changed model of `GY`,
has the structure morphism of the restricted image system of `GX` as its image over the base. -/
lemma comp_modelMap (M : MorphismAt D f GX GY i₀ hX hY) (j : Over (op i₀)) :
    (M.maps.app j ≫ (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).imageι ≫
        pullback.snd _ _) ≫ GY.modelMap = (GX.imageSystemToBase hX hY).app j := by
  rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% (M.over_base j)]
  rfl

/-- The component of a system morphism, read in the model `GY.W`, is the restriction of its
component at any earlier stage. -/
lemma comp_snd_map (M : MorphismAt D f GX GY i₀ hX hY) {j k : Over (op i₀)} (b : j ⟶ k) :
    M.maps.app j ≫ (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).imageι ≫
        pullback.snd _ _ =
      imageTransition GX ((Over.map ((homOfLE hX).op)).map b) ≫ M.maps.app k ≫
        (stageMap GY ((Over.map ((homOfLE hY).op)).obj k)).imageι ≫ pullback.snd _ _ := by
  have hnat : imageTransition GX ((Over.map ((homOfLE hX).op)).map b) ≫ M.maps.app k =
      M.maps.app j ≫ imageTransition GY ((Over.map ((homOfLE hY).op)).map b) :=
    M.maps.naturality b
  conv_rhs => rw [← Category.assoc, hnat, Category.assoc, imageTransition_imageι_assoc,
    stageTargetMap_snd]

/-- The component of a system morphism, read in the model `GY.W`, pulled back along the canonical
map from `X`, is `X ⟶ Y ⟶ V`. -/
lemma toImage_comp_snd (M : MorphismAt D f GX GY i₀ hX hY) (j : Over (op i₀)) :
    (stageMap GX ((Over.map ((homOfLE hX).op)).obj j)).toImage ≫ M.maps.app j ≫
        (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).imageι ≫ pullback.snd _ _ =
      f ≫ GY.toModel := by
  rw [reassoc_of% (M.induces j)]
  show f ≫ (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).toImage ≫
    (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).imageι ≫ pullback.snd _ _ = _
  rw [Scheme.Hom.toImage_imageι_assoc, stageMap_snd]

end MorphismAt

/-- **Stacks Project, Tag 0CNR, existence**, with Tag 0CNQ for the source good diagram taken as
the hypothesis `hGX`. A morphism of schemes over the limit is realized by a morphism of the
systems of images on a sufficiently late common tail.

`AlgebraicGeometry.LimitNoetherianSituation.exists_morphismAt` discharges `hGX`; this form is
stated here because Tag 0CNQ is proved in a module above this one. -/
theorem exists_morphismAt_of_isLimit (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (hGX : IsLimit (GoodDiagram.imageCone GX)) :
    ∃ (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀),
      Nonempty (MorphismAt D f GX GY i₀ hX hY) := by
  obtain ⟨i', h₁', h₂'⟩ := directed_of (· ≤ ·) GX.index GY.index
  have _ : ∀ j, CompactSpace
      ((Over.map ((homOfLE h₁').op) ⋙ imageSystem GX).obj j) :=
    GX.compactSpace_imageSystem h₁'
  have _ : ∀ j, QuasiSeparatedSpace
      ((Over.map ((homOfLE h₁').op) ⋙ imageSystem GX).obj j) :=
    GX.quasiSeparatedSpace_imageSystem h₁'
  have _ : ∀ {j k : Over (op i')} (a : j ⟶ k), IsAffineHom
      ((Over.map ((homOfLE h₁').op) ⋙ imageSystem GX).map a) :=
    GX.isAffineHom_imageSystem h₁'
  have _ : LocallyOfFiniteType GY.modelMap := GY.locallyOfFiniteType
  have _ : LocallyOfFinitePresentation GY.modelMap := inferInstance
  have _ := GX.isSchemeTheoreticallyDominant_whisker h₁'
  obtain ⟨j₀, g, hg₁, hg₂⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_dominant_slice
      (Over.map ((homOfLE h₁').op) ⋙ imageSystem GX)
      (GX.imageSystemToBase h₁' h₂') GY.modelMap
      ((imageCone GX).whisker (Over.map ((homOfLE h₁').op)))
      (GX.isLimitImageConeWhisker hGX h₁')
      (f ≫ GY.toModel) (by
        ext j
        show (stageMap GX ((Over.map ((homOfLE h₁').op)).obj j)).toImage ≫
            (stageMap GX ((Over.map ((homOfLE h₁').op)).obj j)).imageι ≫
              pullback.fst _ _ ≫ D.system.map (j.hom ≫ (homOfLE h₂').op) =
          (f ≫ GY.toModel) ≫ GY.modelMap
        rw [Scheme.Hom.toImage_imageι_assoc, stageMap_fst_assoc, D.limitCone.w,
          Category.assoc, ← GY.commutes, ← Category.assoc, hf])
  refine ⟨unop j₀.left, h₁'.trans (leOfHom j₀.hom.unop),
    h₂'.trans (leOfHom j₀.hom.unop), ?_⟩
  refine nonempty_morphismAt_of_hom_model (h := imageTransition GX
    (Over.homMk (𝟙 _) (Subsingleton.elim _ _) :
      Over.mk ((homOfLE (h₁'.trans (leOfHom j₀.hom.unop))).op) ⟶
        (Over.map ((homOfLE h₁').op)).obj j₀) ≫ g) hf ?_ ?_
  · rw [← Category.assoc, toImage_comp_imageTransition]
    exact hg₁
  · rw [Category.assoc, hg₂]
    exact imageTransition_imageι_fst_map GX _ _ _

/-- **Stacks Project, Tag 0CNR, eventual uniqueness**, with Tag 0CNQ for the source good diagram
taken as the hypothesis `hGX`. Two system morphisms inducing the same limit morphism agree at
every sufficiently late stage.

`AlgebraicGeometry.LimitNoetherianSituation.eventually_eq_morphismAt` discharges `hGX`. -/
theorem eventually_eq_morphismAt_of_isLimit
    (D : LimitNoetherianSituation.{v, u} I) {X Y : Scheme.{u}}
    {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F G : MorphismAt D f GX GY i₀ hX hY)
    (hGX : IsLimit (GoodDiagram.imageCone GX)) :
    ∃ (i₃ : I) (_hi : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)) (_hj : i₃ ≤ unop j.left),
        F.maps.app j = G.maps.app j := by
  have _ := GX.quasiCompact_toLimit
  have _ := GX.locallyOfFiniteType_toLimit
  have _ := GX.quasiSeparated_toLimit
  have _ : ∀ j, CompactSpace
      ((Over.map ((homOfLE hX).op) ⋙ imageSystem GX).obj j) :=
    GX.compactSpace_imageSystem hX
  have _ : ∀ {j k : Over (op i₀)} (a : j ⟶ k), IsAffineHom
      ((Over.map ((homOfLE hX).op) ⋙ imageSystem GX).map a) :=
    GX.isAffineHom_imageSystem hX
  have _ : LocallyOfFiniteType GY.modelMap := GY.locallyOfFiniteType
  have _ := GX.isSchemeTheoreticallyDominant_whisker hX
  obtain ⟨k, hik, hjk, hk⟩ :=
    Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant_slice
      (Over.map ((homOfLE hX).op) ⋙ imageSystem GX)
      (GX.imageSystemToBase hX hY) GY.modelMap
      ((imageCone GX).whisker (Over.map ((homOfLE hX).op)))
      (GX.isLimitImageConeWhisker hGX hX)
      (i := Over.mk (𝟙 (op i₀)))
      (F.maps.app (Over.mk (𝟙 (op i₀))) ≫
        (stageMap GY ((Over.map ((homOfLE hY).op)).obj (Over.mk (𝟙 (op i₀))))).imageι ≫
          pullback.snd _ _)
      (F.comp_modelMap _).symm
      (j := Over.mk (𝟙 (op i₀)))
      (G.maps.app (Over.mk (𝟙 (op i₀))) ≫
        (stageMap GY ((Over.map ((homOfLE hY).op)).obj (Over.mk (𝟙 (op i₀))))).imageι ≫
          pullback.snd _ _)
      (G.comp_modelMap _).symm
      (by
        show (stageMap GX ((Over.map ((homOfLE hX).op)).obj (Over.mk (𝟙 (op i₀))))).toImage ≫
            _ = (stageMap GX ((Over.map ((homOfLE hX).op)).obj (Over.mk (𝟙 (op i₀))))).toImage ≫ _
        rw [F.toImage_comp_snd, G.toImage_comp_snd])
  refine ⟨unop k.left, leOfHom k.hom.unop, fun j hj ↦ ?_⟩
  refine (cancel_mono (stageMap GY ((Over.map ((homOfLE hY).op)).obj j)).imageι).mp ?_
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, F.over_base j, G.over_base j]
  · have hcb : (Over.homMk ((homOfLE hj).op) (Subsingleton.elim _ _) : j ⟶ k) ≫ hik =
      Over.homMk j.hom (Subsingleton.elim _ _) := Subsingleton.elim _ _
    have hji : hjk = hik := Subsingleton.elim _ _
    rw [Category.assoc, Category.assoc,
      F.comp_snd_map (Over.homMk j.hom (Subsingleton.elim _ _) : j ⟶ Over.mk (𝟙 (op i₀))),
      G.comp_snd_map (Over.homMk j.hom (Subsingleton.elim _ _) : j ⟶ Over.mk (𝟙 (op i₀))),
      ← hcb, Functor.map_comp, ← imageTransition_comp]
    rw [hji] at hk
    simp only [Functor.comp_map] at hk
    rw [Category.assoc, Category.assoc, hk]

end LimitNoetherianSituation

end AlgebraicGeometry
