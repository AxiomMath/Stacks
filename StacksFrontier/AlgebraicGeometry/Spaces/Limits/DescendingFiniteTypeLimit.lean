module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteTypeModel
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# The limit of the system of scheme-theoretic images of a good diagram

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces over
a scheme `S` with affine transition morphisms — an
`AlgebraicGeometry.Space.NoetherianLimitSystem`, Stacks 0CP6 — let `X ⟶ B` be a quasi-separated
morphism of finite type, and let `G` be a diagram

```
X ⟶ W
↓    ↓
B ⟶ B_i
```

as in Stacks 0CP8, that is, an `AlgebraicGeometry.Space.GoodDiagram`. For a stage `i' ≥ i` the
space `X_{i'}` is the scheme-theoretic image of `X ⟶ B_{i'} ×_{B_i} W`, and these form the
inverse system `AlgebraicGeometry.Space.GoodDiagram.imageSystem` with the canonical cone
`AlgebraicGeometry.Space.GoodDiagram.imageCone` from `X`. Stacks 0CP9 asserts that the cone is a
limit cone, `X = lim_{i' ≥ i} X_{i'}`.

This file reduces that assertion to a single inclusion of subfunctors of `B ×_{B_i} W` and proves
one of its two halves.

The base changes `B_{i'} ×_{B_i} W` of the model to the later stages form an inverse system whose
limit is `B ×_{B_i} W`: this is Stacks 07SF, part (2), for the model, and it is nothing but the
commutation of a cofiltered limit with a fibre product, so it is obtained by transporting the
limiting cone of the system through `CategoryTheory.Over.pullback` and
`CategoryTheory.Over.forget`. Every `X_{i'}` is a subfunctor of `B_{i'} ×_{B_i} W`, so the limit
of the image system is computed inside `B ×_{B_i} W` as the intersection

`⨅_{i'} (projection to B_{i'} ×_{B_i} W)⁻¹ (X_{i'})`,

which is `AlgebraicGeometry.Space.GoodDiagram.imageInter`. Since `X ⟶ B ×_{B_i} W` is a closed
immersion, hence a monomorphism, `X` is the subfunctor `CategoryTheory.Subfunctor.range` of that
morphism, and Stacks 0CP9 becomes the equality of those two subfunctors. One inclusion is formal,
because `X` maps to every `X_{i'}`; the other is
`AlgebraicGeometry.Space.GoodDiagram.nonempty_isLimit_imageCone_iff`, which shows it to be
*equivalent* to Stacks 0CP9 and is therefore exactly what remains to be proved.

The formal inclusion already gives half of Stacks 0CP9: the cone is jointly monic, so `X` is a
subspace of the limit of the system of images. That is
`AlgebraicGeometry.Space.GoodDiagram.mono_lift_of_isLimit`.

## Main definitions

* `AlgebraicGeometry.Space.GoodDiagram.modelSystem`, `.modelCone` and `.modelπ`: the inverse
  system of base changes of the model to the later stages, its canonical cone with vertex
  `B ×_{B_i} W`, and the projections of that cone.
* `AlgebraicGeometry.Space.GoodDiagram.imageInter`: the limit of the image system, read as a
  subfunctor of `B ×_{B_i} W`.
* `AlgebraicGeometry.Space.GoodDiagram.interCone` and `.coneToModel`: the cone on the image
  system carried by that subfunctor, and the morphism to `B ×_{B_i} W` induced by an arbitrary
  cone on the image system.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.isLimit_modelCone` is **Stacks 07SF, part (2)**, for the
  model of a good diagram: the base change of the model to the limit space is the limit of its
  base changes to the later stages.
* `AlgebraicGeometry.Space.GoodDiagram.range_induced_le_imageInter`: `X` is contained in the
  limit of the system of its scheme-theoretic images.
* `AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone_of_imageInter_le` and
  `AlgebraicGeometry.Space.GoodDiagram.imageInter_le_range_induced_of_isLimit`, combined in
  `AlgebraicGeometry.Space.GoodDiagram.nonempty_isLimit_imageCone_iff`: **Stacks 0CP9 holds
  exactly when the reverse inclusion `imageInter G ≤ Subfunctor.range G.induced` does.**
* `AlgebraicGeometry.Space.GoodDiagram.eq_of_comp_imageCone_π_eq` and
  `AlgebraicGeometry.Space.GoodDiagram.mono_lift_of_isLimit` are **the monomorphism half of
  Stacks 0CP9**: the canonical cone from `X` to the system of scheme-theoretic images is jointly
  monic, so the comparison morphism from `X` to any limit of that system is a monomorphism.

## What is not proved

Stacks 0CP9 itself is not obtained. What is missing is the single inclusion

`imageInter G ≤ Subfunctor.range G.induced`,

by `AlgebraicGeometry.Space.GoodDiagram.nonempty_isLimit_imageCone_iff` equivalent to it. Being
an inclusion of subfunctors it is a pointwise statement about points of `B ×_{B_i} W` over the
objects of the big fppf site, so it needs none of the hypotheses of Stacks 0CP9 beyond the good
diagram itself, and it is amenable to the chart-local machinery of Stacks 03MB: membership in the
closed subspace `X ⊆ B ×_{B_i} W` is local on `B ×_{B_i} W` by
`AlgebraicGeometry.Space.mem_obj_of_surjective_etale` and
`AlgebraicGeometry.Space.mem_obj_of_sieve_le`, and on an affine étale chart it is the inclusion of
ideals `AlgebraicGeometry.Space.mem_obj_iff_definingIdealAt_le`.

The affine étale charts of `B ×_{B_i} W` to use are those cut out by an affine étale chart
`U₀ ⟶ W` of the model: the chart `B ×_{B_i} U₀` of `B ×_{B_i} W` is the limit of the affine charts
`B_{i'} ×_{B_i} U₀` of the stages, which is
`AlgebraicGeometry.Space.NoetherianLimitSystem.chartLimitBridge` together with
`AlgebraicGeometry.Space.NoetherianLimitSystem.isPullback_chartToLimit`. Over such a chart the
defining ideal of `X` is, by Stacks 082Z in the form
`AlgebraicGeometry.Space.definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf` and its part
(3) in the form
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact`,
the inverse image of the defining ideal of `X_{i'}` over the chart `B_{i'} ×_{B_i} U₀` at every
stage; and a regular function on the affine limit `B ×_{B_i} U₀` of affine schemes comes from one
of those stages. That is the argument of Stacks 0CP9, and of its scheme analogue
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isLimit_imageCone` of Stacks 0CNQ, whose
local computation `AlgebraicGeometry.le_iSup_comap_map_of_isLimit` is the scheme-level form of the
last step.

## Implementation notes

The system of base changes of the model is `CategoryTheory.Over.post` of the system followed by
`CategoryTheory.Over.pullback` along the structure morphism of the model and
`CategoryTheory.Over.forget`, which is the shape in which the base change of a cofiltered limit is
available: `AlgebraicGeometry.Space.isLimitPullbackLimitOverPost` proves it for the chosen limit
`CategoryTheory.Limits.limit` of the system, and the same two preservation statements prove it for
the cone carried by an `AlgebraicGeometry.Space.NoetherianLimitSystem`, which is the cone the
image system is built from. Writing the system this way makes its objects and transition morphisms
*definitionally* the fibre products and the morphisms
`AlgebraicGeometry.Space.GoodDiagram.stageTargetMap` of the image system, so no transport appears
anywhere; `AlgebraicGeometry.Space.GoodDiagram.modelCone_π_app` and
`AlgebraicGeometry.Space.GoodDiagram.modelSystem_map` record this.

No hypothesis is placed on `X` or on `f` beyond the good diagram. Stacks 0CP9 assumes `X ⟶ B` to
be quasi-separated and of finite type, but that is used only to produce the diagram of Stacks
0CP8, which is Stacks 0CP7; everything here holds for an arbitrary
`AlgebraicGeometry.Space.GoodDiagram`, and in particular the monomorphism half needs only that
`X ⟶ B ×_{B_i} W` is a closed immersion, which is one of the fields of that structure.

The reduction is stated with `Nonempty (IsLimit _)` rather than with `IsLimit _` because
`CategoryTheory.Limits.IsLimit` carries data; the two directions are also available separately as
`AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone_of_imageInter_le`, which produces the
limiting structure, and
`AlgebraicGeometry.Space.GoodDiagram.imageInter_le_range_induced_of_isLimit`.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CNQ](https://stacks.math.columbia.edu/tag/0CNQ)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ D.limitCone.pt}

/-! ### The system of base changes of the model, and its limit -/

/-- The inverse system of base changes `B_{i'} ×_{B_i} W` of the model of a good diagram to the
stages above its index. -/
noncomputable abbrev modelSystem (G : GoodDiagram B S hS hZ D f) :
    Over (op G.index) ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Over.post D.system ⋙ Over.pullback G.modelMap ⋙ Over.forget G.model

/-- The transition morphisms of the system of base-changed models are the ones the image system
is built from. -/
lemma modelSystem_map (G : GoodDiagram B S hS hZ D f) {j k : Over (op G.index)} (a : j ⟶ k) :
    (modelSystem G).map a = stageTargetMap G a := rfl

/-- The canonical cone on the system of base-changed models, with vertex the base change
`B ×_{B_i} W` of the model to the limit space. -/
noncomputable abbrev modelCone (G : GoodDiagram B S hS hZ D f) : Cone (modelSystem G) :=
  (Over.pullback G.modelMap ⋙ Over.forget G.model).mapCone
    ((Over.conePost D.system (op G.index)).obj D.limitCone)

/-- The projection `B ×_{B_i} W ⟶ B_{i'} ×_{B_i} W` from the base change of the model to the
limit space down to its base change to a later stage. -/
noncomputable def modelπ (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    pullback (D.limitCone.π.app (op G.index)) G.modelMap ⟶
      pullback (D.system.map j.hom) G.modelMap :=
  pullback.lift
    (pullback.fst (D.limitCone.π.app (op G.index)) G.modelMap ≫ D.limitCone.π.app j.left)
    (pullback.snd (D.limitCone.π.app (op G.index)) G.modelMap)
    (by rw [Category.assoc, D.limitCone.w j.hom]; exact pullback.condition)

/-- The legs of the canonical cone on the system of base-changed models are the projections
`AlgebraicGeometry.Space.GoodDiagram.modelπ`. -/
lemma modelCone_π_app (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    (modelCone G).π.app j = modelπ G j := rfl

/-- **Stacks 07SF, part (2), for the model of a good diagram.** The base change `B ×_{B_i} W` of
the model to the limit space is the limit of the base changes `B_{i'} ×_{B_i} W` to the later
stages: a fibre product commutes with the cofiltered limit of the stages. -/
noncomputable def isLimit_modelCone (G : GoodDiagram B S hS hZ D f) : IsLimit (modelCone G) :=
  isLimitOfPreserves (Over.pullback G.modelMap ⋙ Over.forget G.model)
    (Over.isLimitConePost (op G.index) D.isLimit)

/-- A morphism into `B ×_{B_i} W` is determined by its composites with the projections `modelπ`. -/
private lemma hom_ext_modelπ (G : GoodDiagram B S hS hZ D f) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a b : Y ⟶ pullback (D.limitCone.π.app (op G.index)) G.modelMap}
    (h : ∀ j, a ≫ modelπ G j = b ≫ modelπ G j) : a = b :=
  (isLimit_modelCone G).hom_ext h

/-- The projection to a later stage, followed by that stage's projection out of the fibre
product. -/
@[reassoc (attr := simp)]
lemma modelπ_fst (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    modelπ G j ≫ pullback.fst _ _ =
      pullback.fst (D.limitCone.π.app (op G.index)) G.modelMap ≫ D.limitCone.π.app j.left :=
  pullback.lift_fst _ _ _

/-- The projection to a later stage is compatible with the projections to the model. -/
@[reassoc (attr := simp)]
lemma modelπ_snd (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    modelπ G j ≫ pullback.snd _ _ =
      pullback.snd (D.limitCone.π.app (op G.index)) G.modelMap :=
  pullback.lift_snd _ _ _

/-- The projections to the stages are compatible with the transition morphisms of the system of
base-changed models. -/
lemma modelπ_comp_stageTargetMap (G : GoodDiagram B S hS hZ D f) {j k : Over (op G.index)}
    (a : j ⟶ k) : modelπ G j ≫ stageTargetMap G a = modelπ G k :=
  (modelCone G).w a

/-- The closed immersion `X ⟶ B ×_{B_i} W` of a good diagram, followed by the projection to a
later stage, is the stage map of that stage. -/
lemma induced_comp_modelπ (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    G.induced ≫ modelπ G j = stageMap G j := by
  apply pullback.hom_ext
  · rw [Category.assoc, modelπ_fst, ← Category.assoc, pullback.lift_fst, stageMap_fst]
  · rw [Category.assoc, modelπ_snd, pullback.lift_snd, stageMap_snd]

/-- Any morphism to `X`, followed by the closed immersion into `B ×_{B_i} W` and the projection to
a later stage, is its leg of the canonical cone on the image system followed by the inclusion of
that image into the base-changed model. -/
lemma comp_induced_comp_modelπ (G : GoodDiagram B S hS hZ D f)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : Y ⟶ X) (j : Over (op G.index)) :
    (m ≫ G.induced) ≫ modelπ G j =
      (m ≫ (imageCone G).π.app j) ≫ (stageImage G j).ι := by
  rw [imageCone_π_app, Category.assoc, Category.assoc, induced_comp_modelπ,
    toSchemeTheoreticImage_ι]

/-! ### The limit of the image system inside the base-changed model -/

/-- The inclusions of the scheme-theoretic images into the base-changed models, as a morphism
from the image system to the system of base-changed models. -/
noncomputable def imageToModelSystem (G : GoodDiagram B S hS hZ D f) :
    imageSystem G ⟶ modelSystem G where
  app j := (stageImage G j).ι
  naturality _ _ a := imageTransition_ι G a

/-- The limit of the image system of a good diagram, read as a subfunctor of the base change
`B ×_{B_i} W` of the model to the limit space: the intersection, over the stages above the index
of the diagram, of the inverse images of the scheme-theoretic images `X_{i'}`. -/
noncomputable def imageInter (G : GoodDiagram B S hS hZ D f) :
    Subfunctor (pullback (D.limitCone.π.app (op G.index)) G.modelMap) :=
  ⨅ j : Over (op G.index), (stageImage G j).preimage (modelπ G j)

/-- A point of the intersection lies in the inverse image of the scheme-theoretic image at every
stage. -/
lemma imageInter_le (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    imageInter G ≤ (stageImage G j).preimage (modelπ G j) :=
  iInf_le _ j

/-- **One half of Stacks 0CP9.** The space `X` is contained in the limit of the system of its
scheme-theoretic images: its morphism to each base-changed model factors through its own
scheme-theoretic image. -/
lemma range_induced_le_imageInter (G : GoodDiagram B S hS hZ D f) :
    Subfunctor.range G.induced ≤ imageInter G := by
  refine le_iInf fun j => ?_
  rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp, induced_comp_modelπ]
  exact range_le_schemeTheoreticImageSubfunctor B S hS (stageMap G j)

/-- The projection from the intersection to the scheme-theoretic image at a stage. -/
noncomputable def interToImage (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    (imageInter G).toFunctor ⟶ (stageImage G j).toFunctor :=
  Subfunctor.homOfLe (imageInter_le G j) ≫ (stageImage G j).fromPreimage (modelπ G j)

/-- The projection from the intersection to a scheme-theoretic image is compatible with the
inclusions into the base-changed models. -/
lemma interToImage_comp_ι (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    interToImage G j ≫ (stageImage G j).ι = (imageInter G).ι ≫ modelπ G j := by
  rw [interToImage, Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc,
    Subfunctor.homOfLe_ι]

/-- The projections from the intersection are compatible with the transition morphisms of the
image system. -/
lemma interToImage_comp_imageTransition (G : GoodDiagram B S hS hZ D f)
    {j k : Over (op G.index)} (a : j ⟶ k) :
    interToImage G j ≫ imageTransition G a = interToImage G k := by
  refine (cancel_mono (stageImage G k).ι).1 ?_
  rw [Category.assoc, imageTransition_ι, ← Category.assoc, interToImage_comp_ι,
    Category.assoc, modelπ_comp_stageTargetMap, interToImage_comp_ι]

/-- The cone on the image system carried by the intersection of the inverse images of the
scheme-theoretic images. -/
noncomputable def interCone (G : GoodDiagram B S hS hZ D f) : Cone (imageSystem G) where
  pt := (imageInter G).toFunctor
  π :=
    { app := interToImage G
      naturality := fun j k a => by
        have h : 𝟙 (imageInter G).toFunctor ≫ interToImage G k =
            interToImage G j ≫ imageTransition G a := by
          rw [Category.id_comp, interToImage_comp_imageTransition]
        exact h }

/-- The legs of the cone carried by the intersection are the projections
`AlgebraicGeometry.Space.GoodDiagram.interToImage`. -/
lemma interCone_π_app (G : GoodDiagram B S hS hZ D f) (j : Over (op G.index)) :
    (interCone G).π.app j = interToImage G j := rfl

/-! ### Lifting a cone on the image system to the base-changed model -/

/-- The morphism to `B ×_{B_i} W` induced by a cone on the image system: its legs land in the
scheme-theoretic images, hence in the base-changed models, and `B ×_{B_i} W` is their limit. -/
noncomputable def coneToModel (G : GoodDiagram B S hS hZ D f) (s : Cone (imageSystem G)) :
    s.pt ⟶ pullback (D.limitCone.π.app (op G.index)) G.modelMap :=
  (isLimit_modelCone G).lift ((Cone.postcompose (imageToModelSystem G)).obj s)

/-- The morphism induced by a cone on the image system is compatible with the projections to the
later stages. -/
lemma coneToModel_comp_modelπ (G : GoodDiagram B S hS hZ D f) (s : Cone (imageSystem G))
    (j : Over (op G.index)) :
    coneToModel G s ≫ modelπ G j = s.π.app j ≫ (stageImage G j).ι :=
  (isLimit_modelCone G).fac ((Cone.postcompose (imageToModelSystem G)).obj s) j

/-- The morphism to `B ×_{B_i} W` induced by a cone on the image system lands in the limit of the
image system, read as a subfunctor of `B ×_{B_i} W`. -/
lemma range_coneToModel_le (G : GoodDiagram B S hS hZ D f) (s : Cone (imageSystem G)) :
    Subfunctor.range (coneToModel G s) ≤ imageInter G := by
  refine le_iInf fun j => ?_
  rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp, coneToModel_comp_modelπ]
  simpa only [Subfunctor.range_ι] using
    Subfunctor.range_comp_le (s.π.app j) (stageImage G j).ι

/-- The morphism to `B ×_{B_i} W` induced by the cone carried by the intersection is the inclusion
of that intersection. -/
lemma coneToModel_interCone (G : GoodDiagram B S hS hZ D f) :
    coneToModel G (interCone G) = (imageInter G).ι :=
  hom_ext_modelπ G fun j => by
    rw [coneToModel_comp_modelπ]
    exact interToImage_comp_ι G j

/-- A morphism to `X` over the legs of a cone on the image system agrees, after composition with
the closed immersion into `B ×_{B_i} W`, with the morphism that cone induces. -/
lemma comp_induced_eq_coneToModel (G : GoodDiagram B S hS hZ D f) (s : Cone (imageSystem G))
    (m : s.pt ⟶ X) (hm : ∀ j, m ≫ (imageCone G).π.app j = s.π.app j) :
    m ≫ G.induced = coneToModel G s :=
  hom_ext_modelπ G fun j => by rw [comp_induced_comp_modelπ, hm j, coneToModel_comp_modelπ]

/-! ### The monomorphism half of Stacks 0CP9 -/

/-- The closed immersion `X ⟶ B ×_{B_i} W` of a good diagram is a monomorphism. -/
private lemma mono_induced (G : GoodDiagram B S hS hZ D f) : Mono G.induced :=
  mono_of_isClosedImmersion B S hS _ G.isClosedImmersion

/-- **The canonical cone from `X` to the system of its scheme-theoretic images is jointly
monic.** Two morphisms to `X` which agree after composition with every factorization of a stage
map through its scheme-theoretic image are equal.

Composing with the closed immersion `X ⟶ B ×_{B_i} W`, which is a monomorphism, the two morphisms
agree after composition with every projection of the limiting cone on the system of base-changed
models. -/
theorem eq_of_comp_imageCone_π_eq (G : GoodDiagram B S hS hZ D f)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m₁ m₂ : Y ⟶ X)
    (h : ∀ j, m₁ ≫ (imageCone G).π.app j = m₂ ≫ (imageCone G).π.app j) : m₁ = m₂ := by
  have := mono_induced G
  exact (cancel_mono G.induced).1 <| hom_ext_modelπ G fun j => by
    rw [comp_induced_comp_modelπ, comp_induced_comp_modelπ, h j]

/-- **The monomorphism half of Stacks 0CP9.** In Situation 0CP6, for a diagram as in Stacks 0CP8,
the space `X` is a *subspace* of the limit of the inverse system of the scheme-theoretic images
`X_{i'}` of `X ⟶ B_{i'} ×_{B_i} W`: the comparison morphism from `X` to the vertex of any limiting
cone on that system is a monomorphism.

The remaining half, that the comparison morphism is an isomorphism, is not proved; by
`AlgebraicGeometry.Space.GoodDiagram.nonempty_isLimit_imageCone_iff` it is equivalent to the
inclusion `imageInter G ≤ Subfunctor.range G.induced` of subfunctors of `B ×_{B_i} W`. -/
@[stacks 0CP9 "X is a subspace of the limit: the cone to the images is jointly monic"]
theorem mono_lift_of_isLimit (G : GoodDiagram B S hS hZ D f) {c : Cone (imageSystem G)}
    (hc : IsLimit c) : Mono (hc.lift (imageCone G)) where
  right_cancellation m₁ m₂ h := by
    refine eq_of_comp_imageCone_π_eq G m₁ m₂ fun j => ?_
    rw [← hc.fac (imageCone G) j, ← Category.assoc, h, Category.assoc]

/-! ### Stacks 0CP9 as an inclusion of subfunctors -/

/-- The morphism to `X` from the vertex of a cone on the image system, produced from the inclusion
of the limit of the image system into `X`. -/
noncomputable def imageConeLift (G : GoodDiagram B S hS hZ D f)
    (hle : imageInter G ≤ Subfunctor.range G.induced) (s : Cone (imageSystem G)) : s.pt ⟶ X :=
  haveI : Mono G.induced := mono_of_isClosedImmersion B S hS _ G.isClosedImmersion
  Subfunctor.lift (coneToModel G s) ((range_coneToModel_le G s).trans hle) ≫
    inv (Subfunctor.toRange G.induced)

/-- The morphism produced by `AlgebraicGeometry.Space.GoodDiagram.imageConeLift` is a
factorization, through the closed immersion `X ⟶ B ×_{B_i} W`, of the morphism the cone
induces. -/
lemma imageConeLift_comp_induced (G : GoodDiagram B S hS hZ D f)
    (hle : imageInter G ≤ Subfunctor.range G.induced) (s : Cone (imageSystem G)) :
    imageConeLift G hle s ≫ G.induced = coneToModel G s := by
  have := mono_induced G
  have hinv : inv (Subfunctor.toRange G.induced) ≫ G.induced =
      (Subfunctor.range G.induced).ι := by
    rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
  rw [imageConeLift, Category.assoc, hinv, Subfunctor.lift_ι]

/-- **Stacks 0CP9 follows from the inclusion of the limit of the image system into `X`.** If every
point of `B ×_{B_i} W` lying in all the scheme-theoretic images `X_{i'}` lies in `X`, then the
canonical cone from `X` to the image system is a limit cone.

A cone on the image system induces a morphism to `B ×_{B_i} W`, which is the limit of the
base-changed models; the inclusion makes it factor through the closed immersion `X ⟶ B ×_{B_i} W`,
and the factorization is unique because that morphism is a monomorphism. -/
noncomputable def isLimit_imageCone_of_imageInter_le (G : GoodDiagram B S hS hZ D f)
    (hle : imageInter G ≤ Subfunctor.range G.induced) : IsLimit (imageCone G) := by
  have : Mono G.induced := mono_of_isClosedImmersion B S hS _ G.isClosedImmersion
  refine
    { lift := imageConeLift G hle
      fac := fun s j => ?_
      uniq := fun s m hm => ?_ }
  · refine (cancel_mono (stageImage G j).ι).1 ?_
    rw [Category.assoc, imageCone_π_app, toSchemeTheoreticImage_ι, ← induced_comp_modelπ,
      ← Category.assoc, imageConeLift_comp_induced, coneToModel_comp_modelπ]
  · refine (cancel_mono G.induced).1 ?_
    rw [comp_induced_eq_coneToModel G s m hm, imageConeLift_comp_induced]

/-- **Stacks 0CP9 implies the inclusion of the limit of the image system into `X`.** The
intersection of the inverse images of the scheme-theoretic images carries a cone on the image
system, which lifts to `X` and recovers its own inclusion into `B ×_{B_i} W`. -/
lemma imageInter_le_range_induced_of_isLimit (G : GoodDiagram B S hS hZ D f)
    (hL : IsLimit (imageCone G)) : imageInter G ≤ Subfunctor.range G.induced := by
  have hι : hL.lift (interCone G) ≫ G.induced = (imageInter G).ι := by
    rw [comp_induced_eq_coneToModel G (interCone G) _ (hL.fac (interCone G)),
      coneToModel_interCone]
  exact (Subfunctor.range_ι _).symm.trans_le (hι ▸ Subfunctor.range_comp_le _ _)

/-- **Stacks 0CP9 is equivalent to one inclusion of subfunctors of `B ×_{B_i} W`.** The canonical
cone from `X` to the system of its scheme-theoretic images is a limit cone exactly when every
point of `B ×_{B_i} W` which lies in the scheme-theoretic image `X_{i'}` at every stage already
lies in `X`. The reverse inclusion is
`AlgebraicGeometry.Space.GoodDiagram.range_induced_le_imageInter`. -/
theorem nonempty_isLimit_imageCone_iff (G : GoodDiagram B S hS hZ D f) :
    Nonempty (IsLimit (imageCone G)) ↔ imageInter G ≤ Subfunctor.range G.induced :=
  ⟨fun ⟨hL⟩ => imageInter_le_range_induced_of_isLimit G hL,
    fun hle => ⟨isLimit_imageCone_of_imageInter_le G hle⟩⟩

end GoodDiagram

end AlgebraicGeometry.Space

end
