module

public import StacksFrontier.AlgebraicGeometry.GoodDiagramLimit.Uniqueness
public import StacksFrontier.AlgebraicGeometry.KerDetected.Basic
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit

/-!
# Eventual uniqueness of a morphism of image systems, from the limit assertion of Stacks 0CNQ

Let `S` be the limit of a directed inverse system of Noetherian schemes with affine transition
morphisms, let `f : X ⟶ Y` be a morphism of schemes over `S`, let good diagrams for `X` and for
`Y` be given, and let `F`, `G` be two morphisms of the associated inverse systems of
scheme-theoretic images on the stages above a common index, both inducing `f`, as in
`StacksFrontier/AlgebraicGeometry/LimitMorphismAt/MorphismAt.lean`.

This file proves the eventual-uniqueness half of Stacks 0CNR, with no hypothesis on either
model, from the limit assertion of Stacks 0CNQ and the rigidity of morphisms out of a cofiltered
limit into a scheme locally of finite type over a stage.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.restrictedStageProj`: the structure
  morphism of a stage of the image system restricted to the stages above a common index, down to
  the corresponding stage of the base system.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.restrictedStructureMap`: that
  restricted image system viewed as a system of schemes over the stage of the target's good
  diagram.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.modelComponent`: the component of a
  stage morphism along the model of the target's good diagram.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isLimitImageCone`: the limit assertion
  of Stacks 0CNQ with its three morphism hypotheses *discharged* — they follow from the good
  diagram itself (see "What the good diagram already gives" below).
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isLimitWhiskerImageCone`: the same
  assertion for the image system restricted to the stages above a later index.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.exists_eq_app`: two morphisms of the
  image systems inducing the same morphism on the limits agree at *some* stage.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.eventually_eq_morphismAt`: the
  eventual-uniqueness conclusion of Stacks 0CNR.

## Route

A morphism `X_j ⟶ Y_j` of stages is pinned by its two components along the closed embedding
`Y_j ↪ S_j ×_{S_{i_Y}} V` of the target into the base change of the target's model. The
component to `S_j` is fixed by the axiom `MorphismAt.over_base`, which `F` and `G` share, so
everything happens in the component to the model `V`, and
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.modelComponent` is that component.

The two model components agree after the cone leg `X ⟶ X_j`, by the axiom `MorphismAt.induces`.
`X` is the limit of the restricted image system, so
`AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_initiallySmall`
— the injective half of Stacks 01ZC, whose hypotheses are met because the image stages are
compact with affine transitions and `V` is locally of finite type over its stage — makes them
agree after a transition of the system. By
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.app_comp_snd` the model component at a
later stage is that transition followed by the model component at the earlier one, so `F` and
`G` agree at that later stage outright, and
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.app_eq_of_eq_app` of
`GoodDiagramLimit/Uniqueness.lean` propagates the agreement to every stage above it.

That the restricted image cone is still a limit is `Functor.Initial.isLimitWhiskerEquiv` applied
to `CategoryTheory.Over.map`, which is initial here because the stages form a thin cofiltered
category: `Over.map g ⋙ Over.forget _` is `Over.forget _`, which Mathlib already knows to be
initial over a cofiltered category, and `Over.forget` is full as well as faithful when the
ambient category is thin.

## What the good diagram already gives

Stacks 0CNQ is stated, and tagged, with `QuasiSeparated f`, `LocallyOfFiniteType f` and
`QuasiCompact f` as hypotheses. All three are *consequences* of `GoodDiagram D f`:
`f` factors as the closed immersion `X ⟶ S ×_{S_i} W` followed by the first projection, which is
a base change of the model morphism; and the model is Noetherian, being of finite type over a
Noetherian stage, hence a quasi-separated space. So
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isLimitImageCone` needs no hypotheses
beyond the diagram.

## The residue, and why no `@[stacks 0CNR]` attribute is attached here

`EssentiallySmall.{u} I` is a hypothesis that the statement of Stacks 0CNR does not carry, and
the tag is not attached to an assertion carrying a hypothesis the source does not. It is needed because the descent of morphisms out of a cofiltered limit is proved in
Mathlib only for an index category at the scheme universe, and freed from that only up to
`CategoryTheory.InitiallySmall` — a genuine cofinality restriction, not an artifact (see
`StacksFrontier/AlgebraicGeometry/LimitUniverse/AffineTransitionLimit.lean`). The same
hypothesis is carried by Stacks 0CNN, which is what produces the good diagrams that 0CNR
consumes, so the omission is in the statement of 0CNR rather than in the mathematics.

The existence half of Stacks 0CNR is not proved here. It needs the surjective half of Stacks
01ZC — available as
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall`,
whose finite-presentation hypothesis is met since the model is of finite type over a Noetherian
stage — plus the factorisation of the resulting morphism `X_j ⟶ S_j ×_{S_{i_Y}} V` through the
scheme-theoretic image `Y_j`, and then the construction of the whole natural transformation on a
tail. None of that is carried out.

## Universe situation

The index type is at a universe `v` independent of the scheme universe `u`, as everywhere in
this development. `EssentiallySmall.{u} I` relates the two, and is the only place they meet.

## Transparency gotchas

`GoodDiagram.imageSystem` is a semireducible `def`, so a composite written with the raw
`AlgebraicGeometry.Scheme.Hom.imageι` on one side and an object of the restricted system on the
other elaborates but is rejected by `rw` as not type-correct at implicit transparency; this is
the warning in `GoodDiagramLimit/Uniqueness.lean`, and it is why the two axioms of `MorphismAt`
are used here through `Eq.trans`, `calc` and `congrArg` rather than through `rw`.

Instance search does not chain through `Scheme.Hom.imageι` on its own: `IsClosedImmersion`,
`QuasiCompact`, `IsSeparated` and `IsAffineHom` of the closed embedding of an image are
restated as named instances below, and the two lemmas that consume them are applied with their
instance arguments given explicitly, because otherwise elaboration fixes those arguments before
the expected type has forced the system object to be the image.

## References

* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR), the eventual-uniqueness
  half.
* [Stacks Project, Tag 0CNQ](https://stacks.math.columbia.edu/tag/0CNQ), the limit assertion this
  argument rests on.
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC), the rigidity of
  morphisms out of a cofiltered limit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

/-- The stages above an index form a thin category: a morphism of an overcategory is determined
by its underlying morphism, and the ambient category is thin. -/
instance isThin_over_of_isThin {T : Type v} [Category.{u} T] [Quiver.IsThin T] (c : T) :
    Quiver.IsThin (Over c) :=
  fun _ _ => ⟨fun _ _ => Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

/-- Over a thin category the forgetful functor of an overcategory is full: the triangle a
morphism of the overcategory has to make commute, commutes automatically. -/
instance full_forget_of_isThin {T : Type v} [Category.{u} T] [Quiver.IsThin T] (c : T) :
    (Over.forget c).Full where
  map_surjective g := ⟨Over.homMk g (Subsingleton.elim _ _), rfl⟩

/-- Restriction of an overcategory along a morphism of a thin cofiltered category is initial, so
limits over the larger overcategory restrict to limits over the smaller one. -/
instance initial_overMap_of_isThin {T : Type v} [Category.{u} T] [Quiver.IsThin T]
    [IsCofilteredOrEmpty T] {a b : T} (g : a ⟶ b) : (Over.map g).Initial := by
  have h : (Over.map g ⋙ Over.forget b).Initial := by
    rw [Over.mapForget_eq]
    infer_instance
  exact Functor.initial_of_comp_full_faithful _ (Over.forget b)

end CategoryTheory

namespace AlgebraicGeometry.LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

namespace GoodDiagram

variable {X : Scheme.{u}} {f : X ⟶ D.limitScheme} (G : GoodDiagram D f)

/-! ### Instances that instance search does not chain through on its own -/

/-- The closed embedding of the scheme-theoretic image at a stage. -/
instance isClosedImmersion_stageMap_imageι (j : Over (op G.index)) :
    IsClosedImmersion (G.stageMap j).imageι :=
  inferInstance

/-- A closed immersion is quasi-compact. -/
instance quasiCompact_stageMap_imageι (j : Over (op G.index)) :
    QuasiCompact (G.stageMap j).imageι :=
  inferInstance

/-- A closed immersion is separated. -/
instance isSeparated_stageMap_imageι (j : Over (op G.index)) :
    IsSeparated (G.stageMap j).imageι :=
  inferInstance

/-- A closed immersion is affine. -/
instance isAffineHom_stageMap_imageι (j : Over (op G.index)) :
    IsAffineHom (G.stageMap j).imageι :=
  inferInstance

/-- The model of a good diagram is quasi-compact, being quasi-compact over a Noetherian, hence
quasi-compact, stage. -/
instance compactSpace_model : CompactSpace G.W :=
  QuasiCompact.compactSpace_of_compactSpace G.modelMap

/-- The model of a good diagram is Noetherian, being of finite type over a Noetherian stage. -/
instance isNoetherian_model : IsNoetherian G.W where
  __ := LocallyOfFiniteType.isLocallyNoetherian G.modelMap

/-- The model morphism of a good diagram is quasi-separated, since a Noetherian scheme is a
quasi-separated space. -/
instance quasiSeparated_modelMap : QuasiSeparated G.modelMap :=
  QuasiSeparated.of_quasiSeparatedSpace _

/-- Each base change of the model is quasi-compact. -/
instance compactSpace_stageTarget (j : Over (op G.index)) : CompactSpace (G.stageTarget j) :=
  have : CompactSpace G.modelOver.left := G.compactSpace_model
  compactSpace_baseChangeDiagram_obj D.system (op G.index) G.modelOver j

/-- Each stage of the image system is quasi-compact, being a closed subscheme of a base change
of the model. -/
instance compactSpace_imageSystem_obj (j : Over (op G.index)) :
    CompactSpace (G.imageSystem.obj j) :=
  @QuasiCompact.compactSpace_of_compactSpace _ _ (G.stageMap j).imageι
    (G.quasiCompact_stageMap_imageι j) (G.compactSpace_stageTarget j)

/-- The transitions of the image system are affine: composed with the closed embedding of the
target image they are the closed embedding of the source image followed by a transition between
base changes of the model, and the closed embedding is separated. -/
instance isAffineHom_imageSystem_map {j k : Over (op G.index)} (a : j ⟶ k) :
    IsAffineHom (G.imageSystem.map a) :=
  have h : IsAffineHom (G.imageSystem.map a ≫ (G.stageMap k).imageι) :=
    (G.imageSystem_map_imageι a) ▸ (inferInstance : IsAffineHom
      ((G.stageMap j).imageι ≫ G.stageTargetMap a))
  @IsAffineHom.of_comp _ _ _ (G.imageSystem.map a) (G.stageMap k).imageι h
    (G.isSeparated_stageMap_imageι k)

include G in
/-- A scheme with a good diagram is quasi-compact over the limit: the structure morphism is the
closed immersion into the base change of the model followed by the first projection. -/
alias quasiCompact_of_goodDiagram := quasiCompact_toLimit

include G in
/-- A scheme with a good diagram is locally of finite type over the limit. -/
alias locallyOfFiniteType_of_goodDiagram := locallyOfFiniteType_toLimit

include G in
/-- A scheme with a good diagram is quasi-separated over the limit, because the model is
Noetherian. -/
alias quasiSeparated_of_goodDiagram := quasiSeparated_toLimit

/-- **Stacks Project, Tag 0CNQ, with its hypotheses discharged.** The scheme-theoretic images of
a good diagram at all later stages have limit `X`, with no hypothesis beyond the diagram: the
`QuasiSeparated`, `LocallyOfFiniteType` and `QuasiCompact` hypotheses of
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isLimit_imageCone` are consequences of
it. -/
noncomputable def isLimitImageCone : IsLimit G.imageCone :=
  have : QuasiSeparated f := G.quasiSeparated_of_goodDiagram
  have : LocallyOfFiniteType f := G.locallyOfFiniteType_of_goodDiagram
  have : QuasiCompact f := G.quasiCompact_of_goodDiagram
  G.isLimit_imageCone

/-- `X` is also the limit of the image system restricted to the stages above a later index,
because that restriction is an initial functor. -/
noncomputable def isLimitWhiskerImageCone {i₀ : I} (h : G.index ≤ i₀) :
    IsLimit (G.imageCone.whisker (Over.map (homOfLE h).op)) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.map (homOfLE h).op) G.imageCone).symm
    G.isLimitImageCone

variable {Y : Scheme.{u}} {pY : Y ⟶ D.limitScheme}

/-- The structure morphism of a stage of the restricted image system down to the corresponding
stage of the base system: the closed embedding of the image followed by the first projection of
the base change of the model. -/
noncomputable def restrictedStageProj (GX : GoodDiagram D f) {i₀ : I} (hX : GX.index ≤ i₀)
    (j : Over (op i₀)) :
    (Over.map (homOfLE hX).op ⋙ GX.imageSystem).obj j ⟶ D.system.obj j.left :=
  GX.restrictedImageι hX j ≫
    pullback.fst (D.system.map ((Over.map (homOfLE hX).op).obj j).hom) GX.modelMap

/-- The structure morphisms of the restricted image system are natural for its transitions. -/
lemma restrictedStageProj_naturality (GX : GoodDiagram D f) {i₀ : I} (hX : GX.index ≤ i₀)
    {j k : Over (op i₀)} (a : j ⟶ k) :
    (Over.map (homOfLE hX).op ⋙ GX.imageSystem).map a ≫ GX.restrictedStageProj hX k =
      GX.restrictedStageProj hX j ≫ D.system.map a.left := by
  rw [restrictedStageProj, restrictedStageProj, ← Category.assoc,
    GX.restrictedImageι_naturality hX a, Category.assoc, GX.stageTargetMap_fst, Category.assoc,
    Over.map_map_left]

/-- The restricted image system of a good diagram for `X`, as a system of schemes over the stage
of a good diagram for `Y` below the common index. This is the natural transformation that the
descent of morphisms into the model of `Y` is stated over. -/
noncomputable def restrictedStructureMap (GX : GoodDiagram D f) {i₀ : I} (hX : GX.index ≤ i₀)
    (GY : GoodDiagram D pY) (hY : GY.index ≤ i₀) :
    (Over.map (homOfLE hX).op ⋙ GX.imageSystem) ⟶
      (Functor.const (Over (op i₀))).obj (D.stage GY.index) where
  app j := GX.restrictedStageProj hX j ≫
    D.system.map ((Over.map (homOfLE hY).op).obj j).hom
  naturality j k a := by
    have hw : a.left ≫ ((Over.map (homOfLE hY).op).obj k).hom =
        ((Over.map (homOfLE hY).op).obj j).hom := Subsingleton.elim _ _
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [← Category.assoc, GX.restrictedStageProj_naturality hX a, Category.assoc,
      ← D.system.map_comp, hw]

end GoodDiagram

namespace MorphismAt

variable {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme} {f : X ⟶ Y}
  {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
  {i₀ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}

/-- The component of a stage morphism along the model of the target's good diagram: the stage
morphism, the closed embedding of the target's image, and the projection of the base change to
the model. -/
noncomputable def modelComponent (F : MorphismAt D f GX GY i₀ hX hY) (j : Over (op i₀)) :
    (Over.map (homOfLE hX).op ⋙ GX.imageSystem).obj j ⟶ GY.W :=
  F.maps.app j ≫ GY.restrictedImageι hY j ≫
    pullback.snd (D.system.map ((Over.map (homOfLE hY).op).obj j).hom) GY.modelMap

/-- The model component of a stage morphism is a morphism over the stage of the target's good
diagram: this is `MorphismAt.over_base` together with the pullback square of the base change. -/
lemma modelComponent_comp_modelMap (F : MorphismAt D f GX GY i₀ hX hY) (j : Over (op i₀)) :
    F.modelComponent j ≫ GY.modelMap = (GX.restrictedStructureMap hX GY hY).app j :=
  calc F.modelComponent j ≫ GY.modelMap
      = F.maps.app j ≫ GY.restrictedImageι hY j ≫
          pullback.snd (D.system.map ((Over.map (homOfLE hY).op).obj j).hom) GY.modelMap ≫
            GY.modelMap := by
        simp only [modelComponent, Category.assoc]
    _ = (F.maps.app j ≫ GY.restrictedImageι hY j ≫
          pullback.fst (D.system.map ((Over.map (homOfLE hY).op).obj j).hom) GY.modelMap) ≫
            D.system.map ((Over.map (homOfLE hY).op).obj j).hom := by
        rw [← pullback.condition]
        simp only [Category.assoc]
    _ = (GX.restrictedImageι hX j ≫
          pullback.fst (D.system.map ((Over.map (homOfLE hX).op).obj j).hom) GX.modelMap) ≫
            D.system.map ((Over.map (homOfLE hY).op).obj j).hom :=
        congrArg (· ≫ D.system.map ((Over.map (homOfLE hY).op).obj j).hom) (F.over_base j)
    _ = (GX.restrictedStructureMap hX GY hY).app j := rfl

/-- **Single-stage agreement.** Two morphisms of the image systems inducing the same morphism `f`
on the limits agree at some stage. -/
theorem exists_eq_app [EssentiallySmall.{u} I] (F G : MorphismAt D f GX GY i₀ hX hY) :
    ∃ k : Over (op i₀), F.maps.app k = G.maps.app k := by
  have hIS : CategoryTheory.InitiallySmall.{u} (Over (op i₀)) :=
    initiallySmall_of_essentiallySmall _
  have hAff : ∀ {j k : Over (op i₀)} (g : j ⟶ k),
      IsAffineHom ((Over.map (homOfLE hX).op ⋙ GX.imageSystem).map g) :=
    fun g => GX.isAffineHom_imageSystem_map ((Over.map (homOfLE hX).op).map g)
  have hCpt : ∀ j : Over (op i₀),
      CompactSpace ((Over.map (homOfLE hX).op ⋙ GX.imageSystem).obj j) :=
    fun j => GX.compactSpace_imageSystem_obj ((Over.map (homOfLE hX).op).obj j)
  obtain ⟨k, hik, hjk, hk⟩ :=
    Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_initiallySmall
      (Over.map (homOfLE hX).op ⋙ GX.imageSystem)
      (GX.imageCone.whisker (Over.map (homOfLE hX).op))
      (GX.restrictedStructureMap hX GY hY) GY.modelMap (GX.isLimitWhiskerImageCone hX)
      (i := Over.mk (𝟙 (op i₀))) (F.modelComponent _)
      (F.modelComponent_comp_modelMap _).symm
      (j := Over.mk (𝟙 (op i₀))) (G.modelComponent _)
      (G.modelComponent_comp_modelMap _).symm
      (by
        simp only [modelComponent, Cone.whisker_π, Functor.whiskerLeft_app, ← Category.assoc,
          F.induces, G.induces])
  refine ⟨k, ?_⟩
  have he : hjk = hik := Subsingleton.elim _ _
  rw [he] at hk
  rw [← cancel_mono (GY.restrictedImageι hY k)]
  refine pullback.hom_ext ?_ ?_ <;> simp only [Category.assoc]
  · exact (F.over_base k).trans (G.over_base k).symm
  · exact (F.app_comp_snd hik).trans (hk.trans (G.app_comp_snd hik).symm)

/-- **Stacks Project, Tag 0CNR, eventual uniqueness, up to smallness of the index.** Two
morphisms of the image systems inducing the same morphism on the limits agree at every
sufficiently late stage. -/
theorem eventually_eq_morphismAt [EssentiallySmall.{u} I] (F G : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → F.maps.app j = G.maps.app j := by
  obtain ⟨k, hk⟩ := F.exists_eq_app G
  refine ⟨unop k.left, leOfHom k.hom.unop, fun j hj => ?_⟩
  exact F.app_eq_of_eq_app G (Over.homMk (homOfLE hj).op (Subsingleton.elim _ _)) hk

end MorphismAt

end AlgebraicGeometry.LimitNoetherianSituation

/-! ### Faithfulness check

The conclusion proved above, restated with the binders of the source's own statement — every one
explicit, in the source's order — and closed by it. The only difference from the source is the
added `EssentiallySmall.{u} I`; the structure `MorphismAt` and the good diagrams it is stated
over are the library's, which are name- and type-identical to the source's.
-/

namespace Tag0CNR

open AlgebraicGeometry AlgebraicGeometry.LimitNoetherianSituation

example {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    [CategoryTheory.EssentiallySmall.{u} I] (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F G : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)) (_ : i₃ ≤ unop j.left),
        F.maps.app j = G.maps.app j :=
  F.eventually_eq_morphismAt G

end Tag0CNR

end
