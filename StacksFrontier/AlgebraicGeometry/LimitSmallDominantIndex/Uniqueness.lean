module

public import StacksFrontier.AlgebraicGeometry.LimitSmallDominantIndex.Descent
public import StacksFrontier.AlgebraicGeometry.SystemUniqueness.Basic

/-!
# Eventual uniqueness of morphisms of image systems, for an arbitrary index

Let `X` and `Y` be schemes over the limit of a Noetherian limit situation indexed by a directed
preorder `I`, with good diagrams `GX` and `GY`. Two morphisms of the image systems inducing the
same morphism `f : X ⟶ Y` on the limits agree at every sufficiently late stage. No smallness
hypothesis is placed on `I` relative to the universe of the schemes.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.tailAmbient`: the base change
  `S_{i₀} ×_{S_i} W` of the model to the common stage, over which the restricted image system is
  affine.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageOverHom`: the structure morphism
  of a stage of the restricted image system down to `tailAmbient`.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.tailImageSystem`,
  `tailImageCone` and `tailImageHom`: the restricted image system reindexed by `Set.Ici i₀`, its
  cone from `X`, and its natural family of affine morphisms to `tailAmbient`.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.exists_eq_app_of_dominant`: two
  morphisms of the image systems inducing the same morphism on the limits agree at some stage.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.eventually_eq_morphismAt_of_dominant`:
  two morphisms of the image systems inducing the same morphism on the limits agree at every
  sufficiently late stage.

## Implementation notes

The restricted image system `X_j`, `j ≥ i₀`, is affine over `S_{i₀} ×_{S_i} W`: each `X_j` is a
closed subscheme of `S_j ×_{S_i} W`, and the transition `S_j ×_{S_i} W ⟶ S_{i₀} ×_{S_i} W` is a
base change of an affine transition of the base system. Its limit vertex `X` is affine over the
same scheme, since `X ⟶ S ×_{S_i} W` is a closed immersion and `S ×_{S_i} W ⟶ S_{i₀} ×_{S_i} W`
is a projection of a cofiltered limit with affine transitions. The cone legs
`X ⟶ X_j = im(X ⟶ S_j ×_{S_i} W)` are quasi-compact and scheme-theoretically dominant, so
`AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant`
applies to the model components of the two stage morphisms at the base stage.

That statement is indexed by the opposite of a directed preorder, so the index category
`CategoryTheory.Over (Opposite.op i₀)` is replaced by the opposite of `Set.Ici i₀` along the
initial functor `AlgebraicGeometry.tailToOver`.

The index type lives in a universe `v` independent of the scheme universe `u`.

## References

* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

/-- The terminal stage of the tail above an index: the index itself. -/
public abbrev tailBase {I : Type v} [Preorder I] (i₀ : I) : Over (op i₀) :=
  Over.mk (homOfLE (le_refl i₀)).op

/-- Every stage above an index maps to the terminal one. -/
public def toTailBase {I : Type v} [Preorder I] {i₀ : I} (j : Over (op i₀)) : j ⟶ tailBase i₀ :=
  Over.homMk j.hom (Subsingleton.elim _ _)

end CategoryTheory

namespace AlgebraicGeometry.LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

namespace GoodDiagram

variable {X : Scheme.{u}} {f : X ⟶ D.limitScheme}

/-! ### Instances on the image system -/

/-- Every stage map of a good diagram is affine. -/
public instance isAffineHom_stageMap (G : GoodDiagram D f) (j : Over (op G.index)) :
    IsAffineHom (G.stageMap j) := by
  rw [← G.induced_comp_stageProj j]
  infer_instance

/-- Every leg of the image cone is quasi-compact. -/
public instance quasiCompact_imageCone_π_app (G : GoodDiagram D f) (j : Over (op G.index)) :
    QuasiCompact (G.imageCone.π.app j) := by
  rw [G.imageCone_π_app j]
  have : QuasiCompact ((G.stageMap j).toImage ≫ (G.stageMap j).imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  exact QuasiCompact.of_comp (G.stageMap j).toImage (G.stageMap j).imageι

/-! ### The restricted image system as a system affine over a fixed base -/

/-- The base change `S_{i₀} ×_{S_i} W` of the model of a good diagram to the common stage `i₀`.
The whole restricted image system is affine over this scheme. -/
public noncomputable abbrev tailAmbient (G : GoodDiagram D f) {i₀ : I} (hX : G.index ≤ i₀) :
    Scheme.{u} :=
  G.stageTarget ((Over.map (homOfLE hX).op).obj (tailBase i₀))

/-- The structure morphism of a stage of the restricted image system down to
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.tailAmbient`: the closed embedding of the
image followed by the transition between the base changes of the model. -/
public noncomputable def imageOverHom (G : GoodDiagram D f) {i₀ : I} (hX : G.index ≤ i₀)
    (j : Over (op i₀)) :
    (Over.map (homOfLE hX).op ⋙ G.imageSystem).obj j ⟶ G.tailAmbient hX :=
  G.restrictedImageι hX j ≫
    G.stageTargetMap ((Over.map (homOfLE hX).op).map (toTailBase j))

/-- The structure morphism of a stage of the restricted image system down to
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.tailAmbient` is affine. -/
public instance isAffineHom_imageOverHom (G : GoodDiagram D f) {i₀ : I} (hX : G.index ≤ i₀)
    (j : Over (op i₀)) : IsAffineHom (G.imageOverHom hX j) := by
  rw [imageOverHom]
  infer_instance

/-- The structure morphisms are natural for the transitions of the restricted system. -/
public lemma imageOverHom_naturality (G : GoodDiagram D f) {i₀ : I} (hX : G.index ≤ i₀)
    {j k : Over (op i₀)} (a : j ⟶ k) :
    (Over.map (homOfLE hX).op ⋙ G.imageSystem).map a ≫ G.imageOverHom hX k =
      G.imageOverHom hX j := by
  rw [imageOverHom, imageOverHom, ← Category.assoc, G.restrictedImageι_naturality hX a,
    Category.assoc, G.stageTargetMap_comp, ← Functor.map_comp,
    show a ≫ toTailBase k = toTailBase j from Subsingleton.elim _ _]

/-- The cone leg from `X` followed by the structure morphism of a stage is the stage map at the
base stage, independently of the stage. -/
public lemma imageCone_π_comp_imageOverHom (G : GoodDiagram D f) {i₀ : I} (hX : G.index ≤ i₀)
    (j : Over (op i₀)) :
    G.imageCone.π.app ((Over.map (homOfLE hX).op).obj j) ≫ G.imageOverHom hX j =
      G.stageMap ((Over.map (homOfLE hX).op).obj (tailBase i₀)) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ G.stageTargetMap ((Over.map (homOfLE hX).op).map (toTailBase j)))
      (G.imageCone_π_app_imageι ((Over.map (homOfLE hX).op).obj j))).trans
      (G.stageMap_comp_stageTargetMap _))

/-- The restricted image system, reindexed by the stages above `i₀` as the opposite of the
preorder `Set.Ici i₀`. -/
public noncomputable abbrev tailImageSystem (G : GoodDiagram D f) {i₀ : I} (hX : G.index ≤ i₀) :
    (Set.Ici i₀)ᵒᵖ ⥤ Scheme.{u} :=
  tailToOver i₀ ⋙ (Over.map (homOfLE hX).op ⋙ G.imageSystem)

/-- The cone from `X` to the reindexed restricted image system. -/
public noncomputable abbrev tailImageCone (G : GoodDiagram D f) {i₀ : I} (hX : G.index ≤ i₀) :
    Cone (G.tailImageSystem hX) :=
  (G.imageCone.whisker (Over.map (homOfLE hX).op)).whisker (tailToOver i₀)

/-- The natural family of affine morphisms from the reindexed restricted image system down to
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.tailAmbient`. -/
public noncomputable def tailImageHom (G : GoodDiagram D f) {i₀ : I} (hX : G.index ≤ i₀) :
    G.tailImageSystem hX ⟶ (Functor.const ((Set.Ici i₀)ᵒᵖ)).obj (G.tailAmbient hX) where
  app x := G.imageOverHom hX ((tailToOver i₀).obj x)
  naturality _ _ a := by
    simp only [Functor.const_obj_map]
    exact G.imageOverHom_naturality hX ((tailToOver i₀).map a)

/-- The cone from `X` to the reindexed restricted image system is a limit cone. -/
public noncomputable def isLimitTailImageCone (G : GoodDiagram D f) {i₀ : I}
    (hX : G.index ≤ i₀) : IsLimit (G.tailImageCone hX) :=
  have := initial_tailToOver (I := I) i₀
  (Functor.Initial.isLimitWhiskerEquiv (tailToOver i₀)
    (G.imageCone.whisker (Over.map (homOfLE hX).op))).symm (G.isLimitWhiskerImageCone hX)

end GoodDiagram

namespace MorphismAt

variable {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme} {f : X ⟶ Y}
  {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
  {i₀ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}

/-- The natural family of morphisms from the reindexed restricted image system of the source to
the stage of the target's good diagram. -/
public noncomputable def tailStructureMap (GX : GoodDiagram D pX) {i₀ : I} (hX : GX.index ≤ i₀)
    (GY : GoodDiagram D pY) (hY : GY.index ≤ i₀) :
    GX.tailImageSystem hX ⟶ (Functor.const ((Set.Ici i₀)ᵒᵖ)).obj (D.stage GY.index) where
  app x := (GX.restrictedStructureMap hX GY hY).app ((tailToOver i₀).obj x)
  naturality _ _ a := (GX.restrictedStructureMap hX GY hY).naturality ((tailToOver i₀).map a)

/-- The cone leg from `X` followed by the model component of a stage morphism does not depend on
the stage morphism: it is `f` followed by the target's own cone leg and the projection to the
model. -/
public lemma π_comp_modelComponent (F : MorphismAt D f GX GY i₀ hX hY) (j : Over (op i₀)) :
    GX.imageCone.π.app ((Over.map (homOfLE hX).op).obj j) ≫ F.modelComponent j =
      (f ≫ GY.imageCone.π.app ((Over.map (homOfLE hY).op).obj j)) ≫
        (GY.restrictedImageι hY j ≫
          pullback.snd (D.system.map ((Over.map (homOfLE hY).op).obj j).hom) GY.modelMap) :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (GY.restrictedImageι hY j ≫
      pullback.snd (D.system.map ((Over.map (homOfLE hY).op).obj j).hom) GY.modelMap))
      (F.induces j))

/-- Two morphisms of the image systems inducing the same morphism `f` on the limits agree at some
stage above `i₀`. -/
public theorem exists_eq_app_of_dominant (F G : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (hi : i₀ ≤ i₃), F.maps.app (stageAt hi) = G.maps.app (stageAt hi) := by
  have hne : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have hdir := directed_tail (I := I) i₀
  obtain ⟨k, hik, hjk, hk⟩ :=
    Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_dominant
      (GX.tailImageSystem hX) (GX.tailImageCone hX) (GX.isLimitTailImageCone hX)
      (GX.tailImageHom hX) (GX.stageMap ((Over.map (homOfLE hX).op).obj (tailBase i₀)))
      (fun x => GX.imageCone_π_comp_imageOverHom hX ((tailToOver i₀).obj x))
      (fun x => GX.isAffineHom_imageOverHom hX ((tailToOver i₀).obj x))
      (GX.isAffineHom_stageMap _)
      (fun x => GX.quasiCompact_imageCone_π_app _)
      (fun x => GX.isSchemeTheoreticallyDominant_π _)
      (fun x => GX.compactSpace_imageSystem_obj _)
      (tailStructureMap GX hX GY hY) GY.modelMap GY.locallyOfFiniteType
      (i := ⟨i₀, le_rfl⟩) (F.modelComponent (tailBase i₀))
      (F.modelComponent_comp_modelMap (tailBase i₀)).symm
      (j := ⟨i₀, le_rfl⟩) (G.modelComponent (tailBase i₀))
      (G.modelComponent_comp_modelMap (tailBase i₀)).symm
      ((F.π_comp_modelComponent (tailBase i₀)).trans
        (G.π_comp_modelComponent (tailBase i₀)).symm)
  refine ⟨k.val, k.property, ?_⟩
  have ha : stageAt k.property ⟶ tailBase i₀ := (tailToOver i₀).map ((homOfLE hik).op)
  rw [← cancel_mono (GY.restrictedImageι hY (stageAt k.property))]
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((F.over_base (stageAt k.property)).trans
      ((G.over_base (stageAt k.property)).symm.trans (Category.assoc _ _ _).symm))
  · exact (Category.assoc _ _ _).trans ((F.app_comp_snd ha).trans
      (hk.trans ((G.app_comp_snd ha).symm.trans (Category.assoc _ _ _).symm)))

/-- Two morphisms of the image systems inducing the same morphism on the limits agree at every
sufficiently late stage. -/
@[stacks 0CNR "eventual uniqueness"]
public theorem eventually_eq_morphismAt_of_dominant (F G : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → F.maps.app j = G.maps.app j :=
  F.eventually_eq_of_exists_eq_app G (F.exists_eq_app_of_dominant G)

end MorphismAt

end AlgebraicGeometry.LimitNoetherianSituation


namespace Tag0CNRDominant

open AlgebraicGeometry AlgebraicGeometry.LimitNoetherianSituation

example {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F G : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)) (_ : i₃ ≤ unop j.left),
        F.maps.app j = G.maps.app j :=
  F.eventually_eq_morphismAt_of_dominant G

end Tag0CNRDominant

end
