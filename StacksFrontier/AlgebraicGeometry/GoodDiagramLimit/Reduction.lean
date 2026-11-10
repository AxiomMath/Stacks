module

public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.ImageSystem
public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.Situation
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange

/-!
# The limit assertion of a good diagram, reduced to one statement about kernels

Fix a good diagram for `X ⟶ S` over the stage `S_i`, as in
`StacksFrontier/AlgebraicGeometry/LimitMorphismAt/Situation.lean`, and let `X_{i'}` be the
inverse system of scheme-theoretic images of `X` in the base changes `S_{i'} ×_{S_i} W` of the
model, as in `StacksFrontier/AlgebraicGeometry/LimitMorphismAt/ImageSystem.lean`. Stacks 0CNQ
asserts that the canonical cone from `X` to that system is a limit cone.

This file proves that assertion *equivalent* to a single statement with no limits, no cones and
no functors in it: that the quasi-coherent ideal of `X` inside `S ×_{S_i} W` is detected by the
images at the stages.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.KerDetectedOnStages`: for every
  morphism `w` into `S ×_{S_i} W` whose composite with each projection to `S_{i'} ×_{S_i} W`
  kills the ideal of `X_{i'}`, the morphism `w` already kills the ideal of `X`.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isLimit_imageCone_of_kerDetected` and
  `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.kerDetectedOnStages_of_isLimit`: the
  two implications, assembled in
  `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.nonempty_isLimit_imageCone_iff`.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.stageConeIsLimit`: the base changes
  `S_{i'} ×_{S_i} W` of the model are an inverse system with limit `S ×_{S_i} W`.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.induced_comp_stageProj`: the stage map
  of `StacksFrontier/AlgebraicGeometry/LimitMorphismAt/ImageSystem.lean` is the closed
  immersion `X ⟶ S ×_{S_i} W` followed by a projection of that limit.

## Implementation notes

The system `GoodDiagram.stageSystem` is `AlgebraicGeometry.baseChangeDiagram` of the model with
its objects spelled as the pullbacks `GoodDiagram.stageTarget` and its morphisms as
`GoodDiagram.stageTargetMap`, so that `rw` works on both. The objects of
`AlgebraicGeometry.baseChangeDiagram` are not reducibly these pullbacks, and neither are the
vertex and objects of `GoodDiagram.imageCone` and `GoodDiagram.imageSystem`; for the same reason
the legs `GoodDiagram.imageConeπ` and `GoodDiagram.coneOfKerπ` are definitions with their types
written out.

The equivalence uses none of the hypotheses `QuasiSeparated f`, `LocallyOfFiniteType f`,
`QuasiCompact f` of Stacks 0CNQ, and the index type lives in a universe `v` independent of the
scheme universe `u`.

## References

* [Stacks Project, Tag 0CNQ](https://stacks.math.columbia.edu/tag/0CNQ).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I} {X : Scheme.{u}} {f : X ⟶ D.limitScheme}
  (G : GoodDiagram D f)

/-- The model of a good diagram, viewed as a scheme over the stage it is defined over. -/
abbrev modelOver : Over (D.stage G.index) := Over.mk G.modelMap

/-- The inverse system of base changes `S_{i'} ×_{S_i} W` of the model of a good diagram, with
objects `GoodDiagram.stageTarget` and transition morphisms `GoodDiagram.stageTargetMap`. -/
noncomputable abbrev stageSystem : Over (op G.index) ⥤ Scheme.{u} where
  obj j := G.stageTarget j
  map a := G.stageTargetMap a
  map_id j := G.stageTargetMap_id j
  map_comp a b := (G.stageTargetMap_comp a b).symm

/-- The projection from `S ×_{S_i} W` to the base change `S_{i'} ×_{S_i} W` of the model. -/
noncomputable def stageProj (j : Over (op G.index)) :
    pullback (D.proj G.index) G.modelMap ⟶ G.stageTarget j :=
  pullback.lift (pullback.fst (D.proj G.index) G.modelMap ≫ D.limitCone.π.app j.left)
    (pullback.snd (D.proj G.index) G.modelMap) (by
      rw [Category.assoc, D.limitCone.w j.hom]
      exact pullback.condition)

/-- The first component of the projection `S ×_{S_i} W ⟶ S_{i'} ×_{S_i} W` is the first projection
followed by the limit projection `S ⟶ S_{i'}`. -/
@[simp]
lemma stageProj_fst (j : Over (op G.index)) :
    G.stageProj j ≫ pullback.fst (D.system.map j.hom) G.modelMap =
      pullback.fst (D.proj G.index) G.modelMap ≫ D.limitCone.π.app j.left :=
  pullback.lift_fst _ _ _

/-- The second component of the projection `S ×_{S_i} W ⟶ S_{i'} ×_{S_i} W` is the second
projection to `W`. -/
@[simp]
lemma stageProj_snd (j : Over (op G.index)) :
    G.stageProj j ≫ pullback.snd (D.system.map j.hom) G.modelMap =
      pullback.snd (D.proj G.index) G.modelMap :=
  pullback.lift_snd _ _ _

/-- The projections of `S ×_{S_i} W` to the base changes of the model are compatible with the
transitions between those base changes. -/
@[simp]
lemma stageProj_comp_stageTargetMap {j k : Over (op G.index)} (a : j ⟶ k) :
    G.stageProj j ≫ G.stageTargetMap a = G.stageProj k := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, G.stageTargetMap_fst, ← Category.assoc, G.stageProj_fst,
      G.stageProj_fst, Category.assoc, D.limitCone.w a.left]
  · rw [Category.assoc, G.stageTargetMap_snd, G.stageProj_snd, G.stageProj_snd]

/-- The cone on the system of base changes of the model whose vertex is `S ×_{S_i} W`. -/
noncomputable def stageCone : Cone G.stageSystem where
  pt := pullback (D.proj G.index) G.modelMap
  π.app j := G.stageProj j
  π.naturality j k a := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
    exact (G.stageProj_comp_stageTargetMap a).symm

/-- The legs of `GoodDiagram.stageCone` are the projections `GoodDiagram.stageProj`. -/
@[simp]
lemma stageCone_π_app (j : Over (op G.index)) : G.stageCone.π.app j = G.stageProj j := rfl

/-- `S ×_{S_i} W` is the limit of the base changes `S_{i'} ×_{S_i} W` of the model: it is the base
change to the limit `S` of the model over the stage `S_i`, and base change preserves the cofiltered
limit of the system. -/
noncomputable def stageConeIsLimit : IsLimit G.stageCone :=
  baseChangeConeIsLimit D.system D.isLimit (op G.index) G.modelOver

/-- Two morphisms into `S ×_{S_i} W` agreeing after every projection to a base change of the model
are equal. -/
lemma hom_ext_stageProj {Z : Scheme.{u}} {p q : Z ⟶ pullback (D.proj G.index) G.modelMap}
    (h : ∀ j : Over (op G.index), p ≫ G.stageProj j = q ≫ G.stageProj j) : p = q :=
  G.stageConeIsLimit.hom_ext h

/-- Every stage map of a good diagram is its closed immersion into `S ×_{S_i} W` followed by the
projection of the limit to that stage. -/
@[simp]
lemma induced_comp_stageProj (j : Over (op G.index)) :
    G.induced ≫ G.stageProj j = G.stageMap j :=
  pullback.hom_ext
    (by rw [Category.assoc, G.stageProj_fst, ← Category.assoc, G.induced_fst, G.stageMap_fst])
    (by rw [Category.assoc, G.stageProj_snd, G.induced_snd, G.stageMap_snd])

/-- The morphism `X ⟶ S ×_{S_i} W` of a good diagram is a closed immersion. -/
instance isClosedImmersion_induced : IsClosedImmersion G.induced := G.isClosedImmersion

/-- The closed embeddings of the scheme-theoretic images into the base changes of the model, as a
natural transformation from the image system to the system of base changes. -/
noncomputable def imageSystemι : G.imageSystem ⟶ G.stageSystem where
  app j := (G.stageMap j).imageι
  naturality _ _ a := G.imageSystem_map_imageι a

/-- The embedding of the scheme-theoretic image at a stage into `S_{i'} ×_{S_i} W` is a closed
immersion. -/
instance isClosedImmersion_imageSystemι_app (j : Over (op G.index)) :
    IsClosedImmersion (G.imageSystemι.app j) :=
  inferInstanceAs (IsClosedImmersion (G.stageMap j).imageι)

/-- The ideal of the scheme-theoretic image at a stage is the kernel of the stage map. -/
lemma ker_imageSystemι_app (j : Over (op G.index)) :
    (G.imageSystemι.app j).ker = (G.stageMap j).ker :=
  Scheme.Hom.ker_imageι _

/-- The leg of the canonical cone at a stage, as a morphism from `X` to the object of the image
system. -/
noncomputable def imageConeπ (j : Over (op G.index)) : X ⟶ G.imageSystem.obj j :=
  G.imageCone.π.app j

/-- The legs of `GoodDiagram.imageCone` are the morphisms `GoodDiagram.imageConeπ`. -/
lemma imageCone_π_app_eq (j : Over (op G.index)) :
    G.imageCone.π.app j = G.imageConeπ j :=
  rfl

/-- The leg of the canonical cone at a stage followed by the embedding of the image is the stage
map. -/
@[simp]
lemma imageConeπ_comp_imageSystemι (j : Over (op G.index)) :
    G.imageConeπ j ≫ G.imageSystemι.app j = G.stageMap j :=
  G.imageCone_π_app_imageι j

/-- The cone on the system of base changes of the model obtained from a cone on the system of
scheme-theoretic images by composing with the closed embeddings of the images. -/
noncomputable def ambientCone (c : Cone G.imageSystem) : Cone G.stageSystem where
  pt := c.pt
  π.app j := c.π.app j ≫ G.imageSystemι.app j
  π.naturality j k a := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
    rw [Category.assoc, ← G.imageSystemι.naturality a, ← Category.assoc, c.w a]

/-- The legs of `GoodDiagram.ambientCone c` are the legs of `c` followed by the embeddings of the
images. -/
@[simp]
lemma ambientCone_π_app (c : Cone G.imageSystem) (j : Over (op G.index)) :
    (G.ambientCone c).π.app j = c.π.app j ≫ G.imageSystemι.app j :=
  rfl

/-- The comparison morphism from the vertex of a cone on the image system into `S ×_{S_i} W`. -/
noncomputable def ambientLift (c : Cone G.imageSystem) :
    c.pt ⟶ pullback (D.proj G.index) G.modelMap :=
  G.stageConeIsLimit.lift (G.ambientCone c)

/-- The comparison morphism `GoodDiagram.ambientLift c` followed by a projection to a stage is the
leg of `c` followed by the embedding of the image. -/
@[simp]
lemma ambientLift_comp_stageProj (c : Cone G.imageSystem) (j : Over (op G.index)) :
    G.ambientLift c ≫ G.stageProj j = c.π.app j ≫ G.imageSystemι.app j :=
  G.stageConeIsLimit.fac (G.ambientCone c) j

/-- The quasi-coherent ideal of `X` inside `S ×_{S_i} W` is detected by the scheme-theoretic
images at the stages: a morphism into `S ×_{S_i} W` whose composite with the projection to each
`S_{i'} ×_{S_i} W` kills the ideal of the image `X_{i'}` already kills the ideal of `X`. -/
def KerDetectedOnStages : Prop :=
  ∀ {Z : Scheme.{u}} (w : Z ⟶ pullback (D.proj G.index) G.modelMap),
    (∀ j : Over (op G.index), (G.stageMap j).ker ≤ (w ≫ G.stageProj j).ker) →
      G.induced.ker ≤ w.ker

/-- The comparison morphism `GoodDiagram.ambientLift c` followed by the projection to a stage kills
the ideal of the image at that stage. -/
lemma ker_le_ker_ambientLift_comp_stageProj (c : Cone G.imageSystem) (j : Over (op G.index)) :
    (G.stageMap j).ker ≤ (G.ambientLift c ≫ G.stageProj j).ker := by
  rw [G.ambientLift_comp_stageProj c j]
  exact (G.ker_imageSystemι_app j).symm.le.trans (Scheme.Hom.le_ker_comp (c.π.app j) _)

/-- The morphism from the vertex of a cone on the image system to `X`, obtained by lifting the
comparison morphism into `S ×_{S_i} W` through the closed immersion `X ⟶ S ×_{S_i} W`. -/
noncomputable def kerLift (H : G.KerDetectedOnStages) (c : Cone G.imageSystem) : c.pt ⟶ X :=
  @IsClosedImmersion.lift _ _ _ G.induced (G.ambientLift c) G.isClosedImmersion
    (H (G.ambientLift c) (G.ker_le_ker_ambientLift_comp_stageProj c))

/-- The morphism `GoodDiagram.kerLift H c` followed by the closed immersion `X ⟶ S ×_{S_i} W` is
the comparison morphism `GoodDiagram.ambientLift c`. -/
@[simp]
lemma kerLift_comp_induced (H : G.KerDetectedOnStages) (c : Cone G.imageSystem) :
    G.kerLift H c ≫ G.induced = G.ambientLift c :=
  IsClosedImmersion.lift_fac _ _ _

/-- The morphism `GoodDiagram.kerLift H c` followed by the leg of the canonical cone at a stage is
the leg of `c` at that stage. -/
lemma kerLift_fac (H : G.KerDetectedOnStages) (c : Cone G.imageSystem) (j : Over (op G.index)) :
    G.kerLift H c ≫ G.imageConeπ j = c.π.app j := by
  rw [← cancel_mono (G.imageSystemι.app j), Category.assoc,
    G.imageConeπ_comp_imageSystemι j, ← G.induced_comp_stageProj j, ← Category.assoc,
    G.kerLift_comp_induced H c, G.ambientLift_comp_stageProj c j]

/-- A morphism `m` into `X` followed by `X ⟶ S ×_{S_i} W` is `w` as soon as their composites with
the projections to the stages agree, `m` being followed by the legs of the canonical cone. -/
private lemma comp_induced_eq_of_comp_imageConeπ {Z : Scheme.{u}} (m : Z ⟶ X)
    (w : Z ⟶ pullback (D.proj G.index) G.modelMap)
    (h : ∀ j : Over (op G.index), (m ≫ G.imageConeπ j) ≫ G.imageSystemι.app j = w ≫ G.stageProj j) :
    m ≫ G.induced = w := by
  refine G.hom_ext_stageProj fun j ↦ ?_
  rw [Category.assoc, G.induced_comp_stageProj j, ← G.imageConeπ_comp_imageSystemι j,
    ← Category.assoc, h j]

/-- A morphism to `X` whose composites with the legs of the canonical cone are the legs of `c` is
`GoodDiagram.kerLift H c`. -/
lemma kerLift_uniq (H : G.KerDetectedOnStages) (c : Cone G.imageSystem) {m : c.pt ⟶ X}
    (hm : ∀ j : Over (op G.index), m ≫ G.imageConeπ j = c.π.app j) :
    m = G.kerLift H c := by
  rw [← cancel_mono G.induced, G.kerLift_comp_induced H c]
  exact G.comp_induced_eq_of_comp_imageConeπ m _ fun j ↦ by
    rw [hm j, G.ambientLift_comp_stageProj c j]

/-- If the ideal of `X` in `S ×_{S_i} W` is detected on the stages, then `X`
is the limit of the inverse system of its scheme-theoretic images. -/
noncomputable def isLimit_imageCone_of_kerDetected (H : G.KerDetectedOnStages) :
    IsLimit G.imageCone where
  lift c := G.kerLift H c
  fac c j := G.kerLift_fac H c j
  uniq c _ hm := G.kerLift_uniq H c hm

/-- The cone on the image system obtained from a morphism into `S ×_{S_i} W` whose composite with
every projection kills the ideal of the image at that stage. -/
noncomputable def coneOfKer {Z : Scheme.{u}} (w : Z ⟶ pullback (D.proj G.index) G.modelMap)
    (hw : ∀ j : Over (op G.index), (G.stageMap j).ker ≤ (w ≫ G.stageProj j).ker) :
    Cone G.imageSystem where
  pt := Z
  π.app j := IsClosedImmersion.lift (G.imageSystemι.app j) (w ≫ G.stageProj j)
    ((G.ker_imageSystemι_app j).le.trans (hw j))
  π.naturality j k a := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
    rw [← cancel_mono (G.imageSystemι.app k), Category.assoc, G.imageSystemι.naturality a,
      ← Category.assoc, IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac, Category.assoc,
      G.stageProj_comp_stageTargetMap a]

/-- The leg of `GoodDiagram.coneOfKer w hw` at a stage, as a morphism from `Z`. -/
noncomputable def coneOfKerπ {Z : Scheme.{u}} (w : Z ⟶ pullback (D.proj G.index) G.modelMap)
    (hw : ∀ j : Over (op G.index), (G.stageMap j).ker ≤ (w ≫ G.stageProj j).ker)
    (j : Over (op G.index)) : Z ⟶ G.imageSystem.obj j :=
  (G.coneOfKer w hw).π.app j

/-- The leg of `GoodDiagram.coneOfKer w hw` at a stage followed by the embedding of the image is
`w` followed by the projection to that stage. -/
@[simp]
lemma coneOfKerπ_comp_imageSystemι {Z : Scheme.{u}}
    (w : Z ⟶ pullback (D.proj G.index) G.modelMap)
    (hw : ∀ j : Over (op G.index), (G.stageMap j).ker ≤ (w ≫ G.stageProj j).ker)
    (j : Over (op G.index)) :
    G.coneOfKerπ w hw j ≫ G.imageSystemι.app j = w ≫ G.stageProj j :=
  IsClosedImmersion.lift_fac _ _ _

/-- If `X` is the limit of the inverse system of its scheme-theoretic images, then
the ideal of `X` in `S ×_{S_i} W` is detected on the stages. -/
theorem kerDetectedOnStages_of_isLimit (hl : IsLimit G.imageCone) : G.KerDetectedOnStages := by
  intro Z w hw
  rw [← G.comp_induced_eq_of_comp_imageConeπ (hl.lift (G.coneOfKer w hw)) w fun j ↦ by
    rw [← G.imageCone_π_app_eq, hl.fac]
    exact G.coneOfKerπ_comp_imageSystemι w hw j]
  exact Scheme.Hom.le_ker_comp _ _

/-- `X` is the limit of the inverse system of its scheme-theoretic images exactly when the
ideal of `X` inside `S ×_{S_i} W` is detected by the scheme-theoretic images at the stages. -/
theorem nonempty_isLimit_imageCone_iff :
    Nonempty (IsLimit G.imageCone) ↔ G.KerDetectedOnStages :=
  ⟨fun ⟨hl⟩ ↦ G.kerDetectedOnStages_of_isLimit hl,
    fun H ↦ ⟨G.isLimit_imageCone_of_kerDetected H⟩⟩

end AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram
