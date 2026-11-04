module

public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.MorphismAt

/-!
# Agreement of two morphisms of image systems propagates to all later stages

Let `f : X ⟶ Y` be a morphism of schemes over the limit `S` of a directed inverse system of
Noetherian schemes, let good diagrams for `X` and for `Y` be given, and let `F` and `G` be two
morphisms of the associated inverse systems of scheme-theoretic images on the stages above a
common index, both inducing `f`, in the sense of
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt`.

Stacks 0CNR asserts, among other things, that `F` and `G` agree at every sufficiently late stage.
We show that this follows from agreement at a single stage, with no further hypotheses: if `F`
and `G` agree at one stage then they agree at every stage above it.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.app_eq_of_eq_app`: agreement at a stage
  propagates to every stage mapping to it.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.eventually_eq_of_exists_eq_app`: `F`
  and `G` agree at every stage above some index, provided they agree at one stage.

## Implementation notes

A morphism `X_{i'} ⟶ Y_{i'}` of stages is determined by its two components along the closed
embedding `Y_{i'} ↪ S_{i'} ×_{S_{i_2}} V` of the target into the base change of the target's
model. The component to `S_{i'}` is pinned by the axiom `MorphismAt.over_base`, which `F` and `G`
share. For the component to the model `V`, naturality of `F.maps` along a transition
`a : j ⟶ j₀` and `GoodDiagram.stageTargetMap_snd` — the transition between two base changes of
the model is the identity on the model component — show that the `V`-component of `F.maps.app j`
is the transition `X_j ⟶ X_{j₀}` followed by the `V`-component of `F.maps.app j₀`. So agreement
at `j₀` forces agreement of both components at `j`, and the closed embedding of the image is a
monomorphism.

The stages above an index form the overcategory of that index in the opposite preorder, which is
thin, so the transition from a later stage to `j₀` exists as soon as the index of `j₀` is below it
and its triangle commutes automatically.

The propagation uses no quasi-compactness, no separatedness of either model, and nothing about the
limit assertion of Stacks 0CNQ. The single-stage agreement itself comes, in the source, from
identifying `X` with the limit of its image system (Stacks 0CNQ) and then applying the rigidity of
morphisms into a scheme locally of finite type over a stage,
`AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`. When the target's model
is separated over its stage, agreement holds at every stage, which is
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.app_eq`.

The index type lives in a universe `v` independent of the scheme universe `u`, and no smallness
of the index is used.

`GoodDiagram.imageSystem` is a semireducible `def`, so an object of the restricted system is not
reducibly the scheme-theoretic image it is defined to be, and a composite of `F.maps.app j` with
the raw `AlgebraicGeometry.Scheme.Hom.imageι` is rejected by `rw` as not type-correct at implicit
transparency. `GoodDiagram.restrictedImageι` is that closed embedding with its source written as
the object of the restricted system and its target as the pullback.

## References

* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR), the eventual-uniqueness
  half.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

namespace GoodDiagram

variable {Y : Scheme.{u}} {pY : Y ⟶ D.limitScheme}

/-- The closed embedding of the scheme-theoretic image at a stage of the system restricted to the
stages above a common index, with its source spelled as the object of the restricted system. -/
noncomputable def restrictedImageι (GY : GoodDiagram D pY) {i₀ : I} (hY : GY.index ≤ i₀)
    (j : Over (op i₀)) :
    (Over.map (homOfLE hY).op ⋙ GY.imageSystem).obj j ⟶
      GY.stageTarget ((Over.map (homOfLE hY).op).obj j) :=
  (GY.stageMap ((Over.map (homOfLE hY).op).obj j)).imageι

/-- The closed embedding `GoodDiagram.restrictedImageι` of the image at a stage is a closed
immersion. -/
instance isClosedImmersion_restrictedImageι (GY : GoodDiagram D pY) {i₀ : I}
    (hY : GY.index ≤ i₀) (j : Over (op i₀)) : IsClosedImmersion (GY.restrictedImageι hY j) :=
  inferInstanceAs
    (IsClosedImmersion (GY.stageMap ((Over.map (homOfLE hY).op).obj j)).imageι)

/-- The closed embeddings of the images are natural for the transitions of the restricted
system. -/
lemma restrictedImageι_naturality (GY : GoodDiagram D pY) {i₀ : I} (hY : GY.index ≤ i₀)
    {j k : Over (op i₀)} (a : j ⟶ k) :
    (Over.map (homOfLE hY).op ⋙ GY.imageSystem).map a ≫ GY.restrictedImageι hY k =
      GY.restrictedImageι hY j ≫ GY.stageTargetMap ((Over.map (homOfLE hY).op).map a) :=
  GY.imageSystem_map_imageι _

/-- The transition between two base changes of the model is the identity on the model
component, in the restricted indexing. -/
lemma stageTargetMap_restricted_snd (GY : GoodDiagram D pY) {i₀ : I} (hY : GY.index ≤ i₀)
    {j k : Over (op i₀)} (a : j ⟶ k) :
    GY.stageTargetMap ((Over.map (homOfLE hY).op).map a) ≫
        pullback.snd (D.system.map ((Over.map (homOfLE hY).op).obj k).hom) GY.modelMap =
      pullback.snd (D.system.map ((Over.map (homOfLE hY).op).obj j).hom) GY.modelMap :=
  GY.stageTargetMap_snd _

/-- The composite of the closed embedding of the image with the projection to the model is
compatible with the transitions of the restricted system. -/
lemma restrictedImageι_comp_snd (GY : GoodDiagram D pY) {i₀ : I} (hY : GY.index ≤ i₀)
    {j k : Over (op i₀)} (a : j ⟶ k) :
    GY.restrictedImageι hY j ≫
        pullback.snd (D.system.map ((Over.map (homOfLE hY).op).obj j).hom) GY.modelMap =
      (Over.map (homOfLE hY).op ⋙ GY.imageSystem).map a ≫ GY.restrictedImageι hY k ≫
        pullback.snd (D.system.map ((Over.map (homOfLE hY).op).obj k).hom) GY.modelMap := by
  rw [← Category.assoc, GY.restrictedImageι_naturality hY a, Category.assoc,
    GY.stageTargetMap_restricted_snd hY a]

end GoodDiagram

namespace MorphismAt

variable {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme} {f : X ⟶ Y}
  {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
  {i₀ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀}

/-- The model component of a stage morphism at a later stage is the transition of the source
system followed by the model component at the earlier stage. -/
lemma app_comp_snd (F : MorphismAt D f GX GY i₀ hX hY) {j k : Over (op i₀)} (a : j ⟶ k) :
    F.maps.app j ≫ GY.restrictedImageι hY j ≫
        pullback.snd (D.system.map ((Over.map (homOfLE hY).op).obj j).hom) GY.modelMap =
      (Over.map (homOfLE hX).op ⋙ GX.imageSystem).map a ≫ F.maps.app k ≫
        GY.restrictedImageι hY k ≫
          pullback.snd (D.system.map ((Over.map (homOfLE hY).op).obj k).hom) GY.modelMap := by
  rw [GY.restrictedImageι_comp_snd hY a]
  simp only [← Category.assoc, ← F.maps.naturality a]

/-- If two morphisms of the image systems inducing the same morphism on the limits agree at one
stage, they agree at every stage mapping to it, that is, at every later stage. -/
theorem app_eq_of_eq_app (F G : MorphismAt D f GX GY i₀ hX hY) {j k : Over (op i₀)} (a : j ⟶ k)
    (h : F.maps.app k = G.maps.app k) : F.maps.app j = G.maps.app j := by
  rw [← cancel_mono (GY.restrictedImageι hY j)]
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((F.over_base j).trans
      ((G.over_base j).symm.trans (Category.assoc _ _ _).symm))
  · rw [Category.assoc, Category.assoc, F.app_comp_snd a, G.app_comp_snd a, h]

/-- The stage above an index `i₃` above `i₀`, as an object of the overcategory of `i₀`. -/
abbrev stageAt {i₀ i₃ : I} (hi : i₀ ≤ i₃) : Over (op i₀) := Over.mk (homOfLE hi).op

/-- Every stage whose index is above `i₃` maps to the stage at `i₃`. -/
def toStageAt {i₃ : I} (hi : i₀ ≤ i₃) (j : Over (op i₀)) (hj : i₃ ≤ unop j.left) :
    j ⟶ stageAt hi :=
  Over.homMk (homOfLE hj).op (Subsingleton.elim _ _)

/-- If two morphisms of the image systems inducing the same morphism on the limits agree at the
stage at some index `i₃ ≥ i₀`, then they agree at every stage whose index is above `i₃`. -/
theorem eventually_eq_of_exists_eq_app (F G : MorphismAt D f GX GY i₀ hX hY)
    (h : ∃ (i₃ : I) (hi : i₀ ≤ i₃),
      F.maps.app (stageAt hi) = G.maps.app (stageAt hi)) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → F.maps.app j = G.maps.app j := by
  obtain ⟨i₃, hi, h⟩ := h
  exact ⟨i₃, hi, fun j hj ↦ F.app_eq_of_eq_app G (toStageAt hi j hj) h⟩

end MorphismAt

end AlgebraicGeometry.LimitNoetherianSituation
