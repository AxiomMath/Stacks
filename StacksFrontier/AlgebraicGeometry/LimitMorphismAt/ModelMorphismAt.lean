module

public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.FibreProductModel
public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.FibreProductSystem

/-!
# The morphism of image systems attached to a morphism of models over one stage

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, let `G` be a good diagram for `Y ⟶ S` over a stage `S_i`, and let `M` be a
model for `X ⟶ S` over the same stage whose model maps to that of `G` compatibly with a morphism
`u : X ⟶ Y`. Then `u` is induced by a morphism of the two systems of scheme-theoretic images on
the whole tail above any index above `i`, with no passage to a later stage: the morphism of
models gives a morphism of the base changes at every stage, and the scheme-theoretic image is
functorial for commuting squares.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ModelOver.stageTargetHom`: the
  morphism `S_j ×_{S_i} W_X ⟶ S_j ×_{S_i} W_Y` of base-changed models at a stage.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ModelOver.morphismAt`: the resulting
  morphism of image systems.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ModelOver.morphismAt_app_imageι`: its
  component at a stage, read inside the base change of the target model. This is the identity
  the closed-immersion argument for Stacks 0CNW runs on, and it is what distinguishes this
  morphism of systems from an arbitrary one, which is only determined at sufficiently late
  stages (Stacks 0CNR).

## Route

Everything is the functoriality `AlgebraicGeometry.Scheme.Hom.imageMap` of the scheme-theoretic
image, applied to the square whose horizontal arrows are the stage maps of the two diagrams and
whose right-hand arrow is `stageTargetHom`; that square commutes because the morphism of models
is compatible with the two horizontal morphisms. Functoriality in the stage is the agreement of
`stageTargetHom` with the transitions of the two base changes, and the two axioms of
`AlgebraicGeometry.LimitNoetherianSituation.MorphismAt` are the two projection identities of
`imageMap`.

## Universe situation

The index type is at a universe independent of the universe of the schemes and carries no
smallness hypothesis: no limit is taken.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR), whose existence half
  this makes explicit in the special case of a morphism of models over one stage
* [Stacks Project, Tag 01R9](https://stacks.math.columbia.edu/tag/01R9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.LimitNoetherianSituation

namespace GoodDiagram.ModelOver

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I} {X Y : Scheme.{u}} {g : Y ⟶ D.limitScheme}
  {G : GoodDiagram D g} {u : X ⟶ Y} {f : X ⟶ D.limitScheme} (M : G.ModelOver u f)

/-- The morphism `S_j ×_{S_i} W_X ⟶ S_j ×_{S_i} W_Y` of base-changed models at a stage. -/
noncomputable def stageTargetHom (j : Over (op G.index)) :
    pullback (D.system.map j.hom) M.toGoodDiagram.modelMap ⟶
      pullback (D.system.map j.hom) G.modelMap :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ M.toBase) (by
    rw [Category.assoc, M.modelMap_eq]
    exact pullback.condition)

/-- The morphism `stageTargetHom` commutes with the first projections to `S_j`. -/
@[reassoc (attr := simp)]
lemma stageTargetHom_fst (j : Over (op G.index)) :
    M.stageTargetHom j ≫ pullback.fst (D.system.map j.hom) G.modelMap =
      pullback.fst (D.system.map j.hom) M.toGoodDiagram.modelMap :=
  pullback.lift_fst _ _ _

/-- Composing `stageTargetHom` with the second projection to `W_Y` is the second projection to
`W_X` followed by the model morphism `W_X ⟶ W_Y`. -/
@[reassoc (attr := simp)]
lemma stageTargetHom_snd (j : Over (op G.index)) :
    M.stageTargetHom j ≫ pullback.snd (D.system.map j.hom) G.modelMap =
      pullback.snd (D.system.map j.hom) M.toGoodDiagram.modelMap ≫ M.toBase :=
  pullback.lift_snd _ _ _

/-- The stage maps of the two diagrams and the morphism of base-changed models form a commuting
square. -/
lemma stageMap_comp_stageTargetHom (hu : u ≫ g = f) (j : Over (op G.index)) :
    M.toGoodDiagram.stageMap j ≫ M.stageTargetHom j = u ≫ G.stageMap j := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, M.stageTargetHom_fst, GoodDiagram.stageMap_fst M.toGoodDiagram j,
      Category.assoc, GoodDiagram.stageMap_fst G j, ← Category.assoc, hu]
  · rw [Category.assoc, M.stageTargetHom_snd, ← Category.assoc,
      GoodDiagram.stageMap_snd M.toGoodDiagram j, M.compat, Category.assoc,
      GoodDiagram.stageMap_snd G j]

/-- The morphism of base-changed models commutes with the transitions between stages. -/
lemma stageTargetMap_comp_stageTargetHom {j k : Over (op G.index)} (c : j ⟶ k) :
    M.toGoodDiagram.stageTargetMap c ≫ M.stageTargetHom k =
      M.stageTargetHom j ≫ G.stageTargetMap c := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, M.stageTargetHom_fst,
      GoodDiagram.stageTargetMap_fst M.toGoodDiagram c, Category.assoc,
      GoodDiagram.stageTargetMap_fst G c, ← Category.assoc, M.stageTargetHom_fst]
  · rw [Category.assoc, M.stageTargetHom_snd, ← Category.assoc,
      GoodDiagram.stageTargetMap_snd M.toGoodDiagram c, Category.assoc,
      GoodDiagram.stageTargetMap_snd G c, M.stageTargetHom_snd]

/-- **The morphism of image systems attached to a morphism of models over one stage.** It is
defined on the whole tail above any index above the common stage, not merely on a later tail as
the existence half of Stacks 0CNR gives in general. -/
noncomputable def morphismAt (hu : u ≫ g = f) (i₀ : I) (h : G.index ≤ i₀) :
    MorphismAt D u M.toGoodDiagram G i₀ h h where
  maps :=
    { app j := Scheme.Hom.imageMap
        (M.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j))
        (G.stageMap ((Over.map (homOfLE h).op).obj j)) u
        (M.stageTargetHom ((Over.map (homOfLE h).op).obj j))
        (M.stageMap_comp_stageTargetHom hu ((Over.map (homOfLE h).op).obj j))
      naturality := by
        intro j k c
        refine (cancel_mono (G.stageMap ((Over.map (homOfLE h).op).obj k)).imageι).mp ?_
        simp only [Functor.comp_map, Category.assoc,
          Scheme.Hom.imageMap_imageι, GoodDiagram.imageTransition_imageι,
          GoodDiagram.imageTransition_imageι_assoc, Scheme.Hom.imageMap_imageι_assoc]
        rw [M.stageTargetMap_comp_stageTargetHom] }
  over_base j := by
    rw [← Category.assoc, Scheme.Hom.imageMap_imageι, Category.assoc, stageTargetHom_fst]
  induces j := Scheme.Hom.toImage_imageMap
    (M.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j))
    (G.stageMap ((Over.map (homOfLE h).op).obj j)) u
    (M.stageTargetHom ((Over.map (homOfLE h).op).obj j))
    (M.stageMap_comp_stageTargetHom hu ((Over.map (homOfLE h).op).obj j))

/-- The component of the morphism of image systems at a stage, read inside the base change of
the target model. -/
@[reassoc]
lemma morphismAt_app_imageι (hu : u ≫ g = f) (i₀ : I) (h : G.index ≤ i₀) (j : Over (op i₀)) :
    (M.morphismAt hu i₀ h).maps.app j ≫
        (G.stageMap ((Over.map (homOfLE h).op).obj j)).imageι =
      (M.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j)).imageι ≫
        M.stageTargetHom ((Over.map (homOfLE h).op).obj j) :=
  Scheme.Hom.imageMap_imageι
    (M.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j))
    (G.stageMap ((Over.map (homOfLE h).op).obj j)) u
    (M.stageTargetHom ((Over.map (homOfLE h).op).obj j))
    (M.stageMap_comp_stageTargetHom hu ((Over.map (homOfLE h).op).obj j))

end GoodDiagram.ModelOver

end AlgebraicGeometry.LimitNoetherianSituation
