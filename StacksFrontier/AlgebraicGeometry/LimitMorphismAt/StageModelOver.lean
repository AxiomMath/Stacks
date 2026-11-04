module

public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.FibreProductModel
public import StacksFrontier.AlgebraicGeometry.Limits.FlatImageSystem

/-!
# Compatible models from a morphism of image systems

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, let `f : X ⟶ Y` be a morphism of schemes quasi-compact over `S`, and let
good diagrams for `X ⟶ S` and `Y ⟶ S` be chosen *independently*: their stages are different and
their models admit no morphism between them. A morphism `F` of the two image systems
(Stacks 0CNR) repairs this at every stage of a common tail: taking the scheme-theoretic images
`X_j` and `Y_j` at one stage `j` as new models -- which is
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ofStageSmallnessFree`, the replacement
of Remark 0CNS -- the component `F_j : X_j ⟶ Y_j` is a morphism of models over one and the
same stage, compatible with `f`.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.stageModelOver`: the model of `X` over
  the stage-`j` model of the good diagram for `Y`, with `F_j` as its morphism of models.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ofStageSmallnessFree_index`,
  `ofStageSmallnessFree_W`, `ofStageSmallnessFree_modelMap` and
  `ofStageSmallnessFree_toModel`: the four data of the replaced good diagram.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.stageModelOver_toGoodDiagram`: the good
  diagram underlying that model is the stage replacement of the good diagram of `X`.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.stageModelOver_toBase`: the morphism of
  models of `stageModelOver F j` is the component `F_j`.

## Implementation notes

The three finiteness fields and the closed immersion are those of
`GoodDiagram.ofStageSmallnessFree` applied to the good diagram of `X` at the same stage; the
morphism of models is `F.maps.app j`; that it lies over the stage is the axiom
`MorphismAt.over_base` of a morphism of image systems, and that it is compatible with `f` is
the axiom `MorphismAt.induces`. The two stages agree because `((Over.map g).obj j).left` is
`j.left` definitionally.

The index type lives in a universe independent of the universe of the schemes and carries no
smallness hypothesis.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNP](https://stacks.math.columbia.edu/tag/0CNP)
* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR)
* [Stacks Project, Tag 0CNS](https://stacks.math.columbia.edu/tag/0CNS)
* [Stacks Project, Tag 0CNW](https://stacks.math.columbia.edu/tag/0CNW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

namespace GoodDiagram

variable {X : Scheme.{u}} {pX : X ⟶ D.limitScheme} [QuasiCompact pX]

/-- The index of the stage replacement of `G` at `j` is the stage `j` itself. -/
@[simp]
lemma ofStageSmallnessFree_index (G : GoodDiagram D pX) (j : Over (op G.index)) :
    (G.ofStageSmallnessFree j).index = unop j.left :=
  rfl

/-- The model of the stage replacement of `G` at `j` is the scheme-theoretic image of the
stage map at `j`. -/
@[simp]
lemma ofStageSmallnessFree_W (G : GoodDiagram D pX) (j : Over (op G.index)) :
    (G.ofStageSmallnessFree j).W = (G.stageMap j).image :=
  rfl

/-- The structure morphism of the model of the stage replacement of `G` at `j` is the inclusion
of the scheme-theoretic image followed by the first projection of the base change of the model
of `G` to the stage `j`. -/
@[simp]
lemma ofStageSmallnessFree_modelMap (G : GoodDiagram D pX) (j : Over (op G.index)) :
    (G.ofStageSmallnessFree j).modelMap =
      (G.stageMap j).imageι ≫ pullback.fst (D.system.map j.hom) G.modelMap :=
  rfl

/-- The morphism to the model of the stage replacement of `G` at `j` is the factorisation of the
stage map at `j` through its scheme-theoretic image. -/
@[simp]
lemma ofStageSmallnessFree_toModel (G : GoodDiagram D pX) (j : Over (op G.index)) :
    (G.ofStageSmallnessFree j).toModel = (G.stageMap j).toImage :=
  rfl

end GoodDiagram

namespace MorphismAt

variable {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
  [QuasiCompact pX] [QuasiCompact pY] {f : X ⟶ Y}
  {GX : GoodDiagram D pX} {GY : GoodDiagram D pY} {i₀ : I} {hX : GX.index ≤ i₀}
  {hY : GY.index ≤ i₀}

/-- **Two independently chosen good diagrams become compatible at every stage.** Given a
morphism `F` of the image systems of good diagrams for `X ⟶ S` and `Y ⟶ S` inducing
`f : X ⟶ Y`, and a stage `j` of their common tail, the scheme-theoretic image `X_j` is a model
for `X` over the stage-`j` model `Y_j` of the good diagram for `Y`, the morphism of models being
the component `F_j` of `F`. -/
noncomputable def stageModelOver (F : MorphismAt D f GX GY i₀ hX hY) (j : Over (op i₀)) :
    (GY.ofStageSmallnessFree ((Over.map (homOfLE hY).op).obj j)).ModelOver f pX where
  W := (GX.ofStageSmallnessFree ((Over.map (homOfLE hX).op).obj j)).W
  toBase := F.maps.app j
  modelMap := (GX.ofStageSmallnessFree ((Over.map (homOfLE hX).op).obj j)).modelMap
  modelMap_eq := F.over_base j
  toModel := (GX.ofStageSmallnessFree ((Over.map (homOfLE hX).op).obj j)).toModel
  commutes := (GX.ofStageSmallnessFree ((Over.map (homOfLE hX).op).obj j)).commutes
  compat := F.induces j
  locallyOfFiniteType :=
    (GX.ofStageSmallnessFree ((Over.map (homOfLE hX).op).obj j)).locallyOfFiniteType
  quasiCompact := (GX.ofStageSmallnessFree ((Over.map (homOfLE hX).op).obj j)).quasiCompact
  isClosedImmersion :=
    (GX.ofStageSmallnessFree ((Over.map (homOfLE hX).op).obj j)).isClosedImmersion

/-- The good diagram underlying the model of `stageModelOver` is the stage replacement of the
good diagram of the source. -/
@[simp]
lemma stageModelOver_toGoodDiagram (F : MorphismAt D f GX GY i₀ hX hY) (j : Over (op i₀)) :
    (F.stageModelOver j).toGoodDiagram =
      GX.ofStageSmallnessFree ((Over.map (homOfLE hX).op).obj j) :=
  rfl

/-- The morphism of models of `stageModelOver F j` is the component `F_j` of `F`. -/
@[simp]
lemma stageModelOver_toBase (F : MorphismAt D f GX GY i₀ hX hY) (j : Over (op i₀)) :
    (F.stageModelOver j).toBase = F.maps.app j :=
  rfl

end MorphismAt

end AlgebraicGeometry.LimitNoetherianSituation
