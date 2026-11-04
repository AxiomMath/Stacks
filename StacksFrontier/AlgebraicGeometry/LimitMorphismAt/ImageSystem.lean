module

public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.Dominant
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeSystem

/-!
# Density of `X` in the inverse system of scheme-theoretic images of a good diagram

Fix a good diagram for `X ⟶ S` over the stage `S_i`. For every stage above `i` the scheme `X`
maps to the base change `S_{i'} ×_{S_i} W` of the model, and the scheme-theoretic images of those
maps form an inverse system with a canonical cone from `X`. That system
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageSystem`, its cone
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageCone`, and the underlying morphisms
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.stageMap` and
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.stageTargetMap` are defined elsewhere.

This file gives a name for the base change of the model, the commuting square the transition of
images comes from, the two characterisations of the cone and of the functor against the closed
embedding of the image, and the density of `X` in every stage.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.stageTarget`: the base change
  `S_{i'} ×_{S_i} W`.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.stageMap_square`: the square whose
  horizontal arrows are the stage maps at two stages and whose vertical arrows are the identity
  of `X` and the transition of base changes commutes.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageSystem_map_imageι` and
  `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageCone_π_app_imageι`: the transition
  of the image system and the leg of the cone at a stage, each followed by the closed embedding
  of the image.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isSchemeTheoreticallyDominant_π`: each
  leg `X ⟶ X_{i'}` of the cone has trivial kernel, that is, `X` is scheme-theoretically dense in
  every stage of the system.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isSeparated_imageι_comp_fst`: the
  structure morphism `X_{i'} ⟶ S_{i'}` of a stage of the system is separated as soon as the model
  is.

## Implementation notes

The index type is at a universe `v` independent of the scheme universe `u`.

`stageTarget` is an `abbrev`, so that the `pullback.lift` and `pullback.fst` simp lemmas apply to
the pullback projections out of it.

Quasi-compactness of `stageMap` is a hypothesis of `isSchemeTheoreticallyDominant_π`. It follows
from `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.quasiCompact_stageMap` under a
smallness hypothesis on the index.

## References

* [Stacks Project, Tag 0CNQ](https://stacks.math.columbia.edu/tag/0CNQ), the construction of the
  system and of its cone.
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8), part (4), the density
  statement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I} {X : Scheme.{u}} {f : X ⟶ D.limitScheme}
  (G : GoodDiagram D f)

/-- The base change `S_{i'} ×_{S_i} W` of the model of a good diagram to a later stage. -/
noncomputable abbrev stageTarget (j : Over (op G.index)) : Scheme.{u} :=
  pullback (D.system.map j.hom) G.modelMap

/-- The commuting square whose horizontal arrows are the stage maps at two stages. -/
lemma stageMap_square {j k : Over (op G.index)} (a : j ⟶ k) :
    G.stageMap j ≫ G.stageTargetMap a = 𝟙 X ≫ G.stageMap k := by
  rw [Category.id_comp]
  exact G.stageMap_comp_stageTargetMap a

/-- The transition of the image system followed by the closed embedding of the image at the
target stage is the closed embedding of the image at the source stage followed by the transition
of base changes. -/
@[simp]
lemma imageSystem_map_imageι {j k : Over (op G.index)} (a : j ⟶ k) :
    G.imageSystem.map a ≫ (G.stageMap k).imageι =
      (G.stageMap j).imageι ≫ G.stageTargetMap a :=
  G.imageTransition_imageι a

/-- The leg of the image cone at a stage followed by the closed embedding of the image is the
stage map. -/
@[simp]
lemma imageCone_π_app_imageι (j : Over (op G.index)) :
    G.imageCone.π.app j ≫ (G.stageMap j).imageι = G.stageMap j :=
  Scheme.Hom.toImage_imageι _

/-- The structure morphism `X_{i'} ⟶ S_{i'}` of a stage of the system is separated as soon as the
model is, since the closed embedding of the image is a monomorphism and the first projection
of the base change inherits separatedness from the model. -/
instance isSeparated_imageι_comp_fst [IsSeparated G.modelMap] (j : Over (op G.index)) :
    IsSeparated ((G.stageMap j).imageι ≫ pullback.fst (D.system.map j.hom) G.modelMap) :=
  inferInstance

/-- `X` is scheme-theoretically dense in every stage of the system: the leg `X ⟶ X_{i'}` of the
cone has trivial kernel ideal sheaf. -/
lemma isSchemeTheoreticallyDominant_π (j : Over (op G.index))
    [QuasiCompact (G.stageMap j)] :
    IsSchemeTheoreticallyDominant (G.imageCone.π.app j) := by
  have h : IsSchemeTheoreticallyDominant (G.stageMap j).toImage := inferInstance
  rw [G.imageCone_π_app j]
  exact h

end AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram
