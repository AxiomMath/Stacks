module

public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.GoodDiagramLimit.Reduction
public import StacksFrontier.AlgebraicGeometry.KerDetected.IdealComap
public import StacksFrontier.AlgebraicGeometry.Limits.ImageSystemLimit
import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# Stacks 0CNQ: the kernel statement

Fix a good diagram for `X ⟶ S` over the stage `S_i` and let `X_{i'}` be the inverse system of
scheme-theoretic images of `X` in the base changes `S_{i'} ×_{S_i} W` of the model.
`StacksFrontier/AlgebraicGeometry/GoodDiagramLimit/Reduction.lean` proves Stacks 0CNQ, that the
canonical cone from `X` to that system is a limit cone, equivalent to
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.KerDetectedOnStages`: the quasi-coherent
ideal of `X` inside `S ×_{S_i} W` is detected by the images at the stages. This file proves that
statement.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.kerDetectedOnStages`: the kernel
  statement. The limit assertion itself is
  `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isLimit_imageCone`, in
  `StacksFrontier/AlgebraicGeometry/Limits/ImageSystemLimit.lean`, which this file imports.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isAffineHom_stageProj` and
  `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.quasiCompact_stageMap'`: the projections
  `S ×_{S_i} W ⟶ S_{i'} ×_{S_i} W` are affine and the stage maps are quasi-compact, as instances.

## Route

`S ×_{S_i} W` is the limit of the base changes of the model
(`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.stageConeIsLimit`), whose transition
morphisms are affine. The local computation of the Stacks proof is
`AlgebraicGeometry.le_iSup_comap_map_of_isLimit`, in
`StacksFrontier/AlgebraicGeometry/Limits/ImageSystemLimit.lean`: an ideal sheaf on
such a limit is below the supremum of the pullbacks of its images at the stages. Applied to the
ideal of `X`, whose image at a stage is the ideal of the stage map, it gives the kernel statement.

The hypotheses `QuasiSeparated f`, `LocallyOfFiniteType f` and `QuasiCompact f` of Stacks 0CNQ
are not used.

## Universe situation

The index type is at a universe `v` independent of the scheme universe `u`. The limit cone is
given by `stageConeIsLimit`, so no limit is constructed and no smallness of the index is needed.

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

/-- The projections of `S ×_{S_i} W` to the base changes of the model are affine, being the
projections of a cofiltered limit with affine transitions. -/
instance isAffineHom_stageProj (j : Over (op G.index)) : IsAffineHom (G.stageProj j) :=
  EventualLimit.isAffineHom_π_app G.stageSystem G.stageCone G.stageConeIsLimit j

/-- The legs of `stageCone` are the projections, so instance search must see them as affine
under that spelling too. -/
instance isAffineHom_stageCone_π_app (j : Over (op G.index)) :
    IsAffineHom (G.stageCone.π.app j) :=
  G.isAffineHom_stageProj j

/-- Every stage map is quasi-compact: it is a closed immersion followed by an affine
morphism.

This is `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.quasiCompact_stageMap` with both
of its hypotheses dropped: neither `CategoryTheory.FinallySmall` on the index nor
quasi-compactness of `f` is needed once the projections out of `S ×_{S_i} W` are known to be
affine, which `isAffineHom_stageProj` supplies from the limit cone itself. It is also an
instance, which that statement is not. -/
instance quasiCompact_stageMap' (j : Over (op G.index)) : QuasiCompact (G.stageMap j) := by
  rw [← G.induced_comp_stageProj j]
  infer_instance

/-- **Stacks Project, Tag 0CNQ, the kernel statement.** The quasi-coherent ideal of `X` inside
`S ×_{S_i} W` is detected by the scheme-theoretic images at the stages. By
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.nonempty_isLimit_imageCone_iff` this is
equivalent to the limit assertion of 0CNQ.

`S ×_{S_i} W` is the limit of the base changes of the model, whose transitions are affine, so by
`AlgebraicGeometry.le_iSup_comap_map_of_isLimit` the ideal of `X` lies below the supremum of the
pullbacks of its images at the stages; the image at a stage is the ideal of the stage map. -/
theorem kerDetectedOnStages : G.KerDetectedOnStages := fun w hw => by
  refine (le_iSup_comap_map_of_isLimit G.stageSystem G.stageCone G.stageConeIsLimit
    G.induced.ker).trans (iSup_le fun j => ?_)
  have hmap : G.induced.ker.map (G.stageProj j) = (G.stageMap j).ker :=
    (Scheme.Hom.ker_comp G.induced (G.stageProj j)).symm.trans
      (congrArg Scheme.Hom.ker (G.induced_comp_stageProj j))
  refine (congrArg (fun J => J.comap (G.stageProj j)) hmap).le.trans ?_
  refine Scheme.IdealSheafData.le_map_iff_comap_le.mp ?_
  rw [← Scheme.Hom.ker_comp]
  exact hw j

end AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram

end
