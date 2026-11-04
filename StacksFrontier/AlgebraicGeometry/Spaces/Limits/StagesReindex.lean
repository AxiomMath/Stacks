module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartNoetherianSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent

/-!
# Reindexing a chart system by the stages of a limit situation

An `AlgebraicGeometry.Space.AffineChartSystem` for an inverse system `D : I ⥤ _` at a stage `i₀`
is indexed by the slice `Over i₀`, and so is its limit bridge.  The consumer of the equalizer
presentation of Stacks 07SI,
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation_of_isAffine`,
asks instead for a functor out of `(A.Stages)ᵒᵖ`, the opposite of the preorder of indices of the
limit situation at or beyond its chosen index.  The two index categories are equivalent — in a
preorder, the slice of the opposite category over `op a` *is* the opposite of the upper set of
`a`, which is `CategoryTheory.iciOpEquivalenceOverOp` — and this file applies that equivalence to
a chart system and carries a limiting cone of schemes across it.

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.stagesOverEquivalence` is
  `CategoryTheory.iciOpEquivalenceOverOp` at the chosen index of a limit situation, so with
  source `(A.Stages)ᵒᵖ`.
* `AlgebraicGeometry.Space.LimitSituation.stagesSchemeDiagram` is the diagram of schemes
  underlying a chart system, reindexed by the stages, and
  `AlgebraicGeometry.Space.LimitSituation.stagesSchemeCone` is a cone over it obtained from a
  limit bridge.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.isAffine_stagesSchemeDiagram_obj`: every value of the
  reindexed diagram is affine.
* `AlgebraicGeometry.Space.LimitSituation.isLimit_stagesSchemeCone`: the reindexed cone of a
  limit bridge is limiting.

Together these are exactly the three inputs
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation_of_isAffine`
asks of a system of schemes.

## Implementation notes

`AlgebraicGeometry.Space.LimitSituation.Stages` is the subtype `{i // A.base ≤ i}` and the
carrier of `Set.Ici A.base` is the subtype `{i // i ∈ Set.Ici A.base}`; the two are the same
type, with the same preorder, so `CategoryTheory.iciOpEquivalenceOverOp` applies to the stages
with no conversion.  That equivalence is stated in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartNoetherianSituation.lean`, which is why this
file imports a Noetherian-situation module for a purely order-theoretic fact; the alternative
would be a second copy of the equivalence.

The reindexing is *not* already available from the chart system: the "Available" bullet of the
module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitDescent.lean` lists the chart system
and its limit bridge as inputs to the consumer, but the chart system is indexed by `Over i₀` and
the consumer by `(A.Stages)ᵒᵖ`, so the bullet understates what is needed by exactly this file.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (A : LimitSituation B S hS hZ X)

/-- **The stages of a limit situation index the slice of its index category over the chosen
index.**  This is `CategoryTheory.iciOpEquivalenceOverOp` at the chosen index of the situation:
`A.Stages` is the upper set of that index, and the slice is the index category of a chart system
at it. -/
abbrev stagesOverEquivalence : (A.Stages)ᵒᵖ ≌ Over (op A.base) :=
  iciOpEquivalenceOverOp A.base

variable {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
    (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)

/-- **The diagram of schemes underlying a chart system, reindexed by the stages.**  This is the
shape in which
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation_of_isAffine`
consumes a system of schemes, and it is the chart system's own diagram composed with
`AlgebraicGeometry.Space.LimitSituation.stagesOverEquivalence`. -/
noncomputable abbrev stagesSchemeDiagram : (A.Stages)ᵒᵖ ⥤ Scheme.{u} :=
  (stagesOverEquivalence A).functor ⋙ C.schemeDiagram

/-- **Every chart of a reindexed chart system is affine**, reindexing not changing the values of
the diagram. -/
theorem isAffine_stagesSchemeDiagram_obj (a : (A.Stages)ᵒᵖ) :
    IsAffine ((stagesSchemeDiagram A C).obj a) :=
  C.isAffine_obj _

/-- **The limit of a chart system, as a cone over the reindexed diagram of schemes.** -/
noncomputable def stagesSchemeCone (L : AffineChartSystem.LimitBridge C) :
    Cone (stagesSchemeDiagram A C) :=
  ((BigFppfOver.toScheme B S hS).mapCone L.cone).whisker (stagesOverEquivalence A).functor

/-- **The reindexed cone of a limit bridge is limiting**, reindexing along an equivalence of
index categories preserving limits (`CategoryTheory.Limits.IsLimit.whiskerEquivalence`). -/
noncomputable def isLimit_stagesSchemeCone (L : AffineChartSystem.LimitBridge C) :
    IsLimit (stagesSchemeCone A C L) :=
  L.schemeIsLimit.whiskerEquivalence (stagesOverEquivalence A)

end AlgebraicGeometry.Space.LimitSituation

end
