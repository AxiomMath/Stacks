module

public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctors

/-!
# The two readings of the limit preserving condition agree

Limits, Remark 05LX asks of a functor `F` on `Sch/S` that it carry an inverse limit of affine
schemes over `S` to a filtered colimit of sets.  Two shapes of inverse system occur in this
library: the system indexed by the opposite of a nonempty directed poset, which is
`AlgebraicGeometry.ExtendingFunctors.PreservesAffineLimits`, and the system indexed by an
arbitrary cofiltered category, which is `AlgebraicGeometry.Scheme.IsLimitPreserving`.  This file
proves that the two conditions are equivalent.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.preservesAffineLimits_of_isLimitPreserving`: the cofiltered
  condition implies the directed one.
* `AlgebraicGeometry.Scheme.isLimitPreserving_of_preservesAffineLimits`: the directed condition
  implies the cofiltered one.
* `AlgebraicGeometry.ExtendingFunctors.preservesAffineLimits_iff_isLimitPreserving`: the two
  conditions are equivalent.

## References

* [Stacks Project, Tag 05LX](https://stacks.math.columbia.edu/tag/05LX)
* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe w u

variable {S : Scheme.{u}}

/-- A functor on `Sch/S` which carries every cofiltered inverse limit of affine schemes over `S`
to a filtered colimit carries in particular every such limit indexed by the opposite of a
nonempty directed poset to one. -/
theorem ExtendingFunctors.preservesAffineLimits_of_isLimitPreserving
    {F : (Over S)ᵒᵖ ⥤ Type w} (h : Scheme.IsLimitPreserving S F) :
    ExtendingFunctors.PreservesAffineLimits F := by
  intro Λ _ _ _ D hD c hc
  exact (h Λᵒᵖ D hD).preserves hc.op

/-- **The cofiltered reading of Remark 05LX from the directed one.** A functor on `Sch/S` which
carries every inverse limit of affine schemes over `S` indexed by the opposite of a nonempty
directed poset to a filtered colimit carries every *cofiltered* such limit to a filtered
colimit. -/
theorem Scheme.isLimitPreserving_of_preservesAffineLimits {F : (Over S)ᵒᵖ ⥤ Type w}
    (h : ExtendingFunctors.PreservesAffineLimits F) : Scheme.IsLimitPreserving S F := by
  intro I _ _ D hD
  obtain ⟨Λ, _, _, _, G, _⟩ := IsFiltered.exists_directed Iᵒᵖ
  refine ⟨fun {c} hc ↦ ?_⟩
  let c₀ : Cone D := coneUnopOfCocone c
  obtain ⟨hcol⟩ := h Λ (G.leftOp ⋙ D) (fun l ↦ hD (G.leftOp.obj l)) (c₀.whisker G.leftOp)
    ((Functor.Initial.isLimitWhiskerEquiv G.leftOp c₀).symm (isLimitConeUnopOfCocone D.op hc))
  exact ⟨Functor.Final.isColimitWhiskerEquiv G (F.mapCocone c₀.op)
    (hcol.whiskerEquivalence (opOpEquivalence Λ).symm)⟩

/-- **The two readings of Remark 05LX agree.** For a functor on `Sch/S`, carrying every inverse
limit of affine schemes over `S` indexed by the opposite of a nonempty directed poset to a
filtered colimit is the same condition as carrying every cofiltered such limit to one. -/
theorem ExtendingFunctors.preservesAffineLimits_iff_isLimitPreserving
    {F : (Over S)ᵒᵖ ⥤ Type w} :
    ExtendingFunctors.PreservesAffineLimits F ↔ Scheme.IsLimitPreserving S F :=
  ⟨Scheme.isLimitPreserving_of_preservesAffineLimits,
    ExtendingFunctors.preservesAffineLimits_of_isLimitPreserving⟩

end AlgebraicGeometry

end
