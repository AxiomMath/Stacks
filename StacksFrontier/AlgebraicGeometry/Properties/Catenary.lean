module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Scheme
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.Topology.Dimension.Catenary
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.CatenaryEncodings
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunction
public import StacksFrontier.Topology.Noetherian.CatenaryOpenCovering

/-!
# Catenary schemes and local dimension functions

A scheme is catenary when its underlying topological space is catenary. A locally Noetherian
scheme is catenary precisely when dimension functions exist locally in the Zariski topology.

## Main results

* `AlgebraicGeometry.isCatenarySpace_iff_locally_dimensionFunction` characterizes catenarity by
  the existence of a dimension function on an open neighbourhood of every point.

## Implementation notes

The existing predicate `IrreducibleClosedsCodim.IsCatenarySpace` applies directly to a scheme
through its underlying topological space, so it states the definition without a scheme-specific
wrapper. Local existence is expressed pointwise: each point belongs to an open subset whose
induced topological space carries a `TopologicalSpace.DimensionFunction`.

## References

* [Stacks Project, Tag 02IW](https://stacks.math.columbia.edu/tag/02IW)
* [Stacks Project, Tag 02IY](https://stacks.math.columbia.edu/tag/02IY)
-/

public section

open TopologicalSpace
open IrreducibleClosedsCodim

universe u

namespace AlgebraicGeometry

/-- A locally Noetherian scheme is catenary if and only if every point has an open
neighbourhood admitting a dimension function. -/
@[stacks 02IY, sga "6 X 1.6" "more general"]
public theorem isCatenarySpace_iff_locally_dimensionFunction
    (S : Scheme.{u}) [IsLocallyNoetherian S] :
    IrreducibleClosedsCodim.IsCatenarySpace S ↔
      ∀ x : S, ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ Nonempty (DimensionFunction U) := by
  refine ⟨fun hCat x => ?_, fun hLocal => ?_⟩
  · exact TopologicalSpace.exists_open_nhd_with_dimension_function S
      (isLocallyNoetherianSpace_of_isLocallyNoetherian S) hCat.isTopologicallyCatenary x
  · apply (CatenaryTopologicalSpace.isCatenary_iff_hasOpenCoveringByCatenarySpaces S).2
    choose U hUo hxU hδU using hLocal
    refine ⟨S, U, hUo, Set.iUnion_eq_univ_iff.2 fun x => ⟨x, hxU x⟩, fun x => ?_⟩
    obtain ⟨δ⟩ := hδU x
    have : QuasiSober (U x) := (hUo x).isOpenEmbedding_subtypeVal.quasiSober
    have hδ : IsDimensionFunctionForCatenary (fun z : U x => δ z) :=
      ⟨fun _ _ h hne => δ.strictAnti_specializes h hne, fun _ _ h => δ.step_immediate h⟩
    exact (isCatenarySpace_and_topCodim_eq_of_isDimensionFunction (U x)
      (stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩) δ hδ).1

end AlgebraicGeometry

add_to_stacks 02IW IrreducibleClosedsCodim.IsCatenarySpace

end
