module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FiberSequence

/-!
# Quasi-finiteness and relative dimension zero

A morphism locally of finite type is quasi-finite at a point exactly when the dimension of its
fibre at that point is zero: the fibre is locally Noetherian there, and in a locally Noetherian
space a point has local dimension zero precisely when it is isolated. Globally, such a morphism
is locally quasi-finite exactly when it has relative dimension zero — the fibres are then
discrete, hence equidimensional of dimension zero, and conversely dimension zero makes each
fibre locally Artinian and so discrete.

## Main results

* `AlgebraicGeometry.quasiFiniteAt_iff_fiberDimensionAt_eq_zero` characterizes quasi-finiteness
  at a point by the local dimension of the fibre.
* `AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero` characterizes locally
  quasi-finite morphisms by relative dimension zero.

## Implementation notes

The dimension at `x` of the fibre over `f x` is expressed using `topologicalKrullDimAt` and the
canonical point `f.asFiber x`. The source's two conclusions are stated separately. Under the
standing local finite-type hypothesis, Mathlib's `LocallyQuasiFinite` is the remaining
fibre-isolation condition in the source's notion of a locally quasi-finite morphism.

## References

* [Stacks Project, Tag 0397](https://stacks.math.columbia.edu/tag/0397)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A fibre of a morphism locally of finite type is a locally Noetherian scheme. -/
private alias fiber_isLocallyNoetherian := Stacks.AlgebraicGeometry.isLocallyNoetherian_fiber

/-- A discrete space is equidimensional: every irreducible closed subset is a point. -/
private lemma equidimensional_of_discreteTopology
    (Y : Type*) [TopologicalSpace Y] [DiscreteTopology Y] :
    TopologicalSpace.Equidimensional Y := by
  intro Z hZ W hW
  obtain ⟨z, hz⟩ := hZ.1.nonempty; obtain ⟨w, hw⟩ := hW.1.nonempty
  let _ : Nonempty Z := ⟨⟨z, hz⟩⟩; let _ : Nonempty W := ⟨⟨w, hw⟩⟩
  let _ : DiscreteTopology Z := inferInstance; let _ : DiscreteTopology W := inferInstance
  exact (topologicalKrullDim_eq_zero_of_discreteTopology_nonempty (X := Z)).trans
    (topologicalKrullDim_eq_zero_of_discreteTopology_nonempty (X := W)).symm

/-- A morphism locally of finite type is quasi-finite at a point if and only if the local
dimension of its fibre at that point is zero. -/
@[stacks 0397 "pointwise characterization"]
public theorem quasiFiniteAt_iff_fiberDimensionAt_eq_zero
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    quasiFiniteAt f x ↔
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 0 := by
  let _ : IsLocallyNoetherian (f.fiber (f x)) := fiber_isLocallyNoetherian f (f x)
  simpa only [topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint] using
    (quasiFiniteAt_tfae f x).out 1 2

/-- A morphism locally of finite type is locally quasi-finite if and only if it has relative
dimension zero. -/
@[stacks 0397 "global characterization"]
public theorem locallyQuasiFinite_iff_relativeDimension_zero
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyQuasiFinite f ↔ RelativeDimension f 0 := by
  rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
  have key (s : S) : _root_.IsDiscrete (f ⁻¹' {s}) ↔ DiscreteTopology (f.fiber s) :=
    _root_.isDiscrete_iff_discreteTopology.trans (f.fiberHomeo s).discreteTopology_iff.symm
  constructor
  · intro hf s hs
    have := (key s).mp (hf s)
    refine ⟨equidimensional_of_discreteTopology (f.fiber s), ?_⟩
    let _ : Nonempty (f.fiber s) := hs
    exact topologicalKrullDim_eq_zero_of_discreteTopology_nonempty
  · intro hrel s
    refine (key s).mpr ?_
    rcases isEmpty_or_nonempty (f.fiber s) with _ | hs
    · infer_instance
    · have : IsLocallyNoetherian (f.fiber s) := fiber_isLocallyNoetherian f s
      have : IsLocallyArtinian (f.fiber s) :=
        IsLocallyArtinian.of_topologicalKrullDim_le_zero (hrel s hs).2.le
      infer_instance

end AlgebraicGeometry
