module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Adic rings are weakly admissible

A ring whose topology is the `I`-adic one for an ideal `I` has `I` as a weak ideal of
definition, and is weakly admissible as soon as it is `I`-adically complete: adic completeness
is exactly completeness and separatedness for the adic topology
(`IsAdic.isAdicComplete_iff`), and the uniformity of the adic topology is the canonical
right uniformity of its additive group.

This file also records the two continuity lemmas relating a ring map to the adic topologies on
its source and target: a map carrying `I` into `J` is continuous, and a continuous map into a
local ring whose topology is the maximal-adic one carries `I` into the maximal ideal.

## Main results

* `TopologicalRing.isWeakIdealOfDefinition_of_isAdic`
* `TopologicalRing.isWeaklyAdmissible_of_isAdic`
* `continuous_of_isAdic_of_map_le`
* `Ideal.map_le_maximalIdeal_of_continuous`

## References

* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
-/

@[expose] public section

namespace TopologicalRing

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The defining ideal of an adic topology is a weak ideal of definition: it is open, and all
its elements are topologically nilpotent because `xⁿ ∈ Iⁿ`. -/
theorem isWeakIdealOfDefinition_of_isAdic {I : Ideal A} (h : _root_.IsAdic I) :
    IsWeakIdealOfDefinition I := by
  refine ⟨by simpa using (isAdic_iff.mp h).1 1, fun x hx => ?_⟩
  refine h.hasBasis_nhds_zero.tendsto_right_iff.mpr fun n _ => ?_
  filter_upwards [Filter.eventually_ge_atTop n] with k hk
  exact Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow hx k)

/-- Every positive power of the defining ideal of an adic topology is a weak ideal of
definition. -/
theorem isWeakIdealOfDefinition_pow_of_isAdic {I : Ideal A} (h : _root_.IsAdic I) (n : ℕ) :
    IsWeakIdealOfDefinition (I ^ (n + 1)) :=
  ⟨(isAdic_iff.mp h).1 _, fun x hx =>
    (isWeakIdealOfDefinition_of_isAdic h).2 x (Ideal.pow_le_self (by omega) hx)⟩

/-- An `I`-adically complete ring carrying the `I`-adic topology is weakly admissible. -/
theorem isWeaklyAdmissible_of_isAdic [IsLinearTopology A A] {I : Ideal A}
    (h : _root_.IsAdic I)
    (hc : IsAdicComplete I A) : IsWeaklyAdmissible A := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  obtain ⟨hcomplete, hT2⟩ := (IsAdic.isAdicComplete_iff h).mp hc
  exact ⟨⟨I, isWeakIdealOfDefinition_of_isAdic h⟩, hcomplete, hT2⟩

end TopologicalRing

variable {A R : Type*} [CommRing A] [CommRing R] [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- A ring homomorphism between adically topologized rings which carries the defining ideal of
the source into the defining ideal of the target is continuous. -/
theorem continuous_of_isAdic_of_map_le {I : Ideal A} {J : Ideal R} (hI : IsAdic I)
    (hJ : IsAdic J) (φ : A →+* R) (hφ : I.map φ ≤ J) : Continuous φ := by
  refine continuous_of_continuousAt_zero φ ?_
  have hzero : Filter.Tendsto φ (nhds 0) (nhds (φ 0)) → ContinuousAt φ 0 := id
  refine hzero ?_
  rw [map_zero]
  refine (hI.hasBasis_nhds_zero.tendsto_iff hJ.hasBasis_nhds_zero).mpr fun n _ => ?_
  refine ⟨n, trivial, fun x hx => ?_⟩
  have hpow : (I ^ n).map φ ≤ J ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hφ n
  exact Ideal.map_le_iff_le_comap.mp hpow hx

/-- A continuous map from an adically topologized ring to a local ring carrying its
maximal-adic topology sends the defining ideal into the maximal ideal: the powers of an element
of `I` tend to zero, hence eventually lie in the maximal ideal, which is prime. -/
theorem Ideal.map_le_maximalIdeal_of_continuous [IsLocalRing R] {I : Ideal A} (hI : IsAdic I)
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) (φ : A →+* R) (hφ : Continuous φ) :
    I.map φ ≤ IsLocalRing.maximalIdeal R := by
  refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
  rw [Ideal.mem_comap]
  have ht : Filter.Tendsto (fun n : ℕ => φ (x ^ n)) Filter.atTop (nhds 0) := by
    simpa only [map_zero, Function.comp_def] using (hφ.tendsto 0).comp
      ((TopologicalRing.isWeakIdealOfDefinition_of_isAdic hI).2 x hx)
  obtain ⟨n, hn⟩ := (ht.eventually
    ((TopologicalRing.isWeakIdealOfDefinition_of_isAdic hR).1.mem_nhds
      (Ideal.zero_mem _))).exists
  rw [map_pow] at hn
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance n hn

end
