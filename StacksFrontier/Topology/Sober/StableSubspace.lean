module

public import Mathlib.Topology.Sober
public import Mathlib.Topology.Inseparable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Subspaces stable under generalization are quasi-sober

A subset of a topological space is *stable under generalization* when it contains every
generalization of each of its points. Such a subset of a quasi-sober space is quasi-sober in
the subspace topology. In a Kolmogorov space the set `{y | y ⤳ x ∧ y ≠ x}` of proper
generalizations of a point is stable under generalization, so it is quasi-sober as soon as the
ambient space is.

## Main results

* `StableUnderGeneralization.quasiSober`: a subspace stable under generalization of a
  quasi-sober space is quasi-sober.
* `stableUnderGeneralization_properGeneralizations`: in a Kolmogorov space the proper
  generalizations of a point are stable under generalization.
* `quasiSober_properGeneralizations`: the proper generalizations of a point of a quasi-sober
  Kolmogorov space form a quasi-sober subspace.

## References

* [Stacks Project, Tag 004X](https://stacks.math.columbia.edu/tag/004X)
* [Stacks Project, Tag 0B31](https://stacks.math.columbia.edu/tag/0B31)
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- A subspace of a quasi-sober space which is stable under generalization is quasi-sober. -/
@[sga "4 IV 9.1.11" "9.1.11 g), special case"]
theorem StableUnderGeneralization.quasiSober [QuasiSober X] {W : Set X}
    (hW : StableUnderGeneralization W) : QuasiSober W := by
  refine ⟨?_⟩
  intro E hEirr hEclosed
  obtain ⟨T, hT, hTE⟩ := isClosed_induced_iff.mp hEclosed
  obtain ⟨y, hy⟩ := hEirr.nonempty
  have hE'irr : IsIrreducible (Subtype.val '' E) :=
    hEirr.image _ continuous_subtype_val.continuousOn
  obtain ⟨η, hη⟩ := QuasiSober.sober hE'irr.closure isClosed_closure
  have hηW : η ∈ W := hW (hη.specializes (subset_closure ⟨y, hy, rfl⟩)) y.2
  have hE'T : Subtype.val '' E ⊆ T := by
    rintro z ⟨zW, hzW, rfl⟩
    rw [← hTE] at hzW
    exact hzW
  refine ⟨⟨η, hηW⟩, ?_⟩
  rw [isGenericPoint_def]
  refine Set.ext fun z ↦ ?_
  rw [closure_subtype, Set.image_singleton, hη.def]
  exact ⟨fun hz ↦ hTE ▸ (hT.closure_subset_iff.mpr hE'T) hz,
    fun hz ↦ subset_closure (show (z : X) ∈ Subtype.val '' E from ⟨z, hz, rfl⟩)⟩

/-- In a Kolmogorov space the proper generalizations of a point `x` — the points `y ⤳ x`
distinct from `x` — form a set stable under generalization. -/
theorem stableUnderGeneralization_properGeneralizations [T0Space X] (x : X) :
    StableUnderGeneralization {y : X | y ⤳ x ∧ y ≠ x} := by
  rintro a b hba ⟨hax, hane⟩
  refine ⟨hba.trans hax, ?_⟩
  rintro rfl
  exact hane (hax.antisymm hba).eq

/-- The proper generalizations of a point of a quasi-sober Kolmogorov space form a
quasi-sober subspace. -/
theorem quasiSober_properGeneralizations [QuasiSober X] [T0Space X] (x : X) :
    QuasiSober {y : X // y ⤳ x ∧ y ≠ x} :=
  (stableUnderGeneralization_properGeneralizations x).quasiSober

end
