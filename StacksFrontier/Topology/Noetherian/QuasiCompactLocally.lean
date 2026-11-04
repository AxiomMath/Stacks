module

public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# Quasi-compact locally Noetherian spaces are Noetherian

## Main results

* `noetherianSpace_of_isLocallyNoetherianSpace`: a quasi-compact locally Noetherian topological
  space is Noetherian.
-/

@[expose] public section

open TopologicalSpace Set

/-- A quasi-compact locally Noetherian topological space is Noetherian. -/
@[stacks 04ZB]
theorem noetherianSpace_of_isLocallyNoetherianSpace (X : Type*) [TopologicalSpace X]
    [CompactSpace X] (hX : IsLocallyNoetherianSpace X) : NoetherianSpace X := by
  choose U hUopen hxU hUnoeth using hX
  obtain ⟨t, ht⟩ : ∃ t : Finset X, (univ : Set X) ⊆ ⋃ x ∈ t, U x :=
    isCompact_univ.elim_finite_subcover U hUopen fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩
  rw [noetherianSpace_iff_opens]
  rintro ⟨V, _⟩
  rw [TopologicalSpace.Opens.coe_mk, show V = ⋃ x ∈ t, V ∩ U x by
    rw [← inter_iUnion₂, inter_eq_left.mpr ((subset_univ V).trans ht)]]
  refine t.finite_toSet.isCompact_biUnion fun x _ => ?_
  have := hUnoeth x
  rw [inter_comm, ← Subtype.image_preimage_coe (U x) V]
  exact (NoetherianSpace.isCompact _).image continuous_subtype_val
