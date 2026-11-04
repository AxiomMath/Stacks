module

public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Disjoint unions of quasi-separated spaces

A disjoint union, over an arbitrary index type, of quasi-separated spaces each of which has a
basis of quasi-compact opens is quasi-separated.

## Main results

* `quasiSeparatedSpace_sigma`: a disjoint union of quasi-separated prespectral spaces is
  quasi-separated.
-/

@[expose] public section

open Set TopologicalSpace

/-- **A disjoint union of quasi-separated prespectral spaces is quasi-separated**, for an arbitrary
index type. -/
theorem quasiSeparatedSpace_sigma {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    [∀ i, PrespectralSpace (X i)] [∀ i, QuasiSeparatedSpace (X i)] :
    QuasiSeparatedSpace (Σ i, X i) := by
  refine QuasiSeparatedSpace.of_isTopologicalBasis
    (b := fun p : Σ i, { U : Set (X i) // IsOpen U ∧ IsCompact U } ↦
      (Sigma.mk p.1 '' p.2.1 : Set (Σ i, X i))) ?_ ?_
  · convert IsTopologicalBasis.sigma fun i ↦ PrespectralSpace.isTopologicalBasis (X := X i)
      using 1
    ext W
    simp
  · rintro ⟨i, U, hUo, hUc⟩ ⟨j, V, hVo, hVc⟩
    show IsCompact ((Sigma.mk i '' U) ∩ (Sigma.mk j '' V))
    by_cases hij : i = j
    · subst hij
      rw [← Set.image_inter sigma_mk_injective]
      exact (QuasiSeparatedSpace.inter_isCompact U V hUo hUc hVo hVc).image continuous_sigmaMk
    · convert isCompact_empty
      refine eq_empty_iff_forall_notMem.2 ?_
      rintro x ⟨⟨u, -, rfl⟩, ⟨v, -, hv⟩⟩
      exact hij (congrArg Sigma.fst hv).symm

end
