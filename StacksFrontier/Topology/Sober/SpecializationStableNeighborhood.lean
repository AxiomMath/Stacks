module

public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Sober

/-!
# Doubly stable subsets of a quasi-sober space with finitely many components are open

Let `X` be a quasi-sober topological space with finitely many irreducible components and let
`E : Set X` be stable under specialization and under generalization. Then `E` is open: every
`u ∈ E` has an open neighbourhood contained in `E`, namely the set of points lying in no
irreducible component that misses `u`.

## Main results

* `StableUnderSpecialization.exists_isOpen_subset_of_stableUnderGeneralization`: each point of
  `E` has an open neighbourhood contained in `E`.
* `StableUnderSpecialization.mem_nhds_of_stableUnderGeneralization`: `E` is a neighbourhood of
  each of its points.
* `StableUnderSpecialization.isOpen_of_stableUnderGeneralization`: `E` is open.
-/

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

/-- On a quasi-sober space with finitely many irreducible components, a subset stable under
specialization and under generalization contains an open neighbourhood of each of its points. -/
theorem StableUnderSpecialization.exists_isOpen_subset_of_stableUnderGeneralization
    [QuasiSober X] {E : Set X} (hspec : StableUnderSpecialization E)
    (hgen : StableUnderGeneralization E) (hfin : (irreducibleComponents X).Finite) {u : X}
    (hu : u ∈ E) : ∃ V : Set X, IsOpen V ∧ u ∈ V ∧ V ⊆ E := by
  classical
  refine ⟨(⋃₀ {Z | Z ∈ irreducibleComponents X ∧ u ∉ Z})ᶜ, ?_, ?_, ?_⟩
  · exact isOpen_compl_iff.mpr <| Set.Finite.isClosed_sUnion (hfin.subset fun Z hZ => hZ.1)
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  · exact fun ⟨Z, hZ, huZ⟩ => hZ.2 huZ
  · intro x hx
    have hZmem := irreducibleComponent_mem_irreducibleComponents x
    have huZ : u ∈ irreducibleComponent x := by
      by_contra hu'
      exact hx ⟨irreducibleComponent x, ⟨hZmem, hu'⟩, mem_irreducibleComponent⟩
    have hgp : closure {hZmem.1.genericPoint} = irreducibleComponent x :=
      hZmem.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ hZmem)
    exact hspec (specializes_iff_mem_closure.mpr (hgp ▸ mem_irreducibleComponent))
      (hgen (specializes_iff_mem_closure.mpr (by rwa [hgp])) hu)

/-- On a quasi-sober space with finitely many irreducible components, a subset stable under
specialization and under generalization is a neighbourhood of each of its points. -/
theorem StableUnderSpecialization.mem_nhds_of_stableUnderGeneralization
    [QuasiSober X] {E : Set X} (hspec : StableUnderSpecialization E)
    (hgen : StableUnderGeneralization E) (hfin : (irreducibleComponents X).Finite) {u : X}
    (hu : u ∈ E) : E ∈ nhds u :=
  let ⟨V, hV, huV, hVE⟩ := hspec.exists_isOpen_subset_of_stableUnderGeneralization hgen hfin hu
  mem_nhds_iff.mpr ⟨V, hVE, hV, huV⟩

/-- On a quasi-sober space with finitely many irreducible components, a subset stable under
specialization and under generalization is open. -/
theorem StableUnderSpecialization.isOpen_of_stableUnderGeneralization
    [QuasiSober X] {E : Set X} (hspec : StableUnderSpecialization E)
    (hgen : StableUnderGeneralization E) (hfin : (irreducibleComponents X).Finite) :
    IsOpen E :=
  isOpen_iff_mem_nhds.mpr fun _ hu =>
    hspec.mem_nhds_of_stableUnderGeneralization hgen hfin hu
