module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Irreducible
public import StacksCore.Tactic.StacksAttribute

/-!
# Surjections do not increase the number of irreducible components (Stacks 0GM2)

Let `f : X → Y` be a surjective continuous map of topological spaces. If `X` has a finite
number `n` of irreducible components, then `Y` has at most `n` irreducible components.

The conclusion is stated as the conjunction `(irreducibleComponents Y).Finite` together
with `(irreducibleComponents Y).ncard ≤ (irreducibleComponents X).ncard`; the finiteness
half is needed because `Set.ncard` of an infinite set is `0`, so the inequality alone would
not say what the source says.

Strategy: every irreducible component `T` of `Y` is contained in the finite union of the
closed sets `closure (f '' S)`, `S` an irreducible component of `X`, so by irreducibility
(`isIrreducible_iff_sUnion_isClosed`, applied to the finite family as a `Finset`) it lies
in one of them, and maximality forces `T = closure (f '' S)`. Hence the components of `Y`
form a subset of the image of the components of `X` under `S ↦ closure (f '' S)`, which
gives both the finiteness and the cardinality bound.
-/

@[expose] public section

open Set

/-- For every irreducible component `T` of `Y`, there exists an irreducible component `S` of
`X` such that `T = closure (f '' S)`. -/
lemma exists_mem_irreducibleComponents_eq_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f)
    (hX : (irreducibleComponents X).Finite)
    (T : Set Y) (hT : T ∈ irreducibleComponents Y) :
    ∃ S ∈ irreducibleComponents X, T = closure (f '' S) := by
  classical
  obtain ⟨hT_irr, hT_max⟩ := hT
  have hfin : ((fun S => closure (f '' S)) '' irreducibleComponents X).Finite := hX.image _
  have hT_subset : T ⊆ ⋃₀ (hfin.toFinset : Set (Set Y)) := by
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    refine ⟨closure (f '' irreducibleComponent x), ?_,
      subset_closure ⟨x, mem_irreducibleComponent, rfl⟩⟩
    rw [Finset.mem_coe, hfin.mem_toFinset]
    exact ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, rfl⟩
  obtain ⟨Z, hZmem, hTZ⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp hT_irr hfin.toFinset
      (fun Z hZ => by
        rw [hfin.mem_toFinset] at hZ
        obtain ⟨S, _, rfl⟩ := hZ
        exact isClosed_closure)
      hT_subset
  rw [hfin.mem_toFinset] at hZmem
  obtain ⟨S, hS, rfl⟩ := hZmem
  exact ⟨S, hS, le_antisymm hTZ (hT_max (hS.1.image f hf.continuousOn).closure hTZ)⟩

/-- Let `f : X → Y` be a surjective, continuous map of topological spaces. If `X` has finitely
many irreducible components, then `Y` has finitely many irreducible components and their number
is at most that of `X`. -/
@[stacks 0GM2]
theorem ncard_irreducibleComponents_le_of_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf_cont : Continuous f) (hf_surj : Function.Surjective f)
    (hX : (irreducibleComponents X).Finite) :
    (irreducibleComponents Y).Finite ∧
      (irreducibleComponents Y).ncard ≤ (irreducibleComponents X).ncard := by
  have hsub : irreducibleComponents Y ⊆
      (fun S ↦ closure (f '' S)) '' irreducibleComponents X := fun T hT => by
    obtain ⟨S, hS, hTS⟩ :=
      exists_mem_irreducibleComponents_eq_closure_image f hf_cont hf_surj hX T hT
    exact ⟨S, hS, hTS.symm⟩
  exact ⟨(hX.image _).subset hsub,
    (Set.ncard_le_ncard hsub (hX.image _)).trans (Set.ncard_image_le hX)⟩
