module

public import Mathlib.Topology.Irreducible
public import StacksCore.Tactic.StacksAttribute

/-!
# Irreducible components from an irredundant irreducible-closed covering

Let `X` be a topological space and let `T : Fin n → Set X` be a family of irreducible closed
subsets such that

* `X = ⋃ i, T i`, and
* no `T i` is contained in the union of the other members.

Then the set of irreducible components of `X` is exactly the image of `T`: each `T i` is an
irreducible component, and every irreducible component of `X` equals some `T j`. Stating the
conclusion as the set equality `irreducibleComponents X = Set.range T` records both at once.

## Main results

* `irreducibleComponents_eq_range_of_irredundant_cover`:
  `irreducibleComponents X = Set.range T`.
-/

@[expose] public section

open Set

variable {X : Type*} [TopologicalSpace X]

/-- **Stacks 0G2Y**.
Given an irredundant finite covering of `X` by irreducible closed subsets `T i` (`i : Fin n`),
the set of irreducible components of `X` is exactly the image of `T`. -/
@[stacks 0G2Y, ega "0 2.1.7" "first assertion"]
theorem irreducibleComponents_eq_range_of_irredundant_cover
    {n : ℕ} (T : Fin n → Set X)
    (hcov : ⋃ i, T i = (Set.univ : Set X))
    (hirr : ∀ i, IsIrreducible (T i))
    (hcl : ∀ i, IsClosed (T i))
    (hmin : ∀ i, ¬ T i ⊆ ⋃ j ∈ ({j | j ≠ i} : Set (Fin n)), T j) :
    irreducibleComponents X = Set.range T := by
  classical
  -- Auxiliary fact: every irreducible component equals some `T j`.
  have forward :
      ∀ {Y : Set X}, Y ∈ irreducibleComponents X → ∃ j, Y = T j := by
    intro Y ⟨hYirr, hYmax⟩
    -- `Y` is covered by the finitely many closed sets `T i`.
    have hYcov : Y ⊆ ⋃₀ (Set.range T) := by
      intro y _hy
      have hyU : y ∈ (Set.univ : Set X) := mem_univ _
      rw [← hcov] at hyU
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hyU
      exact ⟨T i, ⟨i, rfl⟩, hyi⟩
    -- The image of `T` is a finite collection of closed sets.
    have hRangeFin : (Set.range T).Finite := finite_range T
    have hRangeClosed : ∀ Z ∈ Set.range T, IsClosed Z := by
      rintro _ ⟨i, rfl⟩; exact hcl i
    -- Apply the finite-cover characterisation of irreducibility.
    have hfsub : Y ⊆ ⋃₀ (hRangeFin.toFinset : Set (Set X)) := by
      simpa [hRangeFin.coe_toFinset] using hYcov
    obtain ⟨Z, hZmem, hYZ⟩ :=
      (isIrreducible_iff_sUnion_isClosed.mp hYirr) hRangeFin.toFinset
        (by
          intro Z hZ
          rw [hRangeFin.mem_toFinset] at hZ
          exact hRangeClosed Z hZ)
        hfsub
    rw [hRangeFin.mem_toFinset] at hZmem
    obtain ⟨j, rfl⟩ := hZmem
    -- Maximality of `Y` upgrades `Y ⊆ T j` to `Y = T j`.
    refine ⟨j, ?_⟩
    have hsup : T j ⊆ Y := hYmax (hirr j) hYZ
    exact hYZ.antisymm hsup
  -- `⊆` is the auxiliary fact; for `⊇` show every `T i` is an irreducible component.
  refine Set.eq_of_subset_of_subset (fun _ hY => (forward hY).imp fun _ hj => hj.symm) ?_
  rintro _ ⟨i, rfl⟩
  -- `T i` is an irreducible subset, hence inside some component `Y`.
  obtain ⟨Y, hYmem, hTiY⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (T i) (hirr i)
  -- By the auxiliary fact, `Y = T j` for some `j`.
  obtain ⟨j, rfl⟩ := forward hYmem
  -- Irredundancy forces `j = i`, so `T i = T j = Y`.
  by_cases hji : j = i
  · cases hji
    exact hYmem
  · -- Otherwise `T i ⊆ T j ⊆ ⋃ k ≠ i, T k`, contradicting `hmin i`.
    exact absurd (fun x hx => mem_iUnion₂.mpr ⟨j, (hji : j ≠ i), hTiY hx⟩) (hmin i)

