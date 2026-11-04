module

public import Mathlib.Topology.NoetherianSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Openness in a Noetherian space, tested on irreducible closed subsets (Stacks 0541)

A subset `E` of a Noetherian topological space `X` is open exactly when, for every irreducible
closed subset `Y ⊆ X`, the intersection `E ∩ Y` is either empty or contains a nonempty open
subset of `Y`. "A nonempty open subset of `Y`" is spelled out as an open `V ⊆ X` with `V ∩ Y`
nonempty and `V ∩ Y ⊆ E`; the sets of that form are precisely the nonempty opens of the subspace
`Y`.

## Main results

* `Topology.isOpen_iff_inter_irreducible_closed`: the openness criterion of Stacks 0541.
* `Topology.exists_irredundant_finite_subcover`: a finite cover by closed sets can be shrunk to an
  irredundant one.
-/

@[expose] public section

open Set TopologicalSpace

namespace TopologicalSpace.Closeds

/-- The supremum of a finite set of closed subsets is their union. -/
lemma coe_sSup_of_finite {X : Type*} [TopologicalSpace X] {S : Set (Closeds X)} (hS : S.Finite) :
    (↑(sSup S) : Set X) = ⋃ t ∈ S, (↑t : Set X) := by
  rw [coe_sSup, sUnion_image]
  exact (Set.Finite.isClosed_biUnion hS fun t _ => t.2).closure_eq

end TopologicalSpace.Closeds

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/-- A finite cover by closed sets can be shrunk to an irredundant one: some subset of the
members still covers, and none of the retained members is contained in the union of the
others. -/
lemma exists_irredundant_finite_subcover {C : Set X} {S : Finset (Closeds X)}
    (hcover : C ⊆ ⋃ t ∈ S, (↑t : Set X)) :
    ∃ T : Finset (Closeds X), T ⊆ S ∧ C ⊆ ⋃ t ∈ T, (↑t : Set X) ∧
      ∀ t ∈ T, ¬ ((↑t : Set X) ⊆ ⋃ (s ∈ T) (_ : s ≠ t), (↑s : Set X)) := by
  classical
  suffices h : ∀ n : ℕ, ∀ S' : Finset (Closeds X), S'.card ≤ n → S' ⊆ S →
      C ⊆ ⋃ t ∈ S', (↑t : Set X) →
      ∃ T : Finset (Closeds X), T ⊆ S ∧ C ⊆ ⋃ t ∈ T, (↑t : Set X) ∧
        ∀ t ∈ T, ¬ ((↑t : Set X) ⊆ ⋃ (s ∈ T) (_ : s ≠ t), (↑s : Set X)) from
    h S.card S le_rfl (Finset.Subset.refl _) hcover
  intro n
  induction n with
  | zero =>
    intro S' hcard _ hcov
    obtain rfl : S' = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exact ⟨∅, Finset.empty_subset _, hcov, fun t ht => absurd ht (by simp)⟩
  | succ n ih =>
    intro S' hcard hS'S hcov
    by_cases h : ∀ t ∈ S', ¬ ((↑t : Set X) ⊆ ⋃ (s ∈ S') (_ : s ≠ t), (↑s : Set X))
    · exact ⟨S', hS'S, hcov, h⟩
    push Not at h
    obtain ⟨t, ht, htsub⟩ := h
    have hcover' : C ⊆ ⋃ s ∈ S'.erase t, (↑s : Set X) := by
      intro p hp
      obtain ⟨s, hs, hps⟩ := mem_iUnion₂.mp (hcov hp)
      by_cases heq : s = t
      · subst heq
        obtain ⟨s', hs', hps'⟩ := mem_iUnion₂.mp (htsub hps)
        obtain ⟨hs'ne, hps''⟩ := mem_iUnion.mp hps'
        exact mem_iUnion₂.mpr ⟨s', Finset.mem_erase.mpr ⟨hs'ne, hs'⟩, hps''⟩
      · exact mem_iUnion₂.mpr ⟨s, Finset.mem_erase.mpr ⟨heq, hs⟩, hps⟩
    have hlt : (S'.erase t).card ≤ n :=
      Nat.le_of_lt_succ ((Finset.card_erase_lt_of_mem ht).trans_le hcard)
    exact ih (S'.erase t) hlt ((Finset.erase_subset t S').trans hS'S) hcover'

/-- Splitting off one member of a finite cover by closed sets: a set covered by `⋃ t ∈ T, ↑t` is
covered by `↑Ycl` together with the union of the members different from `Ycl`. -/
lemma subset_union_biUnion_ne_of_subset_biUnion {T : Finset (Closeds X)} {Ycl : Closeds X}
    {C : Set X} (hC : C ⊆ ⋃ t ∈ T, (↑t : Set X)) :
    C ⊆ (↑Ycl : Set X) ∪ ⋃ (s ∈ T) (_ : s ≠ Ycl), (↑s : Set X) := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := mem_iUnion₂.mp (hC hp)
  by_cases h : t = Ycl
  · exact Or.inl (h ▸ hpt)
  · exact Or.inr (mem_iUnion₂.mpr ⟨t, ht, mem_iUnion.mpr ⟨h, hpt⟩⟩)

/-- The union of the members of a finite family of closed sets other than a given one is
closed. -/
lemma isClosed_biUnion_ne {T : Finset (Closeds X)} {Ycl : Closeds X} :
    IsClosed (⋃ (s ∈ T) (_ : s ≠ Ycl), (↑s : Set X)) := by
  refine Set.Finite.isClosed_biUnion T.finite_toSet fun s _ => ?_
  by_cases h : s = Ycl
  · simp [h]
  · convert s.2 using 1
    simp [h]

/-- If `Y ⊆ closure Eᶜ` is irreducible, `D` is closed, `closure Eᶜ ⊆ Y ∪ D` and `Y ⊄ D`, then
there is no open `U` with `U ∩ Y` nonempty and `U ∩ Y ⊆ E`. -/
lemma not_exists_isOpen_inter_subset_of_subset_closure_compl {E Y D : Set X}
    (hY : IsIrreducible Y) (hYC : Y ⊆ closure Eᶜ) (hD : IsClosed D)
    (hC : closure Eᶜ ⊆ Y ∪ D) (hYD : ¬ Y ⊆ D) :
    ¬ ∃ U : Set X, IsOpen U ∧ (U ∩ Y).Nonempty ∧ U ∩ Y ⊆ E := by
  rintro ⟨U, hUo, hUY, hUYE⟩
  have hDo : IsOpen Dᶜ := hD.isOpen_compl
  have hYDc : (Y ∩ Dᶜ).Nonempty := Set.not_subset.mp hYD
  obtain ⟨p, hpY, hpU, hpD⟩ :=
    hY.2 U Dᶜ hUo hDo (inter_comm U Y ▸ hUY) hYDc
  have hmeets : (U ∩ Dᶜ ∩ closure Eᶜ).Nonempty := ⟨p, ⟨hpU, hpD⟩, hYC hpY⟩
  obtain ⟨z, ⟨hzU, hzD⟩, hzE⟩ :=
    closure_nonempty_iff.mp (hmeets.mono (hUo.inter hDo).inter_closure)
  exact hzE (hUYE ⟨hzU, (hC (subset_closure hzE)).resolve_right hzD⟩)

/-- The reverse direction of Stacks 0541: in a Noetherian space, a subset that meets every
irreducible closed subset either not at all or in a nonempty open of it is open. -/
lemma isOpen_of_inter_irreducible_closed [NoetherianSpace X] (E : Set X)
    (H : ∀ Y : Set X, IsClosed Y → IsIrreducible Y →
      E ∩ Y = ∅ ∨ ∃ V : Set X, IsOpen V ∧ (V ∩ Y).Nonempty ∧ V ∩ Y ⊆ E) :
    IsOpen E := by
  rw [← isClosed_compl_iff, ← closure_subset_iff_isClosed]
  by_contra hF
  obtain ⟨x, hxC, hxnF⟩ := Set.not_subset.mp hF
  have hxE : x ∈ E := Set.notMem_compl_iff.mp hxnF
  set C := closure Eᶜ with hC_def
  obtain ⟨S, hSfin, hSirr, hSsup⟩ :=
    NoetherianSpace.exists_finite_set_closeds_irreducible (⟨C, isClosed_closure⟩ : Closeds X)
  have hC_eq : C = ⋃ t ∈ S, (↑t : Set X) := by
    rw [show C = (↑(sSup S) : Set X) from congrArg Closeds.carrier hSsup,
      Closeds.coe_sSup_of_finite hSfin]
  have hCover : C ⊆ ⋃ t ∈ hSfin.toFinset, (↑t : Set X) := by simp [hC_eq]
  obtain ⟨T, hTS, hTcover, hTirredundant⟩ := exists_irredundant_finite_subcover hCover
  obtain ⟨Ycl, hYmem, hxY⟩ := mem_iUnion₂.mp (hTcover hxC)
  have hYS : Ycl ∈ S := hSfin.mem_toFinset.mp (hTS hYmem)
  have hY_irr : IsIrreducible (Ycl : Set X) := hSirr Ycl hYS
  have hY_sub_C : (Ycl : Set X) ⊆ C := fun p hp => hC_eq ▸ mem_iUnion₂.mpr ⟨Ycl, hYS, hp⟩
  have hEY : (E ∩ (Ycl : Set X)).Nonempty := ⟨x, hxE, hxY⟩
  exact not_exists_isOpen_inter_subset_of_subset_closure_compl hY_irr hY_sub_C
    isClosed_biUnion_ne (subset_union_biUnion_ne_of_subset_biUnion hTcover)
    (hTirredundant Ycl hYmem) ((H _ Ycl.2 hY_irr).resolve_left hEY.ne_empty)

/-- **Stacks 0541.** A subset `E` of a Noetherian topological space is open if and only if, for
every irreducible closed subset `Y`, the intersection `E ∩ Y` is empty or contains a nonempty
open subset of `Y`, that is, a set `V ∩ Y` with `V` open in `X` and `V ∩ Y` nonempty. -/
@[stacks 0541, ega "0 9.2.6"]
theorem isOpen_iff_inter_irreducible_closed [NoetherianSpace X] (E : Set X) :
    IsOpen E ↔ ∀ Y : Set X, IsClosed Y → IsIrreducible Y →
      E ∩ Y = ∅ ∨ ∃ V : Set X, IsOpen V ∧ (V ∩ Y).Nonempty ∧ V ∩ Y ⊆ E := by
  refine ⟨fun hE Y _ _ => ?_, isOpen_of_inter_irreducible_closed E⟩
  exact (eq_empty_or_nonempty (E ∩ Y)).imp id fun h => ⟨E, hE, h, inter_subset_left⟩

end Topology
