module

public import StacksFrontier.Topology.Constructible.LocallyClosedQuasiCompact
public import StacksFrontier.Topology.Constructible.MeetConstructible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible sets are exactly the finite unions of `U ∩ Vᶜ`

Stacks 005G(1) *defines* a subset `E ⊆ X` to be constructible when it is a finite union of
subsets of the form `U ∩ Vᶜ` with `U, V ⊆ X` open and retrocompact in `X`. Mathlib instead
defines `Topology.IsConstructible` as membership in the Boolean subalgebra of `Set X` generated
by the open retrocompact sets. The two notions agree, but Mathlib's is not in Stacks' normal
form; this file supplies the normal form.

The open retrocompact subsets of `X` form a sublattice of `Set X` containing `⊥` and `⊤`, so
`BooleanSubalgebra.mem_closure_iff_sup_sdiff` applies and presents every constructible set as a
finite union of differences of open retrocompact sets. Closure under `∩` goes through
`IsRetrocompact.inter_isOpen`, since Mathlib's unrestricted `IsRetrocompact.inter` carries a
Hausdorff hypothesis. The converse direction needs none of this: it is `IsConstructible.biUnion`
applied to differences of the generators.

## Main results

* `Topology.isConstructible_iff_exists_finset_biUnion_inter_compl`: **Stacks 005G(1)**. A set is
  constructible if and only if it is a finite union of sets `U ∩ Vᶜ` with `U` and `V` open and
  retrocompact.
* `Topology.isConstructible_iff_isConstructibleStratified`: the same result, phrased as the
  agreement of Mathlib's `Topology.IsConstructible` with this repository's normal-form
  predicate `IsConstructibleStratified`.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- **Stacks 005G(1)**.
A subset `s` of a topological space `X` is constructible if and only if it is a finite union of
subsets of the form `U ∩ Vᶜ` with `U, V ⊆ X` open and retrocompact in `X`. The finite union is
encoded by a `Finset` of pairs `(U, V)`. -/
@[stacks 005G "(1)", ega "0 9.1.3", ega "0 9.1.2", sga "3 VIB 3.7"]
theorem Topology.isConstructible_iff_exists_finset_biUnion_inter_compl {s : Set X} :
    Topology.IsConstructible s ↔
      ∃ t : Finset (Set X × Set X),
        (∀ p ∈ t, IsOpen p.1 ∧ IsRetrocompact p.1 ∧ IsOpen p.2 ∧ IsRetrocompact p.2) ∧
        s = ⋃ p ∈ t, p.1 ∩ p.2ᶜ := by
  classical
  constructor
  · intro hs
    obtain ⟨t, rfl⟩ := (BooleanSubalgebra.mem_closure_iff_sup_sdiff
      isSublattice_isOpen_and_isRetrocompact bot_mem_isOpen_and_isRetrocompact
      top_mem_isOpen_and_isRetrocompact).mp hs
    refine ⟨t.image fun q ↦ (q.1.1, q.2.1), ?_, ?_⟩
    · intro p hp
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨q.1.2.1, q.1.2.2, q.2.2.1, q.2.2.2⟩
    · rw [Finset.set_biUnion_finset_image, Finset.sup_set_eq_biUnion]
      simp [Set.sdiff_eq]
  · rintro ⟨t, ht, rfl⟩
    refine Topology.IsConstructible.biUnion t.finite_toSet fun p hp ↦ ?_
    obtain ⟨hU, hU', hV, hV'⟩ := ht p hp
    rw [← Set.sdiff_eq]
    exact (hU'.isConstructible hU).sdiff (hV'.isConstructible hV)

/-- Mathlib's `Topology.IsConstructible` agrees with the normal form `IsConstructibleStratified`
of Stacks 005G(1). -/
theorem Topology.isConstructible_iff_isConstructibleStratified {s : Set X} :
    Topology.IsConstructible s ↔ IsConstructibleStratified s :=
  Topology.isConstructible_iff_exists_finset_biUnion_inter_compl
