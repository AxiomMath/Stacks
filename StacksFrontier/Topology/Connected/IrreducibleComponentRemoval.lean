module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Connected.Basic

/-!
# Deleting one irreducible component of a connected space (Stacks 0GM3)

Let `X` be a connected topological space with finitely many irreducible components
`X₁, …, Xₙ`, and suppose `n > 1`. The Stacks Project shows that some component may be
deleted without disconnecting the rest: there is a `j` with `⋃_{i ≠ j} Xᵢ` connected.

The formalization states this with Mathlib's `irreducibleComponents X : Set (Set X)`, the
finiteness hypothesis as `(irreducibleComponents X).Finite` and `n > 1` as
`1 < (irreducibleComponents X).ncard`. `IsConnected` bundles nonemptiness, which is the
right reading here: the deleted-component union is nonempty precisely because more than one
component remains available.

The proof does not follow the source's argument about a leaf of the intersection graph.
Instead it grows a subfamily `S` of components whose union is connected, starting from a
single component and adding one component at a time: as long as `S` is a proper nonempty
subfamily, connectedness of `X` forces some component outside `S` to meet `⋃₀ S` (else the
two closed unions would disconnect `X`), and `IsConnected.union` extends connectedness
across that intersection point. Stopping one step early leaves exactly one component out.
-/

@[expose] public section

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- A member of a finset equal to the set of irreducible components is an irreducible
component. -/
private lemma mem_irreducibleComponents_of_mem_finset {F : Finset (Set X)}
    (hF : ↑F = irreducibleComponents X) {Z : Set X} (hZ : Z ∈ F) :
    Z ∈ irreducibleComponents X :=
  hF ▸ hZ

/-- The union of a subfamily of the irreducible components is closed, each component being
closed and the subfamily finite. -/
private lemma isClosed_sUnion_subfamily
    (F : Finset (Set X)) (hF : ↑F = irreducibleComponents X)
    (S : Finset (Set X)) (hSF : S ⊆ F) :
    IsClosed (⋃₀ (↑S : Set (Set X))) := by
  rw [Set.sUnion_eq_biUnion]
  exact S.finite_toSet.isClosed_biUnion fun s hs =>
    isClosed_of_mem_irreducibleComponents s (mem_irreducibleComponents_of_mem_finset hF (hSF hs))

/-- The union of a nonempty subfamily of the irreducible components is nonempty, each
component being nonempty. -/
private lemma nonempty_sUnion_subfamily
    (F : Finset (Set X)) (hF : ↑F = irreducibleComponents X)
    (S : Finset (Set X)) (hSF : S ⊆ F) (hSne : S.Nonempty) :
    (⋃₀ (↑S : Set (Set X))).Nonempty := by
  obtain ⟨Z, hZ⟩ := hSne
  have hZne : Z.Nonempty := (mem_irreducibleComponents_of_mem_finset hF (hSF hZ)).1.nonempty
  exact hZne.mono (Set.subset_sUnion_of_mem (Finset.mem_coe.mpr hZ))

/-- For a proper nonempty subfamily `S` of the irreducible components of a connected space,
some component outside `S` meets `⋃₀ S`. Otherwise `⋃₀ S` and the union of the remaining
components would be two disjoint nonempty closed sets covering `X`. -/
private lemma exists_mem_sdiff_inter_sUnion_nonempty [ConnectedSpace X]
    (F : Finset (Set X)) (hF : ↑F = irreducibleComponents X)
    (S : Finset (Set X)) (hSF : S ⊆ F) (hSne : S.Nonempty) (hSlt : S.card < F.card) :
    ∃ Z ∈ F \ S, (⋃₀ (↑S : Set (Set X)) ∩ Z).Nonempty := by
  by_contra h_neg
  push Not at h_neg
  have hFS_ne : (F \ S).Nonempty :=
    Finset.sdiff_nonempty.mpr fun h => absurd (Finset.card_le_card h) (not_le.mpr hSlt)
  -- The two unions cover `X`, since the components do.
  have hcov : ⋃₀ (↑S : Set (Set X)) ∪ ⋃₀ (↑(F \ S) : Set (Set X)) = Set.univ := by
    rw [← Set.sUnion_union, ← Finset.coe_union, Finset.union_sdiff_of_subset hSF, hF,
      sUnion_irreducibleComponents]
  -- ... and by assumption they are disjoint.
  have hdisj : Disjoint (⋃₀ (↑S : Set (Set X))) (⋃₀ (↑(F \ S) : Set (Set X))) := by
    rw [Set.disjoint_sUnion_right]
    exact fun Z hZ => Set.disjoint_iff_inter_eq_empty.mpr (h_neg Z (Finset.mem_coe.mp hZ))
  obtain ⟨x, _, hx_S, hx_FS⟩ := isPreconnected_closed_iff.mp (isPreconnected_univ (α := X)) _ _
    (isClosed_sUnion_subfamily F hF S hSF)
    (isClosed_sUnion_subfamily F hF (F \ S) Finset.sdiff_subset) hcov.ge
    (by rw [Set.univ_inter]; exact nonempty_sUnion_subfamily F hF S hSF hSne)
    (by rw [Set.univ_inter]; exact nonempty_sUnion_subfamily F hF _ Finset.sdiff_subset hFS_ne)
  exact Set.disjoint_left.mp hdisj hx_S hx_FS

/-- The inductive step: a proper nonempty subfamily with connected union can be enlarged by
one component, keeping the union connected. -/
private lemma exists_mem_sdiff_isConnected_sUnion_insert [ConnectedSpace X]
    (F : Finset (Set X)) (hF : ↑F = irreducibleComponents X)
    (S : Finset (Set X)) (hSF : S ⊆ F) (hSne : S.Nonempty) (hSlt : S.card < F.card)
    (hconn : IsConnected (⋃₀ (↑S : Set (Set X)))) :
    ∃ Z ∈ F \ S, IsConnected (⋃₀ (↑(insert Z S) : Set (Set X))) := by
  obtain ⟨Z, hZ_sdiff, hinter⟩ :=
    exists_mem_sdiff_inter_sUnion_nonempty F hF S hSF hSne hSlt
  refine ⟨Z, hZ_sdiff, ?_⟩
  rw [Finset.coe_insert, Set.sUnion_insert, Set.union_comm]
  exact IsConnected.union hinter hconn
    (mem_irreducibleComponents_of_mem_finset hF (Finset.mem_sdiff.mp hZ_sdiff).1).1.isConnected

/-- Growing a subfamily one component at a time until exactly one component is left out. -/
private lemma exists_mem_isConnected_sUnion_erase [ConnectedSpace X]
    (F : Finset (Set X)) (hF : ↑F = irreducibleComponents X) (h_gt : 1 < F.card) :
    ∃ Z ∈ F, IsConnected (⋃₀ (↑(F.erase Z) : Set (Set X))) := by
  obtain ⟨Z₁, hZ₁⟩ := Finset.card_pos.mp (Nat.lt_trans Nat.zero_lt_one h_gt)
  have hconn₁ : IsConnected (⋃₀ (↑({Z₁} : Finset (Set X)) : Set (Set X))) := by
    simp only [Finset.coe_singleton, Set.sUnion_singleton]
    exact (mem_irreducibleComponents_of_mem_finset hF hZ₁).1.isConnected
  -- Induct on the number `F.card - S.card` of components still to be added.
  suffices key : ∀ n : ℕ, ∀ S : Finset (Set X), S ⊆ F → S.Nonempty →
      IsConnected (⋃₀ (↑S : Set (Set X))) → F.card - S.card = n →
      S.card + 1 ≤ F.card →
      ∃ Z ∈ F, IsConnected (⋃₀ (↑(F.erase Z) : Set (Set X))) from
    key (F.card - ({Z₁} : Finset (Set X)).card) {Z₁}
      (Finset.singleton_subset_iff.mpr hZ₁)
      ⟨Z₁, Finset.mem_singleton_self Z₁⟩
      hconn₁ rfl (by simp only [Finset.card_singleton, Nat.reduceAdd]; exact h_gt)
  intro n
  induction n with
  | zero => intros; omega
  | succ k ih =>
    intro S hSF hSne hconn hn hcard
    by_cases h_done : S.card = F.card - 1
    · -- Exactly one component is left out, so `S = F.erase Z` for that component.
      have hFS_card : (F \ S).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSF]
        omega
      obtain ⟨Z, hZ_singleton⟩ := Finset.card_eq_one.mp hFS_card
      have hZmem : Z ∈ F \ S := hZ_singleton ▸ Finset.mem_singleton_self Z
      have hS_eq : S = F.erase Z := by
        rw [← Finset.sdiff_singleton_eq_erase, ← hZ_singleton, Finset.sdiff_sdiff_eq_self hSF]
      exact ⟨Z, (Finset.mem_sdiff.mp hZmem).1, hS_eq ▸ hconn⟩
    · -- Otherwise add one more component and recurse.
      have hSlt : S.card < F.card := by omega
      obtain ⟨Z, hZ_sdiff, hconn'⟩ :=
        exists_mem_sdiff_isConnected_sUnion_insert F hF S hSF hSne hSlt hconn
      have hZ_notin : Z ∉ S := (Finset.mem_sdiff.mp hZ_sdiff).2
      have hS'_card_eq : (insert Z S).card = S.card + 1 :=
        Finset.card_insert_of_notMem hZ_notin
      exact ih (insert Z S) (Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp hZ_sdiff).1, hSF⟩)
        ⟨Z, Finset.mem_insert_self Z S⟩ hconn' (by omega) (by omega)

/-- **Stacks 0GM3.** Let `X` be a connected topological space with finitely many irreducible
components, more than one of them. Then some irreducible component `Z` may be deleted so
that the union of the remaining components is still connected. -/
@[stacks 0GM3]
theorem exists_isConnected_sUnion_irreducibleComponents_sdiff [ConnectedSpace X]
    (h_fin : (irreducibleComponents X).Finite)
    (h_gt : 1 < (irreducibleComponents X).ncard) :
    ∃ Z ∈ irreducibleComponents X,
      IsConnected (⋃₀ (irreducibleComponents X \ {Z})) := by
  set F := h_fin.toFinset with hFdef
  have hF : ↑F = irreducibleComponents X := h_fin.coe_toFinset
  have hcard : 1 < F.card := by
    rwa [hFdef, ← Set.ncard_eq_toFinset_card _ h_fin]
  obtain ⟨Z, hZF, hconn⟩ := exists_mem_isConnected_sUnion_erase F hF hcard
  have herase : (↑(F.erase Z) : Set (Set X)) = irreducibleComponents X \ {Z} := by
    rw [Finset.coe_erase, hF]
  exact ⟨Z, mem_irreducibleComponents_of_mem_finset hF hZF, herase ▸ hconn⟩

end TopologicalSpace
