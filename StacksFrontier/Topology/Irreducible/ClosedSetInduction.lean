module

public import Mathlib.Order.Zorn
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Irreducible

/-!
# Covering a space by members of a family of closed sets, by induction on irreducible closed sets

Let `X` be a topological space and `G` a nonempty family of subsets of `X` each of which has
quasi-compact complement, such that any two members of `G` are contained in a third. Suppose that
every irreducible closed subset `C ⊆ X` is contained in a member of `G` as soon as every closed
subset properly contained in `C` is. Then `X` itself is contained in a member of `G`.

This is a substitute for Noetherian induction which needs no finiteness condition on `X`: the
quasi-compactness of the complements makes the family of closed sets which are *not* contained in
a member of `G` closed under intersections of chains, so Zorn's lemma gives a minimal one, and
minimality together with the union condition makes it irreducible.

## Main results

* `TopologicalSpace.exists_mem_univ_subset_of_isIrreducible_step`: the induction principle.

## References

* [Stacks Project, Tag 0GUP](https://stacks.math.columbia.edu/tag/0GUP), where this replaces the
  Noetherian induction on the approximating space of Stacks 07SU.
-/

@[expose] public section

open Set

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- **Induction on irreducible closed sets.** Let `G` be a nonempty family of subsets of `X` with
quasi-compact complements, directed for inclusion up to containment of unions. If every
irreducible closed `C ⊆ X` all of whose proper closed subsets lie in members of `G` itself lies in
a member of `G`, then `X` lies in a member of `G`. -/
theorem exists_mem_univ_subset_of_isIrreducible_step (G : Set (Set X)) (hne : G.Nonempty)
    (hcpt : ∀ s ∈ G, IsCompact sᶜ) (hunion : ∀ s₁ ∈ G, ∀ s₂ ∈ G, ∃ s ∈ G, s₁ ∪ s₂ ⊆ s)
    (hstep : ∀ C : Set X, IsClosed C → IsIrreducible C →
      (∀ C' : Set X, IsClosed C' → C' ⊂ C → ∃ s ∈ G, C' ⊆ s) → ∃ s ∈ G, C ⊆ s) :
    ∃ s ∈ G, univ ⊆ s := by
  by_contra hbad
  let Bad : Set (Set X) := {C | IsClosed C ∧ ∀ s ∈ G, ¬ C ⊆ s}
  have huniv : univ ∈ Bad := ⟨isClosed_univ, fun s hs h => hbad ⟨s, hs, h⟩⟩
  have hchain : ∀ c ⊆ Bad, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ Bad, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hch hcne
    refine ⟨⋂₀ c, ⟨isClosed_sInter fun C hC => (hc hC).1, fun s hs hsub => ?_⟩,
      fun C hC => sInter_subset_of_mem hC⟩
    have : Nonempty c := hcne.to_subtype
    have hcover : sᶜ ⊆ ⋃ C : c, (C : Set X)ᶜ := by
      intro x hx
      by_contra hx'
      simp only [mem_iUnion, mem_compl_iff, not_exists, not_not] at hx'
      exact hx (hsub (mem_sInter.2 fun C hC => hx' ⟨C, hC⟩))
    have hdir : Directed (· ⊆ ·) fun C : c => (C : Set X)ᶜ := by
      intro C₁ C₂
      rcases eq_or_ne (C₁ : Set X) C₂ with h | h
      · exact ⟨C₁, le_rfl, by simp only [h, le_refl]⟩
      · rcases hch C₁.2 C₂.2 h with h₁ | h₁
        · exact ⟨C₁, le_rfl, compl_subset_compl.2 h₁⟩
        · exact ⟨C₂, compl_subset_compl.2 h₁, le_rfl⟩
    obtain ⟨C, hC⟩ := (hcpt s hs).elim_directed_cover _
      (fun C => (hc C.2).1.isOpen_compl) hcover hdir
    exact (hc C.2).2 s hs (compl_subset_compl.1 hC)
  obtain ⟨m, -, hm⟩ := zorn_superset_nonempty Bad hchain univ huniv
  -- A closed set properly contained in `m` lies in a member of `G`.
  have hsmall : ∀ C' : Set X, IsClosed C' → C' ⊂ m → ∃ s ∈ G, C' ⊆ s := by
    intro C' hC' hlt
    by_contra h
    push Not at h
    exact hlt.2 (hm.2 ⟨hC', h⟩ hlt.1)
  have hnonempty : m.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    obtain ⟨s, hs⟩ := hne
    exact hm.1.2 s hs (empty_subset s)
  have hirr : IsIrreducible m := by
    refine ⟨hnonempty, (isPreirreducible_iff_isClosed_union_isClosed).2 ?_⟩
    intro z₁ z₂ hz₁ hz₂ hsub
    by_contra h
    push Not at h
    have hcut : ∀ z, IsClosed z → ¬ m ⊆ z → ∃ s ∈ G, m ∩ z ⊆ s := fun z hz hmz =>
      hsmall _ (hm.1.1.inter hz) ⟨inter_subset_left, fun h' => hmz (h'.trans inter_subset_right)⟩
    obtain ⟨s₁, hs₁, h₁⟩ := hcut z₁ hz₁ h.1
    obtain ⟨s₂, hs₂, h₂⟩ := hcut z₂ hz₂ h.2
    obtain ⟨s, hs, hs₁₂⟩ := hunion s₁ hs₁ s₂ hs₂
    refine hm.1.2 s hs fun x hx => hs₁₂ ?_
    exact (hsub hx).imp (fun hx' => h₁ ⟨hx, hx'⟩) fun hx' => h₂ ⟨hx, hx'⟩
  obtain ⟨s, hs, hms⟩ := hstep m hm.1.1 hirr hsmall
  exact hm.1.2 s hs hms

end TopologicalSpace

end
