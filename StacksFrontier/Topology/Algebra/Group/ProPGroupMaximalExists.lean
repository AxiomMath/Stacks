module

public import StacksFrontier.Topology.Algebra.Group.ProPGroup

/-!
# Existence of maximal pro-`p` subgroups

Every topological group `G` has a maximal pro-`p` subgroup
(`IsMaximalProPSubgroup p H`): the closure of the union of a chain of closed pro-`p` subgroups is
again a closed pro-`p` subgroup, so Zorn's lemma applies. The pro-`p` property of the closure is
checked at a finite level: an element `x` of the closure has, for every open normal subgroup `N`
of the closure, an element `s` of the union in the coset `x N`, and `s` lies in a member of the
chain, which is pro-`p`.

For a profinite group these are the `p`-Sylow subgroups, which by
`IsMaximalProPSubgroup.exists_sylow_eq_map` have Sylow images in all finite quotients.

## Main results

* `IsProPGroup.topologicalClosure_sSup_of_isChain`: the closure of the union of a chain of
  pro-`p` subgroups is pro-`p`.
* `exists_isMaximalProPSubgroup`: maximal pro-`p` subgroups exist.

## References

* J.-P. Serre, *Galois cohomology*, I.1.4, Proposition 3.
-/

@[expose] public section

namespace IsProPGroup

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The closure of the union of a chain of pro-`p` subgroups is pro-`p`.** -/
theorem topologicalClosure_sSup_of_isChain {c : Set (Subgroup G)}
    (hc : IsChain (· ≤ ·) c) (hpro : ∀ K ∈ c, IsProPGroup p K) :
    IsProPGroup p (sSup c).topologicalClosure := by
  set K := (sSup c).topologicalClosure
  intro N g
  induction g using QuotientGroup.induction_on with
  | H x =>
  -- the coset `x N` is open in `K`
  have hopen : IsOpen {y : K | x⁻¹ * y ∈ N.toSubgroup} :=
    N.isOpen'.preimage (continuous_const.mul continuous_id)
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.1 hopen
  have hxW : x ∈ ((↑) : K → G) ⁻¹' W := by
    rw [hWeq]
    simp
  obtain ⟨s, hsW, hsS⟩ := mem_closure_iff.1 x.2 W hW hxW
  have hsK : s ∈ K := Subgroup.le_topologicalClosure _ hsS
  have hsN : x⁻¹ * ⟨s, hsK⟩ ∈ N.toSubgroup := by
    have : (⟨s, hsK⟩ : K) ∈ ((↑) : K → G) ⁻¹' W := hsW
    rwa [hWeq] at this
  rw [QuotientGroup.eq.2 hsN]
  -- `s` lies in a member of the chain, or is `1`
  rcases c.eq_empty_or_nonempty with hce | hcne
  · have hs1 : s = 1 := by
      have : s ∈ sSup c := hsS
      rwa [hce, sSup_empty, Subgroup.mem_bot] at this
    exact ⟨0, by rw [show (⟨s, hsK⟩ : K) = 1 from Subtype.ext hs1, QuotientGroup.mk_one, one_pow]⟩
  · obtain ⟨Ki, hKi, hsKi⟩ := (Subgroup.mem_sSup_of_directedOn hcne hc.directedOn).1 hsS
    have hle : Ki ≤ K := (le_sSup hKi).trans (Subgroup.le_topologicalClosure _)
    let ι : Ki →* K := Subgroup.inclusion hle
    let N' : OpenNormalSubgroup Ki :=
      { toSubgroup := N.toSubgroup.comap ι
        isOpen' := N.isOpen'.preimage (continuous_subtype_val.subtype_mk _)
        isNormal' := inferInstance }
    obtain ⟨k, hk⟩ := hpro Ki hKi N' (⟨s, hsKi⟩ : Ki)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk ⊢
    have h1 : ι (⟨s, hsKi⟩ ^ p ^ k) ∈ N.toSubgroup := hk
    rwa [map_pow] at h1

end IsProPGroup

/-- **Maximal pro-`p` subgroups exist** in every topological group. -/
theorem exists_isMaximalProPSubgroup (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : ∃ H : Subgroup G, IsMaximalProPSubgroup p H := by
  obtain ⟨m, hm⟩ := zorn_le₀ {K : Subgroup G | IsClosed (K : Set G) ∧ IsProPGroup p K}
    fun c hcS hc => ⟨(sSup c).topologicalClosure,
      ⟨Subgroup.isClosed_topologicalClosure _,
        IsProPGroup.topologicalClosure_sSup_of_isChain hc fun K hK => (hcS hK).2⟩,
      fun z hz => (le_sSup hz).trans (Subgroup.le_topologicalClosure _)⟩
  exact ⟨m, hm⟩

end
