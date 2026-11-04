module

public import StacksFrontier.Topology.Dimension.Catenary
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# The two formulations of a catenary space agree

Catenarity of a topological space is written in two ways here. The bundled form,
`IrreducibleClosedsCodim.IsCatenarySpace`, asks that for every pair `Y ≤ Y'` of irreducible
closed subsets the codimension `IrreducibleClosedsCodim.topCodim Y Y'` — the supremum of the
lengths of *all* chains from `Y` to `Y'` — is finite, and that every maximal chain attains it.
The unbundled form, `TopologicalSpace.IsTopologicallyCatenary`, quantifies over raw sets
`T ⊆ T'` carrying irreducibility and closedness hypotheses and asks that some maximal chain
from `T` to `T'` exists and that all of them have one and the same length.

The two conditions are equivalent, on an arbitrary topological space and with no sobriety,
Noetherian or finiteness hypotheses. One direction is immediate: finiteness of the codimension
produces a maximal chain realising it, and every maximal chain has that length.

The other direction is the one that looks weaker, because `IsTopologicallyCatenary` constrains
only *maximal* chains while `topCodim` is a supremum over all chains, and a chain cannot in
general be refined to a maximal one by inserting intermediate irreducible closed subsets — the
insertion process need not terminate. What rescues it is that `IsTopologicallyCatenary` is
assumed for *every* pair, not just for the pair at hand: given an arbitrary chain
`T = Z₀ ⊊ Z₁ ⊊ ⋯ ⊊ Z_m = T'`, each single step `Z_i ⊆ Z_{i+1}` has a maximal chain of some
length `n_i ≥ 1`, and concatenating those maximal chains is again maximal, so `m ≤ Σ n_i`,
which the uniqueness clause pins to the common maximal length. Hence the supremum is finite
after all.

## Main results

* `IrreducibleClosedsCodim.IsCatenarySpace.isTopologicallyCatenary`: the bundled condition
  implies the unbundled one.
* `TopologicalSpace.IsTopologicallyCatenary.isCatenarySpace`: the unbundled condition implies
  the bundled one.
* `IrreducibleClosedsCodim.isCatenarySpace_iff_isTopologicallyCatenary`: the two are equivalent.

## References

* [Stacks Project, Tag 02I0](https://stacks.math.columbia.edu/tag/02I0)
* [Stacks Project, Tag 02I1](https://stacks.math.columbia.edu/tag/02I1)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace IrreducibleClosedsCodim

variable {X : Type u} [TopologicalSpace X]

/-! ### Translating between the two encodings of a chain -/

/-- The bundled chain in `TopologicalSpace.IrreducibleCloseds X` underlying a maximal chain of
raw sets `c : Fin (n + 1) → Set X`. -/
private def ofClosedChain {n : ℕ} {c : Fin (n + 1) → Set X}
    (hc : IsMaximalIrreducibleClosedChain c) : LTSeries (IrreducibleCloseds X) :=
  RelSeries.mk n (fun i => ⟨c i, (hc.2.1 i).1, (hc.2.1 i).2⟩) fun i => by
    have h : c i.castSucc < c i.succ := hc.1 Fin.castSucc_lt_succ
    have hle : (⟨c i.castSucc, (hc.2.1 _).1, (hc.2.1 _).2⟩ : IrreducibleCloseds X) ≤
        ⟨c i.succ, (hc.2.1 _).1, (hc.2.1 _).2⟩ := SetLike.coe_subset_coe.mp h.le
    exact lt_of_le_of_ne hle fun he => h.ne (congrArg IrreducibleCloseds.carrier he)

private lemma coe_ofClosedChain {n : ℕ} {c : Fin (n + 1) → Set X}
    (hc : IsMaximalIrreducibleClosedChain c) (i : Fin (n + 1)) :
    ((ofClosedChain hc i : IrreducibleCloseds X) : Set X) = c i := rfl

private lemma length_ofClosedChain {n : ℕ} {c : Fin (n + 1) → Set X}
    (hc : IsMaximalIrreducibleClosedChain c) : (ofClosedChain hc).length = n := rfl

/-- Consecutive members of the bundled chain attached to a maximal chain of raw sets are a
covering pair. -/
private lemma covBy_ofClosedChain {n : ℕ} {c : Fin (n + 1) → Set X}
    (hc : IsMaximalIrreducibleClosedChain c) (i : Fin (ofClosedChain hc).length) :
    ofClosedChain hc i.castSucc ⋖ ofClosedChain hc i.succ := by
  refine ⟨(ofClosedChain hc).step i, fun Z hZ1 hZ2 => ?_⟩
  rcases hc.2.2 i (Z : Set X) Z.isIrreducible' Z.isClosed'
    (SetLike.coe_subset_coe.mpr hZ1.le) (SetLike.coe_subset_coe.mpr hZ2.le) with h | h
  · exact hZ1.ne' (IrreducibleCloseds.ext h)
  · exact hZ2.ne (IrreducibleCloseds.ext h)

/-- The family of underlying sets of a bundled chain whose consecutive members are covering
pairs is a maximal chain of raw irreducible closed sets. -/
private lemma isMaximalIrreducibleClosedChain_coe {p : LTSeries (IrreducibleCloseds X)}
    (hcov : ∀ i : Fin p.length, p i.castSucc ⋖ p i.succ) :
    IsMaximalIrreducibleClosedChain fun i => (p i : Set X) := by
  refine ⟨fun i j hij => SetLike.coe_strictMono (p.strictMono hij),
    fun i => ⟨(p i).isIrreducible', (p i).isClosed'⟩, fun i Z hZirr hZcl h₁ h₂ => ?_⟩
  by_cases hlow : (⟨Z, hZirr, hZcl⟩ : IrreducibleCloseds X) = p i.castSucc
  · exact Or.inl (congrArg IrreducibleCloseds.carrier hlow)
  by_cases hupp : (⟨Z, hZirr, hZcl⟩ : IrreducibleCloseds X) = p i.succ
  · exact Or.inr (congrArg IrreducibleCloseds.carrier hupp)
  have hs₁ : p i.castSucc < (⟨Z, hZirr, hZcl⟩ : IrreducibleCloseds X) :=
    lt_of_le_of_ne (SetLike.coe_subset_coe.mpr h₁) (Ne.symm hlow)
  have hs₂ : (⟨Z, hZirr, hZcl⟩ : IrreducibleCloseds X) < p i.succ :=
    lt_of_le_of_ne (SetLike.coe_subset_coe.mpr h₂) hupp
  exact absurd (hcov i) (not_covBy_of_lt_of_lt hs₁ hs₂)

/-- The bundled chain attached to a maximal chain of raw sets from `Y` to `Y'` is a maximal
chain from `Y` to `Y'`. -/
private lemma isMaximalChain_ofClosedChain {n : ℕ} {c : Fin (n + 1) → Set X}
    (hc : IsMaximalIrreducibleClosedChain c) {Y Y' : IrreducibleCloseds X}
    (h0 : c 0 = Y) (hlast : c (Fin.last n) = Y') : IsMaximalChain (ofClosedChain hc) Y Y' :=
  ⟨IrreducibleCloseds.ext h0, IrreducibleCloseds.ext hlast, covBy_ofClosedChain hc⟩

/-- A maximal chain of bundled irreducible closed sets from `Y` to `Y'` gives a maximal chain of
raw sets from `Y` to `Y'`. -/
private lemma exists_isMaximalIrreducibleClosedChain {Y Y' : IrreducibleCloseds X}
    {p : LTSeries (IrreducibleCloseds X)} (hp : IsMaximalChain p Y Y') :
    ∃ c : Fin (p.length + 1) → Set X, c 0 = Y ∧ c (Fin.last p.length) = Y' ∧
      IsMaximalIrreducibleClosedChain c :=
  ⟨fun i => (p i : Set X), congrArg IrreducibleCloseds.carrier hp.1,
    congrArg IrreducibleCloseds.carrier hp.2.1, isMaximalIrreducibleClosedChain_coe hp.2.2⟩

/-! ### Catenary implies topologically catenary -/

/-- A catenary space is topologically catenary: between nested irreducible closed subsets there
is a maximal chain, and all maximal chains have the same length. -/
theorem IsCatenarySpace.isTopologicallyCatenary (hX : IsCatenarySpace X) :
    IsTopologicallyCatenary X := by
  intro T T' hTirr hTcl hT'irr hT'cl hTT'
  obtain ⟨hfin, hmaxlen⟩ :=
    hX ⟨T, hTirr, hTcl⟩ ⟨T', hT'irr, hT'cl⟩ hTT'
  obtain ⟨p, hpmax, hplen⟩ :=
    exists_maximalChain_length_eq_topCodim ⟨T, hTirr, hTcl⟩ ⟨T', hT'irr, hT'cl⟩ hTT' hfin
  refine ⟨p.length, exists_isMaximalIrreducibleClosedChain hpmax, fun m c hc0 hclast hcmax => ?_⟩
  have hlen := (hmaxlen _ (isMaximalChain_ofClosedChain hcmax hc0 hclast)).trans hplen.symm
  rw [length_ofClosedChain hcmax] at hlen
  exact_mod_cast hlen

/-! ### Topologically catenary implies catenary -/

/-- Under `TopologicalSpace.IsTopologicallyCatenary`, every pair `Y ≤ Y'` of irreducible closed
subsets admits a maximal chain, and all maximal chains from `Y` to `Y'` share its length. -/
private lemma exists_isMaximalChain_length_unique (hX : IsTopologicallyCatenary X)
    {Y Y' : IrreducibleCloseds X} (hYY' : Y ≤ Y') :
    ∃ n : ℕ, (∃ p : LTSeries (IrreducibleCloseds X), IsMaximalChain p Y Y' ∧ p.length = n) ∧
      ∀ p : LTSeries (IrreducibleCloseds X), IsMaximalChain p Y Y' → p.length = n := by
  obtain ⟨n, ⟨c, hc0, hclast, hcmax⟩, huniq⟩ :=
    hX Y.isIrreducible' Y.isClosed' Y'.isIrreducible' Y'.isClosed' hYY'
  refine ⟨n, ⟨ofClosedChain hcmax, isMaximalChain_ofClosedChain hcmax hc0 hclast, rfl⟩,
    fun p hp => ?_⟩
  obtain ⟨c', h0, hlast, hmax⟩ := exists_isMaximalIrreducibleClosedChain hp
  exact huniq p.length c' h0 hlast hmax

/-- Under `TopologicalSpace.IsTopologicallyCatenary`, an arbitrary chain is no longer than a
maximal chain with the same endpoints. Concatenating, step by step, a maximal chain across each
of its steps produces a maximal chain at least as long. -/
private lemma length_le_of_isMaximalChain (hX : IsTopologicallyCatenary X) :
    ∀ (m : ℕ) (p q : LTSeries (IrreducibleCloseds X)), p.length = m →
      IsMaximalChain q p.head p.last → m ≤ q.length := by
  intro m
  induction m with
  | zero => exact fun _ _ _ _ => Nat.zero_le _
  | succ m ih =>
    intro p q hlen hq
    have hne : p.length ≠ 0 := by omega
    have hstep := p.step ⟨0, by omega⟩
    have h0 : p.toFun (Fin.castSucc (⟨0, by omega⟩ : Fin p.length)) = p.head := rfl
    have h1 : p.toFun (Fin.succ (⟨0, by omega⟩ : Fin p.length)) = (p.tail hne).head := by
      rw [RelSeries.head_tail]
      congr 1
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_mk, zero_add, Fin.val_one']
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [h0, h1] at hstep
    have htlen : (p.tail hne).length = m := by rw [RelSeries.tail_length]; omega
    have htlast : (p.tail hne).last = p.last := RelSeries.last_tail p hne
    have hZlast : (p.tail hne).head ≤ p.last :=
      htlast ▸ LTSeries.head_le_last (p.tail hne)
    obtain ⟨-, ⟨p₁, hp₁, -⟩, -⟩ := exists_isMaximalChain_length_unique hX hstep.le
    obtain ⟨-, ⟨p₂, hp₂, -⟩, -⟩ := exists_isMaximalChain_length_unique hX hZlast
    have hm_le : m ≤ p₂.length := ih (p.tail hne) p₂ htlen (by rw [htlast]; exact hp₂)
    have h1le : 1 ≤ p₁.length := by
      rcases Nat.eq_zero_or_pos p₁.length with h | h
      · exact absurd (eq_of_isMaximalChain_length_zero _ _ p₁ hp₁ h) hstep.ne
      · exact h
    obtain ⟨r, hr, hrlen⟩ :=
      isMaximalChain_smash p.head (p.tail hne).head p.last p₁ p₂ hp₁ hp₂
    obtain ⟨n, -, huniq⟩ :=
      exists_isMaximalChain_length_unique hX (hstep.le.trans hZlast)
    have hqn := huniq q hq
    have hrn := huniq r hr
    omega

/-- A topologically catenary space is catenary. The content is that the codimension, a supremum
over *all* chains, is finite: an arbitrary chain is bounded by the common length of the maximal
chains with the same endpoints. -/
theorem _root_.TopologicalSpace.IsTopologicallyCatenary.isCatenarySpace
    (hX : IsTopologicallyCatenary X) : IsCatenarySpace X := by
  intro Y Y' hYY'
  obtain ⟨n, ⟨p, hp, hplen⟩, huniq⟩ := exists_isMaximalChain_length_unique hX hYY'
  have hle : topCodim Y Y' ≤ (n : ℕ∞) := by
    refine topCodim_le_iff.mpr fun r hr1 hr2 => ?_
    have hrp : r.length ≤ p.length :=
      length_le_of_isMaximalChain hX r.length r p rfl (by rw [hr1, hr2]; exact hp)
    exact_mod_cast hrp.trans_eq hplen
  have hge : (n : ℕ∞) ≤ topCodim Y Y' := by
    rw [← hplen]
    exact length_le_topCodim Y Y' p hp.1 hp.2.1
  have heq : topCodim Y Y' = (n : ℕ∞) := le_antisymm hle hge
  exact ⟨by rw [heq]; exact ENat.natCast_ne_top n, fun r hr => by rw [heq, huniq r hr]⟩

/-- The bundled and unbundled formulations of catenarity agree on every topological space, with
no sobriety, Noetherian or finiteness hypotheses. -/
theorem isCatenarySpace_iff_isTopologicallyCatenary :
    IsCatenarySpace X ↔ IsTopologicallyCatenary X :=
  ⟨IsCatenarySpace.isTopologicallyCatenary,
    TopologicalSpace.IsTopologicallyCatenary.isCatenarySpace⟩

end IrreducibleClosedsCodim

end
