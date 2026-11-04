module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.DualBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleComm

/-!
# The zero section formula for an extension by an invertible quotient

Let `0 ⟶ ℰ' ⟶ ℱ ⟶ ℒ ⟶ 0` be a short exact sequence of finite locally free modules with `ℰ'` of
rank `e` and `ℒ` invertible. If the zero section formula `o_* β = p^*(c_e(ℰ') ∩ β)` holds for
`ℰ'`, it holds for `ℱ`: the zero section of `𝐕(ℱ^∨)` factors through `i : 𝐕((ℰ')^∨) ⟶ 𝐕(ℱ^∨)`,
Stacks 0FAA for the invertible quotient `ℒ` moves `i_*` past the pullback at the cost of
`c₁(ℒ) ∩ -`, and by the Whitney sum formula (Stacks 02UI) and the commutativity of Chern classes
(Stacks 02UA), `c_{e+1}(ℱ) ∩ β = c₁(ℒ) ∩ c_e(ℰ') ∩ β`.

## Main results

* `Stacks.Chow.chernCap_last_of_shortExact_of_rank_one` — the top Chern class of an extension by
  an invertible module.
* `Stacks.Chow.zeroSectionFormula_of_shortExact_of_rank_one` — the zero section formula for `ℱ`.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The Chern class cap products at equal degrees and equal indices agree. -/
theorem chernCap_heq_congr {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (F : T.Modules)
    (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    {k k' : ℤ} (hk : k = k') {i i' : Fin (r + 1)} (hi : i = i') {x : chowGroup C q k}
    {x' : chowGroup C q k'} (hx : x ≍ x') :
    GenuineChern.chernCap C r q F k i x ≍ GenuineChern.chernCap C r q F k' i' x' := by
  subst hk; subst hi; cases hx; rfl

/-- **The top Chern class of an extension by an invertible module.** For
`0 ⟶ ℰ' ⟶ ℱ ⟶ ℒ ⟶ 0` short exact with `ℰ'` of rank `e`, `ℱ` of rank `e + 1` and `ℒ` of rank one,
`c_{e+1}(ℱ) ∩ β = c₁(ℒ) ∩ (c_e(ℰ') ∩ β)`: the degree `e + 1` part of `c(ℱ) = c(ℰ') c(ℒ)`
(Stacks 02UI) is `c_e(ℰ') c₁(ℒ)`, since `c_{e+1}(ℰ') = 0` and `c_j(ℒ) = 0` for `j ≥ 2`, and the two
caps commute (Stacks 02UA). -/
theorem chernCap_last_of_shortExact_of_rank_one (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (e : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ e]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (e + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ 1]
    (k : ℤ) (β : chowGroup C sX k) :
    GenuineChern.chernCap C (e + 1) sX S.X₂ k (Fin.last (e + 1)) β ≍
      GenuineChern.chernCap C 1 sX S.X₃ (k - e) (Fin.last 1)
        (GenuineChern.chernCap C e sX S.X₁ k (Fin.last e) β) := by
  have hW := GenuineChern.chernFamily_eq_mul_of_shortExact C sX S hS e 1
  have h1 := congrArg (fun a => a k (e + 1) β) hW
  unfold GenuineChern.chernFamily at h1
  rw [chernCapFamilyOnChow_of_le C (GenuineChern.chernCap C) sX S.X₂ (e + 1) k le_rfl,
    gradedCap_mul_apply] at h1
  rw [Finset.sum_eq_single 1] at h1
  · rw [convolveTerm_of_le _ _ k (show 1 ≤ e + 1 by omega), capTo_def,
      chernCapFamilyOnChow_of_le C (GenuineChern.chernCap C) sX S.X₃ 1 k le_rfl,
      chernCapFamilyOnChow_of_le C (GenuineChern.chernCap C) sX S.X₁ e (k - ((1 : ℕ) : ℤ))
        (show e + 1 - 1 ≤ e by omega)] at h1
    refine (heq_of_eq h1).trans ((gradedDegreeCast_heq _ _).trans ?_)
    have hc := GenuineChern.chernCap_chernCap_comm C sX S.X₁ e S.X₃ 1 k
      ⟨e + 1 - 1, by omega⟩ (Fin.last 1) β
    refine (heq_of_eq hc).trans ((chowGroupCast_heq C sX _ _).trans ?_)
    exact chernCap_heq_congr C sX S.X₃ 1 (by simp) rfl
      (chernCap_heq_congr C sX S.X₁ e rfl (Fin.ext (by simp)) HEq.rfl)
  · intro j _ hj
    rcases Nat.lt_or_gt_of_ne hj with h0 | h2
    · obtain rfl : j = 0 := by omega
      rw [convolveTerm_of_le _ _ k (Nat.zero_le _), capTo_def,
        chernCapFamilyOnChow_of_gt C (GenuineChern.chernCap C) sX S.X₁ e _ (by omega)]
      simp
    · by_cases hjl : j ≤ e + 1
      · rw [convolveTerm_of_le _ _ k hjl, capTo_def,
          chernCapFamilyOnChow_of_gt C (GenuineChern.chernCap C) sX S.X₃ 1 k (by omega)]
        simp
      · exact convolveTerm_of_gt _ _ k hjl β
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

section Step

variable (K N L : X.Modules) (e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} K]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} K e]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N (e + 1)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
  (inc : K ⟶ N) (pr : N ⟶ L) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

/-- The zero section of `𝐕(𝒩^∨)` factors through the subbundle `𝐕(𝒦^∨)`. -/
theorem dualVectorBundleZeroSection_comp_subbundleEmbedding :
    dualVectorBundleZeroSection K ≫ subbundleEmbedding K N inc = dualVectorBundleZeroSection N :=
  congrArg (fun h => h.left) (vectorBundleOverZeroSection_comp_vectorBundleMap (dualMap inc))

include hseq in
/-- **The zero section formula for an extension by an invertible module.** If
`0 ⟶ 𝒦 ⟶ 𝒩 ⟶ ℒ ⟶ 0` is short exact with `𝒦` of rank `e` and `ℒ` invertible, the zero section
formula for `𝒦` implies the one for `𝒩`. -/
theorem zeroSectionFormula_of_shortExact_of_rank_one (hZ : ZeroSectionFormula C sX K e) :
    ZeroSectionFormula C sX N (e + 1) := by
  intro k β
  have := GenuineChern.isInvertible_of_rank_one L
  have := isClosedImmersion_subbundleEmbedding_of_shortExact K N L inc pr w hseq
  -- the zero section of `N` is that of `K` followed by `i`
  have hoi := dualVectorBundleZeroSection_comp_subbundleEmbedding K N inc
  have : IsClosedImmersion (dualVectorBundleZeroSection K ≫ subbundleEmbedding K N inc) :=
    inferInstance
  have hcb : (dualVectorBundleZeroSection K ≫ subbundleEmbedding K N inc) ≫
      dualVectorBundleToBase N ≫ sX = sX :=
    (congrArg (· ≫ dualVectorBundleToBase N ≫ sX) hoi).trans
      (dualVectorBundleZeroSection_comp_base C sX N)
  have hc1 : dualZeroSectionPushforward C sX N k β =
      properChowPushforward C sX (dualVectorBundleToBase N ≫ sX)
        (dualVectorBundleZeroSection K ≫ subbundleEmbedding K N inc) hcb k
        (properPushforwardDescends C _ _ _ _ _) β :=
    properChowPushforward_congr_hom C sX (dualVectorBundleToBase N ≫ sX) hoi.symm
      (dualVectorBundleZeroSection_comp_base C sX N) hcb k
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) β
  have h2 := properChowPushforward_comp C sX (dualVectorBundleToBase K ≫ sX)
    (dualVectorBundleToBase N ≫ sX) (dualVectorBundleZeroSection K) (subbundleEmbedding K N inc)
    (dualVectorBundleZeroSection_comp_base C sX K) (subbundleEmbedding_comp_base K N sX inc) k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
  have hcomp : dualZeroSectionPushforward C sX N k β =
      chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase K ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding K N inc)
        (subbundleEmbedding_comp_base K N sX inc) k (dualZeroSectionPushforward C sX K k β) :=
    hc1.trans (congrArg (fun φ => φ β) h2).symm
  rw [hcomp]
  have := locallyOfFiniteType_dualVectorBundleToBase K e
  have := flat_dualVectorBundleToBase K e
  have := locallyOfFiniteType_dualVectorBundleToBase N (e + 1)
  have := flat_dualVectorBundleToBase N (e + 1)
  set γ := GenuineChern.chernCap C e sX K k (Fin.last e) β with hγ
  set γ' := chowGroupCast C sX (show k - (e : ℤ) = k - (e : ℤ) - 1 + 1 by omega) γ with hγ'
  -- the zero section formula for `𝒦`
  have eA : chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase K ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding K N inc)
        (subbundleEmbedding_comp_base K N sX inc) k (dualZeroSectionPushforward C sX K k β) ≍
      chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase K ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding K N inc)
        (subbundleEmbedding_comp_base K N sX inc) (k - e - 1 + 1 + e)
        (dualBundlePullback C sX K e (k - e - 1 + 1) γ') := by
    refine properChowPushforward_heq_congr C _ _ (subbundleEmbedding K N inc)
      (subbundleEmbedding_comp_base K N sX inc) (by omega) _ _ _ _ ((hZ k β).trans ?_)
    exact flatPullbackChow_heq_of_degree C _ sX (dualVectorBundleToBase K) rfl e
      (relativeDimension_dualVectorBundleToBase K e) (by omega)
      (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
      (chowGroupCast_heq C sX _ γ).symm
  -- Stacks 0FAA for the invertible quotient `ℒ`
  have eB := subbundleEmbedding_pushforward_flatPullback_of_rank_one C sX K N L e inc pr w hseq
    (k - e - 1) γ'
  -- the top Chern class of `𝒩`
  have eC : GenuineChern.chernCap C 1 sX L (k - e - 1 + 1) (Fin.last 1) γ' ≍
      GenuineChern.chernCap C (e + 1) sX N k (Fin.last (e + 1)) β :=
    (chernCap_heq_congr C sX L 1 (by rw [Fin.val_last]; omega) rfl
      (chowGroupCast_heq C sX _ γ)).trans
      (chernCap_last_of_shortExact_of_rank_one C sX (ShortComplex.mk inc pr w) hseq e k β).symm
  refine eA.trans (eB.trans ?_)
  exact flatPullbackChow_heq_of_degree C _ sX (dualVectorBundleToBase N) rfl (e + 1)
    (relativeDimension_dualVectorBundleToBase N (e + 1)) (by omega)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) eC

end Step

end Stacks.Chow

end
