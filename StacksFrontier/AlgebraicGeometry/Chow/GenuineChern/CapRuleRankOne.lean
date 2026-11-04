module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleShift
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Inputs
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernBasic

/-!
# The Chern class cap product of an invertible module

For an invertible `𝒪_X`-module `ℒ`, a finite locally free module of rank `1`, the cap product
`c_1(ℒ) ∩ -` of [Stacks, Tag 02U6] is the first Chern class cap `c₁(ℒ) ∩ -` of
[Stacks, Tag 02SO] and [Stacks, Tag 02TI].

## Main results

* `Stacks.Chow.GenuineChern.chernCap_one_eq_invCap`: `c_1(ℒ) ∩ α = c₁(ℒ) ∩ α`.

## References

* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The Chern class cap product of an invertible module is its first Chern class cap.** For a
module `ℒ` of rank `1` on `X` and `α ∈ A_k(X)`, `c_1(ℒ) ∩ α = c₁(ℒ) ∩ α` in `A_{k-1}(X)`. -/
theorem chernCap_one_eq_invCap (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] (k : ℤ)
    (α : chowGroup C sX k) :
    haveI := isInvertible_of_rank_one L
    chernCap C 1 sX L k 1 α =
      (invCap C sX L).capOnChow C sX (k - 1) (chowGroupCast C sX (by omega) α) := by
  have := isInvertible_of_rank_one L
  let := isFiniteLocallyFree_of_rank L 1
  let := flat_bundleProj L 0
  let := locallyOfFiniteType_bundleProj L 0
  have := isInvertible_pullback (bundleProj L) L
  set x := (invCap C sX L).capOnChow C sX (k - 1) (chowGroupCast C sX (by omega) α)
  let c : ∀ j : Fin (0 + 1 + 1), chowGroup C sX (k - (j : ℤ)) :=
    Fin.cons (chowGroupCast C sX (by simp) α)
      (fun j : Fin (0 + 1) ↦ chowGroupCast C sX (by rw [Fin.val_succ, Fin.val_eq_zero j]; simp) x)
  have hc : IsBundleChernCapFamily L 0 C sX k α c := by
    refine ⟨chowGroupCast_chowGroupCast C sX _ _ α, ?_⟩
    show ∑ i : Fin (0 + 1 + 1), (-1 : ℤ) ^ i.val • projectiveBundleChernTerm C sX
      (bundleProj L ≫ sX) (bundleProj L) rfl (0 + 1) (relativeDimension_bundleProj L 0)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
      (bundleTwistCap L C sX) k i.val (Nat.lt_succ_iff.mp i.isLt) (c ⟨0 + 1 - i.val, by omega⟩) = 0
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, one_smul, pow_one, neg_smul,
      ← sub_eq_add_neg, sub_eq_zero]
    rw [projectiveBundleChernTerm_eq_capPow, projectiveBundleChernTerm_eq_capPow,
      capPow_zero_apply, capPow_succ_apply', capPow_zero_apply]
    refine eq_of_heq ?_
    have hfacπ := fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C
      (bundleProj L ≫ sX) sX (bundleProj L) rfl _ (relativeDimension_bundleProj L 0) k
    refine (chowGroupCast_heq C _ _ _).trans ?_
    refine (flatPullbackChow_heq C (bundleProj L ≫ sX) sX (bundleProj L) rfl _
      (relativeDimension_bundleProj L 0) hfacπ (by simp : k - ((0 + 1 - 0 : ℕ) : ℤ) = k - 1)
      (y := x) (chowGroupCast_heq C sX _ x)).trans ?_
    refine HEq.symm ?_
    show firstChernClassCapChow C _ (bundleProj L ≫ sX) (bundleTwist L) _ ≍ _
    rw [← firstChernClassCapChow_congr C (bundleProj L ≫ sX) _ (bundleTwistIsoOfRankOne L)]
    refine (capOnChow_heq C (bundleProj L ≫ sX)
      (invCap C (bundleProj L ≫ sX) ((Scheme.Modules.pullback (bundleProj L)).obj L))
      (d₂ := k - 1 + ((0 + 1 - 1 : ℕ) : ℤ)) (by omega)
      (y := chowGroupCast C _ (by omega)
        (flatPullbackChow C (bundleProj L ≫ sX) sX (bundleProj L) rfl _
          (relativeDimension_bundleProj L 0) (k - 1 + 1) (hfacπ (k - 1 + 1))
          (chowGroupCast C sX (by omega) α))) ?_).trans ?_
    · refine (chowGroupCast_heq C _ _ _).trans (HEq.trans ?_ (chowGroupCast_heq C _ _ _).symm)
      have hc0 : c ⟨0 + 1 - 1, by omega⟩ ≍ chowGroupCast C sX (show k = k - 1 + 1 by omega) α :=
        (chowGroupCast_heq C sX _ α).trans (chowGroupCast_heq C sX _ α).symm
      exact flatPullbackChow_heq C (bundleProj L ≫ sX) sX (bundleProj L) rfl _
        (relativeDimension_bundleProj L 0) hfacπ
        (by simp : k - ((0 + 1 - 1 : ℕ) : ℤ) = k - 1 + 1) hc0
    · exact (flatPullbackChow_firstChernClassCapChow_heq C (bundleProj L ≫ sX) sX (bundleProj L)
        rfl _ (relativeDimension_bundleProj L 0) hfacπ L _ (Iso.refl _) (k - 1)
        (chowGroupCast C sX (by omega) α) _ (chowGroupCast_heq C _ _ _)).symm
  have h := congrFun (eq_bundleChernCapFamily_of_isChernCapFamily L 0 C sX k α c hc) 1
  rw [chernCap_succ, bundleChernCap_apply, ← h]
  rfl

end Stacks.Chow.GenuineChern

end
