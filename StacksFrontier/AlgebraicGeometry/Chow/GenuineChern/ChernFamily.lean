module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlat
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapRing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.ShortExactSequence

/-!
# The Chern classes of a finite locally free module as an element of the ring of cap families

For a finite locally free module `ℱ` of rank `r` on a scheme `T` locally of finite type over the
base of chapter 42, the cap products `c_j(ℱ) ∩ - : A_k(T) ⟶ A_{k-j}(T)` of
[Stacks, Tag 02U6] (`Stacks.Chow.GenuineChern.chernCap`), extended by zero above the rank, form a
graded cap family on the Chow groups of `T`: the *total Chern class*

  `c(ℱ) = 1 + c₁(ℱ) + ⋯ + c_r(ℱ)`

read in the ring of graded cap families of
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapRing`. Its index-`0` component is the
identity, so it is a unit of that ring.

## Main definitions

* `Stacks.Chow.GenuineChern.chernFamily` — the total Chern class of `ℱ` as a graded cap family.

## Main results

* `Stacks.Chow.GenuineChern.chernFamily_apply_zero`, `Stacks.Chow.GenuineChern.isUnit_chernFamily`
  — `c_0(ℱ) = 1`, and `c(ℱ)` is invertible.
* `Stacks.Chow.GenuineChern.chernFamily_congr` — invariance under isomorphisms of modules.
* `Stacks.Chow.GenuineChern.chernFamily_of_rank_zero` — `c(ℱ) = 1` in rank zero.
* `Stacks.Chow.GenuineChern.intertwines_chernFamily` — flat pullback intertwines the total Chern
  classes of `ℱ` and of its pullback, [Stacks, Tag 02U8].

## References

* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q]

/-- **The total Chern class** `c(ℱ) = 1 + c₁(ℱ) + ⋯ + c_r(ℱ)` of a finite locally free module of
rank `r`, as a graded cap family on the Chow groups of `T`: its index-`j` component is
`c_j(ℱ) ∩ - : A_k(T) ⟶ A_{k-j}(T)` for `j ≤ r`, the cap product of Stacks 02U6, and zero for
`j > r`. -/
abbrev chernFamily (F : T.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    GradedCapFamily (chowGroup C q) :=
  chernCapFamilyOnChow C (chernCap C) q F r

variable (F : T.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]

/-- **`c_0(ℱ) = 1`**: the index-`0` component of the total Chern class is the identity. -/
theorem chernFamily_apply_zero (k : ℤ) :
    chernFamily C q F r k 0 = (1 : GradedCapFamily (chowGroup C q)) k 0 := by
  refine AddMonoidHom.ext fun α => ?_
  dsimp only [chernFamily]
  rw [chernCapFamilyOnChow_of_le C (chernCap C) q F r k (Nat.zero_le r),
    gradedCap_one_apply_zero]
  have h := chernCap_zero_apply C q F k r α
  refine eq_of_heq (((chowGroupCast_heq C q _ (chernCap C r q F k 0 α)).symm.trans
    (heq_of_eq h)).trans (gradedDegreeCast_heq _ α).symm)

/-- **The total Chern class is a unit** of the ring of graded cap families. -/
theorem isUnit_chernFamily : IsUnit (chernFamily C q F r) :=
  isUnit_of_apply_zero (chernFamily_apply_zero C q F r)

/-- **Stacks 02U8 for the total Chern class**: for `f : Y ⟶ T` flat of relative dimension `d`
over the base and `ℱ' ≅ f^*ℱ`, flat pullback carries `c(ℱ)` to `c(ℱ')`. -/
theorem intertwines_chernFamily {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : Y ⟶ T) [LocallyOfFiniteType f] [Flat f] (hf : f ≫ q = sY) (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension f d) (F' : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r]
    (eF : F' ≅ (Scheme.Modules.pullback f).obj F) :
    Intertwines
      (fun k => flatPullbackChow C sY q f hf d hd k
        (flatPullbackFactorsThroughRationalEquivalence_general C sY q f hf d hd k))
      (chernFamily C q F r) (chernFamily C sY F' r) := by
  intro k i α
  dsimp only [chernFamily]
  by_cases hi : i ≤ r
  · rw [chernCapFamilyOnChow_of_le C (chernCap C) q F r k hi,
      chernCapFamilyOnChow_of_le C (chernCap C) sY F' r (k + d) hi]
    refine eq_of_heq ((chernCap_flatPullback_heq C q sY f hf d hd F r F' eF k
      ⟨i, Nat.lt_succ_of_le hi⟩
      (flatPullbackFactorsThroughRationalEquivalence_general C sY q f hf d hd k)
      (flatPullbackFactorsThroughRationalEquivalence_general C sY q f hf d hd _) α).symm.trans ?_)
    exact (gradedDegreeCast_heq _ _).symm
  · rw [chernCapFamilyOnChow_of_gt C (chernCap C) q F r k hi,
      chernCapFamilyOnChow_of_gt C (chernCap C) sY F' r (k + d) hi]
    simp

/-- **Invariance under isomorphisms of modules.** Isomorphic modules, of ranks spelled
differently but equal, have the same total Chern class. -/
theorem chernFamily_congr {F' : T.Modules} {r' : ℕ}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r'] (e : F' ≅ F)
    (h : r' = r) : chernFamily C q F' r' = chernFamily C q F r := by
  subst h
  funext k i
  refine AddMonoidHom.ext fun α => ?_
  have hint := intertwines_chernFamily C q F r' q (𝟙 T) (Category.id_comp q) 0
    (relativeDimension_identity T) F' (e ≪≫ ((Scheme.Modules.pullbackId T).app F).symm) k i α
  have h1 := flatPullbackChow_id C q k α
  have h2 := flatPullbackChow_id C q (k - (i : ℤ)) (chernFamily C q F r' k i α)
  have hheq : chernFamily C q F' r' (k + ((0 : ℕ) : ℤ)) i
      (chowGroupCast C q (show k = k + ((0 : ℕ) : ℤ) from by simp) α) ≍
      chernFamily C q F' r' k i α :=
    heq_apply_of_degree C q q (fun d => d) (fun d => d - (i : ℤ))
      (fun d => chernFamily C q F' r' d i) (by simp) (chowGroupCast_heq C q _ α)
  refine eq_of_heq (hheq.symm.trans ?_)
  rw [← h1]
  refine (gradedDegreeCast_heq (show k + ((0 : ℕ) : ℤ) - (i : ℤ) = k - (i : ℤ) + ((0 : ℕ) : ℤ)
    by omega) _).symm.trans ?_
  rw [← hint]
  exact (heq_of_eq h2).trans (chowGroupCast_heq C q _ _)

/-- **The total Chern class in rank zero is `1`.** -/
theorem chernFamily_of_rank_zero
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 0] :
    chernFamily C q F 0 = 1 := by
  funext k i
  rcases i with _ | i
  · exact chernFamily_apply_zero C q F 0 k
  · dsimp only [chernFamily]
    rw [chernCapFamilyOnChow_of_gt C (chernCap C) q F 0 k (by omega),
      gradedCap_one_of_ne (Nat.succ_ne_zero i)]

end Stacks.Chow.GenuineChern

end
