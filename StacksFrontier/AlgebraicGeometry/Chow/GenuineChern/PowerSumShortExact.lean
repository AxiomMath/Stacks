module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleComm
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedPowerSum
public import StacksCore.Tactic.StacksAttribute

/-!
# The power sums of the Chern classes add in a short exact sequence, on cap families

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let

  `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_X`-modules, of ranks `r₁`, `r₁ + r₂`, `r₂`.
Then

  `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)`

for every `p`, where `P_p` is the universal power-sum polynomial of
[Stacks, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B) evaluated at the Chern classes, in
the ring of graded cap families on the Chow groups of `X`, the ring in which the total Chern class
`Stacks.Chow.GenuineChern.chernFamily` of [Stacks, Tag 02U6] lives.

Here `Stacks.Chow.powerSumFamily (Stacks.Chow.GenuineChern.chernFamily C sX ℰ r) p` is the graded
cap family concentrated in index `p` whose component in degree `k` is the operation

  `P_p(ℰ) ∩ - : A_k(X) ⟶ A_{k-p}(X)`.

The convention is `P₀ = 0`: the power sums are the signed components of the logarithmic derivative
`ν(c) = c⁻¹ · D(c)`, where `D` multiplies the index-`m` component by `m`.

## Main results

* `Stacks.Chow.GenuineChern.commute_chernFamily` — the total Chern classes of two finite locally
  free modules commute.
* `Stacks.Chow.GenuineChern.commute_logDerivFamily_chernFamily` — the logarithmic derivative of
  one commutes with the other.
* `Stacks.Chow.GenuineChern.logDerivFamily_chernFamily_eq_add_of_shortExact` — the additivity of
  all the power sums at once, as one equation.
* `Stacks.Chow.GenuineChern.powerSumFamily_chernFamily_eq_add_of_shortExact` — the additivity
  degree by degree.
* `Stacks.Chow.GenuineChern.powerSumCap_eq_add_of_shortExact` — the same, read against a fixed
  Chow class.

## References

* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-! ### The commutativity of the total Chern classes -/

/-- In index at most the rank, the total Chern class is the Chern class cap product of
[Stacks, Tag 02U6]. -/
theorem chernFamily_apply_of_le (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ) {i : ℕ}
    (hi : i ≤ r) :
    chernFamily C sX E r k i = chernCap C r sX E k ⟨i, Nat.lt_succ_of_le hi⟩ :=
  chernCapFamilyOnChow_of_le C (chernCap C) sX E r k hi

/-- Above the rank the total Chern class vanishes. -/
theorem chernFamily_apply_of_gt (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ) {i : ℕ}
    (hi : ¬ i ≤ r) : chernFamily C sX E r k i = 0 :=
  chernCapFamilyOnChow_of_gt C (chernCap C) sX E r k hi

/-- Above the rank the homogeneous components of the total Chern class vanish. -/
theorem homComponent_chernFamily_of_gt (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] {i : ℕ}
    (hi : ¬ i ≤ r) : homComponent i (chernFamily C sX E r) = 0 := by
  funext k j
  rcases eq_or_ne j i with hj | hj
  · subst hj
    rw [homComponent_apply_self, chernFamily_apply_of_gt C sX E r k hi]
    rfl
  · rw [homComponent_apply_of_ne hj]
    rfl

/-- **The homogeneous components of two total Chern classes commute**: the index-`i` component
of `c(ℰ)` and the index-`j` component of `c(ℱ)` commute ([Stacks, Tag 02UA]). -/
theorem commute_homComponent_chernFamily (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (F : X.Modules)
    (s : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s]
    (i j : ℕ) :
    Commute (homComponent i (chernFamily C sX E r))
      (homComponent j (chernFamily C sX F s)) := by
  by_cases hi : i ≤ r
  · by_cases hj : j ≤ s
    · refine commute_of_isHomogeneous_of_capTo (isHomogeneous_homComponent i _)
        (isHomogeneous_homComponent j _) fun k z => ?_
      rw [capTo_def, capTo_def, homComponent_apply_self, homComponent_apply_self,
        homComponent_apply_self, homComponent_apply_self,
        chernFamily_apply_of_le C sX E r (k - (j : ℤ)) hi,
        chernFamily_apply_of_le C sX F s k hj,
        chernFamily_apply_of_le C sX F s (k - (i : ℤ)) hj,
        chernFamily_apply_of_le C sX E r k hi]
      refine eq_of_heq ((gradedDegreeCast_heq _ _).trans
        (HEq.trans ?_ (gradedDegreeCast_heq _ _).symm))
      rw [chernCap_chernCap_comm C sX E r F s k ⟨i, Nat.lt_succ_of_le hi⟩
        ⟨j, Nat.lt_succ_of_le hj⟩ z]
      exact chowGroupCast_heq C sX _ _
    · rw [homComponent_chernFamily_of_gt C sX F s hj]
      exact Commute.zero_right _
  · rw [homComponent_chernFamily_of_gt C sX E r hi]
    exact Commute.zero_left _

/-- **The total Chern classes commute.** The total Chern classes of two finite locally free
modules on `X` commute in the ring of graded cap families on the Chow groups of `X`. -/
theorem commute_chernFamily (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (F : X.Modules)
    (s : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s] :
    Commute (chernFamily C sX E r) (chernFamily C sX F s) :=
  commute_of_commute_homComponent (commute_homComponent_chernFamily C sX E r F s)

/-- The logarithmic derivative of one total Chern class commutes with another. -/
theorem commute_logDerivFamily_chernFamily (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (F : X.Modules)
    (s : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s] :
    Commute (logDerivFamily (chernFamily C sX E r)) (chernFamily C sX F s) :=
  commute_logDerivFamily_of_commute_homComponent (chernFamily_apply_zero C sX E r)
    (commute_homComponent_chernFamily C sX E r F s)

/-! ### The additivity of the power sums -/

/-- **All the power sums at once.** For a short exact sequence
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free modules the logarithmic derivatives of the total
Chern classes add,

  `ν(c(ℰ)) = ν(c(ℰ₁)) + ν(c(ℰ₂))`,

which is the additivity of `P_p` in every degree `p` simultaneously, the degree-`p` component of
`ν` being `(-1)^{p-1} P_p`. -/
theorem logDerivFamily_chernFamily_eq_add_of_shortExact (S : ShortComplex X.Modules)
    (exact_S : S.ShortExact) (r₁ r₂ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂] :
    haveI := isFiniteLocallyFreeOfRank_of_shortExact S exact_S r₁ r₂ ‹_› ‹_›
    logDerivFamily (chernFamily C sX S.X₂ (r₁ + r₂)) =
      logDerivFamily (chernFamily C sX S.X₁ r₁) + logDerivFamily (chernFamily C sX S.X₃ r₂) := by
  rw [chernFamily_eq_mul_of_shortExact C sX S exact_S r₁ r₂]
  exact logDerivFamily_mul_of_commute (chernFamily_apply_zero C sX S.X₁ r₁)
    (chernFamily_apply_zero C sX S.X₃ r₂)
    (commute_logDerivFamily_chernFamily C sX S.X₁ r₁ S.X₃ r₂)

/-- **The additivity of the power sums on cap families.** Let `(S, δ)` be as in Situation 02QL,
let `X` be locally of finite type over `S` and let `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` be a short exact
sequence of finite locally free `𝒪_X`-modules, with `ℰ₁` of rank `r₁` and `ℰ₂` of rank `r₂`. Then
for every `p`

  `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)`,

where `P_p` is the universal power-sum polynomial of Stacks 0F9B evaluated at the Chern classes,
read as a graded cap family on the Chow groups of `X`. -/
theorem powerSumFamily_chernFamily_eq_add_of_shortExact (S : ShortComplex X.Modules)
    (exact_S : S.ShortExact) (r₁ r₂ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂] (p : ℕ) :
    haveI := isFiniteLocallyFreeOfRank_of_shortExact S exact_S r₁ r₂ ‹_› ‹_›
    powerSumFamily (chernFamily C sX S.X₂ (r₁ + r₂)) p =
      powerSumFamily (chernFamily C sX S.X₁ r₁) p +
        powerSumFamily (chernFamily C sX S.X₃ r₂) p := by
  rw [chernFamily_eq_mul_of_shortExact C sX S exact_S r₁ r₂]
  exact powerSumFamily_mul_of_commute (chernFamily_apply_zero C sX S.X₁ r₁)
    (chernFamily_apply_zero C sX S.X₃ r₂)
    (commute_logDerivFamily_chernFamily C sX S.X₁ r₁ S.X₃ r₂) p

/-- **The additivity against a fixed Chow class.** In the situation of
`Stacks.Chow.GenuineChern.powerSumFamily_chernFamily_eq_add_of_shortExact`, for every `k`, every
`α ∈ A_k(X)` and every `p`,

  `P_p(ℰ) ∩ α = P_p(ℰ₁) ∩ α + P_p(ℰ₂) ∩ α`  in  `A_{k-p}(X)`. -/
theorem powerSumCap_eq_add_of_shortExact (S : ShortComplex X.Modules) (exact_S : S.ShortExact)
    (r₁ r₂ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂] (p : ℕ)
    (k : ℤ) (α : chowGroup C sX k) :
    haveI := isFiniteLocallyFreeOfRank_of_shortExact S exact_S r₁ r₂ ‹_› ‹_›
    powerSumFamily (chernFamily C sX S.X₂ (r₁ + r₂)) p k p α =
      powerSumFamily (chernFamily C sX S.X₁ r₁) p k p α +
        powerSumFamily (chernFamily C sX S.X₃ r₂) p k p α := by
  rw [powerSumFamily_chernFamily_eq_add_of_shortExact C sX S exact_S r₁ r₂ p,
    gradedCap_add_apply]

end Stacks.Chow.GenuineChern

end
