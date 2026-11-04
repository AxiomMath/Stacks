module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.TotalChernClassOfModule
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup

/-!
# The Chern class series of a finite locally free module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a scheme
locally of finite type over `S`. For a module `ℰ` that is finite locally free of rank `r`, the
series

  `c(ℰ) = (c_0(ℰ), c_1(ℰ), …, c_r(ℰ), 0, 0, …) ∈ ∏_{i ≥ 0} A^i(X)`

is built out of the bivariant Chern classes of [Stacks, Tag 0B7H] for given Chern cap products
`cap` as in [Stacks, Tag 0B7G]. It is the unique series whose components in the degrees `j ≤ r`
satisfy the characterization of [Stacks, Tag 0B7H] and which vanishes in higher degrees.

## Main definitions

* `Stacks.Chow.chernClassSeriesOfRank` — the series above, as an element of
  `Stacks.Chow.chowCohomologySeries`: the `i`-th bivariant Chern class of Stacks 0B7H in degree
  `i ≤ r`, and `0` in every higher degree.

## Main results

* `Stacks.Chow.isChernClassBivariant_chernClassSeriesOfRank` — each component of the series in a
  degree `j ≤ r` satisfies the characterization `Stacks.Chow.IsChernClassBivariant` of Stacks
  0B7H.
* `Stacks.Chow.chernClassSeriesOfRank_apply_coe_eq_totalChernClass`,
  `Stacks.Chow.chernClassSeriesOfRank_apply_eq_totalChernClass_of_gt` — in every degree the series
  agrees with the total Chern class of Stacks 0FE1, `Stacks.Chow.totalChernClass`.
* `Stacks.Chow.chernClassSeriesOfRank_eq` — a series whose components in the degrees `j ≤ r`
  satisfy that characterization and which vanishes in higher degrees is this one.

## Implementation notes

The parameters are those of `Stacks.Chow.chernClass`: the Chern cap products `cap` of Stacks
0B7G, the three naturality identities of Stacks 0B76 for them, and the isomorphism clause `hiso`
for the Gysin system.

Indices are `ℕ` and the components are indexed by `Fin (r + 1)`, so the degree-`j` component for
`j : Fin (r + 1)` is read at the natural number `(j : ℕ)`. No transport is needed anywhere:
`(⟨i, h⟩ : Fin (r + 1)).val` is `i` by definition, so the two spellings of the degree are the same
term.

## References

* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0FE1](https://stacks.math.columbia.edu/tag/0FE1)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (F : X.Modules) (r : ℕ) (G : GysinSystem C) (cap : HigherChernCapRule C r)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
  (hproper : ∀ i : Fin (r + 1), IdentityCapRule.ProperNaturality C sX (i : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap i))
  (hflat : ∀ i : Fin (r + 1), IdentityCapRule.FlatNaturality C sX (i : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap i))
  (hgysin : ∀ i : Fin (r + 1), IdentityCapRule.GysinNaturality C sX (i : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap i) G)
  (hiso : G.IsNaturalUnderInverseIso)

/-- The Chern class series `c(ℰ) = (c_0(ℰ), …, c_r(ℰ), 0, 0, …)` of a module `ℰ` that is finite
locally free of rank `r`: the `i`-th bivariant Chern class of Stacks 0B7H in each degree `i ≤ r`,
and `0` in every higher degree. -/
def chernClassSeriesOfRank : chowCohomologySeries C G sX := fun i ↦
  if h : i < r + 1 then chernClass C sX F r G cap hproper hflat hgysin hiso ⟨i, h⟩ else 0

/-- The degree-`j` component of the Chern class series is the `j`-th bivariant Chern class of
Stacks 0B7H, for `0 ≤ j ≤ r`. -/
theorem chernClassSeriesOfRank_apply_coe (j : Fin (r + 1)) :
    chernClassSeriesOfRank C sX F r G cap hproper hflat hgysin hiso (j : ℕ) =
      chernClass C sX F r G cap hproper hflat hgysin hiso j := by
  simp only [chernClassSeriesOfRank]
  split
  · rfl
  · exact absurd j.isLt (by assumption)

/-- The Chern class series of a module of rank `r` vanishes in every degree above `r`. -/
theorem chernClassSeriesOfRank_apply_of_gt (i : ℕ) (hi : r < i) :
    chernClassSeriesOfRank C sX F r G cap hproper hflat hgysin hiso i = 0 := by
  simp only [chernClassSeriesOfRank]
  split
  · exact absurd (by assumption : i < r + 1) (by omega)
  · rfl

/-- Each component of the series in a degree `j ≤ r` satisfies the characterization of Stacks
0B7H: on every test scheme `g : T ⟶ X` and in every degree, pushing `c_j(ℰ) ∩ α` forward along the
projection `X ×_X T ⟶ T` gives `c_j(g^*ℰ) ∩ α`. -/
theorem isChernClassBivariant_chernClassSeriesOfRank (j : Fin (r + 1)) :
    IsChernClassBivariant C sX F r G cap
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) j
      (chernClassSeriesOfRank C sX F r G cap hproper hflat hgysin hiso (j : ℕ)) := by
  rw [chernClassSeriesOfRank_apply_coe]
  exact isChernClassBivariant_chernClass C sX F r G cap hproper hflat hgysin hiso j

/-- The series is the total Chern class of Stacks 0FE1 read as a series: in each degree `j ≤ r`
its component is the component of `Stacks.Chow.totalChernClass`. -/
theorem chernClassSeriesOfRank_apply_coe_eq_totalChernClass (j : Fin (r + 1)) :
    chernClassSeriesOfRank C sX F r G cap hproper hflat hgysin hiso (j : ℕ) =
      totalChernClass C sX F r G cap hproper hflat hgysin hiso (j : ℤ) := by
  rw [chernClassSeriesOfRank_apply_coe, totalChernClass_apply_coe]

/-- In every degree above the rank `r`, the Chern class series agrees with the total Chern class
of Stacks 0FE1, both components being zero. -/
theorem chernClassSeriesOfRank_apply_eq_totalChernClass_of_gt (i : ℕ) (hi : r < i) :
    chernClassSeriesOfRank C sX F r G cap hproper hflat hgysin hiso i =
      totalChernClass C sX F r G cap hproper hflat hgysin hiso (i : ℤ) := by
  rw [chernClassSeriesOfRank_apply_of_gt C sX F r G cap hproper hflat hgysin hiso i hi,
    totalChernClass_apply_eq_zero C sX F r G cap hproper hflat hgysin hiso (i : ℤ)
      (Or.inr (by exact_mod_cast hi))]

/-- **Uniqueness of the Chern class series.** A series whose component in each degree `j ≤ r`
satisfies the characterization of Stacks 0B7H and which vanishes in every higher degree is the
series constructed above. -/
theorem chernClassSeriesOfRank_eq (a : chowCohomologySeries C G sX)
    (ha : ∀ j : Fin (r + 1), IsChernClassBivariant C sX F r G cap
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) j (a (j : ℕ)))
    (ha' : ∀ i : ℕ, r < i → a i = 0) :
    a = chernClassSeriesOfRank C sX F r G cap hproper hflat hgysin hiso := by
  funext i
  by_cases hi : i < r + 1
  · have h := eq_chernClass C sX F r G cap hproper hflat hgysin hiso ⟨i, hi⟩ (a i) (ha ⟨i, hi⟩)
    rw [h, ← chernClassSeriesOfRank_apply_coe C sX F r G cap hproper hflat hgysin hiso ⟨i, hi⟩]
  · rw [ha' i (by omega),
      chernClassSeriesOfRank_apply_of_gt C sX F r G cap hproper hflat hgysin hiso i (by omega)]

end Stacks.Chow

end
