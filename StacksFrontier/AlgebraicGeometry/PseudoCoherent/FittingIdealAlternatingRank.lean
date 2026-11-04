module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealLocalDescription

/-!
# The alternating rank sum: the index of the Fitting ideal sheaves of [Stacks, Tag 0ESQ]

The Fitting ideal sheaves `Fit_{i, k_i}(E)` that [Stacks, Tag 0ESQ] blows up are taken at the
index `k_i = r_{i+1} - r_{i+2} + r_{i+3} - ⋯`, the alternating sum of the ranks of the cohomology
of `E` in the degrees above `i`. This file defines that sum and records what pinning the index to
it buys.

The point is a defect of the free index. `Stacks.FittingComplex.FreeData.minorSize p k` is
`tailAlternatingRank p - k`, so for an index `k` far below the alternating sum of the ranks of a
bounded-above finite free model the prescribed size of the minors exceeds the size of the matrix,
the ideal of minors is the zero ideal, and
`AlgebraicGeometry.not_disjoint_support_fittingIdealSheaf_of_card_lt_minorSize` shows the support
of the Fitting ideal sheaf then contains the affine open: disjointness of the support from an open
is *false* for a freely chosen index. At `k = alternatingRankSum r b` and a model whose ranks are
`r` the prescribed size is exactly `0`, so the ideal of minors is the unit ideal and that
mechanism is unavailable.

## Main definitions

* `Stacks.FittingComplex.alternatingRankSum`: the sum `r_{i+1} - r_{i+2} + ⋯ + (-1)^{b-i+1} r_b`
  of a rank function `r : ℤ → ℕ` over the degrees above `i`, up to a degree `b` above which the
  ranks vanish.
* `AlgebraicGeometry.HasLocalFittingDescription`: the local description of [Stacks, Tag 0ESP] in
  the form the disjointness statement consumes — a quasi-coherent ideal sheaf in each degree
  which is bounded above by the ideals of minors on every affine open, and which on affine opens
  covering a given open is bounded below by the ideals of minors of a bounded-above finite free
  model whose ranks are `r`.

## Main results

* `Stacks.FittingComplex.FreeData.minorSize_alternatingRankSum_of_rank_eq`: a model whose ranks
  are `r` and which vanishes above `b` has prescribed minor size `0` at
  `k = alternatingRankSum r b`.
* `Stacks.FittingComplex.FreeData.fittingIdeal_alternatingRankSum_of_rank_eq` and
  `AlgebraicGeometry.FreeModel.minorIdeal_matrix_eq_top_of_rank_eq`: hence its Fitting ideal at
  that index is the unit ideal.
* `AlgebraicGeometry.FreeModel.not_card_lt_minorSize_alternatingRankSum`: hence the hypothesis of
  `AlgebraicGeometry.not_disjoint_support_fittingIdealSheaf_of_card_lt_minorSize` — the prescribed
  size of the minors exceeding the size of the matrix — cannot hold at that index.
* `AlgebraicGeometry.disjoint_support_fittingIdealSheaf_alternatingRankSum`: granted the local
  description, the support of `Fit_{p, k_p}(E)` at `k = alternatingRankSum r b` is disjoint from
  the open.
* `AlgebraicGeometry.hasLocalFittingDescription_of_minorIdeal_le`: that local description asks
  for nothing beyond the inclusion of [Stacks, Tag 0ESP] that the construction of the Fitting
  ideal sheaf does not supply, over the given open only.
* `Stacks.FittingComplex.alternatingRankSum_eq_of_vanishing`: the sum does not depend on the
  chosen bound `b`, as long as the ranks vanish above it.

## Implementation notes

The alternating sum of an infinite tail of ranks needs a finiteness input, and here it is an
explicit degree `b` together, where it matters, with the hypothesis that `r` vanishes above `b`.
This mirrors `Stacks.FittingComplex.FreeData.top` exactly, so that
`Stacks.FittingComplex.FreeData.tailAlternatingRank_eq_alternatingRankSum` holds by definition; a
finiteness hypothesis on the support of `r` would instead have to be unpacked by a choice before
it could feed a definition. `Stacks.FittingComplex.alternatingRankSum_eq_of_vanishing` is what
says that nothing is lost: two bounds above which the ranks vanish give the same sum.

## References

* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
-/

@[expose] public section

namespace Stacks.FittingComplex

universe u

/-- The alternating sum `r_{i+1} - r_{i+2} + ⋯ + (-1)^{b-i+1} r_b` of a rank function over the
degrees above `i`, up to a degree `b`. This is the index at which [Stacks, Tag 0ESQ] takes the
Fitting ideal sheaf in degree `i`, with `r` the ranks of the cohomology of the complex. It is the
whole alternating tail sum as soon as `r` vanishes above `b`. -/
def alternatingRankSum (r : ℤ → ℕ) (b i : ℤ) : ℤ :=
  ∑ j ∈ Finset.range (b - i).toNat, (-1 : ℤ) ^ j * (r (i + 1 + j) : ℤ)

/-- Above the bound the alternating sum is empty, hence zero. -/
theorem alternatingRankSum_of_le {r : ℤ → ℕ} {b i : ℤ} (hi : b ≤ i) :
    alternatingRankSum r b i = 0 := by
  rw [alternatingRankSum, Int.toNat_of_nonpos (by omega), Finset.range_zero, Finset.sum_empty]

/-- The alternating sum does not depend on the bound: raising a bound above which the ranks
vanish only adds zero terms. So `alternatingRankSum r b i` is the alternating sum of the whole
tail `r_{i+1}, r_{i+2}, …` whenever `r` vanishes above `b`. -/
theorem alternatingRankSum_eq_of_vanishing {r : ℤ → ℕ} {b b' : ℤ}
    (hb : ∀ i : ℤ, b < i → r i = 0) (hbb : b ≤ b') (i : ℤ) :
    alternatingRankSum r b' i = alternatingRankSum r b i := by
  have hle : (b - i).toNat ≤ (b' - i).toNat := by omega
  have hsub : Finset.range (b - i).toNat ⊆ Finset.range (b' - i).toNat := fun j hj =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hle)
  refine (Finset.sum_subset hsub ?_).symm
  intro j _ hj
  simp only [Finset.mem_range, not_lt] at hj
  rw [hb (i + 1 + j) (by omega)]
  simp

namespace FreeData

variable {R : Type u} [CommRing R] (C : FreeData R)

/-- The alternating sum of the ranks above `p` of a bounded-above complex of finite free modules
is the alternating rank sum of its rank function, at its own bound. -/
theorem tailAlternatingRank_eq_alternatingRankSum (p : ℤ) :
    C.tailAlternatingRank p = alternatingRankSum C.rank C.top p := rfl

/-- **At the alternating rank sum of its own ranks the prescribed size of the minors is zero.**
This is the identity that pins the index: the size of the minors cutting out the `(p, k)`-th
Fitting ideal is `tailAlternatingRank p - k`, which vanishes exactly at
`k = alternatingRankSum rank top p`. -/
theorem minorSize_alternatingRankSum_self (p : ℤ) :
    C.minorSize p (alternatingRankSum C.rank C.top p) = 0 :=
  sub_self _

/-- A complex of finite free modules whose ranks are `r` and which vanishes above `b` has
prescribed minor size `0` in every degree at the index `alternatingRankSum r b`. -/
theorem minorSize_alternatingRankSum_of_rank_eq {r : ℤ → ℕ} {b : ℤ} (hr : C.rank = r)
    (hb : C.top = b) (p : ℤ) : C.minorSize p (alternatingRankSum r b p) = 0 := by
  subst hr
  subst hb
  exact C.minorSize_alternatingRankSum_self p

/-- The Fitting ideal of a complex of finite free modules whose ranks are `r` and which vanishes
above `b` is the unit ideal at the index `alternatingRankSum r b`: the prescribed size of the
minors is `0`, and the empty minor is `1`. -/
theorem fittingIdeal_alternatingRankSum_of_rank_eq {r : ℤ → ℕ} {b : ℤ} (hr : C.rank = r)
    (hb : C.top = b) (p : ℤ) : C.fittingIdeal p (alternatingRankSum r b p) = ⊤ :=
  C.fittingIdeal_eq_top_of_minorSize_nonpos
    (le_of_eq (C.minorSize_alternatingRankSum_of_rank_eq hr hb p))

/-- **The degenerate case cannot arise at the alternating rank sum.** For a complex of finite
free modules whose ranks are `r` and which vanishes above `b`, the prescribed size of the minors
at the index `alternatingRankSum r b` does not exceed the number of rows or of columns of the
matrix of `d_p`: it is `0`, and the ranks are nonnegative. This is the hypothesis of
`Stacks.FittingComplex.FreeData.fittingIdeal_eq_bot_of_card_lt_minorSize`, so that route to the
zero ideal is closed. -/
theorem not_card_lt_minorSize_alternatingRankSum {r : ℤ → ℕ} {b : ℤ} (hr : C.rank = r)
    (hb : C.top = b) (p : ℤ) :
    ¬((C.rank p : ℤ) < C.minorSize p (alternatingRankSum r b p) ∨
      (C.rank (p + 1) : ℤ) < C.minorSize p (alternatingRankSum r b p)) := by
  rw [C.minorSize_alternatingRankSum_of_rank_eq hr hb p]
  rintro (h | h) <;> omega

end FreeData

end Stacks.FittingComplex

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.FittingComplex
open scoped AlgebraicGeometry

noncomputable section

universe u w

variable {X : Scheme.{u}}

/-- The ideal of minors prescribed at the index `alternatingRankSum r b` is the unit ideal for a
bounded-above finite free model whose ranks are `r` and which vanishes above `b`: the prescribed
size of the minors is `0`. -/
theorem FreeModel.minorIdeal_matrix_eq_top_of_rank_eq {K : CochainComplex X.Modules ℤ}
    {V : X.Opens} (M : FreeModel K V) {r : ℤ → ℕ} {b : ℤ} (hr : M.rank = r) (hb : M.top = b)
    (p : ℤ) :
    minorIdeal (M.matrix p) (M.toFreeData.minorSize p (alternatingRankSum r b p)).toNat = ⊤ := by
  rw [M.toFreeData.minorSize_alternatingRankSum_of_rank_eq hr hb p, Int.toNat_zero,
    minorIdeal_zero]

/-- **The counterexample to a free index does not apply at the alternating rank sum.** For a
bounded-above finite free model whose ranks are `r` and which vanishes above `b`, the hypothesis
of `AlgebraicGeometry.not_disjoint_support_fittingIdealSheaf_of_card_lt_minorSize` — that the
prescribed size of the minors exceeds the size of the matrix of `d_p` — is false at the index
`alternatingRankSum r b`. -/
theorem FreeModel.not_card_lt_minorSize_alternatingRankSum {K : CochainComplex X.Modules ℤ}
    {V : X.Opens} (M : FreeModel K V) {r : ℤ → ℕ} {b : ℤ} (hr : M.rank = r) (hb : M.top = b)
    (p : ℤ) :
    ¬((M.rank p : ℤ) < M.toFreeData.minorSize p (alternatingRankSum r b p) ∨
      (M.rank (p + 1) : ℤ) < M.toFreeData.minorSize p (alternatingRankSum r b p)) :=
  M.toFreeData.not_card_lt_minorSize_alternatingRankSum hr hb p

variable [HasDerivedCategory.{w} X.Modules]

/-- **The local description of [Stacks, Tag 0ESP] in the form the blowup of [Stacks, Tag 0ESQ]
consumes.** For a rank function `r`, a bound `b` and an open `U`: a quasi-coherent sheaf of ideals
`J p` in each degree `p` which on every affine open is contained in the ideal of minors of the
matrix of `d_p` of every bounded-above finite free model there of every complex representing `E`,
and which on affine opens covering `U` contains the ideals of minors of a model whose ranks are
`r` and which vanishes above `b`, in every degree.

The first half is the hypothesis of `AlgebraicGeometry.le_fittingIdealSheaf_of_le_minorIdeal`,
without which no lower bound on the Fitting ideal sheaf is available at all; the second half is
the local situation on `U` that the source reads off from the cohomology of `E` being finite
locally free of rank `r_i` there, the complex splitting locally into its cohomology. Together they
force the Fitting ideal sheaf to be the unit ideal on those affine opens, because the prescribed
size of the minors of such a model at the index `alternatingRankSum r b` is `0`. -/
def HasLocalFittingDescription (E : DerivedCategory X.Modules) (r : ℤ → ℕ) (b : ℤ)
    (U : X.Opens) : Prop :=
  ∃ J : ℤ → X.IdealSheafData,
    (∀ (p : ℤ) (V : X.affineOpens) (K : CochainComplex X.Modules ℤ),
        Nonempty (DerivedCategory.Q.obj K ≅ E) → ∀ M : FreeModel K V.1,
          (J p).ideal V ≤ minorIdeal (M.matrix p)
            (M.toFreeData.minorSize p (alternatingRankSum r b p)).toNat) ∧
      ∀ x ∈ U, ∃ (V : X.affineOpens) (K : CochainComplex X.Modules ℤ) (M : FreeModel K V.1),
        x ∈ V.1 ∧ Nonempty (DerivedCategory.Q.obj K ≅ E) ∧ M.rank = r ∧ M.top = b ∧
          ∀ p : ℤ, minorIdeal (M.matrix p)
            (M.toFreeData.minorSize p (alternatingRankSum r b p)).toNat ≤ (J p).ideal V

/-- **The local description over `U` costs exactly the inclusion that is missing.** Taking the
Fitting ideal sheaves themselves as the witness, `AlgebraicGeometry.HasLocalFittingDescription`
follows from the reverse inclusion of [Stacks, Tag 0ESP] on affine opens covering `U` carrying a
bounded-above finite free model whose ranks are `r` and which vanishes above `b`. The upper bound
is `AlgebraicGeometry.ideal_fittingIdealSheaf_le`, which holds for every model on every affine
open; so the hypothesis asks for nothing beyond the half of the local description that the
construction of the ideal sheaf does not give, and asks for it over `U` only. -/
theorem hasLocalFittingDescription_of_minorIdeal_le
    (E : DerivedCategory X.Modules) {r : ℤ → ℕ} {b : ℤ} {U : X.Opens}
    (h : ∀ x ∈ U, ∃ (V : X.affineOpens) (K : CochainComplex X.Modules ℤ) (M : FreeModel K V.1),
      x ∈ V.1 ∧ Nonempty (DerivedCategory.Q.obj K ≅ E) ∧ M.rank = r ∧ M.top = b ∧
        ∀ p : ℤ, minorIdeal (M.matrix p)
            (M.toFreeData.minorSize p (alternatingRankSum r b p)).toNat ≤
          (fittingIdealSheaf E p (alternatingRankSum r b p)).ideal V) :
    HasLocalFittingDescription E r b U :=
  ⟨fun p => fittingIdealSheaf E p (alternatingRankSum r b p),
    fun p V K hK M => ideal_fittingIdealSheaf_le E p _ V K hK M, h⟩

/-- **The Fitting ideal sheaves at the alternating rank sum are supported away from `U`**, granted
the local description of [Stacks, Tag 0ESP] over `U`. This is the analogue for a complex of
[Stacks, Tag 0C3G], at the index [Stacks, Tag 0ESQ] uses.

On an affine open of the covering the prescribed size of the minors of the given model is `0`, so
the ideal of its minors is the unit ideal; the witness `J p` contains it, hence is the unit ideal
there, and `AlgebraicGeometry.disjoint_support_fittingIdealSheaf` concludes. -/
theorem disjoint_support_fittingIdealSheaf_alternatingRankSum
    (E : DerivedCategory X.Modules) {r : ℤ → ℕ} {b : ℤ} {U : X.Opens}
    (h : HasLocalFittingDescription E r b U) (p : ℤ) :
    Disjoint (U : Set X) ((fittingIdealSheaf E p (alternatingRankSum r b p)).support : Set X) := by
  obtain ⟨J, hJle, hmodel⟩ := h
  refine disjoint_support_fittingIdealSheaf E p _ (J p)
    (fun V K hK M => hJle p V K hK M) U fun x hx => ?_
  obtain ⟨V, K, M, hxV, hK, hr, hb, hge⟩ := hmodel x hx
  exact ⟨V, hxV,
    top_le_iff.mp ((M.minorIdeal_matrix_eq_top_of_rank_eq hr hb p).ge.trans (hge p))⟩

end

end AlgebraicGeometry

end
