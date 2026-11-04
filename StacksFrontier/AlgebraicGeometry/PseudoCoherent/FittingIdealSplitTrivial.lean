module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealAlternatingRank

/-!
# Splitting off a trivial two-term complex does not change the Fitting ideals

Let `R` be a commutative ring and let `F` be a bounded-above complex of finite free
`R`-modules, recorded as `Stacks.FittingComplex.FreeData` by its ranks `n_j` and the matrices of
its differentials. Let `T` be the trivial complex `… → 0 → R^{⊕m} → R^{⊕m} → 0 → …`, the
identity in degrees `i` and `i + 1`. This file proves that `F` and `F ⊕ T` have the *same*
Fitting ideals in every degree and at every index:

`Stacks.FittingComplex.FreeData.fittingIdeal_directSum_trivialComplex`.

This is the step that the proof of [Stacks, Tag 0ESP] leaves to the reader, and the source
flags it as the one place where the formula for the size of the minors is used. Writing
`T_p = n_{p+1} - n_{p+2} + ⋯ + (-1)^{b-p+1} n_b` for the alternating sum of the ranks above `p`,
so that the prescribed size of the minors of `d_p` is `-k + T_p`, the three degrees that the
splitting touches balance as follows.

* In degree `p = i` the matrix of `d_i` acquires an identity block of size `m`, and `T_i` grows
  by exactly `m` because `n_{i+1}` grows by `m` and no other rank above `i` moves. The minors
  grow in size by the same `m` as the block, so the ideal is unchanged:
  `minorIdeal_fromBlocks_identity`.
* In degree `p = i - 1` the matrix of `d_{i-1}` acquires `m` new rows and no new column, and
  `T_{i-1}` does not move at all, because `n_i` and `n_{i+1}` both grow by `m` and enter the
  alternating sum with opposite signs.
* In degree `p = i + 1` the matrix of `d_{i+1}` acquires `m` new columns and no new row, and
  `T_{i+1}` does not move because no rank above `i + 1` does.

In every other degree neither the matrix nor the alternating sum moves. An off-by-one in the
size formula destroys the first of these three balances, which is what makes this computation
the machine check that `Stacks.FittingComplex.FreeData.minorSize` is the size the source
prescribes.

## Main definitions

* `Stacks.FittingComplex.FreeData.directSum`: the direct sum of two bounded-above complexes of
  finite free modules, with block-diagonal differentials.
* `Stacks.FittingComplex.FreeData.trivialRank` and
  `Stacks.FittingComplex.FreeData.trivialComplex`: the trivial complex which is the identity of
  `R^{⊕m}` in degrees `i` and `i + 1`.

## Main results

* `minorIdeal_reindex`: the ideal of minors is unchanged by reindexing the rows and the columns
  along bijections.
* `minorIdeal_fromBlocks_identity`: adjoining an identity block of size `m` and raising the size
  of the minors by `m` leaves the ideal unchanged, for a block that is the identity matrix only
  up to the propositional equalities identifying its index types with `Fin m`.
* `minorIdeal_fromBlocks_identity_eq_top`: at a size at most `m` such a block already generates
  the unit ideal.
* `Stacks.FittingComplex.FreeData.tailAlternatingRank_directSum` and
  `Stacks.FittingComplex.FreeData.minorSize_directSum`: the alternating sum of the ranks above a
  degree is additive in the direct sum, hence so is the correction to the size of the minors.
* `Stacks.FittingComplex.FreeData.tailAlternatingRank_trivialComplex`: the alternating sum of
  the ranks of the trivial complex above `p` is `m` for `p = i` and `0` otherwise.
* `Stacks.FittingComplex.FreeData.fittingIdeal_directSum_trivialComplex`: the Fitting ideals of
  `F ⊕ T` and of `F` agree in every degree and at every index.

## Implementation notes

The direct sum is block-diagonal after reindexing `Fin a ⊕ Fin b` to `Fin (a + b)` along
`finSumFinEquiv`, which is how `StacksFrontier.LinearAlgebra.Matrix.DeterminantalRank` records the
direct sum of its own complexes; `minorIdeal_reindex` is what makes that reindexing invisible to
the ideals. The differential of the trivial complex is written out in coordinates, as
`fun x y => if (x : ℕ) = (y : ℕ) then 1 else 0`, rather than as the identity matrix transported
along `trivialRank i m i = m`: in coordinates the definition typechecks against the index types
`Fin (trivialRank i m (p + 1))` and `Fin (trivialRank i m p)` as they stand, in every degree `p`
at once, so no cast appears in the definition or in any statement about it.

The two conventions of the source interact in degree `i`. When the size `-k + T_i` prescribed
for `F` is nonpositive its Fitting ideal is the unit ideal, while the size prescribed for
`F ⊕ T` is `-k + T_i + m`, which can be positive; the ideals still agree, because a size at most
`m` is met by the minor cut out of the identity block alone, whose determinant is `1`. That is
`minorIdeal_fromBlocks_identity_eq_top`, and it is the reason the proof of the main result splits
on the sign of `Stacks.FittingComplex.FreeData.minorSize`.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
* [Stacks Project, Tag 07Z7](https://stacks.math.columbia.edu/tag/07Z7)
* [Stacks Project, Tag 00MT](https://stacks.math.columbia.edu/tag/00MT)
-/

@[expose] public section

open Matrix

section MinorIdeal

variable {R : Type*} [CommRing R] {l o : Type*}

/-- The ideal generated by the `r × r` minors is unchanged by reindexing the rows and the columns
along bijections: the minors of the two matrices are the same elements of `R`. -/
theorem minorIdeal_reindex {l' o' : Type*} (A : Matrix l o R) (e : l ≃ l') (f : o ≃ o')
    (r : ℕ) : minorIdeal (Matrix.reindex e f A) r = minorIdeal A r := by
  simp only [Matrix.reindex_apply]
  refine le_antisymm (minorIdeal_submatrix_le A e.symm f.symm r) ?_
  have h := minorIdeal_submatrix_le (A.submatrix e.symm f.symm) e f r
  rwa [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Equiv.symm_comp_self,
    Matrix.submatrix_id_id] at h

/-- Adjoining a block which is the identity matrix of size `m` raises the size of the minors by
`m` without changing the ideal they generate.

This is `minorIdeal_fromBlocks_one` for a block whose index types are identified with `Fin m`
only by the propositional equalities `ha` and `hb`, and whose entries are given in coordinates.
That is the shape in which the trivial complex of
`Stacks.FittingComplex.FreeData.trivialComplex` presents its differential. -/
theorem minorIdeal_fromBlocks_identity {a b m : ℕ} (A : Matrix l o R)
    (B : Matrix (Fin a) (Fin b) R) (ha : a = m) (hb : b = m)
    (hB : ∀ (x : Fin a) (y : Fin b), B x y = if (x : ℕ) = (y : ℕ) then 1 else 0) (r : ℕ) :
    minorIdeal (Matrix.fromBlocks A 0 0 B) (r + m) = minorIdeal A r := by
  subst ha
  subst hb
  have hB1 : B = 1 := by
    ext x y
    rw [hB, Matrix.one_apply]
    simp [Fin.ext_iff]
  rw [hB1]
  exact minorIdeal_fromBlocks_one A _ r

/-- A block which is the identity matrix of size `m` already generates the unit ideal at every
size at most `m`: the minor cut out of that block alone has determinant `1`.

This is the inclusion that reconciles the two conventions of [Stacks, Tag 0ESP] in the degree
where the splitting changes the size of the minors. -/
theorem minorIdeal_fromBlocks_identity_eq_top {a b m : ℕ} (A : Matrix l o R)
    (B : Matrix (Fin a) (Fin b) R) (ha : a = m) (hb : b = m)
    (hB : ∀ (x : Fin a) (y : Fin b), B x y = if (x : ℕ) = (y : ℕ) then 1 else 0)
    {t : ℕ} (ht : t ≤ m) :
    minorIdeal (Matrix.fromBlocks A 0 0 B) t = ⊤ := by
  have hm := minorIdeal_fromBlocks_identity A B ha hb hB 0
  rw [zero_add, minorIdeal_zero] at hm
  refine top_le_iff.mp ?_
  rw [← hm]
  exact antitone_nat_of_succ_le (minorIdeal_succ_le (Matrix.fromBlocks A 0 0 B)) ht

end MinorIdeal

namespace Stacks.FittingComplex

namespace FreeData

universe u

variable {R : Type u} [CommRing R]

/-- The direct sum of two bounded-above complexes of finite free modules: the ranks add, a degree
above which both vanish bounds the sum, and the matrix of the differential is block diagonal,
reindexed from `Fin a ⊕ Fin b` to `Fin (a + b)`. -/
def directSum (C D : FreeData R) : FreeData R where
  rank i := C.rank i + D.rank i
  top := max C.top D.top
  rank_eq_zero_of_top_lt i hi := by
    rw [C.rank_eq_zero_of_top_lt i (lt_of_le_of_lt (le_max_left _ _) hi),
      D.rank_eq_zero_of_top_lt i (lt_of_le_of_lt (le_max_right _ _) hi)]
  d i := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (C.d i) 0 0 (D.d i))

/-- The rank of a direct sum in each degree is the sum of the ranks. -/
@[simp]
theorem directSum_rank (C D : FreeData R) (i : ℤ) :
    (C.directSum D).rank i = C.rank i + D.rank i := rfl

/-- The bound of a direct sum is the larger of the two bounds. -/
@[simp]
theorem directSum_top (C D : FreeData R) : (C.directSum D).top = max C.top D.top := rfl

/-- The matrix of the differential of a direct sum is the block diagonal matrix of the two
differentials, reindexed from `Fin a ⊕ Fin b` to `Fin (a + b)`. -/
theorem directSum_d (C D : FreeData R) (i : ℤ) :
    (C.directSum D).d i =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (C.d i) 0 0 (D.d i)) := rfl

/-- The ideal of minors of the differential of a direct sum is the ideal of minors of the block
diagonal matrix: the reindexing from `Fin a ⊕ Fin b` to `Fin (a + b)` is invisible to it. -/
theorem minorIdeal_directSum_d (C D : FreeData R) (i : ℤ) (r : ℕ) :
    minorIdeal ((C.directSum D).d i) r =
      minorIdeal (Matrix.fromBlocks (C.d i) 0 0 (D.d i)) r := by
  rw [directSum_d]
  exact minorIdeal_reindex _ _ _ _

/-- The alternating sum of the ranks above a degree is additive in the direct sum. Both summands
have to be read at the bound of the direct sum, which is where
`Stacks.FittingComplex.alternatingRankSum_eq_of_vanishing` enters: raising the bound above a
degree where the ranks already vanish only adds zero terms. -/
theorem tailAlternatingRank_directSum (C D : FreeData R) (p : ℤ) :
    (C.directSum D).tailAlternatingRank p =
      C.tailAlternatingRank p + D.tailAlternatingRank p := by
  rw [tailAlternatingRank_eq_alternatingRankSum, tailAlternatingRank_eq_alternatingRankSum,
    tailAlternatingRank_eq_alternatingRankSum,
    ← alternatingRankSum_eq_of_vanishing C.rank_eq_zero_of_top_lt (le_max_left C.top D.top) p,
    ← alternatingRankSum_eq_of_vanishing D.rank_eq_zero_of_top_lt (le_max_right C.top D.top) p]
  simp only [alternatingRankSum, directSum_rank, directSum_top]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- The size of the minors prescribed for a direct sum exceeds the one prescribed for the first
summand by the alternating sum of the ranks of the second summand above that degree. -/
theorem minorSize_directSum (C D : FreeData R) (p k : ℤ) :
    (C.directSum D).minorSize p k = C.minorSize p k + D.tailAlternatingRank p := by
  rw [minorSize, minorSize, tailAlternatingRank_directSum]
  ring

/-- The rank function of the trivial two-term complex `… → 0 → R^{⊕m} → R^{⊕m} → 0 → …` with its
nonzero terms in degrees `i` and `i + 1`. -/
def trivialRank (i : ℤ) (m : ℕ) : ℤ → ℕ := fun j => if j = i ∨ j = i + 1 then m else 0

/-- The rank of the trivial complex in degree `i` is `m`. -/
@[simp]
theorem trivialRank_self (i : ℤ) (m : ℕ) : trivialRank i m i = m := by simp [trivialRank]

/-- The rank of the trivial complex in degree `i + 1` is `m`. -/
@[simp]
theorem trivialRank_succ (i : ℤ) (m : ℕ) : trivialRank i m (i + 1) = m := by
  simp [trivialRank]

/-- The rank of the trivial complex vanishes in every degree other than `i` and `i + 1`. -/
theorem trivialRank_eq_zero {i j : ℤ} (m : ℕ) (h₁ : j ≠ i) (h₂ : j ≠ i + 1) :
    trivialRank i m j = 0 := by simp [trivialRank, h₁, h₂]

/-- The trivial two-term complex `… → 0 → R^{⊕m} → R^{⊕m} → 0 → …`, the identity in degrees `i`
and `i + 1`. This is the complex that [Stacks, Tag 00MT] splits off a complex of finite free
modules one of whose differentials has an invertible matrix coefficient. -/
def trivialComplex (R : Type u) [CommRing R] (i : ℤ) (m : ℕ) : FreeData R where
  rank := trivialRank i m
  top := i + 1
  rank_eq_zero_of_top_lt j hj := trivialRank_eq_zero m (by omega) (by omega)
  d j := if j = i then Matrix.of fun x y => if (x : ℕ) = (y : ℕ) then 1 else 0 else 0

/-- The ranks of `trivialComplex R i m` are given by `trivialRank i m`. -/
@[simp]
theorem trivialComplex_rank (i : ℤ) (m : ℕ) :
    (trivialComplex R i m).rank = trivialRank i m := rfl

/-- The bound of `trivialComplex R i m` is `i + 1`. -/
@[simp]
theorem trivialComplex_top (i : ℤ) (m : ℕ) : (trivialComplex R i m).top = i + 1 := rfl

/-- In degree `i` the differential of the trivial complex is the identity matrix, in
coordinates. -/
theorem trivialComplex_d_self_apply (i : ℤ) (m : ℕ)
    (x : Fin ((trivialComplex R i m).rank (i + 1)))
    (y : Fin ((trivialComplex R i m).rank i)) :
    (trivialComplex R i m).d i x y = if (x : ℕ) = (y : ℕ) then (1 : R) else 0 := by
  simp only [trivialComplex]
  rfl

/-- **The alternating sum of the ranks of the trivial complex.** Above `p = i` it is `m`, the only
rank in that range being `n_{i+1} = m`; above every other degree it is `0`, either because the
range is empty or because `n_i = m` and `n_{i+1} = m` enter the alternating sum with opposite
signs and cancel.

This is the numerical half of the main result: it says that the size of the minors prescribed for
`F ⊕ T` exceeds the one prescribed for `F` by `m` in degree `i`, and not at all elsewhere. -/
theorem tailAlternatingRank_trivialComplex (R : Type u) [CommRing R] (i : ℤ) (m : ℕ) (p : ℤ) :
    (trivialComplex R i m).tailAlternatingRank p = if p = i then (m : ℤ) else 0 := by
  rcases lt_trichotomy p i with hp | hp | hp
  · rw [if_neg (by omega : ¬p = i)]
    have ha : ((i - p - 1).toNat : ℤ) = i - p - 1 := by omega
    have hN : ((trivialComplex R i m).top - p).toNat = (i - p - 1).toNat + 1 + 1 := by
      simp only [trivialComplex_top]
      omega
    rw [tailAlternatingRank, hN, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_eq_zero fun j hj => ?_]
    · rw [trivialComplex_rank]
      rw [show p + 1 + ((i - p - 1).toNat : ℤ) = i by omega,
        show p + 1 + (((i - p - 1).toNat : ℕ) + 1 : ℕ) = i + 1 by push_cast; omega]
      rw [trivialRank_self, trivialRank_succ, pow_succ]
      ring
    · have hj' : (j : ℤ) < (i - p - 1).toNat := by
        exact_mod_cast Finset.mem_range.mp hj
      rw [trivialComplex_rank, trivialRank_eq_zero m (by omega) (by omega)]
      simp
  · subst hp
    rw [if_pos rfl, tailAlternatingRank]
    have hN : ((trivialComplex R p m).top - p).toNat = 1 := by
      simp only [trivialComplex_top]
      omega
    rw [hN, Finset.sum_range_one, trivialComplex_rank]
    norm_num
  · rw [if_neg (by omega : ¬p = i)]
    exact (trivialComplex R i m).tailAlternatingRank_of_top_le
      (by simp only [trivialComplex_top]; omega)

/-- **Splitting off a trivial two-term complex does not change the Fitting ideals.** For a
bounded-above complex `F` of finite free `R`-modules and the trivial complex `T` which is the
identity of `R^{⊕m}` in degrees `i` and `i + 1`, the `(p, k)`-th Fitting ideals of `F ⊕ T` and of
`F` agree, for every `p` and every `k`.

This is the step the proof of [Stacks, Tag 0ESP] leaves to the reader, and the one the source
says the formula for the size of the minors is used for. In degree `p = i` the matrix of `d_i`
gains an identity block of size `m` while the prescribed size of the minors gains the same `m`,
and the two changes cancel by `minorIdeal_fromBlocks_identity` — or, when the size prescribed for
`F` is nonpositive, both ideals are the unit ideal by
`minorIdeal_fromBlocks_identity_eq_top`. In every other degree the prescribed size does not move
by `Stacks.FittingComplex.FreeData.tailAlternatingRank_trivialComplex`, and the new block has no
row or no column, so it contributes nothing by `minorIdeal_fromBlocks_of_isEmpty`. -/
theorem fittingIdeal_directSum_trivialComplex (C : FreeData R) (i : ℤ) (m : ℕ) (p k : ℤ) :
    (C.directSum (trivialComplex R i m)).fittingIdeal p k = C.fittingIdeal p k := by
  simp only [fittingIdeal, minorIdeal_directSum_d, minorSize_directSum,
    tailAlternatingRank_trivialComplex]
  by_cases hp : p = i
  · subst hp
    rw [if_pos rfl]
    rcases le_or_gt (C.minorSize p k) 0 with hs | hs
    · rw [Int.toNat_of_nonpos hs, minorIdeal_zero]
      refine minorIdeal_fromBlocks_identity_eq_top (C.d p) _
        (trivialRank_succ p m) (trivialRank_self p m)
        (trivialComplex_d_self_apply p m) ?_
      omega
    · rw [show (C.minorSize p k + (m : ℤ)).toNat = (C.minorSize p k).toNat + m by omega]
      exact minorIdeal_fromBlocks_identity (C.d p) _ (trivialRank_succ p m)
        (trivialRank_self p m) (trivialComplex_d_self_apply p m) _
  · rw [if_neg hp, add_zero]
    refine minorIdeal_fromBlocks_of_isEmpty (C.d p) _ _ ?_
    by_cases hp1 : p = i + 1
    · refine Or.inl ?_
      rw [show (trivialComplex R i m).rank (p + 1) = 0 from
        trivialRank_eq_zero m (by omega) (by omega)]
      infer_instance
    · refine Or.inr ?_
      rw [show (trivialComplex R i m).rank p = 0 from
        trivialRank_eq_zero m (by omega) (by omega)]
      infer_instance

end FreeData

end Stacks.FittingComplex

end
