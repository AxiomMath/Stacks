module

public import StacksFrontier.Algebra.Homology.FiniteFreeComplex
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealSplitTrivial

/-!
# The bridge between the numerical data of a Fitting complex and a complex of finite free modules

Two records of "a complex of finite free modules written in chosen bases" live in this
development, and they are *not* the same type.

* `Stacks.FittingComplex.FreeData R` is a **cochain** complex: its differential in degree `i` is
  a matrix `d i : Matrix (Fin (rank (i + 1))) (Fin (rank i)) R`, the matrix of a map
  `R^{rank i} → R^{rank (i + 1)}`, it records a degree `top` above which the ranks vanish, and
  it deliberately *does not record* that consecutive differentials compose to zero, because the
  ideals of minors that `Stacks.FittingComplex.FreeData.fittingIdeal` extracts from it do not
  depend on that condition.
* `FreeComplex R` is a **chain** complex: its differential in degree `i` is a matrix
  `d i : Matrix (Fin (n i)) (Fin (n (i + 1))) R`, the matrix of a map `R^{n (i+1)} → R^{n i}`,
  it is unbounded, and the complex condition `d i * d (i + 1) = 0` is one of its fields.

So the mismatch between them is threefold: the direction of the differentials, the boundedness,
and the complex condition. Passing from one to the other is a degree flip `i ↦ -i` together with
the complex condition supplied as *new data*, which is what this file provides. It is the only
thing standing between the numerical results about `FreeData` and the two theorems about
`FreeComplex` that the proof of [Stacks, Tag 0ESP] needs:
`exists_splitOff_elementaryComplex_of_hasInvertibleCoeff` and the matrix-level
`freeComplex_split_data` behind it ([Stacks, Tag 00MT]).

## Main definitions

* `Stacks.FittingComplex.FreeData.toFreeComplex`: the chain complex of finite free modules that a
  bounded-above cochain `FreeData` presents, once the complex condition is supplied; the rank in
  chain degree `j` is the rank in cochain degree `-j`.
* `FreeComplex.toFreeData`: the reverse flip, which needs a degree above which the ranks vanish.

## Main results

* `Stacks.FittingComplex.FreeData.minorIdeal_toFreeComplex_d` and
  `FreeComplex.minorIdeal_toFreeData_d`: the flip changes neither the entries of the
  differentials nor therefore the ideals of their minors, only the degree they sit in.
* `Stacks.FittingComplex.FreeData.hasInvertibleCoeff_toFreeComplex`: a unit entry of the matrix
  of `d_i` is a unit matrix coefficient of the flipped complex in the degree `-i`, which is the
  hypothesis of [Stacks, Tag 00MT].
* `FreeComplex.minorIdeal_d_eq_of_conj`: two free complexes whose differentials are conjugate by
  invertible matrices, degree by degree — the conclusion that
  `freeComplex_split_data` and `freeComplex_changeOfBasis` both speak in — have the same ideals
  of minors in every degree. This is what feeds
  `Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_units_mul_mul` from a change of basis of
  complexes rather than of a single matrix.
* `Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_minorIdeal_d_eq`: two bounded-above Fitting
  complexes with the same ranks, the same bound and the same ideals of minors in every degree
  have the same Fitting ideals, the prescribed size of the minors being computed from the ranks
  and the bound alone.
* `Stacks.FittingComplex.FreeData.exists_freeData_fittingIdeal_eq_of_isUnit`: [Stacks, Tag 00MT]
  read back on a `FreeData`, with its effect on the Fitting ideals. If the matrix of `d_i` has a
  unit entry then the ranks in degrees `i` and `i + 1` are at least one and there is a
  bounded-above `FreeData` with those two ranks decremented, the others unchanged, which again
  satisfies the complex condition and has the *same* Fitting ideals in every degree and at every
  index. This is the induction step of the proof of [Stacks, Tag 0ESP], and it is the first
  statement in the development that combines the splitting of [Stacks, Tag 00MT] with the
  numerical step `Stacks.FittingComplex.FreeData.fittingIdeal_directSum_trivialComplex`.

## Implementation notes

The degree flip cannot be made cast-free. A field of `FreeComplex` in degree `j` has rows indexed
by `Fin (n j)` and columns by `Fin (n (j + 1))`, so a flip `n j = rank (-j)` has to produce a
matrix with rows `Fin (rank (-j))` out of `C.d (-(j+1))`, whose rows are
`Fin (rank (-(j + 1) + 1))`; the two integers `-(j + 1) + 1` and `-j` are equal but not
definitionally so, for a variable `j`. One `Fin.cast` therefore appears on the rows of the
flipped differential (and, symmetrically, on the columns of the unflipped one). It is invisible
to the ideals of minors, by `minorIdeal_reindex`, and it is confined to the two private lemmas
`Stacks.FittingComplex.FreeData.d_mul_submatrix_d` and `FreeComplex.submatrix_d_mul_d`, which
transport the complex condition across that equality of degrees by substituting it away.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
* [Stacks Project, Tag 00MT](https://stacks.math.columbia.edu/tag/00MT)
-/

@[expose] public section

open Stacks.FittingComplex

section MinorIdeal

/-- Two matrices whose index types are identified by equalities of their sizes, and whose entries
match under that identification, generate the same ideal of minors. This is
`minorIdeal_reindex` for a reindexing which is a `Fin.cast`. -/
theorem minorIdeal_eq_of_apply {R : Type*} [CommRing R] {a b a' b' : ℕ}
    (A : Matrix (Fin a) (Fin b) R) (A' : Matrix (Fin a') (Fin b') R) (ha : a = a') (hb : b = b')
    (h : ∀ x y, A x y = A' (Fin.cast ha x) (Fin.cast hb y)) (r : ℕ) :
    minorIdeal A r = minorIdeal A' r := by
  have hA : A = Matrix.reindex (finCongr ha).symm (finCongr hb).symm A' := by
    ext x y
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    exact h x y
  rw [hA, minorIdeal_reindex]

end MinorIdeal

namespace FreeComplex

variable {R : Type*} [CommRing R]

/-- The rank of a free complex in the chain degree `-(i + 1) + 1`, which is the degree `-i`
written the way the degree flip produces it. -/
theorem n_neg_add_one (D : FreeComplex R) (i : ℤ) : D.n (-(i + 1) + 1) = D.n (-i) :=
  congrArg D.n (by ring)

/-- The complex condition of a free complex, transported across an equality of degrees by
substituting it away. The `Fin.cast` is what the degree flip of
`FreeComplex.toFreeData` leaves on the columns of its differentials. -/
private theorem submatrix_d_mul_d (D : FreeComplex R) {a b : ℤ} (hb : b = a + 1)
    (h : D.n b = D.n (a + 1)) :
    (D.d a).submatrix id (Fin.cast h) * D.d b = 0 := by
  subst hb
  have hid : Fin.cast h = (id : Fin (D.n (a + 1)) → Fin (D.n (a + 1))) := rfl
  rw [hid, Matrix.submatrix_id_id]
  exact D.dd a

/-- The bounded-above cochain complex of finite free modules that a free complex presents, given
a degree above which its ranks vanish: the rank in cochain degree `i` is the rank in chain
degree `-i`, and the differentials are those of the free complex, reindexed along the flip. -/
noncomputable def toFreeData (D : FreeComplex R) (top : ℤ)
    (hvan : ∀ i : ℤ, top < i → D.n (-i) = 0) : FreeData R where
  rank i := D.n (-i)
  top := top
  rank_eq_zero_of_top_lt := hvan
  d i := (D.d (-(i + 1))).submatrix id (Fin.cast (D.n_neg_add_one i).symm)

/-- The rank of `FreeComplex.toFreeData` in cochain degree `i` is the rank of the free complex in
chain degree `-i`. -/
@[simp]
theorem toFreeData_rank (D : FreeComplex R) (top : ℤ)
    (hvan : ∀ i : ℤ, top < i → D.n (-i) = 0) (i : ℤ) :
    (D.toFreeData top hvan).rank i = D.n (-i) := rfl

/-- The vanishing bound of `FreeComplex.toFreeData` is the given degree `top`. -/
@[simp]
theorem toFreeData_top (D : FreeComplex R) (top : ℤ)
    (hvan : ∀ i : ℤ, top < i → D.n (-i) = 0) : (D.toFreeData top hvan).top = top := rfl

/-- The differential of `FreeComplex.toFreeData` in cochain degree `i` is the differential of the
free complex in chain degree `-(i + 1)`, with its columns reindexed along the degree flip. -/
theorem toFreeData_d (D : FreeComplex R) (top : ℤ)
    (hvan : ∀ i : ℤ, top < i → D.n (-i) = 0) (i : ℤ) :
    (D.toFreeData top hvan).d i
      = (D.d (-(i + 1))).submatrix id (Fin.cast (D.n_neg_add_one i).symm) := rfl

/-- The reverse degree flip does not change the entries of a differential, only the degree it
sits in, so it does not change the ideals of its minors. -/
theorem minorIdeal_toFreeData_d (D : FreeComplex R) (top : ℤ)
    (hvan : ∀ i : ℤ, top < i → D.n (-i) = 0) (i : ℤ) (r : ℕ) :
    minorIdeal ((D.toFreeData top hvan).d i) r = minorIdeal (D.d (-(i + 1))) r :=
  minorIdeal_reindex (D.d (-(i + 1))) (Equiv.refl (Fin (D.n (-(i + 1)))))
    (finCongr (D.n_neg_add_one i)) r

/-- The cochain complex obtained from a free complex by the reverse degree flip satisfies the
complex condition, which the free complex carries as a field. -/
theorem toFreeData_d_mul_d (D : FreeComplex R) (top : ℤ)
    (hvan : ∀ i : ℤ, top < i → D.n (-i) = 0) (i : ℤ) :
    (D.toFreeData top hvan).d (i + 1) * (D.toFreeData top hvan).d i = 0 := by
  have hkey : (D.d (-(i + 1 + 1))).submatrix id (Fin.cast (D.n_neg_add_one (i + 1)).symm)
      * D.d (-(i + 1)) = 0 :=
    D.submatrix_d_mul_d (show (-(i + 1) : ℤ) = -(i + 1 + 1) + 1 by ring) _
  rw [toFreeData_d, toFreeData_d]
  ext x y
  have hx := congrFun (congrFun hkey x) (Fin.cast (D.n_neg_add_one i).symm y)
  simp only [Matrix.zero_apply] at hx ⊢
  exact hx

/-- A unit entry of the matrix of a differential of a free complex, in a degree presented as
`t - 1` only up to an equality of integers, is a unit matrix coefficient in degree `t`: the
hypothesis of [Stacks, Tag 00MT]. -/
theorem hasInvertibleCoeff_of_isUnit_d (D : FreeComplex R) {t s : ℤ} (hts : t - 1 = s)
    (x : Fin (D.n s)) (y : Fin (D.n (s + 1))) (hu : IsUnit (D.d s x y)) :
    D.HasInvertibleCoeff t := by
  subst hts
  exact ⟨x, y, hu⟩

/-- **Two free complexes related by a degreewise invertible change of basis have the same ideals
of minors in every degree.**

This is the shape in which `freeComplex_split_data` and `freeComplex_changeOfBasis` record a
change of basis of complexes: per-degree square matrices `P t` with unit determinant, with
`P t * C.d t = D.d t * P (t + 1)` after the ranks of `D` are identified with those of `C`. On a
single matrix the statement is `minorIdeal_units_mul_mul_units_eq`; what the complex adds is that
the *same* family `P` serves in every degree, so no compatibility is left to check. -/
theorem minorIdeal_d_eq_of_conj (C D : FreeComplex R) (hn : ∀ t, D.n t = C.n t)
    (P : (t : ℤ) → Matrix (Fin (C.n t)) (Fin (C.n t)) R) (hP : ∀ t, IsUnit (P t).det)
    (hconj : ∀ t, P t * C.d t
      = (D.d t).submatrix (Fin.cast (hn t).symm) (Fin.cast (hn (t + 1)).symm) * P (t + 1))
    (t : ℤ) (r : ℕ) : minorIdeal (D.d t) r = minorIdeal (C.d t) r := by
  classical
  let u : (Matrix (Fin (C.n t)) (Fin (C.n t)) R)ˣ :=
    ((Matrix.isUnit_iff_isUnit_det (P t)).2 (hP t)).unit
  let v : (Matrix (Fin (C.n (t + 1))) (Fin (C.n (t + 1))) R)ˣ :=
    ((Matrix.isUnit_iff_isUnit_det (P (t + 1))).2 (hP (t + 1))).unit
  have hu : (u : Matrix (Fin (C.n t)) (Fin (C.n t)) R) = P t := rfl
  have hv : (v : Matrix (Fin (C.n (t + 1))) (Fin (C.n (t + 1))) R) = P (t + 1) := rfl
  have hreindex : (D.d t).submatrix (Fin.cast (hn t).symm) (Fin.cast (hn (t + 1)).symm)
      = Matrix.reindex (finCongr (hn t)) (finCongr (hn (t + 1))) (D.d t) := by
    rw [Matrix.reindex_apply, finCongr_symm, finCongr_symm]
    rfl
  have hE : (D.d t).submatrix (Fin.cast (hn t).symm) (Fin.cast (hn (t + 1)).symm)
      = (u : Matrix (Fin (C.n t)) (Fin (C.n t)) R) * C.d t
        * ((v⁻¹ : (Matrix (Fin (C.n (t + 1))) (Fin (C.n (t + 1))) R)ˣ) :
            Matrix (Fin (C.n (t + 1))) (Fin (C.n (t + 1))) R) := by
    rw [hu, hconj t, ← hv, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  calc minorIdeal (D.d t) r
      = minorIdeal ((D.d t).submatrix (Fin.cast (hn t).symm) (Fin.cast (hn (t + 1)).symm)) r := by
        rw [hreindex, minorIdeal_reindex]
    _ = minorIdeal (C.d t) r := by
        rw [hE]
        exact minorIdeal_units_mul_mul_units_eq _ _ _ _

/-- In the degree where it is nonzero, the differential of the elementary identity complex is the
`1 × 1` identity matrix, in coordinates. The degree is given as a hypothesis rather than as
`i - 1` so that the statement can be used at a degree equal to `i - 1` only up to an equality of
integers. -/
private theorem elementaryComplex_d_eq_one (R : Type*) [CommRing R] {i t : ℤ} (ht : t = i - 1)
    (x : Fin (elemRank i t)) (y : Fin (elemRank i (t + 1))) :
    (elementaryComplex R i).d t x y = 1 := by
  subst ht
  simp only [elementaryComplex]
  rfl

/-- Outside the one degree where it is nonzero, the differential of the elementary identity
complex vanishes. -/
private theorem elementaryComplex_d_eq_zero (R : Type*) [CommRing R] {i t : ℤ} (ht : t ≠ i - 1)
    (x : Fin (elemRank i t)) (y : Fin (elemRank i (t + 1))) :
    (elementaryComplex R i).d t x y = 0 := by
  simp only [elementaryComplex, if_neg ht]
  rfl

end FreeComplex

namespace Stacks.FittingComplex

namespace FreeData

variable {R : Type*} [CommRing R]

/-- The rank of a Fitting complex in the cochain degree `-(j + 1) + 1`, which is the degree `-j`
written the way the degree flip produces it. -/
theorem rank_neg_add_one (C : FreeData R) (j : ℤ) : C.rank (-(j + 1) + 1) = C.rank (-j) :=
  congrArg C.rank (by ring)

/-- The complex condition of a Fitting complex, transported across an equality of degrees by
substituting it away. The `Fin.cast` is what the degree flip of
`Stacks.FittingComplex.FreeData.toFreeComplex` leaves on the rows of its differentials. -/
private theorem d_mul_submatrix_d (C : FreeData R) (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0)
    {a b : ℤ} (ha : a = b + 1) (h : C.rank a = C.rank (b + 1)) :
    C.d a * (C.d b).submatrix (Fin.cast h) id = 0 := by
  subst ha
  have hid : Fin.cast h = (id : Fin (C.rank (b + 1)) → Fin (C.rank (b + 1))) := rfl
  rw [hid, Matrix.submatrix_id_id]
  exact hdd b

/-- The chain complex of finite free modules that a bounded-above Fitting complex presents, once
the complex condition is supplied as new data: the rank in chain degree `j` is the rank in
cochain degree `-j`, and the differentials are those of the Fitting complex, reindexed along the
flip. The boundedness is forgotten, `FreeComplex` having no field for it. -/
noncomputable def toFreeComplex (C : FreeData R) (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) :
    FreeComplex R where
  n j := C.rank (-j)
  d j := (C.d (-(j + 1))).submatrix (Fin.cast (C.rank_neg_add_one j).symm) id
  dd j := by
    have hkey : C.d (-(j + 1))
        * (C.d (-(j + 1 + 1))).submatrix (Fin.cast (C.rank_neg_add_one (j + 1)).symm) id = 0 :=
      C.d_mul_submatrix_d hdd (show (-(j + 1) : ℤ) = -(j + 1 + 1) + 1 by ring) _
    ext x y
    have hx := congrFun (congrFun hkey (Fin.cast (C.rank_neg_add_one j).symm x)) y
    simpa [Matrix.mul_apply] using hx

/-- The rank of `FreeData.toFreeComplex` in chain degree `j` is the rank of the Fitting complex in
cochain degree `-j`. -/
@[simp]
theorem toFreeComplex_n (C : FreeData R) (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) (j : ℤ) :
    (C.toFreeComplex hdd).n j = C.rank (-j) := rfl

/-- The differential of `FreeData.toFreeComplex` in chain degree `j` is the differential of the
Fitting complex in cochain degree `-(j + 1)`, with its rows reindexed along the degree flip. -/
theorem toFreeComplex_d (C : FreeData R) (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) (j : ℤ) :
    (C.toFreeComplex hdd).d j
      = (C.d (-(j + 1))).submatrix (Fin.cast (C.rank_neg_add_one j).symm) id := rfl

/-- The degree flip does not change the entries of a differential, only the degree it sits in, so
it does not change the ideals of its minors. -/
theorem minorIdeal_toFreeComplex_d (C : FreeData R)
    (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) (j : ℤ) (r : ℕ) :
    minorIdeal ((C.toFreeComplex hdd).d j) r = minorIdeal (C.d (-(j + 1))) r :=
  minorIdeal_reindex (C.d (-(j + 1))) (finCongr (C.rank_neg_add_one j))
    (Equiv.refl (Fin (C.rank (-(j + 1))))) r

/-- **A unit entry of the matrix of `d_i` is a unit matrix coefficient of the flipped complex in
degree `-i`.** This is the hypothesis `FreeComplex.HasInvertibleCoeff` of [Stacks, Tag 00MT], and
with it that theorem applies to a `FreeData`. The degree is given as a hypothesis `ht` rather
than as `-i` so that no cast appears in the statement; at the call site `ht` is `by ring`. -/
theorem hasInvertibleCoeff_toFreeComplex (C : FreeData R)
    (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) {i t : ℤ} (ht : -(t - 1 + 1) = i)
    (a : Fin (C.rank (i + 1))) (b : Fin (C.rank i)) (hu : IsUnit (C.d i a b)) :
    (C.toFreeComplex hdd).HasInvertibleCoeff t := by
  subst ht
  change ∃ (k : Fin (C.rank (-(t - 1)))) (l : Fin (C.rank (-(t - 1 + 1)))),
    IsUnit ((C.d (-(t - 1 + 1))).submatrix
      (Fin.cast (C.rank_neg_add_one (t - 1)).symm) id k l)
  exact ⟨Fin.cast (C.rank_neg_add_one (t - 1)) a, b, hu⟩

/-- Two bounded-above Fitting complexes with the same ranks and the same bound have the same
Fitting ideals as soon as their differentials have the same ideals of minors in every degree: the
prescribed size of the minors is computed from the ranks and the bound alone. -/
theorem fittingIdeal_eq_of_minorIdeal_d_eq (C D : FreeData R)
    (hrank : ∀ i, D.rank i = C.rank i) (htop : D.top = C.top)
    (hd : ∀ (p : ℤ) (r : ℕ), minorIdeal (D.d p) r = minorIdeal (C.d p) r) (p k : ℤ) :
    D.fittingIdeal p k = C.fittingIdeal p k := by
  have htail : D.tailAlternatingRank p = C.tailAlternatingRank p := by
    simp only [tailAlternatingRank, htop, hrank]
  have hsize : D.minorSize p k = C.minorSize p k := by
    simp only [minorSize, htail]
  rw [fittingIdeal, fittingIdeal, hsize, hd]

/-- `Stacks.FittingComplex.FreeData.minorIdeal_toFreeComplex_d` at a cochain degree presented as
`-(j + 1)` only up to an equality of integers. -/
theorem minorIdeal_toFreeComplex_d' (C : FreeData R)
    (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) {j p : ℤ} (hjp : -(j + 1) = p) (r : ℕ) :
    minorIdeal ((C.toFreeComplex hdd).d j) r = minorIdeal (C.d p) r := by
  subst hjp
  exact C.minorIdeal_toFreeComplex_d hdd j r

/-- Outside the one degree where it is nonzero, the differential of the trivial two-term complex
vanishes. -/
theorem trivialComplex_d_eq_zero (i p : ℤ) (m : ℕ) (hp : p ≠ i)
    (x : Fin ((trivialComplex R i m).rank (p + 1))) (y : Fin ((trivialComplex R i m).rank p)) :
    (trivialComplex R i m).d p x y = 0 := by
  simp only [trivialComplex, if_neg hp]
  rfl

/-- Under the degree flip the elementary identity complex of `FreeComplex.elementaryComplex` in
chain degree `-i` is the trivial two-term complex of
`Stacks.FittingComplex.FreeData.trivialComplex` of rank one in cochain degrees `i` and `i + 1`:
their rank functions agree. -/
private theorem elemRank_neg_eq_trivialRank (i j : ℤ) :
    FreeComplex.elemRank (-i) (-j) = trivialRank i 1 j := by
  simp only [FreeComplex.elemRank, trivialRank]
  by_cases h : j = i ∨ j = i + 1
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- The entries of the differential of the trivial two-term complex are those of the elementary
identity complex it corresponds to under the degree flip. -/
private theorem trivialComplex_d_apply_eq (i p : ℤ)
    (ha : (trivialComplex R i 1).rank (p + 1) = FreeComplex.elemRank (-i) (-(p + 1)))
    (hb : (trivialComplex R i 1).rank p = FreeComplex.elemRank (-i) (-(p + 1) + 1))
    (x : Fin ((trivialComplex R i 1).rank (p + 1)))
    (y : Fin ((trivialComplex R i 1).rank p)) :
    (trivialComplex R i 1).d p x y
      = (FreeComplex.elementaryComplex R (-i)).d (-(p + 1)) (Fin.cast ha x) (Fin.cast hb y) := by
  by_cases hp : p = i
  · subst hp
    have hr1 : (trivialComplex R p 1).rank (p + 1) = 1 := trivialRank_succ p 1
    have hr0 : (trivialComplex R p 1).rank p = 1 := trivialRank_self p 1
    have hx : (x : ℕ) = 0 := by have := x.isLt; omega
    have hy : (y : ℕ) = 0 := by have := y.isLt; omega
    rw [trivialComplex_d_self_apply, if_pos (hx.trans hy.symm)]
    exact (FreeComplex.elementaryComplex_d_eq_one R
      (show (-(p + 1) : ℤ) = -p - 1 from by ring) _ _).symm
  · rw [trivialComplex_d_eq_zero i p 1 hp]
    exact (FreeComplex.elementaryComplex_d_eq_zero R (by omega) _ _).symm

/-- The differentials of the trivial two-term complex and of the elementary identity complex it
corresponds to under the degree flip have the same ideals of minors. -/
private theorem minorIdeal_trivialComplex_d (i p : ℤ) (r : ℕ) :
    minorIdeal ((trivialComplex R i 1).d p) r
      = minorIdeal ((FreeComplex.elementaryComplex R (-i)).d (-(p + 1))) r := by
  have ha : (trivialComplex R i 1).rank (p + 1) = FreeComplex.elemRank (-i) (-(p + 1)) :=
    (elemRank_neg_eq_trivialRank i (p + 1)).symm
  have hb : (trivialComplex R i 1).rank p = FreeComplex.elemRank (-i) (-(p + 1) + 1) := by
    rw [show (-(p + 1) + 1 : ℤ) = -p from by ring]
    exact (elemRank_neg_eq_trivialRank i p).symm
  exact minorIdeal_eq_of_apply _ _ ha hb (trivialComplex_d_apply_eq i p ha hb) r

/-- Reindexing a sum of two `Fin`s along an equality of the sums is the sum of the reindexings. -/
private theorem finSumFinEquiv_symm_cast {a b a' b' : ℕ} (h₁ : a = a') (h₂ : b = b')
    (h : a + b = a' + b') (x : Fin (a + b)) :
    finSumFinEquiv.symm (Fin.cast h x)
      = Sum.map (Fin.cast h₁) (Fin.cast h₂) (finSumFinEquiv.symm x) := by
  subst h₁
  subst h₂
  rw [show Fin.cast h x = x from rfl]
  cases finSumFinEquiv.symm x <;> rfl

/-- **The direct sum with the trivial two-term complex, read under the degree flip, is the
block-diagonal sum with the elementary identity complex**: the two differentials have the same
entries, up to the reindexing of the ranks. -/
theorem directSum_trivialComplex_d_eq (D : FreeComplex R) (top i : ℤ)
    (hvan : ∀ i' : ℤ, top < i' → D.n (-i') = 0) (p : ℤ)
    (h₁ : (D.toFreeData top hvan).rank (p + 1) + (trivialComplex R i 1).rank (p + 1)
      = (FreeComplex.combine D (FreeComplex.elementaryComplex R (-i))).n (-(p + 1)))
    (h₂ : (D.toFreeData top hvan).rank p + (trivialComplex R i 1).rank p
      = (FreeComplex.combine D (FreeComplex.elementaryComplex R (-i))).n (-(p + 1) + 1)) :
    ((D.toFreeData top hvan).directSum (trivialComplex R i 1)).d p
      = ((FreeComplex.combine D (FreeComplex.elementaryComplex R (-i))).d (-(p + 1))).submatrix
        (Fin.cast h₁) (Fin.cast h₂) := by
  have hD₁ : (D.toFreeData top hvan).rank (p + 1) = D.n (-(p + 1)) := rfl
  have hT₁ : (trivialComplex R i 1).rank (p + 1) = FreeComplex.elemRank (-i) (-(p + 1)) :=
    (elemRank_neg_eq_trivialRank i (p + 1)).symm
  have hD₂ : (D.toFreeData top hvan).rank p = D.n (-(p + 1) + 1) := by
    rw [FreeComplex.toFreeData_rank, show (-(p + 1) + 1 : ℤ) = -p from by ring]
  have hT₂ : (trivialComplex R i 1).rank p = FreeComplex.elemRank (-i) (-(p + 1) + 1) := by
    rw [show (-(p + 1) + 1 : ℤ) = -p from by ring]
    exact (elemRank_neg_eq_trivialRank i p).symm
  refine Matrix.ext fun x y => ?_
  change Matrix.fromBlocks ((D.toFreeData top hvan).d p) 0 0 ((trivialComplex R i 1).d p)
      (finSumFinEquiv.symm x) (finSumFinEquiv.symm y)
    = Matrix.fromBlocks (D.d (-(p + 1))) 0 0
        ((FreeComplex.elementaryComplex R (-i)).d (-(p + 1)))
        (finSumFinEquiv.symm (Fin.cast h₁ x)) (finSumFinEquiv.symm (Fin.cast h₂ y))
  rw [finSumFinEquiv_symm_cast hD₁ hT₁ h₁ x, finSumFinEquiv_symm_cast hD₂ hT₂ h₂ y]
  rcases hx : finSumFinEquiv.symm x with u | u <;> rcases hy : finSumFinEquiv.symm y with v | v <;>
    simp only [Sum.map_inl, Sum.map_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  · rfl
  · exact trivialComplex_d_apply_eq i p hT₁ hT₂ u v

/-- The direct sum with the trivial two-term complex of rank one in degrees `i` and `i + 1`, read
under the degree flip, is the block-diagonal sum with the elementary identity complex in chain
degree `-i`: in every degree and at every size the two have the same ideals of minors. -/
private theorem minorIdeal_directSum_trivialComplex_d (D : FreeComplex R) (top i : ℤ)
    (hvan : ∀ i' : ℤ, top < i' → D.n (-i') = 0) (p : ℤ) (r : ℕ) :
    minorIdeal (((D.toFreeData top hvan).directSum (trivialComplex R i 1)).d p) r
      = minorIdeal ((FreeComplex.combine D
          (FreeComplex.elementaryComplex R (-i))).d (-(p + 1))) r := by
  have hc : (FreeComplex.combine D (FreeComplex.elementaryComplex R (-i))).d (-(p + 1))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (D.d (-(p + 1))) 0 0
          ((FreeComplex.elementaryComplex R (-i)).d (-(p + 1)))) := rfl
  rw [minorIdeal_directSum_d, hc, minorIdeal_reindex, minorIdeal_fromBlocks,
    minorIdeal_fromBlocks]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [D.minorIdeal_toFreeData_d top hvan p q.1, minorIdeal_trivialComplex_d i p q.2]

/-- A family of matrices indexed by the degree, read at two degrees that are equal. -/
private theorem matrix_family_deg_eq {Cf : FreeComplex R}
    (Pmat : ∀ t : ℤ, Matrix (Fin (Cf.n t)) (Fin (Cf.n t)) R) {t₁ t₂ : ℤ} (h : t₁ = t₂)
    (h₁ : Cf.n t₁ = Cf.n t₂) :
    Pmat t₁ = (Pmat t₂).submatrix (Fin.cast h₁) (Fin.cast h₁) := by
  subst h
  rfl

/-- The differential of the flipped complex, read back as a differential of the Fitting
complex. -/
private theorem toFreeComplex_d_eq (C : FreeData R)
    (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) {t j : ℤ} (ht : -(t + 1) = j)
    (h₁ : (C.toFreeComplex hdd).n t = C.rank (j + 1))
    (h₂ : (C.toFreeComplex hdd).n (t + 1) = C.rank j) :
    (C.toFreeComplex hdd).d t = (C.d j).submatrix (Fin.cast h₁) (Fin.cast h₂) := by
  subst ht
  rfl

/-- **[Stacks, Tag 00MT] for a bounded-above complex of finite free modules recorded by its
ranks and matrices, and its effect on the Fitting ideals.**

Let `C` be such a complex, satisfying the complex condition, and suppose the matrix of `d_i` has
a unit entry. Then the ranks in degrees `i` and `i + 1` are at least one, and there is a
bounded-above complex `C'` with those two ranks decremented, the others unchanged, which again
satisfies the complex condition and has *the same Fitting ideals as `C` in every degree and at
every index*.

[Stacks, Tag 00MT] supplies the splitting `C ≅ C' ⊕ T` for the trivial two-term complex `T` of
rank one in degrees `i` and `i + 1`, as a degreewise invertible change of basis; the degree flip
of `Stacks.FittingComplex.FreeData.toFreeComplex` is what lets it be applied here, and
`FreeComplex.minorIdeal_d_eq_of_conj` turns the change of basis into the equality of the ideals
of minors. The numerical step — that passing from `C' ⊕ T` to `C'` changes neither the ideals,
although it changes both the ranks and the prescribed size of the minors — is
`Stacks.FittingComplex.FreeData.fittingIdeal_directSum_trivialComplex`. -/
theorem exists_freeData_fittingIdeal_eq_of_isUnit (C : FreeData R)
    (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) {i : ℤ}
    (a : Fin (C.rank (i + 1))) (b : Fin (C.rank i)) (hu : IsUnit (C.d i a b)) :
    1 ≤ C.rank i ∧ 1 ≤ C.rank (i + 1) ∧
      ∃ C' : FreeData R,
        (∀ j : ℤ, C'.rank j = if j = i then C.rank i - 1 else
          if j = i + 1 then C.rank (i + 1) - 1 else C.rank j) ∧
        (∀ j : ℤ, C'.d (j + 1) * C'.d j = 0) ∧
        (∀ p k : ℤ, C'.fittingIdeal p k = C.fittingIdeal p k) ∧
        ∃ (P : ∀ j : ℤ, Matrix (Fin ((C'.directSum (trivialComplex R i 1)).rank j))
              (Fin (C.rank j)) R)
          (Q : ∀ j : ℤ, Matrix (Fin (C.rank j))
              (Fin ((C'.directSum (trivialComplex R i 1)).rank j)) R),
          (∀ j : ℤ, P j * Q j = 1) ∧ (∀ j : ℤ, Q j * P j = 1) ∧
          ∀ j : ℤ, (C'.directSum (trivialComplex R i 1)).d j * P j = P (j + 1) * C.d j := by
  have hri : 1 ≤ C.rank i := by have := b.isLt; omega
  have hri1 : 1 ≤ C.rank (i + 1) := by have := a.isLt; omega
  refine ⟨hri, hri1, ?_⟩
  have htopi : i + 1 ≤ C.top := by
    by_contra hcon
    rw [C.rank_eq_zero_of_top_lt (i + 1) (by omega)] at hri1
    omega
  -- the ranks of the flipped complex, read back on `C`
  have hn0 : (C.toFreeComplex hdd).n (-i) = C.rank i := by
    rw [toFreeComplex_n, neg_neg]
  have hn1 : (C.toFreeComplex hdd).n (-i - 1 + 1) = C.rank i := by
    rw [toFreeComplex_n, show (-(-i - 1 + 1) : ℤ) = i from by ring]
  have hn2 : (C.toFreeComplex hdd).n (-i - 1) = C.rank (i + 1) := by
    rw [toFreeComplex_n, show (-(-i - 1) : ℤ) = i + 1 from by ring]
  -- [Stacks, Tag 00MT]: a unit matrix coefficient in chain degree `-i` splits off the
  -- elementary identity complex, by a degreewise invertible change of basis
  obtain ⟨kk, jj, hu'⟩ := C.hasInvertibleCoeff_toFreeComplex hdd (t := -i) (by ring) a b hu
  obtain ⟨hp, hq, P, Q, M, hPdet, hQdet, hblock⟩ :=
    exists_pivot_block_split ((C.toFreeComplex hdd).d (-i - 1)) kk jj hu'
  obtain ⟨D, Pmat, hn, hrank, hPmatdet, hconj⟩ :=
    freeComplex_split_data (C.toFreeComplex hdd) (-i) (hn1 ▸ hri) (hn2 ▸ hri1) P Q M
      hPdet hQdet hblock
  -- flip the reduced complex back, with the bound of `C`
  have hvan : ∀ i' : ℤ, C.top < i' → D.n (-i') = 0 := by
    intro i' hi'
    have hz : (C.toFreeComplex hdd).n (-i') = 0 := by
      rw [toFreeComplex_n, neg_neg]
      exact C.rank_eq_zero_of_top_lt i' hi'
    rw [hrank]
    split_ifs with h1 h2
    · exfalso; omega
    · exfalso; omega
    · exact hz
  have hrank' : ∀ j : ℤ,
      ((D.toFreeData C.top hvan).directSum (trivialComplex R i 1)).rank j = C.rank j := by
    intro j
    rw [directSum_rank, FreeComplex.toFreeData_rank, hrank, trivialComplex_rank]
    by_cases h1 : j = i
    · subst h1
      rw [if_pos rfl, trivialRank_self, toFreeComplex_n, neg_neg]
      omega
    · by_cases h2 : j = i + 1
      · subst h2
        rw [if_neg (by omega : ¬(-(i + 1) : ℤ) = -i), if_pos (by omega), trivialRank_succ, hn2]
        omega
      · rw [if_neg (by omega : ¬(-j : ℤ) = -i), if_neg (by omega : ¬(-j : ℤ) = -i - 1),
          trivialRank_eq_zero 1 h1 h2, toFreeComplex_n, neg_neg, add_zero]
  refine ⟨D.toFreeData C.top hvan, ?_, D.toFreeData_d_mul_d C.top hvan, ?_, ?_⟩
  · intro j
    rw [FreeComplex.toFreeData_rank, hrank]
    by_cases h1 : j = i
    · subst h1
      rw [if_pos rfl, if_pos rfl, hn0]
    · by_cases h2 : j = i + 1
      · subst h2
        rw [if_neg (by omega : ¬(-(i + 1) : ℤ) = -i), if_pos (by omega), if_neg h1, if_pos rfl,
          hn2]
      · rw [if_neg (by omega : ¬(-j : ℤ) = -i), if_neg (by omega : ¬(-j : ℤ) = -i - 1),
          if_neg h1, if_neg h2, toFreeComplex_n, neg_neg]
  · -- the ranks and the bound of `C' ⊕ T` are those of `C`, and so are its ideals of minors
    have htop' : ((D.toFreeData C.top hvan).directSum (trivialComplex R i 1)).top = C.top := by
      rw [directSum_top, FreeComplex.toFreeData_top, trivialComplex_top]
      omega
    have hd' : ∀ (p : ℤ) (r : ℕ),
        minorIdeal (((D.toFreeData C.top hvan).directSum (trivialComplex R i 1)).d p) r
          = minorIdeal (C.d p) r := by
      intro p r
      rw [minorIdeal_directSum_trivialComplex_d D C.top i hvan p r,
        FreeComplex.minorIdeal_d_eq_of_conj (C.toFreeComplex hdd)
          (FreeComplex.combine D (FreeComplex.elementaryComplex R (-i))) hn Pmat hPmatdet hconj
          (-(p + 1)) r]
      exact C.minorIdeal_toFreeComplex_d' hdd (show -(-(p + 1) + 1) = p from by ring) r
    intro p k
    rw [← fittingIdeal_directSum_trivialComplex (D.toFreeData C.top hvan) i 1 p k]
    exact fittingIdeal_eq_of_minorIdeal_d_eq C _ hrank' htop' hd' p k
  · -- the degreewise invertible change of basis, read on the cochain side
    have hcf : ∀ j : ℤ, (C.toFreeComplex hdd).n (-j) = C.rank j := by
      intro j
      rw [toFreeComplex_n, neg_neg]
    have e₁ : ∀ j : ℤ,
        ((D.toFreeData C.top hvan).directSum (trivialComplex R i 1)).rank j
          = (C.toFreeComplex hdd).n (-j) := fun j => (hrank' j).trans (hcf j).symm
    have e₂ : ∀ j : ℤ, C.rank j = (C.toFreeComplex hdd).n (-j) := fun j => (hcf j).symm
    refine ⟨fun j => (Pmat (-j)).submatrix (finCongr (e₁ j)) (finCongr (e₂ j)),
      fun j => ((((Matrix.isUnit_iff_isUnit_det (Pmat (-j))).2 (hPmatdet (-j))).unit⁻¹ :
          (Matrix (Fin ((C.toFreeComplex hdd).n (-j))) (Fin ((C.toFreeComplex hdd).n (-j))) R)ˣ) :
          Matrix (Fin ((C.toFreeComplex hdd).n (-j))) (Fin ((C.toFreeComplex hdd).n (-j))) R
        ).submatrix (finCongr (e₂ j)) (finCongr (e₁ j)), ?_, ?_, ?_⟩
    · intro j
      rw [Matrix.submatrix_mul_equiv _ _ _ (finCongr (e₂ j)) _,
        show Pmat (-j) * ((((Matrix.isUnit_iff_isUnit_det (Pmat (-j))).2
              (hPmatdet (-j))).unit⁻¹ :
            (Matrix (Fin ((C.toFreeComplex hdd).n (-j)))
              (Fin ((C.toFreeComplex hdd).n (-j))) R)ˣ) :
            Matrix (Fin ((C.toFreeComplex hdd).n (-j)))
              (Fin ((C.toFreeComplex hdd).n (-j))) R) = 1 from
          Units.mul_inv ((Matrix.isUnit_iff_isUnit_det (Pmat (-j))).2 (hPmatdet (-j))).unit,
        Matrix.submatrix_one_equiv]
    · intro j
      rw [Matrix.submatrix_mul_equiv _ _ _ (finCongr (e₁ j)) _,
        show ((((Matrix.isUnit_iff_isUnit_det (Pmat (-j))).2 (hPmatdet (-j))).unit⁻¹ :
            (Matrix (Fin ((C.toFreeComplex hdd).n (-j)))
              (Fin ((C.toFreeComplex hdd).n (-j))) R)ˣ) :
            Matrix (Fin ((C.toFreeComplex hdd).n (-j)))
              (Fin ((C.toFreeComplex hdd).n (-j))) R) * Pmat (-j) = 1 from
          Units.inv_mul ((Matrix.isUnit_iff_isUnit_det (Pmat (-j))).2 (hPmatdet (-j))).unit,
        Matrix.submatrix_one_equiv]
    · intro j
      have hdeg : (-(j + 1) + 1 : ℤ) = -j := by ring
      have hc : (C.toFreeComplex hdd).n (-(j + 1) + 1) = (C.toFreeComplex hdd).n (-j) :=
        congrArg (C.toFreeComplex hdd).n hdeg
      have a₁ : (C.toFreeComplex hdd).n (-(j + 1)) = C.rank (j + 1) := hcf (j + 1)
      have a₂ : (C.toFreeComplex hdd).n (-(j + 1) + 1) = C.rank j := hc.trans (hcf j)
      have h₁ : ((D.toFreeData C.top hvan).directSum (trivialComplex R i 1)).rank (j + 1)
          = (FreeComplex.combine D (FreeComplex.elementaryComplex R (-i))).n (-(j + 1)) :=
        (e₁ (j + 1)).trans (hn (-(j + 1))).symm
      have h₂ : ((D.toFreeData C.top hvan).directSum (trivialComplex R i 1)).rank j
          = (FreeComplex.combine D (FreeComplex.elementaryComplex R (-i))).n (-(j + 1) + 1) :=
        (((e₁ j).trans (hcf j)).trans a₂.symm).trans (hn (-(j + 1) + 1)).symm
      refine Matrix.ext fun x y => ?_
      calc (((D.toFreeData C.top hvan).directSum (trivialComplex R i 1)).d j
              * (Pmat (-j)).submatrix (finCongr (e₁ j)) (finCongr (e₂ j))) x y
          = ∑ z : Fin (((D.toFreeData C.top hvan).directSum (trivialComplex R i 1)).rank j),
              ((FreeComplex.combine D (FreeComplex.elementaryComplex R (-i))).d
                  (-(j + 1))).submatrix (Fin.cast (hn (-(j + 1))).symm)
                  (Fin.cast (hn (-(j + 1) + 1)).symm)
                  (Fin.cast (h₁.trans (hn (-(j + 1)))) x)
                  ((finCongr (h₂.trans (hn (-(j + 1) + 1)))) z)
                * Pmat (-(j + 1) + 1) ((finCongr (h₂.trans (hn (-(j + 1) + 1)))) z)
                    (Fin.cast a₂.symm y) := by
            rw [Matrix.mul_apply]
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [directSum_trivialComplex_d_eq D C.top i hvan j h₁ h₂,
              matrix_family_deg_eq Pmat hdeg hc]
            rfl
        _ = ∑ w' : Fin ((C.toFreeComplex hdd).n (-(j + 1) + 1)),
              ((FreeComplex.combine D (FreeComplex.elementaryComplex R (-i))).d
                  (-(j + 1))).submatrix (Fin.cast (hn (-(j + 1))).symm)
                  (Fin.cast (hn (-(j + 1) + 1)).symm)
                  (Fin.cast (h₁.trans (hn (-(j + 1)))) x) w'
                * Pmat (-(j + 1) + 1) w' (Fin.cast a₂.symm y) :=
            Fintype.sum_equiv (finCongr (h₂.trans (hn (-(j + 1) + 1)))) _ _ fun _ => rfl
        _ = ∑ z' : Fin ((C.toFreeComplex hdd).n (-(j + 1))),
              Pmat (-(j + 1)) (Fin.cast (h₁.trans (hn (-(j + 1)))) x) z'
                * (C.toFreeComplex hdd).d (-(j + 1)) z' (Fin.cast a₂.symm y) := by
            have key := congrFun (congrFun (hconj (-(j + 1)))
              (Fin.cast (h₁.trans (hn (-(j + 1)))) x)) (Fin.cast a₂.symm y)
            rw [Matrix.mul_apply, Matrix.mul_apply] at key
            exact key.symm
        _ = ∑ w : Fin (C.rank (j + 1)),
              ((Pmat (-(j + 1))).submatrix (finCongr (e₁ (j + 1)))
                  (finCongr (e₂ (j + 1)))) x w * C.d j w y :=
            (Fintype.sum_equiv (finCongr (hcf (j + 1)).symm) _ _ fun w => by
              rw [toFreeComplex_d_eq C hdd (show -(-(j + 1) + 1) = j from by ring) a₁ a₂]
              rfl).symm
        _ = ((Pmat (-(j + 1))).submatrix (finCongr (e₁ (j + 1))) (finCongr (e₂ (j + 1)))
              * C.d j) x y := (Matrix.mul_apply ..).symm

end FreeData

end Stacks.FittingComplex
