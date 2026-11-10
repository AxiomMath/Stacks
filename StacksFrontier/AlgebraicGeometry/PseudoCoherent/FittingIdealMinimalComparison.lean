module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealMatrixHomotopy

/-!
# Comparing two minimal complexes of finite free modules over a local ring

Let `R` be a local ring with maximal ideal `𝔪` and let `C₁`, `C₂` be bounded-above complexes of
finite free `R`-modules, recorded as `Stacks.FittingComplex.FreeData` by their ranks and the
matrices of their differentials. Call such a complex *minimal above `c`* if the matrix of `d_i`
has all its entries in `𝔪` for every `i ≥ c`. This file proves that two complexes which are
minimal above `c` and homotopy equivalent agree, above `c`, up to a degreewise invertible change
of basis: their ranks are equal in every degree `> c` and their differentials are conjugate
there. Consequently their Fitting ideals agree in every degree `> c`
(`Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_homotopyEquiv_of_minimal`).

This is the second half of the proof of [Stacks, Tag 0ESP]: the first half splits off trivial
two-term complexes until the complex is minimal, and this is the uniqueness of what is left. What
the first half has to supply is one statement: that a bounded-above complex of finite free modules
over a local ring admits, for every cutoff `c`, a complex which is minimal above `c`, has the same
Fitting ideals, and is *homotopy equivalent to it*. The two numerical halves of that statement are
already available — `Stacks.FittingComplex.FreeData.exists_freeData_fittingIdeal_eq_of_isUnit`
removes one unit entry while preserving every Fitting ideal, and the removal strictly decreases
the sum of the ranks in the degrees `≥ c`, which is finite because the ranks vanish above `top` —
and what is missing is the homotopy equivalence between the complex and the result, i.e. the
transport of the splitting `C ≅ C' ⊕ T` of [Stacks, Tag 00MT] across the contractibility of the
trivial two-term complex `T`.

## Main results

* `Stacks.FittingComplex.FreeData.rank_eq_of_matrixHtpy_of_minimal`: the ranks agree above `c`.
* `Stacks.FittingComplex.FreeData.minorIdeal_d_eq_of_matrixHtpy_of_minimal`: the ideals of
  minors of the differentials agree above `c`, at every size.
* `Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_matrixHtpy_of_minimal`, with its
  `_of_homotopyEquiv_` form: hence so do the Fitting ideals.
* `Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_derivedIso_of_minimal`: the same with the
  hypothesis read in the derived category, which is the form in which the local description of
  [Stacks, Tag 0ESP] supplies it.

## Implementation notes

The argument is Nakayama's lemma, and it is carried out on matrices rather than on modules. A
homotopy equivalence `e` carries, in each degree, the matrices of `e.hom` and `e.inv` and the
matrices of the two homotopies; the identity `e.hom ≫ e.inv ≃ 𝟙` reads, in degree `i`, as

`G i * F i = H * d_i + d_{i-1} * K + 1`,

and both `d_i` and `d_{i-1}` reduce to zero modulo `𝔪` as soon as `i - 1 ≥ c`. So `F i` and
`G i` are mutually inverse modulo `𝔪`, which forces the two ranks to agree — a two-sided inverse
makes the reductions mutually inverse linear maps between free modules over the residue field —
and then makes the determinant of `F i`, read as a square matrix through that equality of ranks,
a unit of `R`, the complement of the maximal ideal being the units.

The equality of the ideals of minors needs no determinant: once the ranks agree, the
conjugation `d_p^{C₂} * F_p = F_{p+1} * d_p^{C₁}` can be solved for either differential in terms
of the other, and `minorIdeal_mul_le` together with `minorIdeal_mul_le_right` gives both
inclusions. The determinant is used only to produce the inverse matrices that solving requires.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
* [Stacks Project, Tag 00MT](https://stacks.math.columbia.edu/tag/00MT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Matrix

namespace Stacks.FittingComplex.FreeData

universe u w

variable {R : Type u} [CommRing R]

/-- A matrix all of whose entries lie in an ideal reduces to zero. -/
theorem map_quotient_eq_zero_of_mem {l o : Type*} {I : Ideal R} (A : Matrix l o R)
    (hA : ∀ a b, A a b ∈ I) : A.map (Ideal.Quotient.mk I) = 0 := by
  ext a b
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hA a b)

/-- Two rectangular matrices over a nontrivial commutative ring which are mutually inverse have
square shapes: the numbers of rows and of columns agree. -/
theorem card_eq_of_mul_eq_one {S : Type*} [CommRing S] [Nontrivial S] {a b : ℕ}
    (A : Matrix (Fin b) (Fin a) S) (B : Matrix (Fin a) (Fin b) S)
    (hBA : B * A = 1) (hAB : A * B = 1) : a = b := by
  have e : (Fin a → S) ≃ₗ[S] (Fin b → S) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' A) (Matrix.toLin' B)
      (by rw [← Matrix.toLin'_mul, hAB, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hBA, Matrix.toLin'_one])
  simpa using e.finrank_eq

/-- Reindexing the rows and the columns of a matrix along equalities of their sizes does not
change the ideal generated by its minors. -/
theorem minorIdeal_submatrix_cast {a a' b b' : ℕ} (A : Matrix (Fin b) (Fin a) R)
    (hb : b' = b) (ha : a' = a) (r : ℕ) :
    minorIdeal (A.submatrix (Fin.cast hb) (Fin.cast ha)) r = minorIdeal A r := by
  subst hb
  subst ha
  rw [show (Fin.cast (rfl : b' = b') : Fin b' → Fin b') = id from rfl,
    show (Fin.cast (rfl : a' = a') : Fin a' → Fin a') = id from rfl, Matrix.submatrix_id_id]

section LocalRing

variable [IsLocalRing R]

/-- The determinant of a square matrix which is invertible modulo the maximal ideal is a unit. -/
theorem isUnit_det_of_mul_map_eq_one {a : ℕ} (A B : Matrix (Fin a) (Fin a) R)
    (h : (B.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))) *
      (A.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))) = 1) : IsUnit A.det := by
  by_contra hcon
  have hmem : A.det ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcon)
  have hdet : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) A.det = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  have h1 : (B.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))).det *
      (A.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))).det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  have hA0 : (A.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]
  rw [hA0, mul_zero] at h1
  exact zero_ne_one h1

/-- **The two matrices of a homotopy equivalence are mutually inverse modulo the maximal ideal**,
in every degree above `c`, when both complexes are minimal above `c`. -/
theorem map_matrixHtpy_mul_map_matrixHtpy {C₁ C₂ : FreeData R} (e : MatrixHtpy C₁ C₂) (c : ℤ)
    (h₁ : ∀ i : ℤ, c ≤ i → ∀ a b, C₁.d i a b ∈ IsLocalRing.maximalIdeal R)
    (j : ℤ) (hj : c ≤ j) :
    (e.invMat (j + 1)).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) *
        (e.toMat (j + 1)).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) = 1 := by
  have hd1 : (C₁.d (j + 1)).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) = 0 :=
    map_quotient_eq_zero_of_mem _ (h₁ (j + 1) (by omega))
  have hd0 : (C₁.d j).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) = 0 :=
    map_quotient_eq_zero_of_mem _ (h₁ j hj)
  have key := congrArg (Matrix.map · (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))
    (e.invMat_toMat j)
  simpa only [Matrix.map_add _ (map_add _), Matrix.map_mul, hd1, hd0,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add] using key

/-- **The ranks of two homotopy equivalent complexes which are minimal above `c` agree above
`c`.** The two matrices of the homotopy equivalence are mutually inverse over the residue field,
so they are the matrices of mutually inverse maps of free modules there. -/
theorem rank_eq_of_matrixHtpy_of_minimal {C₁ C₂ : FreeData R} (e : MatrixHtpy C₁ C₂) (c : ℤ)
    (h₁ : ∀ i : ℤ, c ≤ i → ∀ a b, C₁.d i a b ∈ IsLocalRing.maximalIdeal R)
    (h₂ : ∀ i : ℤ, c ≤ i → ∀ a b, C₂.d i a b ∈ IsLocalRing.maximalIdeal R)
    (i : ℤ) (hi : c + 1 ≤ i) : C₁.rank i = C₂.rank i := by
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by ring⟩
  exact card_eq_of_mul_eq_one _ _
    (map_matrixHtpy_mul_map_matrixHtpy e c h₁ j (by omega))
    (map_matrixHtpy_mul_map_matrixHtpy e.symm c h₂ j (by omega))

/-- **The matrix of a homotopy equivalence is invertible above `c`**, once squared up along the
equality of the ranks: its determinant is a unit, being a unit modulo the maximal ideal. -/
theorem isUnit_det_submatrix_of_matrixHtpy_of_minimal {C₁ C₂ : FreeData R} (e : MatrixHtpy C₁ C₂)
    (c : ℤ) (h₁ : ∀ i : ℤ, c ≤ i → ∀ a b, C₁.d i a b ∈ IsLocalRing.maximalIdeal R)
    (i : ℤ) (hi : c + 1 ≤ i) (hr : C₁.rank i = C₂.rank i) :
    IsUnit ((e.toMat i).submatrix (Fin.cast hr) id).det := by
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by ring⟩
  refine isUnit_det_of_mul_map_eq_one _ ((e.invMat (j + 1)).submatrix id (Fin.cast hr)) ?_
  have hsub : (e.invMat (j + 1)).submatrix id (Fin.cast hr) *
      (e.toMat (j + 1)).submatrix (Fin.cast hr) id =
      e.invMat (j + 1) * e.toMat (j + 1) :=
    (Matrix.submatrix_mul_equiv (e.invMat (j + 1)) (e.toMat (j + 1)) id (finCongr hr) id).trans
      (Matrix.submatrix_id_id _)
  rw [← Matrix.map_mul, hsub, Matrix.map_mul]
  exact map_matrixHtpy_mul_map_matrixHtpy e c h₁ j (by omega)

/-- **The ideals of minors of the differentials of two homotopy equivalent complexes which are
minimal above `c` agree above `c`**, at every size: the differentials are conjugate by the
degreewise invertible matrices of the homotopy equivalence. -/
theorem minorIdeal_d_eq_of_matrixHtpy_of_minimal {C₁ C₂ : FreeData R} (e : MatrixHtpy C₁ C₂)
    (c : ℤ) (h₁ : ∀ i : ℤ, c ≤ i → ∀ a b, C₁.d i a b ∈ IsLocalRing.maximalIdeal R)
    (h₂ : ∀ i : ℤ, c ≤ i → ∀ a b, C₂.d i a b ∈ IsLocalRing.maximalIdeal R)
    (p : ℤ) (hp : c + 1 ≤ p) (r : ℕ) : minorIdeal (C₂.d p) r = minorIdeal (C₁.d p) r := by
  classical
  have hr0 : C₁.rank p = C₂.rank p := rank_eq_of_matrixHtpy_of_minimal e c h₁ h₂ p hp
  have hr1 : C₁.rank (p + 1) = C₂.rank (p + 1) :=
    rank_eq_of_matrixHtpy_of_minimal e c h₁ h₂ (p + 1) (by omega)
  have hunit : ∀ q, c + 1 ≤ q → ∀ hr : C₁.rank q = C₂.rank q,
      ∃ u : (Matrix (Fin (C₁.rank q)) (Fin (C₁.rank q)) R)ˣ,
        (u : Matrix (Fin (C₁.rank q)) (Fin (C₁.rank q)) R) =
          (e.toMat q).submatrix (Fin.cast hr) id := fun q hq hr =>
    ⟨((Matrix.isUnit_iff_isUnit_det _).2
      (isUnit_det_submatrix_of_matrixHtpy_of_minimal e c h₁ q hq hr)).unit, rfl⟩
  obtain ⟨u, hu⟩ := hunit p hp hr0
  obtain ⟨v, hv⟩ := hunit (p + 1) (by omega) hr1
  have hsq : (C₂.d p).submatrix (Fin.cast hr1) (Fin.cast hr0)
      * (e.toMat p).submatrix (Fin.cast hr0) id
      = (e.toMat (p + 1)).submatrix (Fin.cast hr1) id * C₁.d p :=
    calc (C₂.d p).submatrix (Fin.cast hr1) (Fin.cast hr0)
          * (e.toMat p).submatrix (Fin.cast hr0) id
        = (C₂.d p * e.toMat p).submatrix (Fin.cast hr1) id :=
          Matrix.submatrix_mul_equiv (C₂.d p) (e.toMat p) (Fin.cast hr1) (finCongr hr0) id
      _ = (e.toMat (p + 1) * C₁.d p).submatrix (Fin.cast hr1) id :=
          congrArg (Matrix.submatrix · (Fin.cast hr1) id) (e.toMat_comm p)
      _ = (e.toMat (p + 1)).submatrix (Fin.cast hr1) id * C₁.d p :=
          (Matrix.submatrix_mul_equiv (e.toMat (p + 1)) (C₁.d p) (Fin.cast hr1)
            (Equiv.refl _) id).symm
  have hBform : (C₂.d p).submatrix (Fin.cast hr1) (Fin.cast hr0)
      = (v : Matrix _ _ R) * C₁.d p * ((u⁻¹ : _ˣ) : Matrix _ _ R) := by
    rw [hv, ← hsq, ← hu, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [← minorIdeal_submatrix_cast (C₂.d p) hr1 hr0 r, hBform]
  exact minorIdeal_units_mul_mul_units_eq (C₁.d p) v u⁻¹ r

/-- **The Fitting ideals of two homotopy equivalent bounded-above complexes of finite free
modules over a local ring which are minimal above `c` agree in every degree above `c`.**

This is the uniqueness half of the proof of [Stacks, Tag 0ESP]: the ranks agree above `c`, so the
prescribed size of the minors is the same for both, and the differentials in that range are
conjugate by invertible matrices, so the ideals those minors generate agree. -/
theorem fittingIdeal_eq_of_matrixHtpy_of_minimal {C₁ C₂ : FreeData R} (e : MatrixHtpy C₁ C₂)
    (c : ℤ) (h₁ : ∀ i : ℤ, c ≤ i → ∀ a b, C₁.d i a b ∈ IsLocalRing.maximalIdeal R)
    (h₂ : ∀ i : ℤ, c ≤ i → ∀ a b, C₂.d i a b ∈ IsLocalRing.maximalIdeal R)
    (p k : ℤ) (hp : c + 1 ≤ p) : C₁.fittingIdeal p k = C₂.fittingIdeal p k := by
  have htail : C₁.tailAlternatingRank p = C₂.tailAlternatingRank p := by
    rw [tailAlternatingRank_eq_alternatingRankSum, tailAlternatingRank_eq_alternatingRankSum,
      ← alternatingRankSum_eq_of_vanishing C₁.rank_eq_zero_of_top_lt
        (le_max_left C₁.top C₂.top) p,
      ← alternatingRankSum_eq_of_vanishing C₂.rank_eq_zero_of_top_lt
        (le_max_right C₁.top C₂.top) p, alternatingRankSum, alternatingRankSum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [rank_eq_of_matrixHtpy_of_minimal e c h₁ h₂ (p + 1 + j) (by omega)]
  rw [fittingIdeal, fittingIdeal, minorSize, minorSize, htail,
    minorIdeal_d_eq_of_matrixHtpy_of_minimal e c h₁ h₂ p hp]

/-- `Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_matrixHtpy_of_minimal` with the hypothesis
in the form of a homotopy equivalence of the cochain complexes. -/
theorem fittingIdeal_eq_of_homotopyEquiv_of_minimal (C₁ C₂ : FreeData R)
    (hdd₁ : ∀ i : ℤ, C₁.d (i + 1) * C₁.d i = 0) (hdd₂ : ∀ i : ℤ, C₂.d (i + 1) * C₂.d i = 0)
    (e : HomotopyEquiv (C₁.toCochain hdd₁) (C₂.toCochain hdd₂)) (c : ℤ)
    (h₁ : ∀ i : ℤ, c ≤ i → ∀ a b, C₁.d i a b ∈ IsLocalRing.maximalIdeal R)
    (h₂ : ∀ i : ℤ, c ≤ i → ∀ a b, C₂.d i a b ∈ IsLocalRing.maximalIdeal R)
    (p k : ℤ) (hp : c + 1 ≤ p) : C₁.fittingIdeal p k = C₂.fittingIdeal p k :=
  fittingIdeal_eq_of_matrixHtpy_of_minimal (MatrixHtpy.ofHomotopyEquiv e) c h₁ h₂ p k hp

/-- **The Fitting ideals of two bounded-above complexes of finite free modules over a local ring
which are isomorphic in the derived category and minimal above `c` agree in every degree above
`c`.**

This is `Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_matrixHtpy_of_minimal` with the
hypothesis in the form the local description of [Stacks, Tag 0ESP] supplies it: an isomorphism of
`D(R)`. The passage to a homotopy equivalence is `CochainComplex.exists_quasiIso_of_derived_iso`
together with `CochainComplex.IsKProjective.quasiIso_iff`, both available because a bounded-above
complex of finite free modules is K-projective
(`Stacks.FittingComplex.FreeData.isKProjective_toCochain`). -/
theorem fittingIdeal_eq_of_derivedIso_of_minimal [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (C₁ C₂ : FreeData R) (hdd₁ : ∀ i : ℤ, C₁.d (i + 1) * C₁.d i = 0)
    (hdd₂ : ∀ i : ℤ, C₂.d (i + 1) * C₂.d i = 0)
    (e : DerivedCategory.Q.obj (C₁.toCochain hdd₁) ≅ DerivedCategory.Q.obj (C₂.toCochain hdd₂))
    (c : ℤ) (h₁ : ∀ i : ℤ, c ≤ i → ∀ a b, C₁.d i a b ∈ IsLocalRing.maximalIdeal R)
    (h₂ : ∀ i : ℤ, c ≤ i → ∀ a b, C₂.d i a b ∈ IsLocalRing.maximalIdeal R)
    (p k : ℤ) (hp : c + 1 ≤ p) : C₁.fittingIdeal p k = C₂.fittingIdeal p k := by
  have := C₁.isKProjective_toCochain hdd₁
  have := C₂.isKProjective_toCochain hdd₂
  obtain ⟨π, hπ⟩ := CochainComplex.exists_quasiIso_of_derived_iso
    (C₁.toCochain hdd₁) (C₂.toCochain hdd₂) C₁.top e
  obtain ⟨eq, -⟩ := (CochainComplex.IsKProjective.quasiIso_iff π).1 hπ
  exact fittingIdeal_eq_of_homotopyEquiv_of_minimal C₁ C₂ hdd₁ hdd₂ eq c h₁ h₂ p k hp

end LocalRing

end Stacks.FittingComplex.FreeData

end
