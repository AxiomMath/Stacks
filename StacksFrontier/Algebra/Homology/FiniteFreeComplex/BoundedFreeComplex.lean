module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Bounded complexes of finite free modules

This file defines `BoundedFreeComplex`, a complex `0 → R^{n_e} → ⋯ → R^{n_0}` of finite free
modules given by matrices, together with exactness, isomorphisms of complexes and trivial
complexes, and proves the first steps towards splitting off identity blocks over a Noetherian
local ring of depth `0`: unit entries of differentials, invariance of exactness under
isomorphism, and the block form of a complex at an index with a unit entry.
-/

@[expose] public section

open Matrix

variable {R : Type*} [CommRing R]

/-- A complex `0 → R^{n_e} → R^{n_{e-1}} → ⋯ → R^{n_0}` of finite free `R`-modules, as in
Stacks Situation 10.102.1 (tag 00MS). The ranks are given by `n : ℕ → ℕ` with `n i = 0` for
`i > e`, and the differential `R^{n_{i+1}} → R^{n_i}` by the matrix
`φ i : Matrix (Fin (n i)) (Fin (n (i + 1))) R`. -/
@[stacks 00MS, sga "4½ Rapport 4.11"]
structure BoundedFreeComplex (R : Type*) [CommRing R] where
  /-- The top homological degree. -/
  e : ℕ
  /-- The rank in each homological degree. -/
  n : ℕ → ℕ
  /-- The differential out of degree `i + 1` into degree `i`, as a matrix. -/
  φ : ∀ i : ℕ, Matrix (Fin (n i)) (Fin (n (i + 1))) R
  /-- The complex has length `e`: all ranks above `e` vanish. -/
  length : ∀ i, e < i → n i = 0
  /-- Consecutive differentials compose to zero. -/
  isComplex : ∀ i, φ i * φ (i + 1) = 0

namespace BoundedFreeComplex

/-- The complex is exact at `R^{n_e}, …, R^{n_1}`: for every `i ≤ e`, the kernel of `φ i` equals
the image of `φ (i + 1)`. For `i = e` the source of `φ (e + 1)` is zero, so this clause says that
the leading differential `φ e` is injective. -/
def Exact (C : BoundedFreeComplex R) : Prop :=
  ∀ i : ℕ, i ≤ C.e →
    LinearMap.ker (C.φ i).toLin' = LinearMap.range (C.φ (i + 1)).toLin'

/-- The differential `D.φ i` of a complex `D` with the same ranks as `C`, reindexed along
`hn : ∀ i, C.n i = D.n i` to a matrix with `C`'s index types. -/
def transportφ (C D : BoundedFreeComplex R) (hn : ∀ i, C.n i = D.n i) (i : ℕ) :
    Matrix (Fin (C.n i)) (Fin (C.n (i + 1))) R :=
  (D.φ i).submatrix (Fin.cast (hn i)) (Fin.cast (hn (i + 1)))

/-- An **isomorphism of complexes** `C ≅ D`: `C` and `D` have the same ranks, and there is a
degreewise change of basis `P i` with unit determinant such that
`P i * D.φ i = C.φ i * P (i + 1)` for all `i`, where `D.φ i` is reindexed by `transportφ`. -/
structure Iso (C D : BoundedFreeComplex R) where
  /-- An isomorphism preserves ranks in each homological degree. -/
  hn : ∀ i, C.n i = D.n i
  /-- The degreewise change-of-basis matrix on `R^{n_i}`. -/
  P : ∀ i, Matrix (Fin (C.n i)) (Fin (C.n i)) R
  /-- Each change of basis is an `R`-linear isomorphism (invertible matrix). -/
  unit : ∀ i, IsUnit (P i).det
  /-- The squares commute with the differentials. -/
  comm : ∀ i, P i * transportφ C D hn i = C.φ i * P (i + 1)

end BoundedFreeComplex

/-- `M` is a *partial permutation matrix*: each entry is `0` or `1`, with at most one `1`
in each row and at most one `1` in each column. Up to permuting rows and columns these are
exactly the matrices of the form `[[I, 0], [0, 0]]`, i.e. block diagonals consisting of
`1`'s (identity blocks) and `0`'s. -/
def IsPartialPerm {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) : Prop :=
  (∀ i j, M i j = 0 ∨ M i j = 1) ∧
  (∀ i j j', M i j = 1 → M i j' = 1 → j = j') ∧
  (∀ i i' j, M i j = 1 → M i' j = 1 → i = i')

/-- A complex `D` is a **direct sum of trivial complexes** when every differential `D.φ i` is a
partial permutation matrix. Together with `D.φ i * D.φ (i + 1) = 0`, this means that the standard
bases split `D` into identity blocks `R --id--> R` and single copies of `R` with zero
differential. -/
def BoundedFreeComplex.IsTrivial (D : BoundedFreeComplex R) : Prop :=
  ∀ i, IsPartialPerm (D.φ i)

namespace BoundedFreeComplex

/-! ## Splitting off identity blocks

In an exact complex with a nonzero term in positive degree, the differential out of the top
nonzero degree has a unit entry; a change of basis splits off an identity block `R --id--> R`
there, leaving an exact complex of total rank two less.
-/

/-- Over a Noetherian local ring whose maximal ideal `m` is an associated prime of `R`, there is
a nonzero `x ∈ R` with `m * x = 0`. -/
theorem depth_zero_witness [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (IsLocalRing.maximalIdeal R) ∈ associatedPrimes R R) :
    ∃ x : R, x ≠ 0 ∧ ∀ r ∈ IsLocalRing.maximalIdeal R, r * x = 0 := by
  set m := IsLocalRing.maximalIdeal R with hm
  obtain ⟨hp, x, hx⟩ := hdepth
  have hcolon : ∀ r : R, r ∈ (⊥ : Submodule R R).colon {x} ↔ r * x = 0 := by
    intro r
    rw [Submodule.mem_colon]
    constructor
    · intro h
      have := h x (by simp)
      simpa [smul_eq_mul] using this
    · intro h s hs
      simp only [Set.mem_singleton_iff] at hs
      subst hs
      simp [smul_eq_mul, h]
  have hxne : x ≠ 0 := by
    intro h0
    apply hp.ne_top
    rw [hx]
    have : (⊥ : Submodule R R).colon {x} = ⊤ := by
      ext r; simp [h0]
    rw [this, Ideal.radical_top]
  have hfg : m.FG := IsNoetherian.noetherian m
  have hle : m ≤ ((⊥ : Submodule R R).colon {x}).radical := by
    rw [← hx]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle hfg
  have hP : ∃ k, m ^ k ≤ (⊥ : Submodule R R).colon {x} := ⟨n, hn⟩
  have hP0 : ¬ (m ^ 0 ≤ (⊥ : Submodule R R).colon {x}) := by
    intro h
    have h1 : (1:R) ∈ m ^ 0 := by simp
    have := h h1
    rw [hcolon] at this
    simp only [one_mul] at this
    exact hxne this
  classical
  set k := Nat.find hP with hk
  have hkspec : m ^ k ≤ (⊥ : Submodule R R).colon {x} := Nat.find_spec hP
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd (h ▸ hkspec) hP0
    · exact h
  have hprev : ¬ (m ^ (k-1) ≤ (⊥ : Submodule R R).colon {x}) := by
    have : k - 1 < k := by omega
    exact Nat.find_min hP this
  rw [SetLike.not_le_iff_exists] at hprev
  obtain ⟨w, hw, hwc⟩ := hprev
  rw [hcolon] at hwc
  refine ⟨w * x, hwc, ?_⟩
  intro r hr
  have hrw : r * w ∈ m ^ k := by
    have hsplit : m ^ k = m * m ^ (k-1) := by
      conv_lhs => rw [show k = 1 + (k-1) by omega]
      rw [pow_add, pow_one]
    rw [hsplit]
    exact Ideal.mul_mem_mul hr hw
  have hzero : (r * w) * x = 0 := by
    have := hkspec hrw
    rw [hcolon] at this
    exact this
  rw [← mul_assoc]
  exact hzero

/-- If `A` defines an injective map `R^b → R^a` with `b > 0` and `x ≠ 0`, then some entry `A i j`
satisfies `A i j * x ≠ 0`. -/
theorem injective_has_unit_entry {a b : ℕ} (A : Matrix (Fin a) (Fin b) R)
    (hinj : Function.Injective (A.toLin'))
    (x : R) (hx : x ≠ 0) (j0 : Fin b) :
    ∃ i j, A i j * x ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  set v : Fin b → R := fun j => if j = j0 then x else 0 with hv
  have hAv : A.mulVec v = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, hv]
    rw [Finset.sum_eq_single j0]
    · simp [h i j0]
    · intro j _ hj; simp [hj]
    · intro hcon; simp at hcon
  have hker : A.toLin' v = 0 := by rwa [Matrix.toLin'_apply]
  have hv0 : v = 0 := hinj (by rw [hker]; simp : A.toLin' v = A.toLin' 0)
  have : v j0 = 0 := by rw [hv0]; rfl
  simp only [hv, ite_eq_left rfl] at this
  exact hx this

/-- A matrix with no columns defines the zero map, so its range is `⊥`. -/
theorem range_eq_bot_of_zero_source {a b : ℕ} (hb : b = 0) (M : Matrix (Fin a) (Fin b) R) :
    LinearMap.range (M.toLin') = ⊥ := by
  subst hb
  rw [LinearMap.range_eq_bot]
  apply LinearMap.ext
  intro v
  rw [Subsingleton.elim v 0, map_zero, LinearMap.zero_apply]

/-- In an exact complex, if `j ≤ e` and `n (j + 2) = 0`, then `φ j` is injective. -/
theorem top_map_injective (C : BoundedFreeComplex R) (hC : C.Exact)
    (j : ℕ) (hle : j ≤ C.e) (hzero : C.n (j + 2) = 0) :
    Function.Injective (C.φ j).toLin' := by
  rw [← LinearMap.ker_eq_bot, hC j hle, range_eq_bot_of_zero_source hzero]

/-- Over a Noetherian local ring `R` with maximal ideal in `Ass R`, if `C` is exact, `j ≤ e`,
`n (j + 2) = 0` and `n (j + 1) > 0`, then `φ j` has an entry which is a unit. -/
theorem unit_entry_of_exact [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (IsLocalRing.maximalIdeal R) ∈ associatedPrimes R R)
    (C : BoundedFreeComplex R) (hC : C.Exact) (j : ℕ) (hle : j ≤ C.e)
    (hzero : C.n (j + 2) = 0) (hsrc : 0 < C.n (j + 1)) :
    ∃ a b, IsUnit (C.φ j a b) := by
  obtain ⟨x, hxne, hxkill⟩ := depth_zero_witness hdepth
  have hinj := top_map_injective C hC j hle hzero
  obtain ⟨a, b, hab⟩ := injective_has_unit_entry (C.φ j) hinj x hxne ⟨0, hsrc⟩
  refine ⟨a, b, IsLocalRing.notMem_maximalIdeal.mp ?_⟩
  intro hmem
  exact hab (hxkill _ hmem)

/-- `transportφ` of a complex to itself is its differential. -/
theorem transportφ_self (C : BoundedFreeComplex R) (i : ℕ) :
    transportφ C C (fun _ => rfl) i = C.φ i := by
  unfold transportφ
  ext a b
  simp [Matrix.submatrix_apply]

/-- The identity isomorphism `C ≅ C`, given by identity matrices. -/
def Iso.refl (C : BoundedFreeComplex R) : C.Iso C where
  hn := fun _ => rfl
  P := fun _ => 1
  unit := fun _ => by simp
  comm := fun i => by rw [transportφ_self, Matrix.one_mul, Matrix.mul_one]

/-- The composite `C ≅ E` of isomorphisms `C ≅ D` and `D ≅ E`. -/
def Iso.trans {C D E : BoundedFreeComplex R} (f : C.Iso D) (g : D.Iso E) : C.Iso E where
  hn := fun i => (f.hn i).trans (g.hn i)
  P := fun i => f.P i * (g.P i).submatrix (Fin.cast (f.hn i)) (Fin.cast (f.hn i))
  unit := fun i => by
    rw [Matrix.det_mul]
    refine (f.unit i).mul ?_
    rw [show (Fin.cast (f.hn i) : Fin (C.n i) → Fin (D.n i)) = finCongr (f.hn i) from rfl]
    rw [Matrix.det_submatrix_equiv_self]
    exact g.unit i
  comm := fun i => by
    have hf := f.comm i
    have hg := g.comm i
    simp only [transportφ] at *
    have hsplit :
        (E.φ i).submatrix (Fin.cast ((f.hn i).trans (g.hn i)))
            (Fin.cast ((f.hn (i + 1)).trans (g.hn (i + 1))))
          = ((E.φ i).submatrix (Fin.cast (g.hn i)) (Fin.cast (g.hn (i + 1)))).submatrix
              (Fin.cast (f.hn i)) (Fin.cast (f.hn (i + 1))) := by
      rw [Matrix.submatrix_submatrix]; rfl
    rw [hsplit]
    have hcast : ∀ {a b : ℕ} (h : a = b),
        (Fin.cast h : Fin a → Fin b) = ⇑(finCongr h) := fun h => rfl
    simp only [hcast] at hf hg ⊢
    rw [Matrix.mul_assoc (f.P i), Matrix.submatrix_mul_equiv (g.P i) _
        (finCongr (f.hn i)) (finCongr (f.hn i)) (finCongr (f.hn (i + 1))), hg,
        ← Matrix.submatrix_mul_equiv (D.φ i) (g.P (i + 1))
        (finCongr (f.hn i)) (finCongr (f.hn (i + 1))) (finCongr (f.hn (i + 1))),
        ← Matrix.mul_assoc (f.P i), hf, Matrix.mul_assoc]

/-- A matrix with no columns is a partial permutation matrix. -/
theorem isPartialPerm_of_no_cols {a b : ℕ} (hb : b = 0) (M : Matrix (Fin a) (Fin b) R) :
    IsPartialPerm M := by
  subst hb
  exact ⟨fun i j => j.elim0, fun i j => j.elim0, fun i i' j => j.elim0⟩

/-- If every term in degree `≥ 1` vanishes, the complex is a direct sum of trivial
complexes. -/
theorem isTrivial_of_top_zero (C : BoundedFreeComplex R) (h : ∀ i, 1 ≤ i → C.n i = 0) :
    C.IsTrivial :=
  fun i => isPartialPerm_of_no_cols (h (i + 1) (Nat.le_add_left 1 i)) (C.φ i)

/-- The total rank `∑_{i=0}^{e} n_i` of a complex. -/
def totalRank (C : BoundedFreeComplex R) : ℕ := ∑ i ∈ Finset.range (C.e + 1), C.n i

/-- `C` is isomorphic to a complex of the same length and ranks all of whose differentials are
partial permutation matrices. -/
def Trivializable (C : BoundedFreeComplex R) : Prop :=
  ∃ D : BoundedFreeComplex R, ∃ _ : C.Iso D, D.e = C.e ∧ (∀ i, D.n i = C.n i) ∧ D.IsTrivial

/-- If every term in degree `≥ 1` vanishes, `C` is trivializable. -/
theorem trivializable_of_top_zero (C : BoundedFreeComplex R) (h : ∀ i, 1 ≤ i → C.n i = 0) :
    Trivializable C :=
  ⟨C, Iso.refl C, rfl, fun _ => rfl, isTrivial_of_top_zero C h⟩

/-- If `n i > 0` for some `i ≥ 1`, there is an index `t` with `1 ≤ t ≤ e`, `n t > 0` and
`n (t + 1) = 0`. -/
theorem top_index (C : BoundedFreeComplex R) (i : ℕ) (hi : 1 ≤ i) (hpos : 0 < C.n i) :
    ∃ t, 1 ≤ t ∧ t ≤ C.e ∧ 0 < C.n t ∧ C.n (t + 1) = 0 := by
  have hile : i ≤ C.e := by
    by_contra h
    have : C.n i = 0 := C.length i (Nat.lt_of_not_le h)
    omega
  set S := (Finset.range (C.e + 1)).filter (fun k => 0 < C.n k) with hS
  have hiS : i ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpos⟩
  have hSne : S.Nonempty := ⟨i, hiS⟩
  set t := S.max' hSne with ht
  have htS : t ∈ S := Finset.max'_mem S hSne
  rw [hS, Finset.mem_filter, Finset.mem_range] at htS
  have htle : t ≤ C.e := by omega
  have htpos : 0 < C.n t := htS.right
  have h1t : 1 ≤ t := le_trans hi (Finset.le_max' S i hiS)
  refine ⟨t, h1t, htle, htpos, ?_⟩
  by_cases htop : t + 1 ≤ C.e
  · by_contra hne
    have hpos1 : 0 < C.n (t + 1) := Nat.pos_of_ne_zero hne
    have hmem : t + 1 ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hpos1⟩
    have := Finset.le_max' S (t + 1) hmem
    omega
  · exact C.length (t + 1) (by omega)

/-- A matrix `M` with a unit entry can be brought by invertible row and column operations into
block form `diag(1, ψ)`: there are `L`, `K` with unit determinant and a matrix `ψ` such that
`L * M * K` has corner entry `1`, zeros in the rest of its first row and column, and lower-right
block `ψ`. -/
theorem exists_block_form_of_unit_entry {α β : ℕ} (M : Matrix (Fin (α + 1)) (Fin (β + 1)) R)
    (a : Fin (α + 1)) (b : Fin (β + 1)) (hu : IsUnit (M a b)) :
    ∃ (L : Matrix (Fin (α + 1)) (Fin (α + 1)) R) (K : Matrix (Fin (β + 1)) (Fin (β + 1)) R)
      (ψ : Matrix (Fin α) (Fin β) R),
      IsUnit L.det ∧ IsUnit K.det ∧
      (∀ p q, (L * M * K) (Fin.succ p) (Fin.succ q) = ψ p q) ∧
      (L * M * K) 0 0 = 1 ∧
      (∀ q, (L * M * K) 0 (Fin.succ q) = 0) ∧
      (∀ p, (L * M * K) (Fin.succ p) 0 = 0) := by
  classical
  set σ : Equiv.Perm (Fin (α+1)) := Equiv.swap 0 a with hσ
  set τ : Equiv.Perm (Fin (β+1)) := Equiv.swap 0 b with hτ
  set N : Matrix (Fin (α+1)) (Fin (β+1)) R := M.submatrix σ τ with hN
  have hN00 : N 0 0 = M a b := by
    simp [hN, hσ, hτ, Matrix.submatrix_apply, Equiv.swap_apply_left]
  set v : R := ↑(hu.unit⁻¹) with hv
  have hvu : IsUnit v := by rw [hv]; exact Units.isUnit _
  have hvN : v * N 0 0 = 1 := by rw [hN00, hv]; simp [IsUnit.val_inv_mul]
  set D : Matrix (Fin (α+1)) (Fin (α+1)) R :=
    Matrix.diagonal (fun i => if i = 0 then v else 1) with hD
  set E : Matrix (Fin (α+1)) (Fin (α+1)) R :=
    Matrix.of (fun i k => if i = k then (1:R) else if (i ≠ 0 ∧ k = 0) then -(N i 0) else 0) with hE
  set P : Matrix (Fin (α+1)) (Fin (β+1)) R := E * (D * N) with hP
  set F : Matrix (Fin (β+1)) (Fin (β+1)) R :=
    Matrix.of (fun k j => if k = j then (1:R) else if (k = 0 ∧ j ≠ 0) then -(P 0 j) else 0) with hF
  set Pσ : Matrix (Fin (α+1)) (Fin (α+1)) R := (1 : Matrix (Fin (α+1)) (Fin (α+1)) R).submatrix σ
      id with hPσ
  set Qτ : Matrix (Fin (β+1)) (Fin (β+1)) R := (1 : Matrix (Fin (β+1)) (Fin (β+1)) R).submatrix id
      τ with hQτ
  have hDN : ∀ i j, (D * N) i j = (if i = 0 then v else 1) * N i j := by
    intro i j; rw [hD, Matrix.diagonal_mul]
  have hP0 : ∀ j, P 0 j = v * N 0 j := by
    intro j
    rw [hP, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (α+1))]
    · rw [hE]; simp [hDN]
    · intro k _ hk; rw [hE]; simp [hk, (Ne.symm hk)]
    · intro h; simp at h
  have hP00 : P 0 0 = 1 := by rwa [hP0]
  have hPi0 : ∀ i, i ≠ 0 → P i 0 = 0 := by
    intro i hi
    rw [hP, Matrix.mul_apply]
    rw [Finset.sum_eq_add_of_mem i 0 (Finset.mem_univ _) (Finset.mem_univ _) hi ?_]
    · rw [hE]; rw [hDN, hDN]
      simp only [Matrix.of_apply, hi, ne_eq, not_false_eq_true, true_and, ite_true, ite_false,
        one_mul]
      linear_combination -N i 0 * hvN
    · intro k _ ⟨hki, hk0⟩
      rw [hE]; simp only [Matrix.of_apply]
      rw [ite_eq_right (fun h => hki h.symm), ite_eq_right (by rintro ⟨_, h⟩; exact hk0 h)]
      ring
  have hcol0 : ∀ i, (P * F) i 0 = P i 0 := by
    intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (β+1))]
    · rw [hF]; simp
    · intro k _ hk; rw [hF]; simp only [Matrix.of_apply]; rw [ite_eq_right hk]; simp
    · intro h; simp at h
  have hrow : ∀ i j, j ≠ 0 → (P * F) i j = P i j - P i 0 * P 0 j := by
    intro i j hj
    rw [Matrix.mul_apply, Finset.sum_eq_add_of_mem j 0 (Finset.mem_univ _) (Finset.mem_univ _) hj
        ?_]
    · rw [hF]; simp only [Matrix.of_apply]
      have h0j : (0 : Fin (β+1)) ≠ j := fun h => hj h.symm
      simp only [ite_eq_left, ite_eq_right h0j, hj, ne_eq, not_false_eq_true, and_self]
      ring
    · intro k _ ⟨hkj, hk0⟩
      rw [hF]; simp only [Matrix.of_apply]
      rw [ite_eq_right hkj, ite_eq_right (by rintro ⟨h, _⟩; exact hk0 h)]
      ring
  have hEdet : E.det = 1 := by
    rw [hE, Matrix.det_of_isLowerTriangular]
    · simp
    · intro i j hij
      simp only [Matrix.of_apply]
      have hlt : i < j := hij
      have h1 : i ≠ j := ne_of_lt hlt
      have h2 : j ≠ 0 := by rintro rfl; simp at hlt
      simp [h1, h2]
  have hFdet : F.det = 1 := by
    rw [hF, Matrix.det_of_isUpperTriangular]
    · simp
    · intro i j hij
      simp only [Matrix.of_apply]
      have hlt : j < i := hij
      have h1 : i ≠ j := (ne_of_lt hlt).symm
      have h2 : i ≠ 0 := by rintro rfl; simp at hlt
      rw [ite_eq_right h1, ite_eq_right (by rintro ⟨h,_⟩; exact h2 h)]
  have hEq : E * D * Pσ * M * (Qτ * F) = P * F := by
    have hPMQ : Pσ * M * Qτ = N := by
      rw [hPσ, hQτ, hN]; ext i j
      simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply]
    have h2 : P * F = E * D * (Pσ * M * Qτ) * F := by
      rw [hPMQ, hP, Matrix.mul_assoc E D N]
    rw [h2]; simp only [Matrix.mul_assoc]
  refine ⟨E * D * Pσ, Qτ * F,
    fun p q => (E * D * Pσ * M * (Qτ * F)) (Fin.succ p) (Fin.succ q), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hEdet, one_mul]
    apply IsUnit.mul
    · rw [hD, Matrix.det_diagonal, Finset.prod_ite_eq']; simpa using hvu
    · rw [hPσ, Matrix.det_permute]; simp only [det_one, mul_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h|h <;> simp [h]
  · rw [Matrix.det_mul, hFdet, mul_one]
    rw [hQτ, Matrix.det_permute']; simp only [det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h|h <;> simp [h]
  · intro p q; rfl
  · rw [hEq, hcol0, hP00]
  · intro q; rw [hEq, hrow _ _ (Fin.succ_ne_zero q), hP00]; ring
  · intro p; rw [hEq, hcol0, hPi0 _ (Fin.succ_ne_zero p)]

/-- The inverse `D ≅ C` of an isomorphism `C ≅ D`. -/
noncomputable def Iso.symm {C D : BoundedFreeComplex R} (f : C.Iso D) : D.Iso C := by
  refine { hn := fun i => (f.hn i).symm,
           P := fun i => ((f.P i)⁻¹).submatrix (Fin.cast (f.hn i).symm) (Fin.cast (f.hn i).symm),
           unit := ?_, comm := ?_ }
  · intro i
    rw [show (Fin.cast (f.hn i).symm : Fin (D.n i) → Fin (C.n i)) = finCongr (f.hn i).symm from rfl]
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_nonsing_inv]
    exact (f.unit i).ringInverse
  · intro i
    have hf := f.comm i
    simp only [transportφ] at hf ⊢
    have hcast : ∀ {a b : ℕ} (h : a = b),
        (Fin.cast h : Fin a → Fin b) = ⇑(finCongr h) := fun h => rfl
    simp only [hcast] at hf ⊢
    have hu := f.unit i
    have key : (D.φ i).submatrix (finCongr (f.hn i)) (finCongr (f.hn (i + 1)))
        = (f.P i)⁻¹ * (C.φ i * f.P (i + 1)) := by
      rw [← hf, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [Matrix.submatrix_mul_equiv ((f.P i)⁻¹) (C.φ i)
        (finCongr (f.hn i).symm) (finCongr (f.hn i).symm) (finCongr (f.hn (i + 1)).symm)]
    have hu1 := f.unit (i + 1)
    have hDφ : D.φ i
        = ((f.P i)⁻¹ * (C.φ i * f.P (i + 1))).submatrix
            (finCongr (f.hn i).symm) (finCongr (f.hn (i + 1)).symm) := by
      rw [← key, Matrix.submatrix_submatrix]
      ext a b
      simp [Matrix.submatrix_apply]
    rw [hDφ, Matrix.submatrix_mul_equiv ((f.P i)⁻¹ * (C.φ i * f.P (i + 1))) ((f.P (i + 1))⁻¹)
        (finCongr (f.hn i).symm) (finCongr (f.hn (i + 1)).symm) (finCongr (f.hn (i + 1)).symm)]
    congr 1
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one]

/-- Exactness is preserved by isomorphisms of complexes of the same length. -/
theorem iso_exact {C D : BoundedFreeComplex R} (f : C.Iso D) (he : D.e = C.e)
    (hC : C.Exact) : D.Exact := by
  have hcast : ∀ {a b : ℕ} (h : a = b),
      (Fin.cast h : Fin a → Fin b) = ⇑(finCongr h) := fun _ => rfl
  have hDφ : ∀ j, D.φ j
      = ((f.P j)⁻¹ * C.φ j * f.P (j + 1)).submatrix
          (Fin.cast (f.hn j).symm) (Fin.cast (f.hn (j + 1)).symm) := by
    intro j
    have hf := f.comm j
    simp only [transportφ] at hf
    simp only [hcast] at hf
    have hu := f.unit j
    have key : (D.φ j).submatrix (finCongr (f.hn j)) (finCongr (f.hn (j + 1)))
        = (f.P j)⁻¹ * (C.φ j * f.P (j + 1)) := by
      rw [← hf, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [Matrix.mul_assoc, ← key, Matrix.submatrix_submatrix]
    ext a b
    simp [Matrix.submatrix_apply]
  let : ∀ j, Invertible (f.P j) := fun j => Matrix.invertibleOfIsUnitDet _ (f.unit j)
  set β : ∀ j, (Fin (D.n j) → R) ≃ₗ[R] (Fin (C.n j) → R) :=
    fun j => (LinearEquiv.funCongrLeft R R (finCongr (f.hn j))) ≪≫ₗ
      ((f.P j).toLinearEquiv' (Matrix.invertibleOfIsUnitDet _ (f.unit j))) with hβ
  have hβfwd : ∀ k, (↑(β k) : (Fin (D.n k) → R) →ₗ[R] (Fin (C.n k) → R))
      = (f.P k).toLin'.comp (LinearMap.funLeft R R (⇑(finCongr (f.hn k)))) := by
    intro k
    rw [hβ]
    apply LinearMap.ext; intro x
    rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply,
       show ((f.P k).toLinearEquiv' (Matrix.invertibleOfIsUnitDet _ (f.unit k)))
              ((LinearEquiv.funCongrLeft R R (finCongr (f.hn k))) x)
          = (↑((f.P k).toLinearEquiv' (Matrix.invertibleOfIsUnitDet _ (f.unit k))) :
              (Fin (C.n k) → R) →ₗ[R] _) ((LinearEquiv.funCongrLeft R R (finCongr (f.hn k))) x)
                  from rfl,
       Matrix.toLinearEquiv'_apply]
    simp [LinearEquiv.funCongrLeft, LinearMap.funLeft]
  have hβsymm : ∀ k, (↑(β k).symm : (Fin (C.n k) → R) →ₗ[R] (Fin (D.n k) → R))
      = (LinearMap.funLeft R R (⇑(finCongr (f.hn k)).symm)).comp ((f.P k)⁻¹.toLin') := by
    intro k
    rw [hβ]
    apply LinearMap.ext; intro x
    rw [LinearEquiv.coe_coe, LinearEquiv.symm_trans_apply,
       show ((f.P k).toLinearEquiv' (Matrix.invertibleOfIsUnitDet _ (f.unit k))).symm x
          = (↑((f.P k).toLinearEquiv' (Matrix.invertibleOfIsUnitDet _ (f.unit k))).symm :
              (Fin (C.n k) → R) →ₗ[R] _) x from rfl,
       Matrix.toLinearEquiv'_symm_apply, Matrix.invOf_eq_nonsing_inv]
    simp [LinearEquiv.funCongrLeft, LinearMap.funLeft]
  have hconj : ∀ j, (D.φ j).toLin'
      = (↑(β j).symm : (Fin (C.n j) → R) →ₗ[R] _) ∘ₗ (C.φ j).toLin'
        ∘ₗ (↑(β (j + 1)) : _ →ₗ[R] _) := by
    intro j
    rw [hDφ j]
    rw [show (Fin.cast (f.hn j).symm : Fin (D.n j) → Fin (C.n j)) = ⇑(finCongr (f.hn j).symm) from
        rfl]
    rw [show (Fin.cast (f.hn (j + 1)).symm : Fin (D.n (j + 1)) → Fin (C.n (j + 1)))
        = ⇑(finCongr (f.hn (j + 1)).symm) from rfl]
    rw [Matrix.toLin'_submatrix, Matrix.toLin'_mul, Matrix.toLin'_mul, hβsymm j, hβfwd (j + 1)]
    rw [show ((finCongr (f.hn (j + 1)).symm).symm : Fin (C.n (j+1)) ≃ Fin (D.n (j+1)))
          = finCongr (f.hn (j + 1)) from by ext a; simp]
    rfl
  intro i hi
  have hi' : i ≤ C.e := by rwa [he] at hi
  rw [hconj i, hconj (i + 1), LinearEquiv.ker_comp, LinearMap.ker_comp]
  rw [← LinearMap.comp_assoc, LinearEquiv.range_comp, LinearMap.range_comp]
  rw [hC i hi', Submodule.comap_equiv_eq_map_symm]

/-- If `C ≅ D` with `D` of the same length as `C` and `D` trivializable, then `C` is
trivializable. -/
theorem iso_trivializable {C D : BoundedFreeComplex R} (f : C.Iso D) (he : D.e = C.e)
    (hD : Trivializable D) : Trivializable C := by
  obtain ⟨E, g, hEe, hEn, hEt⟩ := hD
  exact ⟨E, f.trans g, hEe.trans he, fun i => (hEn i).trans (f.hn i).symm, hEt⟩

/-- Let `C` be an exact complex over a Noetherian local ring with maximal ideal in `Ass R`, and
let `t` be an index with `1 ≤ t ≤ e`, `n t > 0` and `n (t + 1) = 0`. Then `C` is isomorphic to an
exact complex `C₁` with the same length and ranks in which `C₁.φ (t - 1)` has block form
`diag(1, ψ)`; if moreover `t ≥ 2`, the column of `C₁.φ (t - 2)` at the pivot index vanishes. -/
theorem exists_iso_blockDiag_one [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (IsLocalRing.maximalIdeal R) ∈ associatedPrimes R R)
    (C : BoundedFreeComplex R) (hC : C.Exact)
    (t : ℕ) (ht1 : 1 ≤ t) (hte : t ≤ C.e) (htpos : 0 < C.n t) (htzero : C.n (t + 1) = 0) :
    ∃ (C₁ : BoundedFreeComplex R) (_ : C.Iso C₁),
      C₁.e = C.e ∧ (∀ i, C₁.n i = C.n i) ∧ C₁.totalRank = C.totalRank ∧ C₁.Exact ∧
      ∃ (α β : ℕ) (hα : C₁.n (t - 1) = α + 1) (hβ : C₁.n (t - 1 + 1) = β + 1)
        (ψ : Matrix (Fin α) (Fin β) R),
        C₁.φ (t - 1) (Fin.cast hα.symm 0) (Fin.cast hβ.symm 0) = 1 ∧
        (∀ q : Fin β, C₁.φ (t - 1) (Fin.cast hα.symm 0) (Fin.cast hβ.symm q.succ) = 0) ∧
        (∀ p : Fin α, C₁.φ (t - 1) (Fin.cast hα.symm p.succ) (Fin.cast hβ.symm 0) = 0) ∧
        (∀ (p : Fin α) (q : Fin β),
          C₁.φ (t - 1) (Fin.cast hα.symm p.succ) (Fin.cast hβ.symm q.succ) = ψ p q) ∧
        ∀ (_ : 2 ≤ t), ∃ hα2 : C₁.n (t - 2 + 1) = α + 1,
          (∀ p, C₁.φ (t - 2) p (Fin.cast hα2.symm 0) = 0) := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hse : s ≤ C.e := by omega
  have hzero' : C.n (s + 2) = 0 := htzero
  have hsrc' : 0 < C.n (s + 1) := htpos
  obtain ⟨a, b, hab⟩ := unit_entry_of_exact hdepth C hC s hse hzero' hsrc'
  have hαpos : 0 < C.n s := Fin.pos_iff_nonempty.mpr ⟨a⟩
  have hβpos : 0 < C.n (s + 1) := Fin.pos_iff_nonempty.mpr ⟨b⟩
  set α := C.n s - 1 with hαdef
  set β := C.n (s + 1) - 1 with hβdef
  have hα : C.n s = α + 1 := by omega
  have hβ : C.n (s + 1) = β + 1 := by omega
  set M : Matrix (Fin (α + 1)) (Fin (β + 1)) R :=
    (C.φ s).submatrix (Fin.cast hα.symm) (Fin.cast hβ.symm) with hM
  have hMab : M (Fin.cast hα a) (Fin.cast hβ b) = C.φ s a b := by
    simp [hM, Matrix.submatrix_apply]
  have hu : IsUnit (M (Fin.cast hα a) (Fin.cast hβ b)) := by rwa [hMab]
  obtain ⟨L, K, ψ, hLdet, hKdet, hψ, hcorner, hrow0, hcol0⟩ :=
    exists_block_form_of_unit_entry M (Fin.cast hα a) (Fin.cast hβ b) hu
  set L' : Matrix (Fin (C.n s)) (Fin (C.n s)) R :=
    L.submatrix (Fin.cast hα) (Fin.cast hα) with hL'
  set K' : Matrix (Fin (C.n (s + 1))) (Fin (C.n (s + 1))) R :=
    K.submatrix (Fin.cast hβ) (Fin.cast hβ) with hK'
  have hL'det : IsUnit L'.det := by
    rwa [hL', show (Fin.cast hα : Fin (C.n s) → Fin (α+1)) = finCongr hα from rfl,
        Matrix.det_submatrix_equiv_self]
  have hK'det : IsUnit K'.det := by
    rwa [hK', show (Fin.cast hβ : Fin (C.n (s+1)) → Fin (β+1)) = finCongr hβ from rfl,
        Matrix.det_submatrix_equiv_self]
  have hL'invdet : IsUnit (L'⁻¹).det := by
    rw [Matrix.det_nonsing_inv]; exact hL'det.ringInverse
  set P : ∀ i, Matrix (Fin (C.n i)) (Fin (C.n i)) R :=
    Function.update (Function.update (fun i => (1 : Matrix (Fin (C.n i)) (Fin (C.n i)) R)) s L'⁻¹)
      (s + 1) K' with hP
  have hPunit : ∀ i, IsUnit (P i).det := by
    intro i
    rw [hP]
    by_cases h1 : i = s + 1
    · subst h1; rwa [Function.update_self]
    · rw [Function.update_of_ne h1]
      by_cases h2 : i = s
      · subst h2; rwa [Function.update_self]
      · rw [Function.update_of_ne h2]; simp
  have hPs : P s = L'⁻¹ := by
    rw [hP, Function.update_of_ne (by omega : s ≠ s + 1), Function.update_self]
  have hPs1 : P (s + 1) = K' := by rw [hP, Function.update_self]
  set C₁ : BoundedFreeComplex R :=
    { e := C.e
      n := C.n
      φ := fun i => (P i)⁻¹ * C.φ i * P (i + 1)
      length := C.length
      isComplex := by
        intro i
        have h1 : (P (i + 1)) * (P (i + 1))⁻¹ = 1 :=
          Matrix.mul_nonsing_inv _ (hPunit (i + 1))
        calc ((P i)⁻¹ * C.φ i * P (i + 1)) * ((P (i + 1))⁻¹ * C.φ (i + 1) * P (i + 1 + 1))
            = (P i)⁻¹ * C.φ i * ((P (i + 1)) * (P (i + 1))⁻¹) * C.φ (i + 1) * P (i + 1 + 1) := by
              simp only [Matrix.mul_assoc]
          _ = (P i)⁻¹ * (C.φ i * C.φ (i + 1)) * P (i + 1 + 1) := by
              rw [h1]; simp only [Matrix.mul_assoc, Matrix.mul_one]
          _ = 0 := by rw [C.isComplex i]; simp } with hC₁
  have htrans : ∀ i, transportφ C C₁ (fun _ => rfl) i = C₁.φ i := by
    intro i; unfold transportφ; ext x y; simp [Matrix.submatrix_apply]
  set f : C.Iso C₁ :=
    { hn := fun _ => rfl
      P := P
      unit := hPunit
      comm := by
        intro i
        rw [htrans]
        show P i * ((P i)⁻¹ * C.φ i * P (i + 1)) = C.φ i * P (i + 1)
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
            Matrix.mul_nonsing_inv _ (hPunit i), Matrix.one_mul] } with hf
  have hC₁exact : C₁.Exact := iso_exact f rfl hC
  have hφs : C₁.φ s = L' * C.φ s * K' := by
    show (P s)⁻¹ * C.φ s * P (s + 1) = L' * C.φ s * K'
    rw [hPs, hPs1, Matrix.nonsing_inv_nonsing_inv _ hL'det]
  have hMsub : C.φ s = M.submatrix (Fin.cast hα) (Fin.cast hβ) := by
    rw [hM, Matrix.submatrix_submatrix]
    ext x y; simp [Matrix.submatrix_apply]
  have hφs2 : C₁.φ s = (L * M * K).submatrix (Fin.cast hα) (Fin.cast hβ) := by
    rw [hφs, hL', hK', hMsub]
    rw [show (Fin.cast hα : Fin (C.n s) → Fin (α+1)) = ⇑(finCongr hα) from rfl,
        show (Fin.cast hβ : Fin (C.n (s+1)) → Fin (β+1)) = ⇑(finCongr hβ) from rfl]
    rw [Matrix.submatrix_mul_equiv L M (finCongr hα) (finCongr hα) (finCongr hβ),
        Matrix.submatrix_mul_equiv (L * M) K (finCongr hα) (finCongr hβ) (finCongr hβ)]
  have heval : ∀ (u : Fin (α + 1)) (v : Fin (β + 1)),
      C₁.φ s (Fin.cast hα.symm u) (Fin.cast hβ.symm v) = (L * M * K) u v := by
    intro u v
    rw [hφs2, Matrix.submatrix_apply, Fin.cast_cast, Fin.cast_cast, Fin.cast_eq_self,
      Fin.cast_eq_self]
  refine ⟨C₁, f, rfl, fun _ => rfl, rfl, hC₁exact, α, β, hα, hβ, ψ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (heval _ _).trans hcorner
  · exact fun q => (heval _ _).trans (hrow0 q)
  · exact fun p => (heval _ _).trans (hcol0 p)
  · exact fun p q => (heval _ _).trans (hψ p q)
  · intro h2t
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hα2 : C₁.n (s' + 1 + 1 - 2 + 1) = α + 1 := hα
    refine ⟨hα2, ?_⟩
    intro p
    have hcomm := C₁.isComplex s'
    have h0 := congrFun (congrFun hcomm p) (Fin.cast hβ.symm 0)
    rw [Matrix.mul_apply] at h0
    simp only [Matrix.zero_apply] at h0
    rw [Finset.sum_eq_single (Fin.cast hα.symm 0)] at h0
    · rw [heval, hcorner, mul_one] at h0
      exact h0
    · intro x _ hx
      obtain ⟨y, rfl⟩ : ∃ y, x = Fin.cast hα.symm y := ⟨Fin.cast hα x, by simp⟩
      refine mul_eq_zero_of_right _ ?_
      cases y using Fin.cases with
      | zero => exact absurd rfl hx
      | succ y => rw [heval]; exact hcol0 y
    · exact fun h => absurd (Finset.mem_univ _) h

/-- Reindexing the columns of a matrix by an equivalence does not change the range. -/
theorem range_reindex_col {m a a' : ℕ} (X : Matrix (Fin m) (Fin a) R) (e : Fin a' ≃ Fin a) :
    LinearMap.range (X.submatrix id e).toLin' = LinearMap.range X.toLin' := by
  rw [show e = ⇑(e : Fin a' ≃ Fin a) from rfl, Matrix.toLin'_submatrix]
  rw [show (LinearMap.funLeft R R (id : Fin m → Fin m)) = LinearMap.id from by
        ext f j; simp [LinearMap.funLeft]]
  rw [LinearMap.id_comp]
  rw [show (LinearMap.funLeft R R ⇑e.symm)
      = ((LinearEquiv.funCongrLeft R R e.symm : (Fin a' → R) ≃ₗ[R] (Fin a → R)) : (Fin a' → R)
          →ₗ[R] _) from rfl]
  rw [LinearEquiv.range_comp]

/-- If column `0` of `B` vanishes, dropping it does not change the range of the map. -/
theorem range_drop_zero_col {m β : ℕ} (B : Matrix (Fin m) (Fin (β + 1)) R)
    (hcol : ∀ p, B p 0 = 0) :
    LinearMap.range (B.submatrix id Fin.succ).toLin' = LinearMap.range B.toLin' := by
  apply le_antisymm
  · rw [LinearMap.range_le_iff_comap, eq_top_iff]
    intro v _
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨Fin.cons 0 v, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    funext p
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fin.sum_univ_succ]
    simp only [Matrix.submatrix_apply, id_eq, Fin.cons_zero, Fin.cons_succ, hcol p, zero_mul,
      zero_add]
  · rw [LinearMap.range_le_iff_comap, eq_top_iff]
    intro v _
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨Fin.tail v, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    funext p
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fin.sum_univ_succ]
    rw [hcol p, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro q _
    simp [Matrix.submatrix_apply, Fin.tail]

/-- Dropping pivot row `0` of the left factor and the pivot row/column `0` of the right
factor (whose row `0` vanishes off the corner) preserves a zero product. -/
theorem peel_drop_both {a α β : ℕ}
    (A : Matrix (Fin a) (Fin (α + 1)) R) (B : Matrix (Fin (α + 1)) (Fin (β + 1)) R)
    (hAB : A * B = 0) (hrow : ∀ q : Fin β, B 0 q.succ = 0) :
    (A.submatrix id Fin.succ) * (B.submatrix Fin.succ Fin.succ) = 0 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.zero_apply]
  have hkey := congrFun (congrFun hAB p) q.succ
  rw [Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_succ, hrow q, mul_zero, zero_add] at hkey
  simpa [Matrix.submatrix_apply] using hkey

/-- A submatrix of a partial permutation matrix along injective row and column selections is
again a partial permutation matrix. -/
theorem isPartialPerm_submatrix {a b a' b' : ℕ} (M : Matrix (Fin a) (Fin b) R)
    (e : Fin a' ≃ Fin a) (e' : Fin b' ≃ Fin b) (hM : IsPartialPerm M) :
    IsPartialPerm (M.submatrix e e') := by
  obtain ⟨h01, hrow, hcol⟩ := hM
  refine ⟨fun i j => h01 _ _, ?_, ?_⟩
  · intro i j j' hj hj'
    simp only [Matrix.submatrix_apply] at hj hj'
    exact e'.injective (hrow _ _ _ hj hj')
  · intro i i' j hi hi'
    simp only [Matrix.submatrix_apply] at hi hi'
    exact e.injective (hcol _ _ _ hi hi')

end BoundedFreeComplex

end
