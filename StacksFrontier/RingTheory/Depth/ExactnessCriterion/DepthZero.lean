module


public import StacksFrontier.LinearAlgebra.Matrix.DeterminantalRank
public import StacksFrontier.RingTheory.Depth.Defs.Defs
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Tactic.Monotonicity.Lemmas
import StacksFrontier.Algebra.Homology.FiniteFreeComplex
import StacksFrontier.RingTheory.Depth.Acyclicity
import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.RingTheory.Module.IdealSmulTop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Buchsbaum–Eisenbud exactness criterion: exact complexes over a depth-zero ring

A step of the forward direction of the Buchsbaum–Eisenbud exactness criterion
(`LinearMap.injective_and_exact_iff_forall_rank_eq_and_le_depth_minors`). Over a local
Noetherian ring of depth `0`, an exact complex `0 → S^{n_{e+1}} → ⋯ → S^{n_0}` of finite free
modules has, at every spot `k ≤ e`, rank the alternating sum `n_{k+1} - n_{k+2} + ⋯ ± n_{e+1}`
and unit determinantal ideal. The complex is conjugate to one whose differentials are partial
permutation matrices (`IsPartialPerm`), whose ranks and determinantal ideals are computed
directly. The file also shows that a complex of finite free modules stays exact after localizing
at a prime, and truncates a complex to the degrees its exactness data cover.

## References

* [StacksProject 00N1](https://stacks.math.columbia.edu/tag/00N1)
* D. A. Buchsbaum and D. Eisenbud, *What makes a complex exact?*, Corollary 1

## Tags

exact complex, finite free module, rank, minor, depth, regular sequence
-/

@[expose] public section

namespace Stacks.Depth.BuchsbaumEisenbud

open RingTheory.Sequence Stacks.DeterminantalRank

/-! ## Partial permutation matrices: rank and minors -/

section PartialPerm

open StacksComplex

variable {R : Type*} [CommRing R] {a b c : ℕ}

open Classical in
/-- The columns of a matrix that contain the entry `1`. For a partial permutation matrix
(`IsPartialPerm`) these index the identity blocks, and there are `rank M` of them. -/
private noncomputable def pivotCols (M : Matrix (Fin a) (Fin b) R) : Finset (Fin b) :=
  Finset.univ.filter fun j => ∃ i, M i j = 1

private lemma mem_pivotCols {M : Matrix (Fin a) (Fin b) R} {j : Fin b} :
    j ∈ pivotCols M ↔ ∃ i, M i j = 1 := by
  classical
  simp [pivotCols]

/-- The transpose of a partial permutation matrix is one: the three conditions are symmetric in
rows and columns. -/
private lemma isPartialPerm_transpose {M : Matrix (Fin a) (Fin b) R} (hM : IsPartialPerm M) :
    IsPartialPerm M.transpose :=
  ⟨fun i j => hM.1 j i, fun i j j' h h' => hM.2.2 j j' i h h',
    fun i i' j h h' => hM.2.1 j i i' h h'⟩

/-- A column of a `0/1` matrix containing no `1` is zero. -/
private lemma eq_zero_of_notMem_pivotCols_of_isPartialPerm {M : Matrix (Fin a) (Fin b) R}
    (hM : IsPartialPerm M) {j : Fin b} (hj : j ∉ pivotCols M) (i : Fin a) : M i j = 0 :=
  (hM.1 i j).resolve_right fun h => hj (mem_pivotCols.mpr ⟨i, h⟩)

/-- **A partial permutation matrix carries an identity minor of size the number of its pivot
columns.** Selecting the pivot columns and, for each, the unique row in which it has its `1`,
cuts out the identity matrix. -/
private lemma exists_submatrix_eq_one_of_isPartialPerm {M : Matrix (Fin a) (Fin b) R}
    (hM : IsPartialPerm M) :
    ∃ (ρ : Fin (pivotCols M).card → Fin a) (γ : Fin (pivotCols M).card → Fin b),
      M.submatrix ρ γ = 1 := by
  classical
  set γ : Fin (pivotCols M).card → Fin b := fun t => ((pivotCols M).equivFin.symm t : Fin b)
    with hγ
  have hγinj : Function.Injective γ := fun t t' h =>
    (pivotCols M).equivFin.symm.injective (Subtype.ext h)
  have hex : ∀ t, ∃ i, M i (γ t) = 1 := fun t =>
    mem_pivotCols.mp ((pivotCols M).equivFin.symm t).2
  choose ρ hρ using hex
  refine ⟨ρ, γ, ?_⟩
  ext s t
  rcases eq_or_ne s t with rfl | hst
  · simpa [Matrix.one_apply_eq] using hρ s
  · have hzero : M (ρ s) (γ t) = 0 :=
      (hM.1 (ρ s) (γ t)).resolve_right fun h =>
        hst (hγinj (hM.2.1 (ρ s) (γ s) (γ t) (hρ s) h))
    simpa [Matrix.one_apply_ne hst] using hzero

/-- **The rank of a partial permutation matrix is the number of its pivot columns.** The
identity minor of that size is nonzero, and a larger square minor either repeats a column or
selects a column with no `1`, which is a zero column; either way its determinant vanishes. -/
private lemma rank_eq_card_pivotCols [Nontrivial R] {M : Matrix (Fin a) (Fin b) R}
    (hM : IsPartialPerm M) : rank M = (pivotCols M).card := by
  classical
  obtain ⟨ρ, γ, hsub⟩ := exists_submatrix_eq_one_of_isPartialPerm hM
  refine le_antisymm (StacksComplex.rank_le M fun r hr => ?_)
    (StacksComplex.le_rank M ⟨ρ, γ, by rw [hsub, Matrix.det_one]; exact one_ne_zero⟩)
  obtain ⟨ρ', γ', hdet⟩ := hr
  by_contra hlt
  push Not at hlt
  by_cases hinj : Function.Injective γ'
  · have hout : ∃ t, γ' t ∉ pivotCols M := by
      by_contra hall
      push Not at hall
      have hcard := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin r))) γ'
        (fun t _ => hall t) hinj.injOn
      simp only [Finset.card_univ, Fintype.card_fin] at hcard
      omega
    obtain ⟨t, ht⟩ := hout
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero t fun i =>
      eq_zero_of_notMem_pivotCols_of_isPartialPerm hM ht (ρ' i))
  · obtain ⟨t, t', hval, hne⟩ := Function.not_injective_iff.mp hinj
    exact hdet (Matrix.det_zero_of_column_eq hne fun k => by
      simp only [Matrix.submatrix_apply, hval])

/-- **The determinantal ideal of a partial permutation matrix is the unit ideal**: the identity
minor of `exists_submatrix_eq_one_of_isPartialPerm` has size the rank and determinant `1`. -/
private lemma minorIdeal_eq_top_of_isPartialPerm [Nontrivial R] {M : Matrix (Fin a) (Fin b) R}
    (hM : IsPartialPerm M) : minorIdeal M = ⊤ := by
  obtain ⟨ρ, γ, hsub⟩ := exists_submatrix_eq_one_of_isPartialPerm hM
  have hr : rank M = (pivotCols M).card := rank_eq_card_pivotCols hM
  refine Ideal.eq_top_of_isUnit_mem _ (?_ : (1 : R) ∈ minorIdeal M) isUnit_one
  refine Ideal.subset_span ⟨fun t => ρ (finCongr hr t), fun t => γ (finCongr hr t), ?_⟩
  have hcast : M.submatrix (fun t => ρ (finCongr hr t)) (fun t => γ (finCongr hr t))
      = (M.submatrix ρ γ).submatrix (finCongr hr) (finCongr hr) := rfl
  rw [hcast, Matrix.det_submatrix_equiv_self, hsub, Matrix.det_one]

/-- Transposing a matrix does not change its rank: the minors of the transpose are the
transposes of the minors. -/
private lemma rank_transpose (M : Matrix (Fin a) (Fin b) R) :
    rank M.transpose = rank M := by
  have hset : rankSet M.transpose = rankSet M := by
    ext r
    constructor
    · rintro ⟨ρ, γ, h⟩
      refine ⟨γ, ρ, fun h0 => h ?_⟩
      rw [← Matrix.transpose_submatrix, Matrix.det_transpose, h0]
    · rintro ⟨ρ, γ, h⟩
      refine ⟨γ, ρ, fun h0 => h ?_⟩
      rw [← Matrix.det_transpose, Matrix.transpose_submatrix, h0]
  rw [rank_eq_sSup, rank_eq_sSup, hset]

/-- **Exactness pins the pivot columns.** For two consecutive partial permutation matrices of a
complex which is exact in the middle, a basis vector of the middle module is either the source of
an identity block of `M` or the target of one of `N`, never both: the pivot columns of `M` are the
complement of the pivot rows of `N`.

Not both, because a column of `M` with a `1` in row `i` and a row of `N` with a `1` in column `k`
would make the entry `(i, k)` of `M * N` equal to `1`. At least one, because a basis vector
spanning a zero column of `M` lies in `Ker M`, hence in `Im N`, and a coordinate of a vector in
`Im N` can only be nonzero in a pivot row of `N`. -/
private lemma pivotCols_compl_eq [Nontrivial R] {M : Matrix (Fin a) (Fin b) R}
    {N : Matrix (Fin b) (Fin c) R} (hM : IsPartialPerm M) (hN : IsPartialPerm N)
    (hMN : M * N = 0) (hex : LinearMap.ker M.mulVecLin ≤ LinearMap.range N.mulVecLin) :
    pivotCols N.transpose = (pivotCols M)ᶜ := by
  classical
  ext j
  simp only [Finset.mem_compl]
  constructor
  · rintro hj hjM
    obtain ⟨k, hk⟩ := mem_pivotCols.mp hj
    obtain ⟨i, hi⟩ := mem_pivotCols.mp hjM
    have h0 : (M * N) i k = 0 := by rw [hMN, Matrix.zero_apply]
    rw [Matrix.mul_apply] at h0
    have hsum : ∑ l, M i l * N l k = M i j * N j k :=
      Finset.sum_eq_single j (fun l _ hl => by
        rcases hM.1 i l with h1 | h1
        · rw [h1, zero_mul]
        · exact absurd (hM.2.1 i l j h1 hi) hl)
        (fun h => absurd (Finset.mem_univ j) h)
    rw [hsum, hi] at h0
    rw [Matrix.transpose_apply] at hk
    rw [hk, one_mul] at h0
    exact one_ne_zero h0
  · intro hj
    have hker : (Pi.single j (1 : R)) ∈ LinearMap.ker M.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      funext i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rcases eq_or_ne l j with rfl | hl
      · rw [eq_zero_of_notMem_pivotCols_of_isPartialPerm hM hj i, zero_mul]
      · rw [Pi.single_eq_of_ne hl, mul_zero]
    obtain ⟨u, hu⟩ := hex hker
    have hone : ∑ l, N j l * u l = 1 := by
      have h1 := congrFun hu j
      rw [Matrix.mulVecLin_apply] at h1
      simpa [Matrix.mulVec, dotProduct] using h1
    have hnz : ∃ l, N j l = 1 := by
      by_contra hall
      push Not at hall
      rw [Finset.sum_congr rfl (fun l _ => by
        rw [(hN.1 j l).resolve_right (hall l), zero_mul])] at hone
      simp only [Finset.sum_const_zero] at hone
      exact zero_ne_one hone
    obtain ⟨l, hl⟩ := hnz
    exact mem_pivotCols.mpr ⟨l, by rw [Matrix.transpose_apply, hl]⟩

/-- **The rank identity for a partial permutation complex.** With `M` and `N`
consecutive partial permutation matrices of a complex exact in the middle, the ranks add up to
the rank of the middle free module. -/
private lemma rank_add_rank_of_exact [Nontrivial R] {M : Matrix (Fin a) (Fin b) R}
    {N : Matrix (Fin b) (Fin c) R} (hM : IsPartialPerm M) (hN : IsPartialPerm N)
    (hMN : M * N = 0) (hex : LinearMap.ker M.mulVecLin ≤ LinearMap.range N.mulVecLin) :
    rank M + rank N = b := by
  classical
  rw [rank_eq_card_pivotCols hM, ← rank_transpose N,
    rank_eq_card_pivotCols (isPartialPerm_transpose hN), pivotCols_compl_eq hM hN hMN hex]
  simp

end PartialPerm


/-- **The alternating sum from the rank identity.** A family of ranks satisfying the recursion
`rk k + rk (k + 1) = n (k + 1)` below `e`, and vanishing above it, is the alternating sum
`n (k + 1) - n (k + 2) + ⋯ ± n (e + 1)`. -/
private lemma cast_eq_alternating_sum_of_add_eq {n rk : ℕ → ℕ} {e : ℕ}
    (hadd : ∀ k, k ≤ e → rk k + rk (k + 1) = n (k + 1)) (htop : rk (e + 1) = 0) :
    ∀ k, k ≤ e → (rk k : ℤ) = ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ) := by
  have key : ∀ d k, k + d = e →
      (rk k : ℤ) = ∑ t ∈ Finset.range (d + 1), (-1) ^ t * (n (k + 1 + t) : ℤ) := by
    intro d
    induction d with
    | zero =>
      intro k hk
      have hke : k = e := by omega
      subst hke
      have h := hadd k le_rfl
      rw [htop, Nat.add_zero] at h
      have hs : ∑ t ∈ Finset.range (0 + 1), (-1 : ℤ) ^ t * (n (k + 1 + t) : ℤ)
          = (n (k + 1) : ℤ) := by simp
      rw [hs]
      exact_mod_cast h
    | succ d ih =>
      intro k hk
      have h2 := ih (k + 1) (by omega)
      have h3 := hadd k (by omega)
      rw [Finset.sum_range_succ']
      have hneg : ∀ t : ℕ, (-1 : ℤ) ^ (t + 1) * (n (k + 1 + (t + 1)) : ℤ)
          = -((-1) ^ t * (n (k + 1 + 1 + t) : ℤ)) := by
        intro t
        rw [pow_succ, show k + 1 + (t + 1) = k + 1 + 1 + t by omega]
        ring
      rw [Finset.sum_congr rfl (fun t _ => hneg t), Finset.sum_neg_distrib, ← h2]
      simp only [pow_zero, one_mul, Nat.add_zero]
      omega
  intro k hk
  have h := key (e - k) k (by omega)
  rwa [show e - k + 1 = e + 1 - k by omega] at h

/-! ## Localizing a complex of finite free modules -/

section Localize

variable {R : Type*} [CommRing R] {a b c : ℕ}

/-- The localization map of a finite free module, componentwise. -/
private def locPi (p : Ideal R) [p.IsPrime] (k : ℕ) :
    (Fin k → R) →ₗ[R] (Fin k → Localization.AtPrime p) :=
  LinearMap.pi fun i => (Algebra.linearMap R (Localization.AtPrime p)) ∘ₗ LinearMap.proj i

private instance instIsLocalizedModuleLocPi (p : Ideal R) [p.IsPrime] (k : ℕ) :
    IsLocalizedModule p.primeCompl (locPi p k) := by
  rw [locPi]; infer_instance

private lemma locPi_apply (p : Ideal R) [p.IsPrime] {k : ℕ} (v : Fin k → R) (i : Fin k) :
    locPi p k v i = algebraMap R (Localization.AtPrime p) (v i) := rfl

/-- Applying a matrix commutes with localizing the entries and the vector. -/
private lemma mulVecLin_map_locPi (p : Ideal R) [p.IsPrime] (A : Matrix (Fin a) (Fin b) R)
    (v : Fin b → R) :
    (A.map (algebraMap R (Localization.AtPrime p))).mulVecLin (locPi p b v)
      = locPi p a (A.mulVecLin v) := by
  funext i
  simp [locPi_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]

/-- **A complex of finite free modules stays exact after localizing at a prime.** Localization is
exact, and a finite product of localizations is the localization of the product
(`IsLocalizedModule.pi`), so the localized differentials are the localizations of the
differentials; those are the matrices reduced entrywise along `R → R_𝔭`. -/
lemma exact_map_algebraMap_atPrime (p : Ideal R) [p.IsPrime]
    (M : Matrix (Fin a) (Fin b) R) (N : Matrix (Fin b) (Fin c) R)
    (h : Function.Exact N.mulVecLin M.mulVecLin) :
    Function.Exact (N.map (algebraMap R (Localization.AtPrime p))).mulVecLin
      (M.map (algebraMap R (Localization.AtPrime p))).mulVecLin := by
  have key : ∀ {u v : ℕ} (A : Matrix (Fin u) (Fin v) R),
      IsLocalizedModule.map p.primeCompl (locPi p v) (locPi p u) A.mulVecLin
        = (A.map (algebraMap R (Localization.AtPrime p))).mulVecLin.restrictScalars R := by
    intro u v A
    refine IsLocalizedModule.ext p.primeCompl (locPi p v)
      (fun s => IsLocalizedModule.map_units (locPi p u) s) (LinearMap.ext fun x => ?_)
    rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
    exact (mulVecLin_map_locPi p A x).symm
  have hmap := IsLocalizedModule.map_exact p.primeCompl (locPi p c) (locPi p b) (locPi p a)
    N.mulVecLin M.mulVecLin h
  rw [key, key] at hmap
  exact hmap

/-- **Localizing an injective map of finite free modules.** Localization is exact, so the
localization of an injective matrix map is injective. -/
lemma injective_map_algebraMap_atPrime (p : Ideal R) [p.IsPrime]
    (M : Matrix (Fin a) (Fin b) R) (h : Function.Injective M.mulVecLin) :
    Function.Injective (M.map (algebraMap R (Localization.AtPrime p))).mulVecLin := by
  have hz : Function.Exact (0 : Matrix (Fin b) (Fin 0) R).mulVecLin M.mulVecLin := by
    rw [LinearMap.exact_iff, LinearMap.ker_eq_bot.mpr h]
    exact (BoundedFreeComplex.range_eq_bot_of_zero_source rfl _).symm
  have hmap := exact_map_algebraMap_atPrime p M (0 : Matrix (Fin b) (Fin 0) R) hz
  rw [LinearMap.exact_iff] at hmap
  rw [← LinearMap.ker_eq_bot, hmap]
  exact BoundedFreeComplex.range_eq_bot_of_zero_source rfl _

/-- **Failure of exactness is invisible at a prime where the localized complex is exact.** If the
complex localized at `𝔭` is exact at a spot and `h` lies in the kernel there, then some `s ∉ 𝔭`
carries `h` into the image. -/
lemma exists_smul_mem_range_of_ker_eq_range_map (p : Ideal R) [p.IsPrime]
    (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin c) R)
    (hex : LinearMap.ker (A.map (algebraMap R (Localization.AtPrime p))).mulVecLin
      = LinearMap.range (B.map (algebraMap R (Localization.AtPrime p))).mulVecLin)
    {h : Fin b → R} (hh : A.mulVecLin h = 0) :
    ∃ s ∈ p.primeCompl, s • h ∈ LinearMap.range B.mulVecLin := by
  have hker : locPi p b h ∈ LinearMap.ker
      (A.map (algebraMap R (Localization.AtPrime p))).mulVecLin := by
    rw [LinearMap.mem_ker, mulVecLin_map_locPi, hh, map_zero]
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (hex ▸ hker)
  obtain ⟨⟨v, s⟩, hvs0⟩ := IsLocalizedModule.surj p.primeCompl (locPi p c) w
  have hvs : (s : R) • w = locPi p c v := hvs0
  have hkey : locPi p b ((s : R) • h) = locPi p b (B.mulVecLin v) :=
    calc locPi p b ((s : R) • h) = (s : R) • locPi p b h := map_smul _ _ _
      _ = (s : R) • (B.map (algebraMap R (Localization.AtPrime p))).mulVecLin w := by rw [hw]
      _ = (B.map (algebraMap R (Localization.AtPrime p))).mulVecLin ((s : R) • w) :=
          (LinearMap.map_smul_of_tower _ _ _).symm
      _ = (B.map (algebraMap R (Localization.AtPrime p))).mulVecLin (locPi p c v) := by rw [hvs]
      _ = locPi p b (B.mulVecLin v) := mulVecLin_map_locPi p B v
  obtain ⟨t, ht0⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl (locPi p b)).mp
    (by rw [map_sub, hkey, sub_self] :
      locPi p b ((s : R) • h - B.mulVecLin v) = 0)
  have ht : (t : R) • ((s : R) • h - B.mulVecLin v) = 0 := ht0
  rw [smul_sub, sub_eq_zero] at ht
  exact ⟨(t : R) * (s : R), mul_mem t.2 s.2,
    ⟨(t : R) • v, by rw [LinearMap.map_smul, ← ht, mul_smul]⟩⟩

end Localize

/-! ## An exact complex over a depth-zero local ring -/

section DepthZero

open scoped Matrix
open StacksComplex BoundedFreeComplex

/-- **An exact complex over a depth-zero local ring.** Over a local Noetherian ring `S` whose
maximal ideal is an associated prime — a ring of depth `0` — an exact complex
`0 → S^{n_{e+1}} → ⋯ → S^{n_0}` of finite free modules has, at every spot `k ≤ e`, rank the
alternating sum `n_{k+1} - n_{k+2} + ⋯ ± n_{e+1}` and unit determinantal ideal.

Here `hn0` says the complex has length `e + 1`, `hA` that it is a complex, and `hex` that it is
exact at `S^{n_{e+1}}, …, S^{n_1}`, the spot `k = e` of `hex` being injectivity of `A e`, since
`A (e + 1)` has no columns. -/
private lemma rank_eq_and_minorIdeal_eq_top_of_exact_of_depthZero
    {S : Type*} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (hdepth : IsLocalRing.maximalIdeal S ∈ associatedPrimes S S)
    (e : ℕ) (n : ℕ → ℕ) (A : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) S)
    (hn0 : ∀ i, e + 1 < i → n i = 0) (hA : ∀ k, A k * A (k + 1) = 0)
    (hex : ∀ k ≤ e + 1, LinearMap.ker (A k).mulVecLin = LinearMap.range (A (k + 1)).mulVecLin) :
    ∀ k ≤ e, ((rank (A k) : ℤ)
        = ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ))
      ∧ minorIdeal (A k) = ⊤ := by
  classical
  set C : BoundedFreeComplex S := ⟨e + 1, n, A, hn0, hA⟩ with hCdef
  have hCex : C.Exact := hex
  obtain ⟨D, iso, -, -, hDtriv⟩ := exists_trivial_iso_of_exact hdepth C hCex
  set ψ : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) S := transportφ C D iso.hn with hψdef
  set P : ∀ i, Matrix (Fin (n i)) (Fin (n i)) S := iso.P with hPdef
  have hPl : ∀ i, P i * (P i)⁻¹ = 1 := fun i => Matrix.mul_nonsing_inv _ (iso.unit i)
  have hPr : ∀ i, (P i)⁻¹ * P i = 1 := fun i => Matrix.nonsing_inv_mul _ (iso.unit i)
  have hψpp : ∀ i, IsPartialPerm (ψ i) := fun i =>
    isPartialPerm_submatrix (D.φ i) (finCongr (iso.hn i)) (finCongr (iso.hn (i + 1))) (hDtriv i)
  have hψconj : ∀ i, ψ i = (P i)⁻¹ * A i * P (i + 1) := fun i => by
    have h := iso.comm i
    calc ψ i = (P i)⁻¹ * (P i * ψ i) := by rw [← Matrix.mul_assoc, hPr, Matrix.one_mul]
    _ = (P i)⁻¹ * (A i * P (i + 1)) := by rw [h]
    _ = (P i)⁻¹ * A i * P (i + 1) := by rw [Matrix.mul_assoc]
  have hrank : ∀ i, rank (ψ i) = rank (A i) := fun i => by
    rw [hψconj i]
    exact rank_conj_eq _ (P i) (A i) _ ((P (i + 1))⁻¹) (hPl i) (hPl (i + 1))
  have hminor : ∀ i, minorIdeal (ψ i) = minorIdeal (A i) := fun i => by
    rw [hψconj i, minorIdeal_mul_right _ (P (i + 1)) ((P (i + 1))⁻¹) (hPl (i + 1)),
      minorIdeal_mul_left _ (P i) (A i) (hPl i)]
  have hψzero : ∀ i, ψ i * ψ (i + 1) = 0 := fun i => by
    rw [hψconj i, hψconj (i + 1)]
    calc (P i)⁻¹ * A i * P (i + 1) * ((P (i + 1))⁻¹ * A (i + 1) * P (i + 2))
        = (P i)⁻¹ * (A i * ((P (i + 1) * (P (i + 1))⁻¹) * A (i + 1))) * P (i + 2) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hPl (i + 1), Matrix.one_mul, hA i]; simp
  have hψex : ∀ i ≤ e + 1,
      LinearMap.ker (ψ i).mulVecLin ≤ LinearMap.range (ψ (i + 1)).mulVecLin := by
    intro i hi v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hψconj i] at hv
    have hker : A i *ᵥ (P (i + 1) *ᵥ v) = 0 := by
      have h2 := congrArg (fun w => (P i) *ᵥ w) hv
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPl i, Matrix.one_mul,
        Matrix.mulVec_zero] at h2
      rw [Matrix.mulVec_mulVec]
      exact h2
    have hmem : P (i + 1) *ᵥ v ∈ LinearMap.ker (A i).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact hker
    obtain ⟨w, hw⟩ := (hex i hi).le hmem
    refine ⟨(P (i + 2))⁻¹ *ᵥ w, ?_⟩
    rw [Matrix.mulVecLin_apply, hψconj (i + 1)]
    have hw' : A (i + 1) *ᵥ w = P (i + 1) *ᵥ v := by
      simpa [Matrix.mulVecLin_apply] using hw
    calc ((P (i + 1))⁻¹ * A (i + 1) * P (i + 2)) *ᵥ ((P (i + 2))⁻¹ *ᵥ w)
        = ((P (i + 1))⁻¹ * A (i + 1) * (P (i + 2) * (P (i + 2))⁻¹)) *ᵥ w := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (P (i + 1))⁻¹ *ᵥ (A (i + 1) *ᵥ w) := by
          rw [hPl (i + 2), Matrix.mul_one, ← Matrix.mulVec_mulVec]
    _ = v := by rw [hw', Matrix.mulVec_mulVec, hPr (i + 1), Matrix.one_mulVec]
  have hadd : ∀ k ≤ e, rank (A k) + rank (A (k + 1)) = n (k + 1) := fun k hk => by
    rw [← hrank k, ← hrank (k + 1)]
    exact rank_add_rank_of_exact (hψpp k) (hψpp (k + 1)) (hψzero k) (hψex k (by omega))
  have htop : rank (A (e + 1)) = 0 := by
    have h0 : n (e + 1 + 1) = 0 := hn0 _ (by omega)
    exact Nat.le_zero.mp (h0 ▸ rank_le_m (A (e + 1)))
  intro k hk
  refine ⟨cast_eq_alternating_sum_of_add_eq hadd htop k hk, ?_⟩
  rw [← hminor k]
  exact minorIdeal_eq_top_of_isPartialPerm (hψpp k)

/-! ### Truncating a complex to the degrees its exactness data cover -/

/-- The ranks of a complex, truncated above degree `E`: `n i` for `i ≤ E` and `0` above. -/
def truncRank (E : ℕ) (n : ℕ → ℕ) (i : ℕ) : ℕ := if i ≤ E then n i else 0

lemma truncRank_le (E : ℕ) (n : ℕ → ℕ) (i : ℕ) : truncRank E n i ≤ n i := by
  rw [truncRank]
  split
  · exact le_rfl
  · exact Nat.zero_le _

lemma truncRank_of_le {E i : ℕ} (n : ℕ → ℕ) (h : i ≤ E) : truncRank E n i = n i := by
  simp [truncRank, h]

lemma truncRank_of_lt {E i : ℕ} (n : ℕ → ℕ) (h : E < i) : truncRank E n i = 0 := by
  simp [truncRank, Nat.not_le.mpr h]

/-- Below the truncation degree the inclusion of index types is a bijection. -/
def truncEquiv {E i : ℕ} (n : ℕ → ℕ) (h : i ≤ E) :
    Fin (truncRank E n i) ≃ Fin (n i) := finCongr (truncRank_of_le n h)

/-- The differentials of a complex, truncated above degree `E`: the entries surviving the
truncation of the index types. -/
def truncMat {S : Type*} (E : ℕ) (n : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) S) (i : ℕ) :
    Matrix (Fin (truncRank E n i)) (Fin (truncRank E n (i + 1))) S :=
  (A i).submatrix (Fin.castLE (truncRank_le E n i)) (Fin.castLE (truncRank_le E n (i + 1)))

lemma truncMat_eq {S : Type*} {E : ℕ} (n : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) S) {i : ℕ}
    (hi : i ≤ E) (hi1 : i + 1 ≤ E) :
    truncMat E n A i = (A i).submatrix (truncEquiv n hi) (truncEquiv n hi1) := rfl

/-- A matrix with no columns is zero. -/
lemma matrix_eq_zero_of_ncols {S : Type*} [CommRing S] {a b : ℕ} (hb : b = 0)
    (M : Matrix (Fin a) (Fin b) S) : M = 0 := by
  ext i j
  exact absurd j.isLt (by omega)

/-- Every submodule of a free module on an empty index type is `⊥`. -/
private lemma submodule_eq_bot_of_ncols {S : Type*} [CommRing S] {b : ℕ} (hb : b = 0)
    (p : Submodule S (Fin b → S)) : p = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun x _ => funext fun i => absurd i.isLt (by omega)

/-- Reindexing the source and target of an injective matrix map along bijections of the index
types keeps it injective. -/
lemma ker_mulVecLin_submatrix_eq_bot {S : Type*} [CommRing S] {a b a' b' : ℕ}
    (M : Matrix (Fin a) (Fin b) S) (α : Fin a' ≃ Fin a) (β : Fin b' ≃ Fin b)
    (h : Function.Injective M.mulVecLin) :
    LinearMap.ker (M.submatrix α β).mulVecLin = ⊥ := by
  rw [Matrix.mulVecLin_submatrix (α : Fin a' → Fin a) β M, LinearMap.ker_eq_bot]
  simp only [LinearMap.coe_comp]
  exact (LinearMap.funLeft_injective_of_surjective S S _ α.surjective).comp
    (h.comp (LinearMap.funLeft_injective_of_surjective S S _ β.symm.surjective))

/-- **An exact complex over a depth-zero local ring, from exactness data alone.** Over a local
Noetherian ring whose maximal ideal is an associated prime, a complex of finite free modules,
injective at the top and exact at the spots below, has at every spot `k ≤ e` rank the
alternating sum and unit determinantal ideal. No vanishing is demanded of `n` above the top
degree. -/
lemma rank_eq_and_minorIdeal_eq_top_of_injective_of_exact_of_depthZero
    {S : Type*} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (hdepth : IsLocalRing.maximalIdeal S ∈ associatedPrimes S S)
    (e : ℕ) (n : ℕ → ℕ) (A : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) S)
    (hA : ∀ k < e, A k * A (k + 1) = 0)
    (hinj : Function.Injective (A e).mulVecLin)
    (hex : ∀ k < e, LinearMap.ker (A k).mulVecLin = LinearMap.range (A (k + 1)).mulVecLin) :
    ∀ k ≤ e, ((rank (A k) : ℤ)
        = ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ))
      ∧ minorIdeal (A k) = ⊤ := by
  have hz : ∀ i, e + 1 < i → truncRank (e + 1) n i = 0 := fun _ hi => truncRank_of_lt n hi
  have hcomplex : ∀ k, truncMat (e + 1) n A k * truncMat (e + 1) n A (k + 1) = 0 := by
    intro k
    by_cases hk : k < e
    · have h1 : k ≤ e + 1 := by omega
      have h2 : k + 1 ≤ e + 1 := by omega
      have h3 : k + 1 + 1 ≤ e + 1 := by omega
      rw [truncMat_eq n A h1 h2, truncMat_eq n A h2 h3,
        Matrix.submatrix_mul_equiv (A k) (A (k + 1)) _ (truncEquiv n h2) _, hA k hk]
      rfl
    · exact matrix_eq_zero_of_ncols (hz _ (by omega)) _
  have hexact : ∀ k ≤ e + 1, LinearMap.ker (truncMat (e + 1) n A k).mulVecLin
      = LinearMap.range (truncMat (e + 1) n A (k + 1)).mulVecLin := by
    intro k hk
    rcases lt_trichotomy k e with hlt | heq | hgt
    · have h1 : k ≤ e + 1 := by omega
      have h2 : k + 1 ≤ e + 1 := by omega
      have h3 : k + 1 + 1 ≤ e + 1 := by omega
      rw [truncMat_eq n A h1 h2, truncMat_eq n A h2 h3]
      exact exact_eqn_reindex (A k) (A (k + 1)) (truncEquiv n h1) (truncEquiv n h2)
        (truncEquiv n h3) (hex k hlt)
    · subst heq
      rw [truncMat_eq (E := k + 1) n A (by omega) (by omega),
        ker_mulVecLin_submatrix_eq_bot (A k) _ _ hinj]
      exact (range_eq_bot_of_zero_source (hz (k + 1 + 1) (by omega)) _).symm
    · have hk1 : k = e + 1 := by omega
      subst hk1
      exact (submodule_eq_bot_of_ncols (hz (e + 1 + 1) (by omega)) _).trans
        (submodule_eq_bot_of_ncols (hz (e + 1 + 1) (by omega)) _).symm
  have hmain := rank_eq_and_minorIdeal_eq_top_of_exact_of_depthZero hdepth e
    (truncRank (e + 1) n) (truncMat (e + 1) n A) hz hcomplex hexact
  intro k hk
  obtain ⟨hr, hI⟩ := hmain k hk
  have h1 : k ≤ e + 1 := by omega
  have h2 : k + 1 ≤ e + 1 := by omega
  rw [truncMat_eq n A h1 h2, rank_submatrix_equiv] at hr
  rw [truncMat_eq n A h1 h2, minorIdeal_submatrix_equiv] at hI
  refine ⟨hr.trans (Finset.sum_congr rfl fun t ht => ?_), hI⟩
  rw [Finset.mem_range] at ht
  rw [truncRank_of_le n (show k + 1 + t ≤ e + 1 by omega)]

end DepthZero

end Stacks.Depth.BuchsbaumEisenbud

end
