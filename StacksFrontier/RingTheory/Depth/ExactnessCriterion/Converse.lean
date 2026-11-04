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
public import StacksFrontier.RingTheory.Depth.ExactnessCriterion.MinorsAndDepth
public import StacksFrontier.RingTheory.Depth.ExactnessCriterion.DepthZero
public import StacksFrontier.RingTheory.Depth.ExactnessCriterion.NumericalConditions

/-!
# The Buchsbaum–Eisenbud exactness criterion

Let `R` be a local Noetherian ring and let
`0 → R^{n_{e+1}} →[φ e] R^{n_e} → ⋯ → R^{n_1} →[φ 0] R^{n_0}`
be a complex of finite free `R`-modules. The criterion says that this complex is exact at
`R^{n_{e+1}}, …, R^{n_1}` if and only if, for every `k ≤ e`, the rank of `φ k` is the alternating
sum `n_{k+1} - n_{k+2} + ⋯ ± n_{e+1}` and the ideal `I(φ k)` of `rank × rank` minors of `φ k`
satisfies `depth_{I(φ k)}(R) ≥ k + 1`.

This file proves the converse direction and assembles the criterion. The converse is a double
induction: the outer one on a natural number bounding the height of the maximal ideal, along
which both numerical conditions are inherited by localizations at non-maximal primes, and the
inner one on the top degree `E`. If `I(φ_E)` is a proper ideal, condition (2)(b) bounds `depth R`
from below and the acyclicity lemma applies. If `I(φ_E)` is the unit ideal, `φ_E` is a split
injection and dividing by its image lowers the top degree.

## Main results

* `LinearMap.injective_and_exact_iff_forall_rank_eq_and_le_depth_minors`: the criterion.

## References

* [StacksProject 00N1](https://stacks.math.columbia.edu/tag/00N1)
* D. A. Buchsbaum and D. Eisenbud, *What makes a complex exact?*, Corollary 1

## Tags

exact complex, finite free module, rank, minor, depth, regular sequence
-/

@[expose] public section

namespace Stacks.Depth.BuchsbaumEisenbud

open RingTheory.Sequence Stacks.DeterminantalRank

section Criterion

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-! ### Rank and minors under a rectangular right factor -/

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Cauchy–Binet for a rectangular right factor: an `r × r` minor of `φ * B` expands as a
combination of `r × r` minors of `φ`. -/
private lemma minor_mul_right' {a b c r : ℕ} (φ : Matrix (Fin a) (Fin b) R)
    (B : Matrix (Fin b) (Fin c) R) (ρ : Fin r → Fin a) (γ : Fin r → Fin c) :
    ((φ * B).submatrix ρ γ).det
      = ∑ g : Fin r → Fin b, (φ.submatrix ρ g).det * (∏ i, B (g i) (γ i)) := by
  have hsub : (φ * B).submatrix ρ γ = (φ.submatrix ρ id) * (B.submatrix id γ) := by
    have := Matrix.submatrix_mul_equiv φ B ρ (Equiv.refl (Fin b)) γ
    simpa using this.symm
  rw [hsub, StacksComplex.det_mul_eq_sum_det_submatrix_mul_prod]
  exact Finset.sum_congr rfl fun g _ => rfl

omit [IsNoetherianRing R] in
/-- A rectangular right factor does not increase the rank. -/
private lemma rank_mul_right_le' {a b c : ℕ} (φ : Matrix (Fin a) (Fin b) R)
    (B : Matrix (Fin b) (Fin c) R) :
    StacksComplex.rank (φ * B) ≤ StacksComplex.rank φ := by
  refine StacksComplex.rank_le _ fun r hr => ?_
  by_contra hlt
  rw [not_le] at hlt
  refine StacksComplex.not_mem_rankSet (φ * B) (fun rows cols => ?_) hr
  rw [minor_mul_right']
  exact Finset.sum_eq_zero fun g _ => by
    rw [StacksComplex.minor_eq_zero_of_rank_lt φ hlt rows g, zero_mul]

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- A rectangular right factor does not enlarge the ideal of minors, once the rank is unchanged. -/
private lemma minorIdeal_mul_right_le' {a b c : ℕ} (φ : Matrix (Fin a) (Fin b) R)
    (B : Matrix (Fin b) (Fin c) R)
    (hrk : StacksComplex.rank (φ * B) = StacksComplex.rank φ) :
    StacksComplex.minorIdeal (φ * B) ≤ StacksComplex.minorIdeal φ := by
  unfold StacksComplex.minorIdeal
  rw [hrk, Ideal.span_le]
  rintro x ⟨ρ, γ, rfl⟩
  rw [minor_mul_right']
  exact Ideal.sum_mem _ fun g _ =>
    Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨ρ, g, rfl⟩)

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Reindexing the exactness equation back: the equation for the reindexed matrices gives it for
the originals, the reindexings being bijections. -/
private lemma exact_eqn_unreindex {a b c a' b' c' : ℕ}
    (Mi : Matrix (Fin a) (Fin b) R) (Mi1 : Matrix (Fin b) (Fin c) R)
    (ea : Fin a' ≃ Fin a) (eb : Fin b' ≃ Fin b) (ec : Fin c' ≃ Fin c)
    (h : LinearMap.ker (Mi.submatrix ea eb).mulVecLin
      = LinearMap.range (Mi1.submatrix eb ec).mulVecLin) :
    LinearMap.ker Mi.mulVecLin = LinearMap.range Mi1.mulVecLin := by
  have h2 : LinearMap.ker ((Mi.submatrix ea eb).submatrix ea.symm eb.symm).mulVecLin
      = LinearMap.range ((Mi1.submatrix eb ec).submatrix eb.symm ec.symm).mulVecLin :=
    BoundedFreeComplex.exact_eqn_reindex (Mi.submatrix ea eb) (Mi1.submatrix eb ec)
      ea.symm eb.symm ec.symm h
  rw [Matrix.submatrix_submatrix, Matrix.submatrix_submatrix] at h2
  simpa using h2

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Deleting columns commutes with left multiplication. -/
private lemma mul_submatrix_right {α β γ δ : Type*} [Fintype β] (X : Matrix α β R)
    (Y : Matrix β γ R) (f : δ → γ) : X * Y.submatrix id f = (X * Y).submatrix id f := by
  ext i j
  simp [Matrix.mul_apply]

/-- Reindexing rows and columns by bijections preserves `exteriorRank`. -/
private lemma exteriorRank_submatrix_equiv' {S : Type*} [CommRing S] [Nontrivial S]
    {a b a' b' : ℕ} (φ : Matrix (Fin a) (Fin b) S)
    (ea : Fin a' ≃ Fin a) (eb : Fin b' ≃ Fin b) :
    exteriorRank (φ.submatrix ea eb) = exteriorRank φ := by
  rw [exteriorRank_eq_rank, exteriorRank_eq_rank, StacksComplex.rank_submatrix_equiv]

/-- Reindexing rows and columns by bijections preserves `detIdeal`. -/
private lemma detIdeal_submatrix_equiv' {S : Type*} [CommRing S] [Nontrivial S]
    {a b a' b' : ℕ} (φ : Matrix (Fin a) (Fin b) S)
    (ea : Fin a' ≃ Fin a) (eb : Fin b' ≃ Fin b) :
    detIdeal (φ.submatrix ea eb) = detIdeal φ := by
  rw [detIdeal_eq_minorIdeal, detIdeal_eq_minorIdeal, StacksComplex.minorIdeal_submatrix_equiv]

/-- If a reindexing of a matrix by bijections is injective, so is the matrix. -/
private lemma injective_of_injective_submatrix {S : Type*} [CommRing S]
    {a b a' b' : ℕ} (M : Matrix (Fin a) (Fin b) S)
    (ea : Fin a' ≃ Fin a) (eb : Fin b' ≃ Fin b)
    (h : Function.Injective (M.submatrix ea eb).mulVecLin) : Function.Injective M.mulVecLin := by
  have := ker_mulVecLin_submatrix_eq_bot _ ea.symm eb.symm h
  rw [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm,
    Matrix.submatrix_id_id] at this
  rwa [← LinearMap.ker_eq_bot]

omit [IsNoetherianRing R] in
/-- Over a local ring an ideal generated by a set is the unit ideal only if the set contains a
unit. -/
private lemma exists_isUnit_of_span_eq_top {s : Set R} (h : Ideal.span s = ⊤) :
    ∃ x ∈ s, IsUnit x := by
  by_contra hc
  push Not at hc
  refine (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp ?_)
  rw [← h, Ideal.span_le]
  exact fun x hx => (IsLocalRing.mem_maximalIdeal x).mpr (by simpa using hc x hx)

omit [IsNoetherianRing R] in
/-- **A unit maximal minor.** If the ideal of minors of `T` is the unit ideal and its rank is the
number `m` of columns, then some `m` distinct rows of `T` form an invertible square matrix. -/
private lemma exists_isUnit_det_submatrix {N m : ℕ} (T : Matrix (Fin N) (Fin m) R)
    (hrk : exteriorRank T = m) (hI : detIdeal T = ⊤) :
    ∃ ρ : Fin m → Fin N, Function.Injective ρ ∧ IsUnit (T.submatrix ρ id).det := by
  classical
  obtain ⟨x, hx, hux⟩ := exists_isUnit_of_span_eq_top (s := minorSet T (exteriorRank T)) hI
  obtain ⟨ρ0, γ0, rfl⟩ := hx
  set e : Fin (exteriorRank T) ≃ Fin m := finCongr hrk with he
  set ρ : Fin m → Fin N := ρ0 ∘ e.symm with hρdef
  set γ : Fin m → Fin m := γ0 ∘ e.symm with hγdef
  have hdet : (T.submatrix ρ γ).det = (T.submatrix ρ0 γ0).det := by
    have h := Matrix.det_reindex_self e (T.submatrix ρ0 γ0)
    rwa [Matrix.reindex_apply, Matrix.submatrix_submatrix] at h
  have hu : IsUnit (T.submatrix ρ γ).det := by rw [hdet]; exact hux
  have hγinj : Function.Injective γ := by
    intro i j hij
    by_contra hne
    rw [Matrix.det_zero_of_column_eq hne fun k => by simp [Matrix.submatrix_apply, hij]] at hu
    exact not_isUnit_zero hu
  refine ⟨ρ, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    rw [Matrix.det_zero_of_row_eq hne (funext fun k => by
      simp [Matrix.submatrix_apply, hij])] at hu
    exact not_isUnit_zero hu
  · set σ : Equiv.Perm (Fin m) := Equiv.ofBijective γ (Finite.injective_iff_bijective.mp hγinj)
      with hσ
    have hsub : T.submatrix ρ γ = (T.submatrix ρ id).submatrix id σ := by
      rw [Matrix.submatrix_submatrix]
      rfl
    rw [hsub, Matrix.det_permute'] at hu
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] at hu <;>
      simpa using hu

omit [IsNoetherianRing R] in
/-- **Splitting a unit maximal minor off the top of the complex.**
If the ideal of minors of the top differential `A (t + 1)` is the unit ideal — which over a local
ring means that some minor of the top size is a unit — then, its rank being the number `n (t + 2)`
of its columns, `A (t + 1)` is a split injection: after a change of basis of `R^{n (t + 1)}` it is
the inclusion of the first `n (t + 2)` coordinates. Dividing `R^{n (t + 1)}` by its image leaves a
complex `A'` of finite free modules of top degree `t + 1`, with the ranks decremented once at
degree `t + 1` and unchanged below, whose differentials have the same rank and determinantal
ideal as those of `A` in every degree `≤ t`, and whose exactness gives back the exactness of `A`
at the spots `1, …, t + 2`.

The construction. Pick `ρ : Fin (n (t + 2)) → Fin (n (t + 1))` with `det ((A (t + 1)).submatrix ρ
id)` a unit; completing `ρ` to a bijection `Fin (n (t + 2)) ⊕ Fin (n (t + 1) - n (t + 2)) ≃
Fin (n (t + 1))` writes `A (t + 1)` in two blocks, the upper one invertible, and clearing the
lower block by an invertible `L` makes `L * A (t + 1)` the standard inclusion. Then `A t * L⁻¹`
has its first `n (t + 2)` columns zero, because `A t * A (t + 1) = 0`, and `A' t` is the block of
its remaining columns. -/
private lemma exists_top_split (t : ℕ) (n : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) R)
    (htop : ∀ i, t + 2 < i → n i = 0)
    (hA : ∀ i, A i * A (i + 1) = 0)
    (hrk : exteriorRank (A (t + 1)) = n (t + 2))
    (hI : detIdeal (A (t + 1)) = ⊤) :
    ∃ (n' : ℕ → ℕ) (A' : ∀ i, Matrix (Fin (n' i)) (Fin (n' (i + 1))) R),
      (∀ i ≤ t, n' i = n i) ∧
      ((n' (t + 1) : ℤ) = (n (t + 1) : ℤ) - (n (t + 2) : ℤ)) ∧
      (∀ i, t + 1 < i → n' i = 0) ∧
      (∀ i, A' i * A' (i + 1) = 0) ∧
      (∀ k ≤ t, exteriorRank (A' k) = exteriorRank (A k)) ∧
      (∀ k ≤ t, detIdeal (A' k) = detIdeal (A k)) ∧
      ((∀ k ≤ t, LinearMap.ker (A' k).mulVecLin = LinearMap.range (A' (k + 1)).mulVecLin) →
        ∀ k ≤ t + 1, LinearMap.ker (A k).mulVecLin
          = LinearMap.range (A (k + 1)).mulVecLin) := by
  classical
  obtain ⟨ρ, hρinj, hBu⟩ := exists_isUnit_det_submatrix (A (t + 1)) hrk hI
  have hmN : n (t + 2) ≤ n (t + 1) := by
    have hbd : exteriorRank (A (t + 1)) ≤ min (n (t + 2)) (n (t + 1)) := by
      rw [exteriorRank]; exact Nat.findGreatest_le _
    have h := le_trans hbd (min_le_right (n (t + 2)) (n (t + 1)))
    rwa [hrk] at h
  have hcard : Fintype.card {x : Fin (n (t + 1)) // x ∉ Set.range ρ}
      = n (t + 1) - n (t + 2) := by
    rw [Fintype.card_subtype_compl]
    have h2 : Fintype.card {x : Fin (n (t + 1)) // x ∈ Set.range ρ} = n (t + 2) := by
      rw [Fintype.card_congr (Equiv.ofInjective ρ hρinj).symm]
      simp
    rw [h2]
    simp
  set τ : Fin (n (t + 2)) ⊕ Fin (n (t + 1) - n (t + 2)) ≃ Fin (n (t + 1)) :=
    (Equiv.sumCongr (Equiv.ofInjective ρ hρinj)
      (Fintype.equivFinOfCardEq hcard).symm).trans (Equiv.sumCompl (· ∈ Set.range ρ)) with hτdef
  have hτinl : ∀ a, τ (Sum.inl a) = ρ a := fun a => rfl
  set B : Matrix (Fin (n (t + 2))) (Fin (n (t + 2))) R := (A (t + 1)).submatrix ρ id with hBdef
  set C : Matrix (Fin (n (t + 1) - n (t + 2))) (Fin (n (t + 2))) R :=
    (A (t + 1)).submatrix (fun b => τ (Sum.inr b)) id with hCdef
  set ψ : Matrix (Fin (n t)) (Fin (n (t + 1) - n (t + 2))) R :=
    (A t).submatrix id (fun b => τ (Sum.inr b)) with hψdef
  set D₁ : Matrix (Fin (n t)) (Fin (n (t + 2))) R := (A t).submatrix id ρ with hD1def
  have hB : IsUnit B.det := hBu
  have hBinv : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have hY : (A (t + 1)).submatrix τ id = Matrix.fromRows B C := by
    ext s j
    cases s with
    | inl a => simp [hBdef, hτinl]
    | inr b => simp [hCdef]
  have hX : (A t).submatrix id τ = Matrix.fromCols D₁ ψ := by
    ext i s
    cases s with
    | inl a => simp [hD1def, hτinl]
    | inr b => simp [hψdef]
  have hrel : D₁ * B + ψ * C = 0 := by
    rw [← Matrix.fromCols_mul_fromRows, ← hX, ← hY,
      Matrix.submatrix_mul_equiv (A t) (A (t + 1)) id τ id, hA t]
    simp
  have hD1 : D₁ = ψ * (-(C * B⁻¹)) := by
    have hD1B : D₁ * B = -(ψ * C) := add_eq_zero_iff_eq_neg.mp hrel
    calc D₁ = D₁ * (B * B⁻¹) := by rw [hBinv, Matrix.mul_one]
      _ = D₁ * B * B⁻¹ := by rw [Matrix.mul_assoc]
      _ = -(ψ * C) * B⁻¹ := by rw [hD1B]
      _ = ψ * (-(C * B⁻¹)) := by
          rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  set Q : Matrix (Fin (n (t + 1) - n (t + 2))) (Fin (n (t + 1))) R :=
    (Matrix.fromCols (-(C * B⁻¹))
      (1 : Matrix (Fin (n (t + 1) - n (t + 2))) (Fin (n (t + 1) - n (t + 2))) R)).submatrix
        id τ.symm with hQdef
  have hDQ : A t = ψ * Q := by
    rw [hQdef, mul_submatrix_right, Matrix.mul_fromCols, Matrix.mul_one, ← hD1, ← hX,
      Matrix.submatrix_submatrix]
    simp
  set P : Matrix (Fin (n (t + 1))) (Fin (n (t + 1) - n (t + 2))) R :=
    (1 : Matrix (Fin (n (t + 1))) (Fin (n (t + 1))) R).submatrix id
      (fun b => τ (Sum.inr b)) with hPdef
  have hψP : ψ = A t * P := by
    rw [hPdef, mul_submatrix_right, Matrix.mul_one, hψdef]
  have hrankeq : StacksComplex.rank ψ = StacksComplex.rank (A t) :=
    le_antisymm (by rw [hψP]; exact rank_mul_right_le' _ P)
      (by rw [hDQ]; exact rank_mul_right_le' ψ Q)
  have hidealeq : StacksComplex.minorIdeal ψ = StacksComplex.minorIdeal (A t) :=
    le_antisymm (by
        rw [hψP]
        exact minorIdeal_mul_right_le' _ P (by rw [← hψP]; exact hrankeq))
      (by
        rw [hDQ]
        exact minorIdeal_mul_right_le' ψ Q (by rw [← hDQ]; exact hrankeq.symm))
  have hrangeeq : LinearMap.range ψ.mulVecLin = LinearMap.range (A t).mulVecLin :=
    le_antisymm
      (by rw [hψP, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _)
      (by rw [hDQ, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _)
  have hTinj : LinearMap.ker (A (t + 1)).mulVecLin = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    have hv' : (A (t + 1)).mulVec v = 0 := hv
    have h1 : B.mulVec v = 0 := by
      funext a
      have h2 : B.mulVec v a = (A (t + 1)).mulVec v (ρ a) := by
        simp [hBdef, Matrix.mulVec, dotProduct]
      rw [h2, hv']
      rfl
    calc v = (1 : Matrix (Fin (n (t + 2))) (Fin (n (t + 2))) R).mulVec v := by
          rw [Matrix.one_mulVec]
      _ = (B⁻¹ * B).mulVec v := by rw [Matrix.nonsing_inv_mul B hB]
      _ = B⁻¹.mulVec (B.mulVec v) := (Matrix.mulVec_mulVec v B⁻¹ B).symm
      _ = 0 := by rw [h1, Matrix.mulVec_zero]
  have hkerD : LinearMap.ker ψ.mulVecLin = ⊥ →
      LinearMap.ker (A t).mulVecLin = LinearMap.range (A (t + 1)).mulVecLin := by
    intro hkψ
    refine le_antisymm (fun v hv => ?_) ?_
    · have hv' : (A t).mulVec v = 0 := hv
      set w := B⁻¹.mulVec (fun a => v (ρ a)) with hw
      set u := v - (A (t + 1)).mulVec w with hu
      have hBw : B.mulVec w = fun a => v (ρ a) := by
        rw [hw, Matrix.mulVec_mulVec, hBinv, Matrix.one_mulVec]
      have hu1 : ∀ a, u (ρ a) = 0 := by
        intro a
        have h2 : (A (t + 1)).mulVec w (ρ a) = B.mulVec w a := by
          simp [hBdef, Matrix.mulVec, dotProduct]
        simp only [hu, Pi.sub_apply, h2, hBw]
        ring
      have hu2 : (A t).mulVec u = 0 := by
        rw [hu, Matrix.mulVec_sub, hv', Matrix.mulVec_mulVec, hA t]
        simp
      have hsplit : (A t).mulVec u
          = D₁.mulVec ((u ∘ (τ : _ → _)) ∘ Sum.inl)
            + ψ.mulVec ((u ∘ (τ : _ → _)) ∘ Sum.inr) := by
        have h3 := Matrix.submatrix_mulVec_equiv (A t) (u ∘ (τ : _ → _))
          (id : Fin (n t) → Fin (n t)) τ
        rw [hX, Matrix.fromCols_mulVec] at h3
        have h4 : (u ∘ (τ : _ → _)) ∘ (τ.symm : Fin (n (t + 1)) → _) = u := by
          funext k; simp
        rw [h4] at h3
        simpa using h3.symm
      have hu3 : ψ.mulVec ((u ∘ (τ : _ → _)) ∘ Sum.inr) = 0 := by
        have h5 : (u ∘ (τ : _ → _)) ∘ Sum.inl = 0 := by
          funext a
          simpa [hτinl a] using hu1 a
        rw [hsplit, h5, Matrix.mulVec_zero, zero_add] at hu2
        exact hu2
      have hu4 : ∀ b, u (τ (Sum.inr b)) = 0 := by
        have h8 := (Submodule.eq_bot_iff _).mp hkψ _ hu3
        intro b
        exact congrFun h8 b
      have hu0 : ∀ k, u k = 0 := by
        intro k
        obtain ⟨s, rfl⟩ : ∃ s, k = τ s := ⟨τ.symm k, (τ.apply_symm_apply k).symm⟩
        cases s with
        | inl a => rw [hτinl a]; exact hu1 a
        | inr b => exact hu4 b
      refine ⟨w, ?_⟩
      have h9 : u = 0 := funext fun k => by rw [hu0 k]; rfl
      rw [hu, sub_eq_zero] at h9
      exact h9.symm
    · rintro x ⟨w, rfl⟩
      show (A t).mulVec ((A (t + 1)).mulVec w) = 0
      rw [Matrix.mulVec_mulVec, hA t]
      simp
  obtain ⟨n', hn'le, hn'mid, hn'hi⟩ : ∃ n' : ℕ → ℕ, (∀ i ≤ t, n' i = n i) ∧
      n' (t + 1) = n (t + 1) - n (t + 2) ∧ (∀ i, t + 1 < i → n' i = 0) :=
    ⟨fun i => if i ≤ t then n i else if i = t + 1 then n (t + 1) - n (t + 2) else 0,
      fun i hi => by simp [hi], by simp, fun i hi => by
        simp [show ¬ (i ≤ t) from by omega, show i ≠ t + 1 from by omega]⟩
  obtain ⟨A', hA'lt, hA'mid, hA'hi⟩ :
      ∃ A' : ∀ i, Matrix (Fin (n' i)) (Fin (n' (i + 1))) R,
        (∀ i, i < t → ∀ (h1 : n' i = n i) (h2 : n' (i + 1) = n (i + 1)),
            A' i = (A i).submatrix (finCongr h1) (finCongr h2)) ∧
          (∀ (h1 : n' t = n t) (h2 : n' (t + 1) = n (t + 1) - n (t + 2)),
            A' t = ψ.submatrix (finCongr h1) (finCongr h2)) ∧
          (∀ i, t < i → A' i = 0) := by
    refine ⟨fun i => Matrix.of fun a b =>
      if i = t then
        (if ha : (a : ℕ) < n t then
          (if hb : (b : ℕ) < n (t + 1) - n (t + 2) then ψ ⟨a, ha⟩ ⟨b, hb⟩ else 0) else 0)
      else if i < t then
        (if ha : (a : ℕ) < n i then
          (if hb : (b : ℕ) < n (i + 1) then A i ⟨a, ha⟩ ⟨b, hb⟩ else 0) else 0)
      else 0, ?_, ?_, ?_⟩
    · intro i hi h1 h2
      ext a b
      have ha : (a : ℕ) < n i := h1 ▸ a.isLt
      have hb : (b : ℕ) < n (i + 1) := h2 ▸ b.isLt
      have hit : i ≠ t := by omega
      simp only [Matrix.of_apply, Matrix.submatrix_apply, finCongr_apply, hit, hi, ha, hb,
        ite_false, ite_true, dite_true]
      rfl
    · intro h1 h2
      ext a b
      have ha : (a : ℕ) < n t := h1 ▸ a.isLt
      have hb : (b : ℕ) < n (t + 1) - n (t + 2) := h2 ▸ b.isLt
      simp only [Matrix.of_apply, Matrix.submatrix_apply, finCongr_apply, ha, hb,
        ite_true, dite_true]
      rfl
    · intro i hi
      ext a b
      have hit : i ≠ t := by omega
      have hit2 : ¬ (i < t) := by omega
      simp [hit, hit2]
  refine ⟨n', A', hn'le, by rw [hn'mid]; omega, hn'hi, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases lt_trichotomy i t with hi | hi | hi
    · rcases Nat.lt_or_ge (i + 1) t with hi1 | hi1
      · rw [hA'lt i hi (hn'le i (by omega)) (hn'le (i + 1) (by omega)),
          hA'lt (i + 1) hi1 (hn'le (i + 1) (by omega)) (hn'le (i + 1 + 1) (by omega)),
          Matrix.submatrix_mul_equiv (A i) (A (i + 1)) _
            (finCongr (hn'le (i + 1) (show i + 1 ≤ t by omega))) _, hA i]
        rfl
      · obtain rfl : i + 1 = t := by omega
        rw [hA'lt i hi (hn'le i (by omega)) (hn'le (i + 1) (by omega)),
          hA'mid (hn'le (i + 1) (by omega)) hn'mid,
          Matrix.submatrix_mul_equiv (A i) ψ _
            (finCongr (hn'le (i + 1) (show i + 1 ≤ i + 1 from le_rfl))) _]
        have hzero : A i * ψ = 0 := by
          rw [hψdef, mul_submatrix_right, hA i]
          simp
        rw [hzero]
        rfl
    · subst hi
      rw [hA'hi (i + 1) (by omega), Matrix.mul_zero]
    · rw [hA'hi i hi, Matrix.zero_mul]
  · intro k hk
    rcases Nat.lt_or_ge k t with hkt | hkt
    · rw [hA'lt k hkt (hn'le k (by omega)) (hn'le (k + 1) (by omega)),
        exteriorRank_submatrix_equiv']
    · obtain rfl : k = t := by omega
      rw [hA'mid (hn'le k le_rfl) hn'mid, exteriorRank_submatrix_equiv', exteriorRank_eq_rank,
        exteriorRank_eq_rank, hrankeq]
  · intro k hk
    rcases Nat.lt_or_ge k t with hkt | hkt
    · rw [hA'lt k hkt (hn'le k (by omega)) (hn'le (k + 1) (by omega)),
        detIdeal_submatrix_equiv']
    · obtain rfl : k = t := by omega
      rw [hA'mid (hn'le k le_rfl) hn'mid, detIdeal_submatrix_equiv', detIdeal_eq_minorIdeal,
        detIdeal_eq_minorIdeal, hidealeq]
  · intro hE k hk
    rcases Nat.lt_or_ge k t with hkt | hkt
    · have hEk := hE k (by omega)
      rcases Nat.lt_or_ge (k + 1) t with hk1 | hk1
      · rw [hA'lt k hkt (hn'le k (by omega)) (hn'le (k + 1) (by omega)),
          hA'lt (k + 1) hk1 (hn'le (k + 1) (by omega)) (hn'le (k + 1 + 1) (by omega))] at hEk
        exact exact_eqn_unreindex (A k) (A (k + 1)) _ _ _ hEk
      · obtain rfl : k + 1 = t := by omega
        rw [hA'lt k hkt (hn'le k (by omega)) (hn'le (k + 1) (by omega)),
          hA'mid (hn'le (k + 1) (show k + 1 ≤ k + 1 from le_rfl)) hn'mid] at hEk
        rw [exact_eqn_unreindex (A k) ψ _ _ _ hEk]
        exact hrangeeq
    · rcases Nat.lt_or_ge k (t + 1) with hkt1 | hkt1
      · obtain rfl : k = t := by omega
        have hEt := hE k le_rfl
        rw [hA'mid (hn'le k le_rfl) hn'mid, hA'hi (k + 1) (by omega)] at hEt
        have hz0 : LinearMap.range
            ((0 : Matrix (Fin (n' (k + 1))) (Fin (n' (k + 1 + 1))) R)).mulVecLin = ⊥ := by
          simp
        rw [hz0, LinearMap.ker_eq_bot] at hEt
        exact hkerD (LinearMap.ker_eq_bot.mpr
          (injective_of_injective_submatrix _ (finCongr (hn'le k le_rfl)) (finCongr hn'mid) hEt))
      · obtain rfl : k = t + 1 := by omega
        rw [hTinj]
        exact (BoundedFreeComplex.range_eq_bot_of_zero_source
          (htop (t + 1 + 1 + 1) (by omega)) (A (t + 1 + 1))).symm

/-- **The converse direction of the criterion, on matrices, by induction on `dim R`.** The outer
induction is on a natural number bounding the height of the maximal ideal: for a non-maximal prime
`𝔮` the height of `𝔮` is strictly smaller, and the localized complex still satisfies the numerical
conditions (`numericalMat_map_atPrime`), so the inductive hypothesis makes it exact.

The inner induction is on the top degree `E`. If the determinantal ideal of the top differential is
proper then it lies in the maximal ideal, so condition (2)(b) bounds the depth of `R` from below by
`E + 1` and the acyclicity step `ker_eq_range_of_forall_atPrime` applies. Otherwise it is the unit
ideal, and `exists_top_split` splits a trivial complex off the top, reducing `E`; for `E = 0` the
unit ideal gives injectivity outright. -/
private theorem ker_eq_range_of_numericalMat :
    ∀ (d E : ℕ) {S : Type*} [CommRing S] [IsNoetherianRing S] [IsLocalRing S] (n : ℕ → ℕ)
      (A : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) S),
      (IsLocalRing.maximalIdeal S).height ≤ (d : ℕ∞) →
      (∀ i, E + 1 < i → n i = 0) → (∀ i, A i * A (i + 1) = 0) →
      (∀ k ≤ E, NumericalMat E n A k) →
      ∀ k ≤ E, LinearMap.ker (A k).mulVecLin = LinearMap.range (A (k + 1)).mulVecLin := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IHd =>
    intro E
    induction E with
    | zero =>
      intro S _ _ _ n A _ htop _ hnum k hk
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      have hb : LinearMap.range (A 1).mulVecLin = ⊥ :=
        BoundedFreeComplex.range_eq_bot_of_zero_source (htop (1 + 1) (by omega)) (A 1)
      show LinearMap.ker (A 0).mulVecLin = LinearMap.range (A 1).mulVecLin
      rw [hb, LinearMap.ker_eq_bot]
      obtain ⟨hr, hdep⟩ := hnum 0 le_rfl
      refine (injective_iff_rank_eq_and_contains_nonZeroDivisor (A 0)).mpr ⟨?_, ?_⟩
      · have : (exteriorRank (A 0) : ℤ) = (n 1 : ℤ) := by rw [hr]; simp
        exact_mod_cast this
      · exact (one_le_depth_self_iff (detIdeal (A 0))).mp (by simpa using hdep)
    | succ t IHE =>
      intro S _ _ _ n A hht htop hA hnum
      by_cases hItop : detIdeal (A (t + 1)) = ⊤
      · have hrk : exteriorRank (A (t + 1)) = n (t + 2) := by
          have h := (hnum (t + 1) le_rfl).1
          rw [show t + 1 + 1 - (t + 1) = 1 from by omega] at h
          simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul] at h
          exact_mod_cast h
        obtain ⟨n', A', hn'le, hn'top, htop', hA', hrank', hideal', htransfer⟩ :=
          exists_top_split t n A htop hA hrk hItop
        refine htransfer (IHE n' A' hht htop' hA' ?_)
        intro k hk
        obtain ⟨hr, hd⟩ := hnum k (by omega)
        refine ⟨?_, ?_⟩
        · rw [hrank' k hk, hr]
          rw [show t + 1 + 1 - k = (t - k) + 2 from by omega,
            show t + 1 - k = (t - k) + 1 from by omega,
            Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
          have hlow : ∀ s ∈ Finset.range (t - k),
              (-1 : ℤ) ^ s * (n' (k + 1 + s) : ℤ) = (-1) ^ s * (n (k + 1 + s) : ℤ) := by
            intro s hs
            rw [Finset.mem_range] at hs
            rw [hn'le (k + 1 + s) (by omega)]
          rw [Finset.sum_congr rfl hlow,
            show k + 1 + (t - k) = t + 1 from by omega, hn'top,
            show k + 1 + (t - k + 1) = t + 2 from by omega]
          ring
        · rw [hideal' k hk]
          exact hd
      · have hIm : detIdeal (A (t + 1)) ≤ IsLocalRing.maximalIdeal S :=
          IsLocalRing.le_maximalIdeal hItop
        have hdep : ((t + 1 + 1 : ℕ) : ℕ∞)
            ≤ Module.depth S (IsLocalRing.maximalIdeal S) S :=
          (hnum (t + 1) le_rfl).2.trans (depth_mono_ideal hIm S)
        refine ker_eq_range_of_forall_atPrime (t + 1) n A htop hA hdep ?_
        intro q _ hqm k hkt
        have : q.FiniteHeight := Ideal.finiteHeight_of_isNoetherianRing q
        have hlt : q.height < (IsLocalRing.maximalIdeal S).height :=
          Ideal.height_strict_mono_of_isPrime
            (lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (‹q.IsPrime›).ne_top) hqm)
        have hqfin : q.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
        obtain ⟨d', hd'⟩ : ∃ d' : ℕ, q.height = (d' : ℕ∞) :=
          ⟨q.height.toNat, by rw [ENat.natCast_toNat hqfin]⟩
        have hd'lt : d' < d := by
          have h : (d' : ℕ∞) < (d : ℕ∞) := hd' ▸ lt_of_lt_of_le hlt hht
          exact_mod_cast h
        have hunder : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).under S = q :=
          Localization.AtPrime.under_maximalIdeal
        have hh1 := IsLocalization.height_under q.primeCompl
          (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        rw [hunder] at hh1
        have hheight : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).height
            ≤ (d' : ℕ∞) := by rw [← hh1, hd']
        exact IHd d' hd'lt (t + 1) n
          (fun i => (A i).map (algebraMap S (Localization.AtPrime q))) hheight htop
          (fun i => by rw [← Matrix.map_mul, hA i, Matrix.map_zero _ (map_zero _)])
          (numericalMat_map_atPrime (t + 1) n A q hnum) k hkt

/-- **The converse direction of the criterion, on matrices.** If the numerical conditions hold at
every matrix of degree `≤ E`, the complex is injective at the top and exact below. -/
private lemma ker_eq_range_of_numericalMat_of_lt (E : ℕ) (n : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) R)
    (hA : ∀ i < E, A i * A (i + 1) = 0)
    (hnum : ∀ k ≤ E, NumericalMat E n A k) :
    Function.Injective (A E).mulVecLin ∧
      ∀ k < E, LinearMap.ker (A k).mulVecLin = LinearMap.range (A (k + 1)).mulVecLin := by
  have hz : ∀ i, E + 1 < i → truncRank (E + 1) n i = 0 := fun i hi => truncRank_of_lt n hi
  have hAAc : ∀ i, truncMat (E + 1) n A i * truncMat (E + 1) n A (i + 1) = 0 := by
    intro i
    by_cases hi : i < E
    · rw [truncMat_eq n A (show i ≤ E + 1 by omega) (show i + 1 ≤ E + 1 by omega),
        truncMat_eq n A (show i + 1 ≤ E + 1 by omega) (show i + 1 + 1 ≤ E + 1 by omega),
        Matrix.submatrix_mul_equiv (A i) (A (i + 1)) _
          (truncEquiv n (show i + 1 ≤ E + 1 by omega)) _, hA i hi]
      rfl
    · exact matrix_eq_zero_of_ncols (hz (i + 2) (by omega)) _
  have hnumAA : ∀ k ≤ E, NumericalMat E (truncRank (E + 1) n) (truncMat (E + 1) n A) k := by
    intro k hk
    obtain ⟨hr, hd⟩ := hnum k hk
    have h1 : k ≤ E + 1 := by omega
    have h2 : k + 1 ≤ E + 1 := by omega
    refine ⟨?_, ?_⟩
    · rw [truncMat_eq n A h1 h2, exteriorRank_submatrix_equiv', hr]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_range] at hs
      rw [truncRank_of_le n (show k + 1 + s ≤ E + 1 by omega)]
    · rw [truncMat_eq n A h1 h2, detIdeal_submatrix_equiv']; exact hd
  have hmain := ker_eq_range_of_numericalMat ((IsLocalRing.maximalIdeal R).height).toNat E
    (truncRank (E + 1) n) (truncMat (E + 1) n A)
    (by rw [ENat.natCast_toNat Ideal.height_ne_top_of_isPrime]) hz hAAc hnumAA
  refine ⟨?_, fun k hk => ?_⟩
  · have hE := hmain E le_rfl
    have hb : LinearMap.range (truncMat (E + 1) n A (E + 1)).mulVecLin = ⊥ :=
      BoundedFreeComplex.range_eq_bot_of_zero_source (hz (E + 2) (by omega)) _
    rw [hb, LinearMap.ker_eq_bot] at hE
    have h1 : E ≤ E + 1 := by omega
    have h2 : E + 1 ≤ E + 1 := le_rfl
    rw [truncMat_eq n A h1 h2] at hE
    exact injective_of_injective_submatrix _ (truncEquiv n h1) (truncEquiv n h2) hE
  · have hkk := hmain k (by omega)
    rw [truncMat_eq n A (show k ≤ E + 1 by omega) (show k + 1 ≤ E + 1 by omega),
      truncMat_eq n A (show k + 1 ≤ E + 1 by omega) (show k + 1 + 1 ≤ E + 1 by omega)] at hkk
    exact exact_eqn_unreindex (A k) (A (k + 1)) _ _ _ hkk

/-- **The converse direction for `e + 1`.** Over a local Noetherian ring, if every `φ k`,
`k ≤ e + 1`, has rank the alternating sum `n_{k+1} - n_{k+2} + ⋯ ± n_{e+2}` and
`depth_{I(φ k)}(R) ≥ k + 1`, then `0 → R^{n_{e+2}} → ⋯ → R^{n_0}` is exact at
`R^{n_{e+2}}, …, R^{n_1}`. -/
private lemma exact_of_forall_succ (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e + 1, φ k ∘ₗ φ (k + 1) = 0)
    (hnum : ∀ k ≤ e + 1, Numerical (e + 1) n φ k) :
    Function.Injective (φ (e + 1)) ∧ ∀ k < e + 1, Function.Exact (φ (k + 1)) (φ k) := by
  have hmv : ∀ i, (LinearMap.toMatrix' (φ i)).mulVecLin = φ i :=
    fun i => Matrix.toLin'_toMatrix' (φ i)
  have hA : ∀ i < e + 1, LinearMap.toMatrix' (φ i) * LinearMap.toMatrix' (φ (i + 1)) = 0 := by
    intro i hi
    rw [← LinearMap.toMatrix'_comp, hφ i hi]
    simp
  obtain ⟨hinj, hex⟩ := ker_eq_range_of_numericalMat_of_lt (e + 1) n
    (fun i => LinearMap.toMatrix' (φ i)) hA fun k hk => (numerical_iff_numericalMat _ n φ k).mp
      (hnum k hk)
  refine ⟨?_, fun k hk => ?_⟩
  · rw [← hmv (e + 1)]
    exact hinj
  · rw [LinearMap.exact_iff, ← hmv k, ← hmv (k + 1)]
    exact hex k hk

/-- **Forward direction of the criterion.** If the complex is exact at `R^{n_{e+1}}, …, R^{n_1}`
then each `φ k` has the expected rank and `I(φ k)` has depth at least `k + 1`. -/
private lemma forward_of_exact (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0)
    (hinj : Function.Injective (φ e))
    (hex : ∀ k < e, Function.Exact (φ (k + 1)) (φ k)) :
    ∀ k ≤ e, Numerical e n φ k := fun k hk =>
  ⟨rank_eq_of_exact e n φ hφ hinj hex k hk, le_depth_detIdeal_of_exact e n φ hφ hinj hex k hk⟩

/-- **Converse direction of the criterion.** If each `φ k` has the expected rank and `I(φ k)` has
depth at least `k + 1`, the complex is exact at `R^{n_{e+1}}, …, R^{n_1}`. -/
private lemma exact_of_forall (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0)
    (hnum : ∀ k ≤ e, Numerical e n φ k) :
    Function.Injective (φ e) ∧ ∀ k < e, Function.Exact (φ (k + 1)) (φ k) := by
  cases e with
  | zero =>
    refine ⟨(numerical_zero_iff n φ).mpr (hnum 0 le_rfl), ?_⟩
    intro k hk
    exact absurd hk (Nat.not_lt_zero k)
  | succ e' => exact exact_of_forall_succ e' n φ hφ hnum

end Criterion

/-- **Buchsbaum–Eisenbud exactness criterion.** A complex
`0 → R^{n_{e+1}} →[φ e] R^{n_e} → ⋯ → R^{n_1} →[φ 0] R^{n_0}` of finite free modules over a
local Noetherian ring is exact at `R^{n_{e+1}}, …, R^{n_1}` if and only if, for every `k ≤ e`,
the rank `r` of `φ k` is the alternating sum `n_{k+1} - n_{k+2} + ⋯ ± n_{e+1}` and the ideal
generated by the `r × r` minors of the matrix of `φ k` has depth at least `k + 1`. -/
public theorem solution
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) :
    (Function.Injective (φ e) ∧ ∀ k < e, Function.Exact (φ (k + 1)) (φ k)) ↔
      ∀ k ≤ e, ∃ r : ℕ,
        (r : ℤ) = ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ) ∧
        IsGreatest {j : ℕ | exteriorPower.map j (φ k) ≠ 0} r ∧
        ((k + 1 : ℕ) : ℕ∞) ≤ Module.depth R (Ideal.span {x : R |
          ∃ (ρ : Fin r → Fin (n k)) (γ : Fin r → Fin (n (k + 1))),
            ((LinearMap.toMatrix' (φ k)).submatrix ρ γ).det = x}) R := by
  have hrewrite : ∀ k : ℕ, (∃ r : ℕ,
      (r : ℤ) = ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ) ∧
      IsGreatest {j : ℕ | exteriorPower.map j (φ k) ≠ 0} r ∧
      ((k + 1 : ℕ) : ℕ∞) ≤ Module.depth R (Ideal.span {x : R |
        ∃ (ρ : Fin r → Fin (n k)) (γ : Fin r → Fin (n (k + 1))),
          ((LinearMap.toMatrix' (φ k)).submatrix ρ γ).det = x}) R) ↔ Numerical e n φ k :=
    fun k => exists_rank_iff (φ k) _ _
  refine ⟨fun h k hk => (hrewrite k).mpr (forward_of_exact e n φ hφ h.1 h.2 k hk),
    fun h => exact_of_forall e n φ hφ fun k hk => (hrewrite k).mp (h k hk)⟩

end Stacks.Depth.BuchsbaumEisenbud

/-- **Buchsbaum–Eisenbud exactness criterion.** A complex
`0 → R^{n_{e+1}} →[φ e] R^{n_e} → ⋯ → R^{n_1} →[φ 0] R^{n_0}` of finite free modules over a
local Noetherian ring is exact at `R^{n_{e+1}}, …, R^{n_1}` if and only if, for every `k ≤ e`,
the rank of `φ k` — the largest `r` with `⋀^r (φ k) ≠ 0` — is the alternating sum
`n_{k+1} - n_{k+2} + ⋯ ± n_{e+1}`, and the ideal generated by the `r × r` minors of the matrix
of `φ k` has depth at least `k + 1`, that is, it is `R` or contains a regular sequence of
length `k + 1`. -/
@[stacks 00N1]
public theorem LinearMap.injective_and_exact_iff_forall_rank_eq_and_le_depth_minors
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) :
    (Function.Injective (φ e) ∧ ∀ k < e, Function.Exact (φ (k + 1)) (φ k)) ↔
      ∀ k ≤ e, ∃ r : ℕ,
        (r : ℤ) = ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ) ∧
        IsGreatest {j : ℕ | exteriorPower.map j (φ k) ≠ 0} r ∧
        ((k + 1 : ℕ) : ℕ∞) ≤ Module.depth R (Ideal.span {x : R |
          ∃ (ρ : Fin r → Fin (n k)) (γ : Fin r → Fin (n (k + 1))),
            ((LinearMap.toMatrix' (φ k)).submatrix ρ γ).det = x}) R :=
  Stacks.Depth.BuchsbaumEisenbud.solution e n φ hφ

end
