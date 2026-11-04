module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.LinearAlgebra.Matrix.DeterminantalRank.ComplexRank

/-!
# Complexes isomorphic to a direct sum of trivial complexes

For a complex `0 → R^{n_e} →^{φ_e} R^{n_{e-1}} → ⋯ → R^{n_1} →^{φ_1} R^{n_0}` of finite free
modules which is isomorphic to a direct sum of trivial complexes, set
`r_i = ∑_{k=i}^e (-1)^{k-i} n_k`. Then `rank (φ_i) = r_i`, `rank (φ_{i+1}) + rank (φ_i) = n_i`
and `I(φ_i) = R`.

The invariance results of `StacksFrontier.LinearAlgebra.Matrix.DeterminantalRank.ComplexRank`
reduce these statements to a complex that is an actual direct sum of trivial complexes, where
they are proved by induction on `StacksComplex.IsSumOfTrivials`.

## Main results

* `StacksComplex.rank_eq_rIndex`, `StacksComplex.rank_add_rank`,
  `StacksComplex.minorIdeal_eq_top`: the ranks and determinantal ideals of a complex isomorphic
  to a direct sum of trivial complexes.

## References

* [StacksProject 00MW](https://stacks.math.columbia.edu/tag/00MW)
-/

@[expose] public section

namespace StacksComplex

variable {R : Type*} [CommRing R] [Nontrivial R] {e : ℕ}

/-! ## Direct sums of trivial complexes

The rank, `rIndex` and `minorIdeal` statements for a complex that is a direct sum of trivial
complexes, by induction on `IsSumOfTrivials`. -/

section NormalForm

open Matrix

omit [Nontrivial R] in
/-- Reindexing the row/column index sets by bijections does not change `rankSet`. -/
theorem rankSet_reindex {m n : ℕ}
    (φ : Matrix (Fin n) (Fin m) R) (eₙ : Fin n ≃ Fin n) (eₘ : Fin m ≃ Fin m) :
    rankSet (φ.reindex eₙ eₘ) = rankSet φ := by
  rw [Matrix.reindex_apply]
  exact rankSet_submatrix_equiv φ eₙ.symm eₘ.symm

omit [Nontrivial R] in
/-- If `N` is reindexed on rows and columns by two equivalences from a common type `T`,
the determinant is nonzero iff `det N` is nonzero (they differ by the sign unit). -/
theorem det_submatrix_two_equiv_ne {r : ℕ} {T : Type*} [Fintype T] [DecidableEq T]
    (N : Matrix (Fin r) (Fin r) R) (f g : T ≃ Fin r) :
    (N.submatrix f g).det ≠ 0 ↔ N.det ≠ 0 := by
  have heq : (N.submatrix (f : T → Fin r) (g : T → Fin r))
      = (N.submatrix f f).submatrix id (g.trans f.symm) := by
    ext x y; simp [Matrix.submatrix_apply]
  rw [heq, Matrix.det_permute', Matrix.det_submatrix_equiv_self f N]
  have hu : IsUnit ((Equiv.Perm.sign (g.trans f.symm) : ℤ) : R) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (g.trans f.symm)) with h | h <;> rw [h] <;> simp
  rw [ne_eq, hu.mul_right_eq_zero, ne_eq]

omit [Nontrivial R] in
/-- A nonzero minor of `A` indexed by an arbitrary fintype `T` yields a nonzero
`Fintype.card T`-minor of `A`. -/
theorem minor_subtype_ne {a a' : ℕ} {T : Type*} [Fintype T] [DecidableEq T]
    (A : Matrix (Fin a) (Fin a') R) (rows : T → Fin a) (cols : T → Fin a')
    (h : (A.submatrix rows cols).det ≠ 0) :
    ∃ (rows' : Fin (Fintype.card T) → Fin a) (cols' : Fin (Fintype.card T) → Fin a'),
      (A.submatrix rows' cols').det ≠ 0 := by
  refine ⟨rows ∘ (Fintype.equivFin T).symm, cols ∘ (Fintype.equivFin T).symm, ?_⟩
  have : A.submatrix (rows ∘ (Fintype.equivFin T).symm) (cols ∘ (Fintype.equivFin T).symm)
        = (A.submatrix rows cols).submatrix
            (Fintype.equivFin T).symm (Fintype.equivFin T).symm := by
    ext x y; simp [Matrix.submatrix_apply]
  rw [this, Matrix.det_submatrix_equiv_self]; exact h

omit [Nontrivial R] in
/-- **Block split for a nonzero minor of a block-diagonal matrix.** A nonzero `r×r`
minor of `fromBlocks A 0 0 B` factors as a product of an `lr×lr` minor of `A` and an
`rr×rr` minor of `B` with `lr + rr = r`. (Holds over any commutative ring.) -/
theorem block_split {a a' b b' r : ℕ}
    (A : Matrix (Fin a) (Fin a') R) (B : Matrix (Fin b) (Fin b') R)
    (ρ : Fin r → Fin a ⊕ Fin b) (γ : Fin r → Fin a' ⊕ Fin b')
    (hdet : (((Matrix.fromBlocks A 0 0 B)).submatrix ρ γ).det ≠ 0) :
    ∃ lr rr, lr + rr = r ∧
      (∃ (rows : Fin lr → Fin a) (cols : Fin lr → Fin a'), (A.submatrix rows cols).det ≠ 0) ∧
      (∃ (rows : Fin rr → Fin b) (cols : Fin rr → Fin b'), (B.submatrix rows cols).det ≠ 0) := by
  set M := Matrix.fromBlocks A 0 0 B with hM
  set N := M.submatrix ρ γ with hN
  let pr : Fin r → Prop := fun i => Sum.isLeft (ρ i) = true
  let pc : Fin r → Prop := fun j => Sum.isLeft (γ j) = true
  have hcard : Fintype.card {i // pr i} = Fintype.card {j // pc j} := by
    rw [Matrix.det_apply] at hdet
    obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
    have hprod : ∀ i, M (ρ (σ i)) (γ i) ≠ 0 := by
      intro i h0
      apply hσ
      have hz : ∏ i, N (σ i) i = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simpa [hN, Matrix.submatrix_apply] using h0
      rw [hz]; simp
    have hmap : ∀ i, Sum.isLeft (ρ (σ i)) = Sum.isLeft (γ i) := by
      intro i
      have := hprod i
      rcases hρ : ρ (σ i) with x | x <;> rcases hγ : γ i with y | y <;>
        simp_all [Matrix.fromBlocks]
    apply (Fintype.card_eq.mpr ?_).symm
    refine ⟨⟨fun j => ⟨σ j.val, by
               show Sum.isLeft (ρ (σ j.val)) = true; rw [hmap]; exact j.property⟩,
             fun i => ⟨σ.symm i.val, ?_⟩, ?_, ?_⟩⟩
    · show Sum.isLeft (γ (σ.symm i.val)) = true
      have := hmap (σ.symm i.val); rw [Equiv.apply_symm_apply] at this
      rw [← this]; exact i.property
    · intro j; ext; simp
    · intro i; ext; simp
  have hcardc : Fintype.card {i // ¬ pr i} = Fintype.card {j // ¬ pc j} := by
    have h1 : Fintype.card {i // pr i} + Fintype.card {i // ¬ pr i} = r := by
      rw [Fintype.card_subtype_compl]
      have : Fintype.card {i // pr i} ≤ Fintype.card (Fin r) := Fintype.card_subtype_le _
      simp at this ⊢; omega
    have h2 : Fintype.card {j // pc j} + Fintype.card {j // ¬ pc j} = r := by
      rw [Fintype.card_subtype_compl]
      have : Fintype.card {j // pc j} ≤ Fintype.card (Fin r) := Fintype.card_subtype_le _
      simp at this ⊢; omega
    omega
  let bl : {i // pr i} ≃ {j // pc j} := Fintype.equivOfCardEq hcard
  let br : {i // ¬ pr i} ≃ {j // ¬ pc j} := Fintype.equivOfCardEq hcardc
  set er := Equiv.sumCompl pr with her
  set g := (Equiv.sumCongr bl br).trans (Equiv.sumCompl pc) with hg
  have hll : ∀ x : {i // pr i}, (ρ x.val).isLeft = true := fun x => x.property
  have hcl : ∀ y : {i // pr i}, (γ (bl y).val).isLeft = true := fun y => (bl y).property
  have hrr : ∀ x : {i // ¬ pr i}, (ρ x.val).isRight = true := by
    intro x; have hx := x.property; simp only [pr] at hx
    rcases h : ρ x.val with z | z
    · rw [h] at hx; simp at hx
    · rfl
  have hcr : ∀ y : {i // ¬ pr i}, (γ (br y).val).isRight = true := by
    intro y; have hy := (br y).property; simp only [pc] at hy
    rcases h : γ (br y).val with z | z
    · rw [h] at hy; simp at hy
    · rfl
  let rowA : {i // pr i} → Fin a := fun x => (ρ x.val).getLeft (hll x)
  let colA : {i // pr i} → Fin a' := fun y => (γ (bl y).val).getLeft (hcl y)
  let rowB : {i // ¬ pr i} → Fin b := fun x => (ρ x.val).getRight (hrr x)
  let colB : {i // ¬ pr i} → Fin b' := fun y => (γ (br y).val).getRight (hcr y)
  have hblock : N.submatrix er g
      = Matrix.fromBlocks (A.submatrix rowA colA) 0 0 (B.submatrix rowB colB) := by
    ext i j
    rcases i with x | x <;> rcases j with y | y <;>
      simp only [hN, hM, her, hg, Matrix.submatrix_apply, Matrix.fromBlocks,
          Equiv.sumCompl_apply_inl,
        Equiv.sumCompl_apply_inr, Equiv.sumCongr_apply, Equiv.coe_trans, Function.comp_apply,
        Sum.map_inl, Sum.map_inr, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    · show M (ρ x.val) (γ (bl y).val) = A (rowA x) (colA y)
      rw [show ρ x.val = Sum.inl (rowA x) from (Sum.inl_getLeft (ρ x.val) (hll x)).symm,
          show γ (bl y).val = Sum.inl (colA y) from (Sum.inl_getLeft (γ (bl y).val) (hcl y)).symm]
      simp [hM]
    · show M (ρ x.val) (γ (br y).val) = 0
      rw [show ρ x.val = Sum.inl (rowA x) from (Sum.inl_getLeft (ρ x.val) (hll x)).symm,
          show γ (br y).val = Sum.inr (colB y) from (Sum.inr_getRight (γ (br y).val) (hcr y)).symm]
      simp [hM]
    · show M (ρ x.val) (γ (bl y).val) = 0
      rw [show ρ x.val = Sum.inr (rowB x) from (Sum.inr_getRight (ρ x.val) (hrr x)).symm,
          show γ (bl y).val = Sum.inl (colA y) from (Sum.inl_getLeft (γ (bl y).val) (hcl y)).symm]
      simp [hM]
    · show M (ρ x.val) (γ (br y).val) = B (rowB x) (colB y)
      rw [show ρ x.val = Sum.inr (rowB x) from (Sum.inr_getRight (ρ x.val) (hrr x)).symm,
          show γ (br y).val = Sum.inr (colB y) from (Sum.inr_getRight (γ (br y).val) (hcr y)).symm]
      simp [hM]
  have hdne : (N.submatrix er g).det ≠ 0 := (det_submatrix_two_equiv_ne N er g).mpr hdet
  rw [hblock, Matrix.det_fromBlocks_zero₁₂] at hdne
  have hA : (A.submatrix rowA colA).det ≠ 0 := fun h => hdne (by rw [h]; ring)
  have hB : (B.submatrix rowB colB).det ≠ 0 := fun h => hdne (by rw [h]; ring)
  refine ⟨Fintype.card {i // pr i}, Fintype.card {i // ¬ pr i}, ?_, ?_, ?_⟩
  · rw [Fintype.card_subtype_compl]
    have : Fintype.card {i // pr i} ≤ Fintype.card (Fin r) := Fintype.card_subtype_le _
    simp at this ⊢; omega
  · exact minor_subtype_ne A rowA colA hA
  · exact minor_subtype_ne B rowB colB hB

omit [Nontrivial R] in
/-- The submatrix of `fromBlocks A 0 0 B` selected by `Sum.map`-indices is the
block-diagonal matrix of the two submatrices. -/
theorem submatrix_fromBlocks_sumMap {a a' b b' r₁ r₂ : ℕ}
    (A : Matrix (Fin a) (Fin a') R) (B : Matrix (Fin b) (Fin b') R)
    (rows₁ : Fin r₁ → Fin a) (cols₁ : Fin r₁ → Fin a')
    (rows₂ : Fin r₂ → Fin b) (cols₂ : Fin r₂ → Fin b') :
    (Matrix.fromBlocks A (0 : Matrix (Fin a) (Fin b') R) (0 : Matrix (Fin b) (Fin a') R)
        B).submatrix
      (Sum.map rows₁ rows₂) (Sum.map cols₁ cols₂)
      = Matrix.fromBlocks (A.submatrix rows₁ cols₁) 0 0 (B.submatrix rows₂ cols₂) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.submatrix_apply, Matrix.fromBlocks]

omit [Nontrivial R] in
/-- **Combine two unit minors into a unit minor of the direct sum.** -/
theorem combine_unit_minor (C₁ C₂ : Complex R e) (k : ℕ) {s₁ s₂ : ℕ}
    (rows₁ : Fin s₁ → Fin (C₁.n k)) (cols₁ : Fin s₁ → Fin (C₁.n (k + 1)))
    (rows₂ : Fin s₂ → Fin (C₂.n k)) (cols₂ : Fin s₂ → Fin (C₂.n (k + 1)))
    (h₁ : IsUnit ((C₁.d k).submatrix rows₁ cols₁).det)
    (h₂ : IsUnit ((C₂.d k).submatrix rows₂ cols₂).det) :
    ∃ (rows : Fin (s₁ + s₂) → Fin ((directSum C₁ C₂).n k))
      (cols : Fin (s₁ + s₂) → Fin ((directSum C₁ C₂).n (k+1))),
      IsUnit (((directSum C₁ C₂).d k).submatrix rows cols).det := by
  refine ⟨finSumFinEquiv ∘ Sum.map rows₁ rows₂ ∘ finSumFinEquiv.symm,
          finSumFinEquiv ∘ Sum.map cols₁ cols₂ ∘ finSumFinEquiv.symm, ?_⟩
  show IsUnit ((((Matrix.fromBlocks (C₁.d k) 0 0 (C₂.d k)).reindex finSumFinEquiv
      finSumFinEquiv).submatrix
      (finSumFinEquiv ∘ Sum.map rows₁ rows₂ ∘ finSumFinEquiv.symm)
      (finSumFinEquiv ∘ Sum.map cols₁ cols₂ ∘ finSumFinEquiv.symm)).det)
  rw [Matrix.reindex_apply, Matrix.submatrix_submatrix]
  have : (Matrix.fromBlocks (C₁.d k) 0 0 (C₂.d k)).submatrix
      (finSumFinEquiv.symm ∘ (finSumFinEquiv ∘ Sum.map rows₁ rows₂ ∘ finSumFinEquiv.symm))
      (finSumFinEquiv.symm ∘ (finSumFinEquiv ∘ Sum.map cols₁ cols₂ ∘ finSumFinEquiv.symm))
      = ((Matrix.fromBlocks (C₁.d k) 0 0 (C₂.d k)).submatrix
            (Sum.map rows₁ rows₂) (Sum.map cols₁ cols₂)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [Matrix.submatrix_submatrix]
    congr 1 <;> (ext z; simp)
  rw [this, submatrix_fromBlocks_sumMap, Matrix.det_submatrix_equiv_self,
      Matrix.det_fromBlocks_zero₁₂]
  exact h₁.mul h₂

/-- **The `≤` direction of rank additivity** (valid over any commutative ring). -/
theorem rank_le_directSum (C₁ C₂ : Complex R e) (k : ℕ) :
    rank ((directSum C₁ C₂).d k) ≤ rank (C₁.d k) + rank (C₂.d k) := by
  apply rank_le
  intro r hr
  obtain ⟨rows, cols, hdet⟩ := hr
  have hdet' : ((Matrix.fromBlocks (C₁.d k) 0 0 (C₂.d k)).submatrix
      (finSumFinEquiv.symm ∘ rows) (finSumFinEquiv.symm ∘ cols)).det ≠ 0 := by
    have : ((directSum C₁ C₂).d k).submatrix rows cols
        = (Matrix.fromBlocks (C₁.d k) 0 0 (C₂.d k)).submatrix
            (finSumFinEquiv.symm ∘ rows) (finSumFinEquiv.symm ∘ cols) := by
      show (((Matrix.fromBlocks (C₁.d k) 0 0 (C₂.d k)).reindex finSumFinEquiv
          finSumFinEquiv).submatrix rows cols) = _
      rw [Matrix.reindex_apply, Matrix.submatrix_submatrix]
    rwa [this] at hdet
  obtain ⟨lr, rr, hsum, ⟨ro1, co1, hd1⟩, ⟨ro2, co2, hd2⟩⟩ :=
    block_split (C₁.d k) (C₂.d k) (finSumFinEquiv.symm ∘ rows) (finSumFinEquiv.symm ∘ cols) hdet'
  have h1 : lr ≤ rank (C₁.d k) := le_rank _ ⟨ro1, co1, hd1⟩
  have h2 : rr ≤ rank (C₂.d k) := le_rank _ ⟨ro2, co2, hd2⟩
  omega

omit [Nontrivial R] in
/-- If `rank φ = 0`, the empty minor is the unit `1`. -/
theorem exists_isUnit_det_submatrix_of_rank_eq_zero {m n : ℕ} (φ : Matrix (Fin n) (Fin m) R)
    (h : rank φ = 0) :
    ∃ (rows : Fin (rank φ) → Fin n) (cols : Fin (rank φ) → Fin m),
      IsUnit (((φ).submatrix rows cols).det) := by
  rw [h]
  exact ⟨Fin.elim0, Fin.elim0, by simp [Matrix.det_fin_zero]⟩

/-- If one of the two modules adjacent to `C.d k` is zero, then `C.d k` has rank `0`. -/
private theorem rank_d_eq_zero_of_n_eq_zero {C : Complex R e} {k : ℕ}
    (h : C.n k = 0 ∨ C.n (k + 1) = 0) : rank (C.d k) = 0 := by
  rcases h with h | h
  · exact Nat.le_zero.mp (le_trans (rank_le_n _) (by rw [h]))
  · exact Nat.le_zero.mp (le_trans (rank_le_m _) (by rw [h]))

/-- If `C.n j = C.n (j + 1) = 1` and all other modules vanish, then `C.d k` has rank `0` for
`k ≠ j`. -/
private theorem rank_d_eq_zero_of_ne {C : Complex R e} {j k : ℕ}
    (hother : ∀ i : ℕ, i ≠ j → i ≠ j + 1 → C.n i = 0) (hk : k ≠ j) : rank (C.d k) = 0 := by
  apply rank_d_eq_zero_of_n_eq_zero
  rcases Nat.lt_or_gt_of_ne hk with hlt | hgt
  · exact Or.inl (hother k hk (by omega))
  · exact Or.inr (hother (k + 1) (by omega) (by omega))

/-- A `1 × 1` differential with entry `1` has a `1 × 1` minor with unit determinant. -/
private theorem exists_isUnit_det_submatrix_one {S : Type*} [CommRing S] {C : Complex S e} {k : ℕ}
    (hnj1 : C.n (k + 1) = 1) (hnj : C.n k = 1) (hentry : ∀ a b, C.d k a b = 1) :
    ∃ (rows : Fin 1 → Fin (C.n k)) (cols : Fin 1 → Fin (C.n (k + 1))),
      IsUnit (((C.d k).submatrix rows cols).det) :=
  ⟨fun _ => ⟨0, by rw [hnj]; omega⟩, fun _ => ⟨0, by rw [hnj1]; omega⟩, by
    rw [Matrix.det_fin_one]; simp [Matrix.submatrix_apply, hentry]⟩

/-- A `1 × 1` differential with entry `1` has rank `1`. -/
private theorem rank_d_eq_one {C : Complex R e} {k : ℕ}
    (hnj1 : C.n (k + 1) = 1) (hnj : C.n k = 1) (hentry : ∀ a b, C.d k a b = 1) :
    rank (C.d k) = 1 := by
  obtain ⟨rows, cols, hu⟩ := exists_isUnit_det_submatrix_one hnj1 hnj hentry
  exact le_antisymm (le_trans (rank_le_n _) (by rw [hnj])) (le_rank _ ⟨rows, cols, hu.ne_zero⟩)

/-- For a trivial complex, some minor of `C.d k` of size `rank (C.d k)` has unit
determinant. -/
theorem IsTrivial.exists_isUnit_det_submatrix {C : Complex R e} (hC : IsTrivial C) (k : ℕ) :
    ∃ (rows : Fin (rank (C.d k)) → Fin (C.n k)) (cols : Fin (rank (C.d k)) → Fin (C.n (k+1))),
      IsUnit (((C.d k).submatrix rows cols).det) := by
  rcases hC with ⟨j, hje, hnj1, hnj, hentry, hother⟩ | ⟨hn0, hother⟩
  · by_cases hk : k = j
    · subst hk
      rw [rank_d_eq_one hnj1 hnj hentry]
      exact exists_isUnit_det_submatrix_one hnj1 hnj hentry
    · exact exists_isUnit_det_submatrix_of_rank_eq_zero _ (rank_d_eq_zero_of_ne hother hk)
  · exact exists_isUnit_det_submatrix_of_rank_eq_zero _
      (rank_d_eq_zero_of_n_eq_zero (Or.inr (hother (k + 1) (by omega))))

/-- **Unit-minor witness for sums of trivials**: there is a maximal (size `rank`) minor
of `C.d k` whose determinant is a unit. -/
theorem IsSumOfTrivials.exists_isUnit_det_submatrix {C : Complex R e} (hC : IsSumOfTrivials C)
    (k : ℕ) :
    ∃ (rows : Fin (rank (C.d k)) → Fin (C.n k)) (cols : Fin (rank (C.d k)) → Fin (C.n (k+1))),
      IsUnit (((C.d k).submatrix rows cols).det) := by
  induction hC with
  | zero => exact exists_isUnit_det_submatrix_of_rank_eq_zero _ (Nat.le_zero.mp (rank_le_n _))
  | trivial h => exact h.exists_isUnit_det_submatrix k
  | @sum C₁ C₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨ro1, co1, hu1⟩ := ih₁
    obtain ⟨ro2, co2, hu2⟩ := ih₂
    obtain ⟨rows, cols, hu⟩ := combine_unit_minor C₁ C₂ k ro1 co1 ro2 co2 hu1 hu2
    have hge : rank (C₁.d k) + rank (C₂.d k) ≤ rank ((directSum C₁ C₂).d k) :=
      le_rank _ ⟨rows, cols, hu.ne_zero⟩
    have heq : rank ((directSum C₁ C₂).d k) = rank (C₁.d k) + rank (C₂.d k) :=
      le_antisymm (rank_le_directSum C₁ C₂ k) hge
    rw [heq]
    exact ⟨rows, cols, hu⟩

/-- **Additivity of rank over a direct sum of sums of trivial complexes.** For sums of trivial
complexes `C₁` and `C₂`, `rank ((directSum C₁ C₂).d k) = rank (C₁.d k) + rank (C₂.d k)`.

The hypotheses `IsSumOfTrivials` cannot be dropped: determinantal rank is not additive over
block-diagonal matrices over a ring with zero divisors. Over `R = ℤ/6` the blocks `[2]` and `[3]`
each have rank `1`, but the `2 × 2` block-diagonal matrix has determinant `6 = 0`, hence rank
`1`. -/
theorem rank_directSum {C₁ C₂ : Complex R e}
    (h₁ : IsSumOfTrivials C₁) (h₂ : IsSumOfTrivials C₂) (k : ℕ) :
    rank ((directSum C₁ C₂).d k) = rank (C₁.d k) + rank (C₂.d k) := by
  refine le_antisymm (rank_le_directSum C₁ C₂ k) ?_
  obtain ⟨ro1, co1, hu1⟩ := h₁.exists_isUnit_det_submatrix k
  obtain ⟨ro2, co2, hu2⟩ := h₂.exists_isUnit_det_submatrix k
  obtain ⟨rows, cols, hu⟩ := combine_unit_minor C₁ C₂ k ro1 co1 ro2 co2 hu1 hu2
  exact le_rank _ ⟨rows, cols, hu.ne_zero⟩

omit [Nontrivial R] in
/-- **Additivity of `rIndex` over a direct sum.** -/
theorem rIndex_directSum (C₁ C₂ : Complex R e) (i : ℕ) :
    rIndex (directSum C₁ C₂) i = rIndex C₁ i + rIndex C₂ i := by
  unfold rIndex directSum
  simp only [Nat.cast_add, mul_add]
  rw [Finset.sum_add_distrib]

/-- If all modules `C.n l` with `i ≤ l` vanish, then `rIndex C i = 0`. -/
private theorem rIndex_eq_zero_of_n_eq_zero {S : Type*} [CommRing S] {C : Complex S e} {i : ℕ}
    (h : ∀ l, i ≤ l → C.n l = 0) : rIndex C i = 0 :=
  Finset.sum_eq_zero fun l hl => by rw [h l (Finset.mem_Icc.mp hl).1]; simp

/-- **rank = rIndex for a sum of trivial complexes.** For a direct sum of trivial complexes,
the rank of `D.d k` is `rIndex D (k+1)` for every `k < e`. -/
theorem rank_eq_rIndex_of_sum {D : Complex R e} (hD : IsSumOfTrivials D)
    (k : ℕ) (hk : k < e) :
    (rank (D.d k) : ℤ) = rIndex D (k + 1) := by
  induction hD with
  | zero =>
    rw [rank_d_eq_zero_of_n_eq_zero (Or.inl rfl), Nat.cast_zero, eq_comm]
    exact rIndex_eq_zero_of_n_eq_zero fun _ _ => rfl
  | @trivial C h =>
    rcases h with ⟨j, hje, hnj1, hnj, hentry, hother⟩ | ⟨hn0, hother⟩
    · by_cases hk' : k = j
      · subst hk'
        rw [rank_d_eq_one hnj1 hnj hentry]
        unfold rIndex
        rw [Finset.sum_eq_single (k + 1)]
        · simp [hnj1]
        · intro l hl hlne
          rw [Finset.mem_Icc] at hl
          rw [hother l (by omega) (by omega)]; simp
        · intro hmem
          exfalso
          apply hmem
          rw [Finset.mem_Icc]
          omega
      · rw [rank_d_eq_zero_of_ne hother hk', Nat.cast_zero, eq_comm]
        rcases Nat.lt_or_ge k j with hlt | hge
        · unfold rIndex
          have hsub : ({j, j + 1} : Finset ℕ) ⊆ Finset.Icc (k + 1) e := by
            intro x hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rw [Finset.mem_Icc]
            rcases hx with rfl | rfl <;> omega
          rw [show Finset.Icc (k + 1) e
              = {j, j + 1} ∪ (Finset.Icc (k + 1) e \ {j, j + 1}) by
            rw [Finset.union_sdiff_of_subset hsub]]
          rw [Finset.sum_union (by
            rw [Finset.disjoint_left]
            intro x hx hx2
            rw [Finset.mem_sdiff] at hx2
            exact hx2.right hx)]
          have hzero1 : ∑ l ∈ (Finset.Icc (k + 1) e \ {j, j + 1}),
              (-1 : ℤ) ^ (l - (k + 1)) * (C.n l : ℤ) = 0 := by
            apply Finset.sum_eq_zero
            intro l hl
            rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hl
            have : C.n l = 0 := hother l (by tauto) (by tauto)
            rw [this]; simp
          rw [hzero1, add_zero]
          rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
            Finset.sum_singleton]
          rw [hnj, hnj1]
          have hpar : (-1 : ℤ) ^ (j + 1 - (k + 1)) = - (-1 : ℤ) ^ (j - (k + 1)) := by
            rw [show j + 1 - (k + 1) = (j - (k + 1)) + 1 by omega, pow_succ]
            ring
          rw [hpar]; push_cast; ring
        · exact rIndex_eq_zero_of_n_eq_zero fun l hl => hother l (by omega) (by omega)
    · rw [rank_d_eq_zero_of_n_eq_zero (Or.inr (hother (k + 1) (by omega))), Nat.cast_zero,
        eq_comm]
      exact rIndex_eq_zero_of_n_eq_zero fun l hl => hother l (by omega)
  | @sum C₁ C₂ h₁ h₂ ih₁ ih₂ =>
    have hrank := rank_directSum h₁ h₂ k
    rw [hrank]
    push_cast
    rw [ih₁, ih₂, ← rIndex_directSum C₁ C₂ (k + 1)]

/-- **minorIdeal = ⊤ for a sum of trivial complexes.** For a direct sum of trivial complexes,
the ideal of minors of every differential is the unit ideal. -/
theorem minorIdeal_eq_top_of_sum {D : Complex R e} (hD : IsSumOfTrivials D)
    (k : ℕ) :
    minorIdeal (D.d k) = ⊤ := by
  obtain ⟨rows, cols, hu⟩ := hD.exists_isUnit_det_submatrix k
  have hmem : ((D.d k).submatrix rows cols).det ∈ minorIdeal (D.d k) :=
    Ideal.subset_span ⟨rows, cols, rfl⟩
  exact (minorIdeal (D.d k)).eq_top_of_isUnit_mem hmem hu

end NormalForm

/-! ## Complexes isomorphic to a direct sum of trivial complexes -/

/-- If the complex is isomorphic to a direct sum of trivial complexes,
then for `1 ≤ i ≤ e` the rank of `φ_i` (which is `d (i-1)`, or equivalently `d k` with
`k = i-1` ranging over `0 ≤ k ≤ e-1`) equals `r_i = ∑_{l=i}^e (-1)^{l-i} n_l`. -/
@[stacks 00MW "(1)"]
theorem rank_eq_rIndex (C : Complex R e) (hC : IsoToSumOfTrivials C)
    (k : ℕ) (hk : k < e) :
    (rank (C.d k) : ℤ) = rIndex C (k + 1) := by
  obtain ⟨D, hD, ⟨φ⟩⟩ := hC
  rw [rank_eq_of_iso φ k, rIndex_eq_of_iso φ (k + 1)]
  exact rank_eq_rIndex_of_sum hD k hk

/-- If the complex is isomorphic to a direct sum of trivial complexes, then for `1 ≤ i ≤ e-1`,
`rank(φ_{i+1}) + rank(φ_i) = n_i`. In the indexing `d j = φ_{j+1}`, with `k = i-1`
ranging over `0 ≤ k ≤ e-2`, this reads `rank (d (k+1)) + rank (d k) = n (k+1)`. -/
@[stacks 00MW "(2)"]
theorem rank_add_rank (C : Complex R e) (hC : IsoToSumOfTrivials C)
    (k : ℕ) (hk : k + 1 < e) :
    rank (C.d (k + 1)) + rank (C.d k) = C.n (k + 1) := by
  have h1 : (rank (C.d (k + 1)) : ℤ) = rIndex C (k + 2) :=
    rank_eq_rIndex C hC (k + 1) hk
  have h2 : (rank (C.d k) : ℤ) = rIndex C (k + 1) :=
    rank_eq_rIndex C hC k (Nat.lt_of_succ_lt hk)
  have htel : rIndex C (k + 1) + rIndex C (k + 2) = (C.n (k + 1) : ℤ) := by
    unfold rIndex
    have hins : Finset.Icc (k + 1) e = insert (k + 1) (Finset.Icc (k + 2) e) := by
      ext l
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    have hbot : (-1 : ℤ) ^ ((k + 1) - (k + 1)) * (C.n (k + 1) : ℤ) = (C.n (k + 1) : ℤ) := by
      simp
    rw [hbot]
    have hcancel : ∑ l ∈ Finset.Icc (k + 2) e, (-1 : ℤ) ^ (l - (k + 1)) * (C.n l : ℤ)
        = - ∑ l ∈ Finset.Icc (k + 2) e, (-1 : ℤ) ^ (l - (k + 2)) * (C.n l : ℤ) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mem_Icc] at hl
      have hstep : l - (k + 1) = (l - (k + 2)) + 1 := by omega
      rw [hstep, pow_succ]
      ring
    rw [hcancel]
    ring
  have hcast : ((rank (C.d (k + 1)) + rank (C.d k) : ℕ) : ℤ) = (C.n (k + 1) : ℤ) := by
    push_cast
    rw [h1, h2]
    linarith [htel]
  exact_mod_cast hcast

/-- If the complex is isomorphic to a direct sum of trivial complexes, then for `1 ≤ i ≤ e`,
the ideal `I(φ_i)` is the unit ideal `R`. In the indexing `d k = φ_{k+1}` with `0 ≤ k ≤ e-1`,
this is `I(d k) = ⊤`. -/
@[stacks 00MW "(3)"]
theorem minorIdeal_eq_top (C : Complex R e) (hC : IsoToSumOfTrivials C)
    (k : ℕ) :
    minorIdeal (C.d k) = ⊤ := by
  obtain ⟨D, hD, ⟨φ⟩⟩ := hC
  rw [minorIdeal_eq_of_iso φ k]
  exact minorIdeal_eq_top_of_sum hD k

end StacksComplex
