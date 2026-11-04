module

public import StacksFrontier.NumberTheory.Padics.LAdicTensorConstructions
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Determinantal weights on tensor constructions

For a tensor construction `C` and the decomposition `u ^ ℓ ^ N = exp A * exp B` of
`Stacks.LAdic.exists_pow_eq_exp_mul_exp_of_normalizes`, the determinant of `C.R u ^ ℓ ^ N` on a
subspace `W` stable under `C.R G` and `C.R u` is that of `C.R (exp B)`
(`Stacks.LAdic.det_stabRestrict_construction`). Bounds `a ≤ ‖ι μ‖ ≤ b` on the eigenvalues of
`exp B` therefore propagate: through Kronecker products as products of bounds, through duals as
inverted bounds, and to determinants on `W` as `a ^ dim W ≤ ‖ι det‖ ≤ b ^ dim W`. This is the
mechanism behind the additivity of determinantal weights (Weil II 1.3.13; Kedlaya,
*Fourier transforms and p-adic Weil II*, Proposition 6.1.6 (ii), (iii)).

## Main definitions

* `Stacks.LAdic.EigenNormIn`: every eigenvalue `μ` of a matrix satisfies `a ≤ ‖ι μ‖ ≤ b`.

## Main results

* `Stacks.LAdic.EigenNormIn.kronecker`: eigenvalue bounds multiply under Kronecker products.
* `Stacks.LAdic.EigenNormIn.dual`: eigenvalue bounds of `g` give inverted bounds for `(g⁻¹)ᵀ`.
* `Stacks.LAdic.norm_det_restrict_mem_Icc`: eigenvalue bounds give
  `a ^ dim W ≤ ‖ι det‖ ≤ b ^ dim W` on an invariant subspace `W`.
* `Stacks.LAdic.TensorConstruction.norm_det_pow_mem_Icc`: the determinantal weight bound for
  `C.R u ^ ℓ ^ N` on a subspace `W`.

## References

* Deligne, *La conjecture de Weil II*, 1.3.13.
* Kedlaya, *Fourier transforms and p-adic Weil II*, Proposition 6.1.6 (ii), (iii).
-/

@[expose] public noncomputable section

open Filter Topology NormedSpace Matrix
open scoped Kronecker

namespace Stacks.LAdic

/-- All eigenvalues `μ` of the matrix `M` satisfy `a ≤ ‖ι μ‖ ≤ b`. -/
def EigenNormIn {F : Type*} [Field F] {m : Type*} [Fintype m] [DecidableEq m] (ι : F →+* ℂ)
    (M : Matrix m m F) (a b : ℝ) : Prop :=
  ∀ μ, Module.End.HasEigenvalue (Matrix.toLin' M) μ → a ≤ ‖ι μ‖ ∧ ‖ι μ‖ ≤ b

section Eigen

variable {F : Type*} [Field F] [IsAlgClosed F] {m p : Type*} [Fintype m] [DecidableEq m]
  [Fintype p] [DecidableEq p] {ι : F →+* ℂ}

/-- If the eigenvalues of `M₁` and `M₂` have norms in `[a₁, b₁]` and `[a₂, b₂]` with `a₁, a₂ ≥ 0`,
then the eigenvalues of `M₁ ⊗ₖ M₂` have norms in `[a₁ * a₂, b₁ * b₂]`. -/
theorem EigenNormIn.kronecker {M₁ : Matrix m m F} {M₂ : Matrix p p F} {a₁ b₁ a₂ b₂ : ℝ}
    (h₁ : EigenNormIn ι M₁ a₁ b₁) (h₂ : EigenNormIn ι M₂ a₂ b₂) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) :
    EigenNormIn ι (M₁ ⊗ₖ M₂) (a₁ * a₂) (b₁ * b₂) := by
  intro lam hlam
  obtain ⟨μ, ν, hμ, hν, rfl⟩ := exists_eq_mul_of_hasEigenvalue_kronecker hlam
  obtain ⟨hμ1, hμ2⟩ := h₁ μ hμ
  obtain ⟨hν1, hν2⟩ := h₂ ν hν
  rw [map_mul, norm_mul]
  exact ⟨mul_le_mul hμ1 hν1 ha₂ (ha₁.trans hμ1), mul_le_mul hμ2 hν2 (norm_nonneg _)
    ((norm_nonneg _).trans hμ2)⟩

omit [IsAlgClosed F] in
/-- A matrix and its transpose have the same eigenvalues. -/
theorem hasEigenvalue_toLin'_transpose_iff {M : Matrix m m F} {μ : F} :
    Module.End.HasEigenvalue (Matrix.toLin' Mᵀ) μ ↔
      Module.End.HasEigenvalue (Matrix.toLin' M) μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Matrix.charpoly_toLin', Matrix.charpoly_toLin', charpoly_transpose]

omit [IsAlgClosed F] in
/-- If the eigenvalues of `g` have norms in `[a, b]` with `0 < a`, then the eigenvalues of
`(g⁻¹)ᵀ` have norms in `[b⁻¹, a⁻¹]`. -/
theorem EigenNormIn.dual {g : (Matrix m m F)ˣ} {a b : ℝ} (h : EigenNormIn ι (g : Matrix m m F) a b)
    (ha : 0 < a) : EigenNormIn ι (((g⁻¹ : (Matrix m m F)ˣ) : Matrix m m F)ᵀ) b⁻¹ a⁻¹ := by
  intro μ hμ
  rw [hasEigenvalue_toLin'_transpose_iff] at hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hgv : (g : Matrix m m F) *ᵥ (μ • v) = v := by
    have h1 : ((g⁻¹ : (Matrix m m F)ˣ) : Matrix m m F) *ᵥ v = μ • v := by
      rw [← Matrix.toLin'_apply]; exact hv.apply_eq_smul
    rw [← h1, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul, Matrix.mulVec_zero] at hgv
    exact hv.2 hgv.symm
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (g : Matrix m m F)) μ⁻¹ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    rw [Matrix.mulVec_smul] at hgv
    calc (g : Matrix m m F) *ᵥ v = μ⁻¹ • (μ • ((g : Matrix m m F) *ᵥ v)) := by
          rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = μ⁻¹ • v := by rw [hgv]
  obtain ⟨h1, h2⟩ := h μ⁻¹ hev
  rw [map_inv₀, norm_inv] at h1 h2
  have hpos : 0 < ‖ι μ‖ := norm_pos_iff.mpr ((map_ne_zero ι).mpr hμ0)
  exact ⟨by rw [inv_le_comm₀ (ha.trans_le h1 |>.trans_le h2 |> fun h => by
      exact lt_of_lt_of_le ha (h1.trans h2)) hpos]; exact h2, by
    rw [le_inv_comm₀ hpos ha]; exact h1⟩

/-- If every element of a multiset `s` of reals lies in `[a, b]` with `0 ≤ a`, then
`a ^ card s ≤ s.prod ≤ b ^ card s`. -/
theorem multiset_prod_mem_Icc {s : Multiset ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ x ∈ s, a ≤ x ∧ x ≤ b) : a ^ Multiset.card s ≤ s.prod ∧ s.prod ≤ b ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    obtain ⟨h1, h2⟩ := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    obtain ⟨hx1, hx2⟩ := h x (Multiset.mem_cons_self x s)
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ, pow_succ]
    exact ⟨by rw [mul_comm (a ^ _)]; exact mul_le_mul hx1 h1 (pow_nonneg ha _) (ha.trans hx1),
      by
        rw [mul_comm (b ^ _)]
        exact mul_le_mul hx2 h2 ((pow_nonneg ha _).trans h1) ((ha.trans hx1).trans hx2)⟩

/-- **Determinant bound on an invariant subspace.**  If all eigenvalues of `M` satisfy
`a ≤ ‖ι μ‖ ≤ b`, then `a ^ dim W ≤ ‖ι det (M |_W)‖ ≤ b ^ dim W` for every `M`-stable `W`. -/
theorem norm_det_restrict_mem_Icc {M : Matrix m m F} {a b : ℝ} (h : EigenNormIn ι M a b)
    (ha : 0 ≤ a) {W : Submodule F (m → F)} (hW : ∀ w ∈ W, Matrix.toLin' M w ∈ W) :
    a ^ Module.finrank F W ≤ ‖ι (LinearMap.det ((Matrix.toLin' M).restrict hW))‖ ∧
      ‖ι (LinearMap.det ((Matrix.toLin' M).restrict hW))‖ ≤ b ^ Module.finrank F W := by
  set f := (Matrix.toLin' M).restrict hW
  have hsplit : f.charpoly.Splits := IsAlgClosed.splits _
  have hcard : Multiset.card f.charpoly.roots = Module.finrank F W := by
    rw [Polynomial.splits_iff_card_roots.mp hsplit, LinearMap.charpoly_natDegree]
  have hroots : ∀ x ∈ (f.charpoly.roots.map ι).map (fun z => ‖z‖), a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [Multiset.map_map, Multiset.mem_map, Function.comp_apply] at hx
    obtain ⟨μ, hμ, rfl⟩ := hx
    have hev : Module.End.HasEigenvalue f μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots (LinearMap.charpoly_monic f).ne_zero).mp hμ
    obtain ⟨w, hw⟩ := hev.exists_hasEigenvector
    refine h μ (Module.End.hasEigenvalue_of_hasEigenvector (x := (w : m → F)) ⟨?_, ?_⟩)
    · rw [Module.End.mem_eigenspace_iff]
      exact congrArg Subtype.val hw.apply_eq_smul
    · exact fun h0 => hw.2 (Subtype.ext h0)
  have hn : ‖ι (LinearMap.det f)‖ = ((f.charpoly.roots.map ι).map fun z => ‖z‖).prod := by
    rw [Module.End.det_eq_prod_roots_charpoly_of_splits hsplit, map_multiset_prod]
    exact map_multiset_prod (normHom : ℂ →*₀ ℝ) _
  rw [hn]
  have := multiset_prod_mem_Icc ha hroots
  simpa [hcard] using this

end Eigen

section Weights

variable {ℓ : ℕ} [Fact ℓ.Prime]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist Matrix.completeSpace_of_ultra

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] [IsAlgClosed K]
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- **Determinantal weights on a tensor construction.**  Let `u ^ ℓ ^ N = exp A * exp B` be the
outer-action decomposition for `(G, u)` and `z = exp B`.  For a construction `C` and a subspace
`W` stable under `C.R G` and `C.R u`, on which the determinants of `C.R G` have finite order, if
all eigenvalues of `C.R z` satisfy `a ≤ ‖ι μ‖ ≤ b`, then
`a ^ dim W ≤ ‖ι det (C.R u ^ ℓ ^ N |_W)‖ ≤ b ^ dim W`. -/
theorem TensorConstruction.norm_det_pow_mem_Icc (C : TensorConstruction ℓ K n m) (ι : K →+* ℂ)
    {G : Subgroup (Matrix n n K)ˣ} (hG : ∀ g ∈ G, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹)
    {u : (Matrix n n K)ˣ} (hu : ‖(u : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹) {N : ℕ}
    {A B : Matrix n n K} (hA : Matrix.toLinAlgEquiv' A ∈ logLieSpan ℓ G)
    (hAn : ‖A‖ < (ℓ : ℝ)⁻¹) (hBn : ‖B‖ < (ℓ : ℝ)⁻¹)
    (hBG : ∀ g ∈ G, Commute B (g : Matrix n n K)) (hAB : Commute A B)
    (hsum : (ℓ ^ N : ℕ) • ladicLog ℓ (u : Matrix n n K) = A + B)
    {z : (Matrix n n K)ˣ} (hz : (z : Matrix n n K) = exp B) {a b : ℝ} (ha : 0 ≤ a)
    (hab : EigenNormIn ι (C.R z : Matrix m m K) a b)
    {W : Submodule K (m → K)}
    (hGW : ∀ g ∈ G, (C.R g : Matrix m m K) ∈ stabilizerSubalgebra W)
    (huW : (C.R u : Matrix m m K) ∈ stabilizerSubalgebra W)
    (hdetW : ∀ g ∈ G, ∃ k : ℕ, 0 < k ∧ ∀ hg : (C.R g : Matrix m m K) ∈ stabilizerSubalgebra W,
      LinearMap.det (stabRestrict (C.R g : Matrix m m K) hg) ^ k = 1)
    (hu' : (C.R u : Matrix m m K) ^ (ℓ ^ N) ∈ stabilizerSubalgebra W) :
    a ^ Module.finrank K W ≤ ‖ι (LinearMap.det (stabRestrict _ hu'))‖ ∧
      ‖ι (LinearMap.det (stabRestrict _ hu'))‖ ≤ b ^ Module.finrank K W := by
  obtain ⟨-, hz', hu'', hdet⟩ := det_stabRestrict_construction hG C.R C.D C.norm_lt C.map_eq hu hA
    hAn hBn hBG hAB hsum hGW huW hdetW
  have hz1 : ‖(z : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹ := by
    rw [hz]; exact (norm_exp_sub_one_le hBn).trans_lt hBn
  have hRz : (C.R z : Matrix m m K) = exp (C.D B) := by
    rw [C.map_eq z hz1, hz]
    exact congrArg (fun X => exp (C.D X)) (ladicLog_exp hBn)
  have hzW : (C.R z : Matrix m m K) ∈ stabilizerSubalgebra W := hRz ▸ hz'
  rw [stabRestrict_congr rfl hu' hu'', hdet, stabRestrict_congr hRz.symm hz' hzW]
  exact norm_det_restrict_mem_Icc hab ha _

end Weights

end Stacks.LAdic
