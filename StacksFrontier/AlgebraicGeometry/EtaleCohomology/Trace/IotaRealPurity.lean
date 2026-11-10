module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoinvariantWeightBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoordinateSubspaceBlocks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerEigenvalue
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerCharpoly

/-!
# The constituents of an `ι`-real representation are `ι`-pure

This file proves Weil II 1.5.1 (Kedlaya, *Fourier transforms and p-adic Weil II*,
Theorem 6.5.2) at the level of groups, from the Frobenius trace formula in the form
`Stacks.EtaleCohomology.SatisfiesFrobeniusTraceFormula`: if `ρ : Γ → GL_r(ℚ_ℓ)` has `ι`-real
Frobenius characteristic polynomials and every continuous representation of `Γ` satisfies the
trace formula, then on every irreducible constituent `W` of `ρ` (a diagonal block of a block
triangular form of `ρ` over `K`) every eigenvalue of the Frobenius `F_y` at a point of degree
`deg y` has absolute value `β ^ deg y`, for one `β > 0` depending only on `W`.

The proof is Kedlaya's: let `β` be the determinantal weight of `W` (the absolute value of the
eigenvalues of the central element `z` of Weil II 1.3.9 on `W`), `E_{>β}` the sum of the
constituents of larger determinantal weight, `N = dim E_{>β}` and `D` its determinant weight.  By
Rankin's bound applied to `⋀^{N+1} ρ`
(`Stacks.EtaleCohomology.norm_le_of_satisfiesFrobeniusTraceFormula`), with the coinvariant bound
of `Stacks.EtaleCohomology.norm_pow_le_of_isRoot_coinvariantsFrobenius` for `T = D β`, every
eigenvalue of `⋀^{N+1} F_y` is at most `(D β) ^ deg y` (suitably normalized); an eigenvalue `μ`
of `F_y` on `W`, times `det (F_y | E_{>β})`, is such an eigenvalue
(`Stacks.EtaleCohomology.hasEigenvalue_exteriorPower_map_mul_det`), so `|μ| ≤ β ^ deg y`; the
determinant of `F_y` on `W` forces equality.

## Main results

* `Stacks.EtaleCohomology.exists_norm_eq_pow_of_isRoot_toSquareBlock`: Weil II 1.5.1 at the level
  of groups.
* `Stacks.EtaleCohomology.charpoly_eq_mul_toSquareBlockProp`,
  `Stacks.EtaleCohomology.exists_norm_eq_of_isRoot_toSquareBlockProp`: eigenvalues of block
  diagonal matrices on unions of blocks.
* `Stacks.EtaleCohomology.multiset_prod_le_mul_of_card_eq_succ`: the combinatorial bound on
  products of `N + 1` determinantal weights.
* `Stacks.EtaleCohomology.norm_det_pow_eq_of_stable`: determinants of Frobenius elements on a
  stable subspace through `z`.
-/

@[expose] public noncomputable section

open Filter Topology NormedSpace Matrix Polynomial Stacks.LAdic

namespace Stacks.EtaleCohomology

section Multiset

/-- A product of elements of `[0, β]` is at most `β ^ card s`. -/
theorem multiset_prod_le_pow {s : Multiset ℝ} {β : ℝ} (h : ∀ x ∈ s, 0 ≤ x ∧ x ≤ β) :
    s.prod ≤ β ^ Multiset.card s := by
  simpa using Multiset.prod_map_le_prod_map₀ id (fun _ => β) (fun x hx => (h x hx).1)
    fun x hx => (h x hx).2

/-- For `β ≥ 0`, a product of elements `≥ β` is at least `β ^ card s`. -/
theorem pow_le_multiset_prod {s : Multiset ℝ} {β : ℝ} (hβ : 0 ≤ β) (h : ∀ x ∈ s, β ≤ x) :
    β ^ Multiset.card s ≤ s.prod := by
  simpa using Multiset.prod_map_le_prod_map₀ (fun _ => β) id (fun _ _ => hβ) h

/-- **Products of `N + 1` weights.**  If `M₁` (of cardinality `N`) has all its elements `> β ≥ 0`
and `M₂` has all its elements in `[0, β]`, every sub-multiset of `M₁ + M₂` of cardinality `N + 1`
has product at most `(∏ M₁) · β`. -/
public theorem multiset_prod_le_mul_of_card_eq_succ {M₁ M₂ s : Multiset ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (h₁ : ∀ x ∈ M₁, β < x) (h₂ : ∀ x ∈ M₂, 0 ≤ x ∧ x ≤ β) (hs : s ≤ M₁ + M₂)
    (hcard : Multiset.card s = Multiset.card M₁ + 1) : s.prod ≤ M₁.prod * β := by
  classical
  set s₁ := s.filter (β < ·)
  set s₂ := s.filter (fun x => ¬ β < x)
  have hsplit : s₁ + s₂ = s := Multiset.filter_add_not _ s
  have hM₁ : (M₁ + M₂).filter (β < ·) = M₁ := by
    rw [Multiset.filter_add, Multiset.filter_eq_self.mpr h₁,
      Multiset.filter_eq_nil.mpr fun x hx => not_lt.mpr (h₂ x hx).2, add_zero]
  have hM₂ : (M₁ + M₂).filter (fun x => ¬ β < x) = M₂ := by
    rw [Multiset.filter_add, Multiset.filter_eq_nil.mpr fun x hx => not_not.mpr (h₁ x hx),
      Multiset.filter_eq_self.mpr fun x hx => not_lt.mpr (h₂ x hx).2, zero_add]
  have hs₁ : s₁ ≤ M₁ := hM₁ ▸ Multiset.filter_le_filter _ hs
  have hs₂ : s₂ ≤ M₂ := hM₂ ▸ Multiset.filter_le_filter _ hs
  set t := M₁ - s₁
  have ht : s₁ + t = M₁ := add_tsub_cancel_of_le hs₁
  have hct : Multiset.card t + 1 = Multiset.card s₂ := by
    have h1 := congrArg Multiset.card hsplit
    have h2 := congrArg Multiset.card ht
    rw [Multiset.card_add] at h1 h2
    omega
  have hβ₁ : ∀ x ∈ s₁, 0 ≤ x := fun x hx => hβ.trans (h₁ x (Multiset.mem_of_le hs₁ hx)).le
  have hp₁ : 0 ≤ s₁.prod := Multiset.prod_nonneg hβ₁
  have hp₂ : s₂.prod ≤ β ^ Multiset.card s₂ :=
    multiset_prod_le_pow fun x hx => h₂ x (Multiset.mem_of_le hs₂ hx)
  have hpt : β ^ Multiset.card t ≤ t.prod :=
    pow_le_multiset_prod hβ fun x hx =>
      (h₁ x (Multiset.mem_of_le (ht ▸ Multiset.le_add_left t s₁) hx)).le
  rw [← hsplit, Multiset.prod_add]
  conv_rhs => rw [← ht, Multiset.prod_add]
  calc s₁.prod * s₂.prod ≤ s₁.prod * (β ^ Multiset.card t * β) := by
        rw [← pow_succ, hct]; exact mul_le_mul_of_nonneg_left hp₂ hp₁
    _ ≤ s₁.prod * (t.prod * β) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpt hβ) hp₁
    _ = s₁.prod * t.prod * β := by ring

end Multiset

section Blocks

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- **The characteristic polynomial of a block triangular matrix with two blocks** is the product
of those of the diagonal blocks. -/
public theorem charpoly_eq_mul_toSquareBlockProp (M : Matrix n n K) (p : n → Prop)
    [DecidablePred p] (h : ∀ i, ¬ p i → ∀ j, p j → M i j = 0) :
    M.charpoly = (M.toSquareBlockProp p).charpoly *
      (M.toSquareBlockProp fun i => ¬ p i).charpoly := by
  have hc : ∀ (q : n → Prop) [DecidablePred q],
      M.charmatrix.toSquareBlockProp q = (M.toSquareBlockProp q).charmatrix := by
    intro q _
    ext ⟨i, hi⟩ ⟨j, hj⟩
    by_cases hij : i = j
    · subst hij
      simp [Matrix.toSquareBlockProp_def, Matrix.charmatrix_apply]
    · have hij' : (⟨i, hi⟩ : {a // q a}) ≠ ⟨j, hj⟩ := fun e => hij (congrArg Subtype.val e)
      rw [Matrix.charmatrix_apply_ne _ _ _ hij', Matrix.toSquareBlockProp_def, Matrix.of_apply,
        Matrix.charmatrix_apply_ne _ _ _ hij]
      rfl
  rw [Matrix.charpoly, Matrix.twoBlockTriangular_det M.charmatrix p, hc, hc, Matrix.charpoly,
    Matrix.charpoly]
  intro i hi j hj
  have hij : i ≠ j := fun e => hi (e ▸ hj)
  rw [Matrix.charmatrix_apply_ne _ _ _ hij, h i hi j hj, map_zero, neg_zero]

/-- A root of the characteristic polynomial of a diagonal block `M.toSquareBlockProp p` of a
matrix with no entries from `p` to `¬ p` is an eigenvalue of `M` with an eigenvector in the
coordinate subspace of `p`. -/
public theorem exists_mulVec_eq_of_isRoot_toSquareBlockProp {M : Matrix n n K} {p : n → Prop}
    [DecidablePred p] (hM : ∀ i j, p j → ¬ p i → M i j = 0) {c : K}
    (hc : (M.toSquareBlockProp p).charpoly.IsRoot c) :
    ∃ v : n → K, v ≠ 0 ∧ v ∈ coordSubspace (K := K) p ∧ M *ᵥ v = c • v := by
  have hM' : ∀ v ∈ coordSubspace (K := K) p, Matrix.toLin' M v ∈ coordSubspace (K := K) p :=
    fun v hv => by rw [Matrix.toLin'_apply]; exact mulVec_mem_coordSubspace hM hv
  rw [← charpoly_restrict_coordSubspace hM', ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hc
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  refine ⟨x, fun h => hx.2 (Subtype.ext h), x.2, ?_⟩
  have := congrArg Subtype.val hx.1
  rwa [LinearMap.coe_restrict_apply, Matrix.toLin'_apply] at this

/-- The norm along `ι` of a product. -/
public theorem norm_map_multiset_prod (ι : K →+* ℂ) (s : Multiset K) :
    ‖ι s.prod‖ = (s.map fun c => ‖ι c‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => rw [Multiset.prod_cons, map_mul, norm_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]

variable {d : n → ℤ}

/-- **The eigenvalues of a block diagonal matrix on a union of blocks.**  Let `M` be block
diagonal along `d : n → ℤ` and assume that every eigenvalue of `M` with an eigenvector supported
on the block `d = t` has absolute value `rr t` along `ι`.  Then every root `c` of the
characteristic polynomial of the diagonal block of `M` on `{i | P (d i)}` has `‖ι c‖ = rr (d i)`
for some `i` with `P (d i)`. -/
public theorem exists_norm_eq_of_isRoot_toSquareBlockProp (ι : K →+* ℂ) {M : Matrix n n K}
    (hM : ∀ i j, d i ≠ d j → M i j = 0) {rr : ℤ → ℝ}
    (hrr : ∀ (t : ℤ) (μ : K) (v : n → K), v ≠ 0 → (∀ i, d i ≠ t → v i = 0) → M *ᵥ v = μ • v →
      ‖ι μ‖ = rr t)
    (P : ℤ → Prop) [DecidablePred P] {c : K}
    (hc : (M.toSquareBlockProp fun i => P (d i)).charpoly.IsRoot c) :
    ∃ i, P (d i) ∧ ‖ι c‖ = rr (d i) := by
  obtain ⟨v, hv0, hvP, hMv⟩ := exists_mulVec_eq_of_isRoot_toSquareBlockProp
    (p := fun i => P (d i)) (fun i j hj hi => hM i j fun e => hi (e ▸ hj)) hc
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hPi : P (d i) := by
    by_contra h
    exact hi (hvP i h)
  refine ⟨i, hPi, hrr (d i) c (fun j => if d j = d i then v j else 0) ?_ ?_ ?_⟩
  · intro h
    have := congrFun h i
    simp only [Pi.zero_apply] at this
    exact hi this
  · intro j hj
    rw [ite_eq_right hj]
  · ext j
    rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    by_cases hj : d j = d i
    · rw [ite_eq_left hj, ← smul_eq_mul, ← Pi.smul_apply, ← hMv, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : d k = d i
      · rw [ite_eq_left hk]
      · rw [ite_eq_right hk, hM j k (fun e => hk (e ▸ hj)), zero_mul, zero_mul]
    · rw [ite_eq_right hj, mul_zero]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : d k = d i
      · rw [hM j k (fun e => hj (e.trans hk)), zero_mul]
      · rw [ite_eq_right hk, mul_zero]

/-- A root of the characteristic polynomial of a diagonal block of an invertible matrix with no
entries from `p` to `¬ p` is nonzero. -/
public theorem ne_zero_of_isRoot_toSquareBlockProp {M : Matrix n n K} (hMu : IsUnit M)
    {p : n → Prop} [DecidablePred p] (hM : ∀ i j, p j → ¬ p i → M i j = 0) {c : K}
    (hc : (M.toSquareBlockProp p).charpoly.IsRoot c) : c ≠ 0 := by
  rintro rfl
  obtain ⟨v, hv0, -, hMv⟩ := exists_mulVec_eq_of_isRoot_toSquareBlockProp hM hc
  obtain ⟨u, rfl⟩ := hMu
  apply hv0
  rw [zero_smul] at hMv
  rw [← Matrix.one_mulVec v, ← Units.inv_mul u, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_zero]

end Blocks

section DetRelation

variable {ℓ : ℕ} [Fact ℓ.Prime]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist Matrix.completeSpace_of_ultra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] [IsAlgClosed K]

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  {r : ℕ}

include ℓ in
/-- **Determinants of Frobenius elements on a stable subspace are read on `z`** (Weil II 1.3.5,
1.3.9): for `W` stable under `σ'` and `g ∈ φ ^ d H`,
`‖ι det (σ'(g) | W)‖ ^ (κ ℓ ^ N) = ‖ι det (z | W)‖ ^ d`, `z = exp B`. -/
public theorem norm_det_pow_eq_of_stable (ι : K →+* ℂ) (σ' : Γ →* (Matrix (Fin r) (Fin r) K)ˣ)
    (hσ : Continuous fun g => (σ' g : Matrix (Fin r) (Fin r) K)) (H : Subgroup Γ) (φ : Γ)
    (hH : ∀ ψ : H → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
      (∀ a b : H, (b : Γ) = φ * a * φ⁻¹ → ψ b = ψ a) → ψ = 0)
    (κ : ℕ) {G : Subgroup (Matrix (Fin r) (Fin r) K)ˣ} (hGH : ∀ g ∈ G, ∃ h ∈ H, σ' h = g)
    (hG : ∀ g ∈ G, ‖(g : Matrix (Fin r) (Fin r) K) - 1‖ < (ℓ : ℝ)⁻¹)
    (hu : ‖(σ' (φ ^ κ) : Matrix (Fin r) (Fin r) K) - 1‖ < (ℓ : ℝ)⁻¹) {N : ℕ}
    {A B : Matrix (Fin r) (Fin r) K} (hA : Matrix.toLinAlgEquiv' A ∈ logLieSpan ℓ G)
    (hAn : ‖A‖ < (ℓ : ℝ)⁻¹) (hBn : ‖B‖ < (ℓ : ℝ)⁻¹)
    (hBG : ∀ g ∈ G, Commute B (g : Matrix (Fin r) (Fin r) K)) (hAB : Commute A B)
    (hsum : (ℓ ^ N : ℕ) • ladicLog ℓ (σ' (φ ^ κ) : Matrix (Fin r) (Fin r) K) = A + B)
    {W : Submodule K (Fin r → K)}
    (hW : ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W) {g : Γ} {d : ℕ}
    (hg : (φ ^ d)⁻¹ * g ∈ H) :
    ∃ hz : exp B ∈ stabilizerSubalgebra W,
      ‖ι (LinearMap.det (stabRestrict (σ' g : Matrix (Fin r) (Fin r) K) (hW g)))‖ ^ (κ * ℓ ^ N) =
        ‖ι (LinearMap.det (stabRestrict (exp B) hz))‖ ^ d := by
  have hGW : ∀ x ∈ G, ((TensorConstruction.id : TensorConstruction ℓ K (Fin r) (Fin r)).R x :
      Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W := by
    intro x hx
    obtain ⟨h, -, rfl⟩ := hGH x hx
    exact hW h
  have hdetW : ∀ x ∈ G, ∃ k : ℕ, 0 < k ∧ ∀ hx : ((TensorConstruction.id :
      TensorConstruction ℓ K (Fin r) (Fin r)).R x : Matrix (Fin r) (Fin r) K) ∈
        stabilizerSubalgebra W, LinearMap.det (stabRestrict _ hx) ^ k = 1 := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := hGH x hx
    exact exists_pow_det_stabRestrict_eq_one ℓ σ' hσ H φ hH (fun h _ => hW h) (hW φ) hh
  obtain ⟨-, hz, hu', hdet⟩ := det_stabRestrict_construction hG
    (TensorConstruction.id : TensorConstruction ℓ K (Fin r) (Fin r)).R TensorConstruction.id.D
    TensorConstruction.id.norm_lt TensorConstruction.id.map_eq hu hA hAn hBn hBG hAB hsum hGW
    (hW (φ ^ κ)) hdetW
  have hz' : exp B ∈ stabilizerSubalgebra W := hz
  have hu'' : (σ' (φ ^ κ) : Matrix (Fin r) (Fin r) K) ^ (ℓ ^ N) ∈ stabilizerSubalgebra W := hu'
  have hdet' : LinearMap.det (stabRestrict _ hu'') = LinearMap.det (stabRestrict (exp B) hz') :=
    hdet
  refine ⟨hz', ?_⟩
  have h1 := norm_detCharacter_eq_pow ℓ ι σ' hσ H φ hH hW hg
  have e1 : LinearMap.det (stabRestrict _ hu'') = detCharacter σ' hW (φ ^ (κ * ℓ ^ N)) := by
    change _ = LinearMap.det (stabRestrict _ (hW _))
    rw [stabRestrict_congr (show (σ' (φ ^ κ) : Matrix (Fin r) (Fin r) K) ^ (ℓ ^ N) =
      (σ' (φ ^ (κ * ℓ ^ N)) : Matrix (Fin r) (Fin r) K) by
        rw [pow_mul, map_pow σ' (φ ^ κ), Units.val_pow_eq_pow_val]) hu'' (hW _)]
  change ‖ι (detCharacter σ' hW g)‖ ^ (κ * ℓ ^ N) = _
  rw [h1, ← hdet', e1, map_pow, map_pow, norm_pow, ← pow_mul, ← pow_mul, mul_comm d]

end DetRelation

section Real

/-- `x ^ e ≤ T ^ m` reads `x ≤ q ^ (m logb_q T / e)`. -/
public theorem pow_le_pow_iff_le_rpow_logb {q T x : ℝ} (hq : 1 < q) (hT : 0 < T) (hx : 0 ≤ x)
    {e : ℕ} (he : 0 < e) (m : ℕ) :
    x ^ e ≤ T ^ m ↔ x ≤ q ^ ((m : ℝ) * Real.logb q T / e) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have hy : (q ^ ((m : ℝ) * Real.logb q T / e)) ^ e = T ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, div_mul_cancel₀ _ he', mul_comm,
      Real.rpow_mul hq0.le, Real.rpow_logb hq0 hq.ne' hT, Real.rpow_natCast]
  rw [← hy, pow_le_pow_iff_left₀ hx (Real.rpow_nonneg hq0.le _) he.ne']

/-- A matrix that is block diagonal along `d` stabilizes the coordinate subspace of any union of
blocks. -/
private theorem mem_stabilizerSubalgebra_coordSubspace {K : Type*} [NontriviallyNormedField K]
    {r : ℕ} {d : Fin r → ℤ} {M : Matrix (Fin r) (Fin r) K} (hM : ∀ i j, d i ≠ d j → M i j = 0)
    (Q : ℤ → Prop) : M ∈ stabilizerSubalgebra (coordSubspace (K := K) fun i => Q (d i)) :=
  fun _ hv => mulVec_mem_coordSubspace (fun i j hj hi => hM i j fun e => hi (e ▸ hj)) hv

end Real

section Purity

variable {ℓ : ℕ} [Fact ℓ.Prime]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist Matrix.completeSpace_of_ultra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] [IsAlgClosed K]

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  {r : ℕ}

/-- **The constituents of an `ι`-real representation are `ι`-pure** (Weil II 1.5.1; Kedlaya,
*Fourier transforms and p-adic Weil II*, Theorem 6.5.2), at the level of groups.

Let `Γ` be a compact group, `H ⊴ Γ` with `Γ / H` abelian (the geometric fundamental group),
`φ ∈ Γ` (a geometric Frobenius) satisfying the geometric input `hD1` of Weil II 1.3.4, and
`Fr y ∈ φ ^ deg y H` (`deg y > 0`) Frobenius elements at the points `y` of `Y`, finitely many of
each degree.  Let `ρ : Γ → GL_r(ℚ_ℓ)` be continuous, with `ι`-real Frobenius characteristic
polynomials (`ι = ι_K ∘ (ℚ_ℓ → K)`), and assume that every continuous representation of `Γ`
satisfies the Frobenius trace formula with `q > 1`.  Over `K`, let `P₀⁻¹ ρ P₀` be block upper
triangular along `d`, with block diagonal part `σ'` continuous and semisimple and with
irreducible blocks.  Then on every block `t` the Frobenius eigenvalues are pure: there is
`β > 0` such that every root of the characteristic polynomial of the `t`-th diagonal block of
`σ'(Fr y)` has absolute value `β ^ deg y` along `ι_K`. -/
public theorem exists_norm_eq_pow_of_isRoot_toSquareBlock (ι : K →+* ℂ) (H : Subgroup Γ)
    [H.Normal] (φ : Γ) (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hD1 : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) →
      ∀ ψ : ↥(H ⊓ U) → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) → ψ = 0)
    {Y : Type*} (Fr : Y → Γ) (deg : Y → ℕ) (hFr : ∀ y, (φ ^ deg y)⁻¹ * Fr y ∈ H)
    (hdeg : ∀ y, 0 < deg y) (hfin : ∀ m : ℕ, 0 < m → {y : Y | deg y ∣ m}.Finite)
    {q : ℝ} (hq : 1 < q)
    (htf : ∀ (m : ℕ) (τ : Γ →* GL (Fin m) ℚ_[ℓ]), Continuous τ →
      SatisfiesFrobeniusTraceFormula q (ι.comp (algebraMap ℚ_[ℓ] K)) H φ Fr deg τ)
    (ρ : Γ →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (hreal : ∀ (y : Y) (m : ℕ), (ι.comp (algebraMap ℚ_[ℓ] K))
      ((ρ (Fr y) : Matrix (Fin r) (Fin r) ℚ_[ℓ]).charpoly.coeff m) ∈ Set.range ((↑) : ℝ → ℂ))
    (P₀ : (Matrix (Fin r) (Fin r) K)ˣ) (d : Fin r → ℤ) (σ' : Γ →* (Matrix (Fin r) (Fin r) K)ˣ)
    (hup : ∀ g, IsGradedUpper d (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
      (ρ g : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) *
        (P₀ : Matrix (Fin r) (Fin r) K)))
    (hσ' : ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) = gradedDiag d
      (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
        (ρ g : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) *
          (P₀ : Matrix (Fin r) (Fin r) K)))
    (hσc : Continuous fun g => (σ' g : Matrix (Fin r) (Fin r) K))
    (hss : ∀ W : Submodule K (Fin r → K),
      (∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (Fin r → K), IsCompl W W' ∧
        ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W')
    (hirr : ∀ (t : ℤ) (W' : Submodule K (Fin r → K)),
      W' ≤ coordSubspace (K := K) (fun i => d i = t) → W' ≠ ⊥ →
      (∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W') →
        W' = coordSubspace (K := K) (fun i => d i = t))
    (t : ℤ) :
    ∃ β : ℝ, 0 < β ∧ ∀ (y : Y) (c : ℂ),
      (((σ' (Fr y) : Matrix (Fin r) (Fin r) K).toSquareBlock d t).charpoly.map ι).IsRoot c →
        ‖c‖ = β ^ deg y := by
  classical
  obtain ⟨U, -, -, hk, hG, hu, N, A, B, hA, hAn, hBn, hBG, -, hAB, hsum, hW⟩ :=
    exists_monodromy_weights (ℓ := ℓ) ι σ' hσc H φ hcomm hD1 hss
  have hH : ∀ ψ : H → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
      (∀ a b : H, (b : Γ) = φ * a * φ⁻¹ → ψ b = ψ a) → ψ = 0 := by
    intro ψ hadd hcont hinv
    have hmem : ∀ a : ↥(H ⊓ ⊤), (a : Γ) ∈ H := fun a => a.2.1
    set ψ' : ↥(H ⊓ ⊤) → K := fun a => ψ ⟨a, hmem a⟩
    have h0 := hD1 ⊤ inferInstance isOpen_univ ψ'
      (fun a b => hadd ⟨a, hmem a⟩ ⟨b, hmem b⟩)
      (hcont.comp ((continuous_subtype_val).subtype_mk _))
      (fun a b hab => hinv _ _ (by rw [Subgroup.index_top, pow_one] at hab; exact hab))
    funext a
    exact congrFun h0 ⟨a, a.2, Subgroup.mem_top _⟩
  have hGH : ∀ g ∈ (H ⊓ U).map σ', ∃ h ∈ H, σ' h = g := by
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨h, hh.1, rfl⟩
  set e : ℕ := U.index * ℓ ^ N with he_def
  have he : 0 < e := Nat.mul_pos hk (pow_pos (Fact.out : ℓ.Prime).pos N)
  have hzu : IsUnit (exp B) := isUnit_exp_of_mem_ball (𝕂 := ℚ_[ℓ]) (mem_eball_expSeries hBn)
  have hσbd : ∀ g i j, d i ≠ d j → (σ' g : Matrix (Fin r) (Fin r) K) i j = 0 := by
    intro g i j h
    rw [hσ' g]
    exact ite_eq_right h
  have hstab : ∀ (Q : ℤ → Prop) [DecidablePred Q] (g : Γ), (σ' g : Matrix (Fin r) (Fin r) K) ∈
      stabilizerSubalgebra (coordSubspace (K := K) fun i => Q (d i)) := fun Q _ g =>
    mem_stabilizerSubalgebra_coordSubspace (hσbd g) Q
  have hV : ∀ t : ℤ, ∃ rt : ℝ, ∀ (μ : K) (v : Fin r → K), v ≠ 0 → (∀ i, d i ≠ t → v i = 0) →
      exp B *ᵥ v = μ • v → ‖ι μ‖ = rt := by
    intro t
    obtain ⟨hzt, -, rt, hrt, -⟩ := hW _ (hstab (· = t)) (hirr t)
    refine ⟨rt, fun μ v hv hvt hzv => hrt μ ?_⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvt⟩) ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨Subtype.ext ?_, fun h => hv (congrArg Subtype.val h)⟩
    rw [stabRestrict_apply]
    exact hzv
  choose rr hrr using hV
  have hzbd : ∀ i j, d i ≠ d j → exp B i j = 0 := by
    intro i j hij
    obtain ⟨hzt, -⟩ := hW _ (hstab (· = d j)) (hirr (d j))
    have h1 : (Pi.single j 1 : Fin r → K) ∈ coordSubspace (K := K) fun i => d i = d j := by
      intro i hi
      have : i ≠ j := fun e => hi (congrArg d e)
      simp [this]
    have h2 := hzt _ h1 i hij
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at h2
  by_cases hne : ∃ i, d i = t
  swap
  · refine ⟨1, one_pos, fun y c hc => ?_⟩
    have : IsEmpty {i // d i = t} := ⟨fun i => hne ⟨i.1, i.2⟩⟩
    rw [Matrix.charpoly, Matrix.det_isEmpty, Polynomial.map_one] at hc
    simp at hc
  obtain ⟨i₀, hi₀⟩ := hne
  set β := rr t with hβ_def
  have hβ : 0 < β := by
    have : Nonempty {i // d i = t} := ⟨⟨i₀, hi₀⟩⟩
    have hdeg0 : ((exp B).toSquareBlockProp fun i => d i = t).charpoly.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree (Matrix.charpoly_monic _).ne_zero,
        Matrix.charpoly_natDegree_eq_dim]
      exact_mod_cast Fintype.card_ne_zero
    obtain ⟨c0, hc0⟩ := IsAlgClosed.exists_root _ hdeg0
    obtain ⟨i, hi, hni⟩ := exists_norm_eq_of_isRoot_toSquareBlockProp ι hzbd hrr (· = t) hc0
    have h0 := ne_zero_of_isRoot_toSquareBlockProp hzu
      (fun i j hj hi => hzbd i j fun e => hi (e ▸ hj)) hc0
    have hi' : d i = t := hi
    rw [hi'] at hni
    rw [hβ_def, ← hni]
    exact norm_pos_iff.mpr ((map_ne_zero ι).mpr h0)
  have hroot : ∀ (P : ℤ → Prop) [DecidablePred P] (x : K),
      x ∈ ((exp B).toSquareBlockProp fun i => P (d i)).charpoly.roots →
        ∃ i, P (d i) ∧ ‖ι x‖ = rr (d i) := fun P _ x hx =>
    exists_norm_eq_of_isRoot_toSquareBlockProp ι hzbd hrr P
      ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hx)
  set p : Fin r → Prop := fun i => β < rr (d i) with hp_def
  set W := coordSubspace (K := K) p with hW_def
  set N' := Fintype.card {i // p i} with hN'_def
  set k := N' + 1 with hk_def
  set Zp := (exp B).toSquareBlockProp p with hZp_def
  set Zq := (exp B).toSquareBlockProp fun i => ¬ p i with hZq_def
  have hzc : (exp B).charpoly = Zp.charpoly * Zq.charpoly :=
    charpoly_eq_mul_toSquareBlockProp _ p fun i hi j hj =>
      hzbd i j fun e => hi (by change β < rr (d i); rw [e]; exact hj)
  have hroots : (exp B).charpoly.roots = Zp.charpoly.roots + Zq.charpoly.roots := by
    rw [hzc, Polynomial.roots_mul]
    exact ((Matrix.charpoly_monic _).mul (Matrix.charpoly_monic _)).ne_zero
  have hM1 : ∀ x ∈ Zp.charpoly.roots.map (fun c => ‖ι c‖), β < x := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨i, hi, hn⟩ := hroot (fun s => β < rr s) c hc
    rw [hn]
    exact hi
  have hM2 : ∀ x ∈ Zq.charpoly.roots.map (fun c => ‖ι c‖), 0 ≤ x ∧ x ≤ β := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨i, hi, hn⟩ := hroot (fun s => ¬ β < rr s) c hc
    refine ⟨norm_nonneg _, ?_⟩
    rw [hn]
    exact not_lt.mp hi
  have hcardp : Multiset.card Zp.charpoly.roots = N' := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]
  set D := (Zp.charpoly.roots.map fun c => ‖ι c‖).prod with hD_def
  have hD : ‖ι Zp.det‖ = D := by
    rw [Matrix.det_eq_prod_roots_charpoly, norm_map_multiset_prod]
  have hDpos : 0 < D := Multiset.prod_pos fun x hx => hβ.trans (hM1 x hx)
  have hT : 0 < D * β := mul_pos hDpos hβ
  have hTz : ∀ c, (Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _)
      (compoundMonoidHom k (hzu.unit : Matrix (Fin r) (Fin r) K))).charpoly.IsRoot c →
        ‖ι c‖ ≤ D * β := by
    intro c hc
    rw [Matrix.charpoly_reindex, IsUnit.unit_spec] at hc
    have hmem : c ∈ (compoundMonoidHom k (exp B)).charpoly.roots :=
      (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mpr hc
    have hcp := charpoly_compoundMonoidHom_map k (RingHom.id K) (exp B)
    rw [Polynomial.map_id, Polynomial.map_id] at hcp
    rw [hcp, show (((exp B).charpoly.roots.powersetCard k).map fun s =>
        Polynomial.X - Polynomial.C s.prod) = (((exp B).charpoly.roots.powersetCard k).map
          Multiset.prod).map (fun a => Polynomial.X - Polynomial.C a) by
        rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C] at hmem
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hmem
    rw [Multiset.mem_powersetCard] at hs
    rw [norm_map_multiset_prod]
    refine multiset_prod_le_mul_of_card_eq_succ hβ.le hM1 hM2 ?_ ?_
    · rw [← Multiset.map_add, ← hroots]
      exact Multiset.map_le_map hs.1
    · rw [Multiset.card_map, Multiset.card_map, hs.2, hcardp]
  have hcoinv : ∀ i : ℕ, 0 < i → ∀ ζ : ℂ, ((LinearMap.charpoly (coinvariantsFrobenius H
      (tensorPowerRepresentation (exteriorPowerRepresentation k ρ) (2 * i)) φ)).map
        (ι.comp (algebraMap ℚ_[ℓ] K))).IsRoot ζ →
      ‖ζ‖ ≤ q ^ ((i : ℝ) * (2 * Real.logb q (D * β) / e)) := by
    intro i _ ζ hζ
    have h4 := norm_pow_le_of_isRoot_coinvariantsFrobenius ι H φ ρ P₀ d σ' hup hσ' U.index hGH
      hG hu hA hAn hBn hBG hAB hsum (z := hzu.unit) hzu.unit_spec k (2 * i) hT.le hTz ζ hζ
    have h5 := (pow_le_pow_iff_le_rpow_logb hq hT (norm_nonneg ζ) he (2 * i)).mp h4
    convert h5 using 2
    push_cast
    ring
  have hrank : ∀ (y : Y) (α : ℂ), ((exteriorPowerRepresentation k ρ (Fr y) :
      Matrix (Fin (Fintype.card (Set.powersetCard (Fin r) k)))
        (Fin (Fintype.card (Set.powersetCard (Fin r) k))) ℚ_[ℓ]).charpoly.map
          (ι.comp (algebraMap ℚ_[ℓ] K))).IsRoot α →
        ‖α‖ ^ e ≤ (D * β) ^ deg y := by
    intro y α hα
    have hτc := continuous_exteriorPowerRepresentation k hρ
    have h := norm_le_of_satisfiesFrobeniusTraceFormula hq.le (ι.comp (algebraMap ℚ_[ℓ] K)) H φ
      Fr deg hfin (exteriorPowerRepresentation k ρ)
      (fun y m => exteriorPowerRepresentation_charpoly_real k _ ρ (Fr y) (hreal y) m)
      (2 * Real.logb q (D * β) / e)
      (fun i _ => htf _ _ (continuous_tensorPowerRepresentation hτc (2 * i))) hcoinv y (hdeg y)
      α hα
    refine (pow_le_pow_iff_le_rpow_logb hq hT (norm_nonneg α) he (deg y)).mpr ?_
    convert h using 2
    ring
  have hdetQ : ∀ (Q : ℤ → Prop) [DecidablePred Q] (y : Y),
      ‖ι (((σ' (Fr y) : Matrix (Fin r) (Fin r) K).toSquareBlockProp fun i => Q (d i)).det)‖ ^ e =
        ‖ι (((exp B).toSquareBlockProp fun i => Q (d i)).det)‖ ^ deg y := by
    intro Q _ y
    obtain ⟨hz, h⟩ := norm_det_pow_eq_of_stable ι σ' hσc H φ hH U.index hGH hG hu hA hAn hBn hBG
      hAB hsum (W := coordSubspace (K := K) fun i => Q (d i)) (fun g => hstab Q g) (hFr y)
    rwa [show LinearMap.det (stabRestrict (σ' (Fr y) : Matrix (Fin r) (Fin r) K)
        (hstab Q (Fr y))) = _ from det_restrict_coordSubspace _,
      show LinearMap.det (stabRestrict (exp B) hz) = _ from det_restrict_coordSubspace _] at h
  have hle : ∀ (y : Y) (μ : K), ((σ' (Fr y) : Matrix (Fin r) (Fin r) K).toSquareBlockProp
      fun i => d i = t).charpoly.IsRoot μ → ‖ι μ‖ ^ e ≤ β ^ deg y := by
    intro y μ hμ
    obtain ⟨v, hv0, hvt, hgv⟩ := exists_mulVec_eq_of_isRoot_toSquareBlockProp
      (p := fun i => d i = t) (fun i j hj hi => hσbd (Fr y) i j fun e => hi (e ▸ hj)) hμ
    have hvW : v ∉ W := by
      intro hvW
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
      have hdi : d i = t := by
        by_contra h
        exact hi (hvt i h)
      have hpi : p i := by
        by_contra h
        exact hi (hvW i h)
      change β < rr (d i) at hpi
      rw [hdi] at hpi
      exact lt_irrefl _ hpi
    set f := Matrix.toLin' (σ' (Fr y) : Matrix (Fin r) (Fin r) K) with hf_def
    have hWf : ∀ v ∈ W, f v ∈ W := fun v hv => by
      rw [Matrix.toLin'_apply]
      exact hstab (fun s => β < rr s) (Fr y) v hv
    have hE := hasEigenvalue_exteriorPower_map_mul_det f W hWf hvW
      (by rw [Matrix.toLin'_apply]; exact hgv)
    have hfr : Module.finrank K W = N' := by
      rw [LinearEquiv.finrank_eq (coordSubspaceEquiv p), Module.finrank_fintype_fun_eq_card]
    rw [hfr, Module.End.hasEigenvalue_iff_isRoot_charpoly] at hE
    have hcp := charpoly_exteriorPower_map_map (RingHom.id K) f k
    rw [Polynomial.map_id, Polynomial.map_id, hf_def, Matrix.charpoly_toLin'] at hcp
    rw [hcp] at hE
    have hρc : (σ' (Fr y) : Matrix (Fin r) (Fin r) K).charpoly =
        (ρ (Fr y) : Matrix (Fin r) (Fin r) ℚ_[ℓ]).charpoly.map (algebraMap ℚ_[ℓ] K) := by
      rw [hσ' (Fr y), charpoly_gradedDiag (hup (Fr y)), Matrix.coe_units_inv,
        Matrix.charpoly_units_conj', Matrix.charpoly_map]
    rw [hρc, ← charpoly_exteriorPowerRepresentation_map k (algebraMap ℚ_[ℓ] K) ρ (Fr y)] at hE
    have hα := hrank y (ι (μ * LinearMap.det (f.restrict hWf)))
      (by rw [← Polynomial.map_map]; exact Polynomial.IsRoot.map hE)
    have e1 : LinearMap.det (f.restrict hWf) =
        ((σ' (Fr y) : Matrix (Fin r) (Fin r) K).toSquareBlockProp p).det :=
      det_restrict_coordSubspace _
    rw [e1, map_mul, norm_mul, mul_pow, hdetQ (fun s => β < rr s) y, hD, mul_pow,
      mul_comm (D ^ deg y)] at hα
    exact le_of_mul_le_mul_right hα (pow_pos hDpos _)
  refine ⟨β ^ ((e : ℝ)⁻¹), Real.rpow_pos_of_pos hβ _, fun y c hc => ?_⟩
  set Mt := (σ' (Fr y) : Matrix (Fin r) (Fin r) K).toSquareBlock d t with hMt_def
  set R := (β ^ ((e : ℝ)⁻¹)) ^ deg y with hR_def
  have hR0 : 0 ≤ R := pow_nonneg (Real.rpow_nonneg hβ.le _) _
  have hRe : R ^ e = β ^ deg y := by
    rw [hR_def, ← pow_mul, mul_comm, pow_mul, Real.rpow_inv_natCast_pow hβ.le he.ne']
  have hroots' : (Mt.charpoly.map ι).roots = Mt.charpoly.roots.map ι :=
    ((Matrix.charpoly_monic _).roots_map_of_card_eq_natDegree ι
      IsAlgClosed.card_roots_eq_natDegree).symm
  have hcm : c ∈ (Mt.charpoly.map ι).roots :=
    (Polynomial.mem_roots ((Matrix.charpoly_monic _).map ι).ne_zero).mpr hc
  refine norm_eq_of_forall_norm_le_of_norm_prod_eq (s := (Mt.charpoly.map ι).roots) (R := R) ?_ ?_
    c hcm
  · intro x hx
    rw [hroots'] at hx
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hx
    have h1 := hle y μ ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hμ)
    rw [← hRe] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR0 he.ne').mp h1
  · rw [hroots', ← map_multiset_prod, ← Matrix.det_eq_prod_roots_charpoly, Multiset.card_map,
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]
    have hdetV : ‖ι Mt.det‖ ^ e = ‖ι (((exp B).toSquareBlockProp fun i => d i = t).det)‖ ^
        deg y := hdetQ (· = t) y
    have hzt : ∀ x ∈ ((exp B).toSquareBlockProp fun i => d i = t).charpoly.roots,
        ‖ι x‖ = β := by
      intro x hx
      obtain ⟨i, hi, hn⟩ := hroot (· = t) x hx
      rw [hn, show d i = t from hi]
    rw [Matrix.det_eq_prod_roots_charpoly ((exp B).toSquareBlockProp _),
      norm_map_multiset_prod, Multiset.map_congr rfl hzt, Multiset.map_const',
      Multiset.prod_replicate, IsAlgClosed.card_roots_eq_natDegree,
      Matrix.charpoly_natDegree_eq_dim] at hdetV
    rw [← pow_left_inj₀ (norm_nonneg _) (pow_nonneg hR0 _) he.ne', hdetV, ← pow_mul R,
      mul_comm (Fintype.card _) e, pow_mul, hRe, ← pow_mul, mul_comm]
    rw [pow_mul]

omit [NontriviallyNormedField K] in
/-- On a diagonal block the graded diagonal part has the entries of the matrix. -/
public theorem toSquareBlock_gradedDiag {R : Type*} [CommRing R] (d : Fin r → ℤ)
    (T : Matrix (Fin r) (Fin r) R) (t : ℤ) :
    (gradedDiag d T).toSquareBlock d t = T.toSquareBlock d t := by
  ext i j
  simp [Matrix.toSquareBlock_def, gradedDiag, i.2, j.2]

/-- **The constituents of an `ι`-real representation are `ι`-pure** (Weil II 1.5.1; Kedlaya,
Theorem 6.5.2), for a block triangular form: if `P₀⁻¹ ρ P₀` is block upper triangular along `d`
over `K` with irreducible diagonal blocks (a subspace of a block stable under the block diagonal
parts is zero or the block), then on every block `t` there is `β > 0` with every root of the
characteristic polynomial of the block `t` of `P₀⁻¹ ρ(F_y) P₀` of absolute value `β ^ deg y`
along `ι`.  The hypotheses on `Γ`, `H`, `φ`, `Fr`, `deg`, `ρ` are those of
`Stacks.EtaleCohomology.exists_norm_eq_pow_of_isRoot_toSquareBlock`. -/
public theorem exists_norm_eq_pow_of_isGradedUpper (ι : K →+* ℂ) (H : Subgroup Γ)
    [H.Normal] (φ : Γ) (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hD1 : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) →
      ∀ ψ : ↥(H ⊓ U) → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) → ψ = 0)
    {Y : Type*} (Fr : Y → Γ) (deg : Y → ℕ) (hFr : ∀ y, (φ ^ deg y)⁻¹ * Fr y ∈ H)
    (hdeg : ∀ y, 0 < deg y) (hfin : ∀ m : ℕ, 0 < m → {y : Y | deg y ∣ m}.Finite)
    {q : ℝ} (hq : 1 < q)
    (htf : ∀ (m : ℕ) (τ : Γ →* GL (Fin m) ℚ_[ℓ]), Continuous τ →
      SatisfiesFrobeniusTraceFormula q (ι.comp (algebraMap ℚ_[ℓ] K)) H φ Fr deg τ)
    (ρ : Γ →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (hreal : ∀ (y : Y) (m : ℕ), (ι.comp (algebraMap ℚ_[ℓ] K))
      ((ρ (Fr y) : Matrix (Fin r) (Fin r) ℚ_[ℓ]).charpoly.coeff m) ∈ Set.range ((↑) : ℝ → ℂ))
    (P₀ : (Matrix (Fin r) (Fin r) K)ˣ) (d : Fin r → ℤ)
    (hup : ∀ g, IsGradedUpper d (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
      (ρ g : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) *
        (P₀ : Matrix (Fin r) (Fin r) K)))
    (hirr : ∀ (t : ℤ) (W' : Submodule K (Fin r → K)),
      W' ≤ coordSubspace (K := K) (fun i => d i = t) → W' ≠ ⊥ →
      (∀ g, ∀ v ∈ W', gradedDiag d (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) :
        Matrix (Fin r) (Fin r) K) * (ρ g : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) *
          (P₀ : Matrix (Fin r) (Fin r) K)) *ᵥ v ∈ W') →
        W' = coordSubspace (K := K) (fun i => d i = t))
    (t : ℤ) :
    ∃ β : ℝ, 0 < β ∧ ∀ (y : Y) (c : ℂ),
      (((((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
        (ρ (Fr y) : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) *
          (P₀ : Matrix (Fin r) (Fin r) K)).toSquareBlock d t).charpoly.map ι).IsRoot c →
        ‖c‖ = β ^ deg y := by
  classical
  set P1 : Matrix (Fin r) (Fin r) K := ((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) :
    Matrix (Fin r) (Fin r) K) with hP1
  set P0 : Matrix (Fin r) (Fin r) K := (P₀ : Matrix (Fin r) (Fin r) K) with hP0
  set T : Γ → Matrix (Fin r) (Fin r) K := fun g =>
    P1 * (ρ g : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) * P0 with hT_def
  have hρK : ∀ g h : Γ, (ρ (g * h) : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) =
      (ρ g : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) *
        (ρ h : Matrix (Fin r) (Fin r) ℚ_[ℓ]).map (algebraMap ℚ_[ℓ] K) := by
    intro g h
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  have hTmul : ∀ g h, T (g * h) = T g * T h := by
    intro g h
    simp only [hT_def, hρK, mul_assoc]
    rw [hP1, hP0, Units.mul_inv_cancel_left]
  have hT1 : T 1 = 1 := by
    simp only [hT_def, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), mul_one,
      hP1, hP0, Units.inv_mul]
  let σ' : Γ →* (Matrix (Fin r) (Fin r) K)ˣ :=
    { toFun := fun g => ⟨gradedDiag d (T g), gradedDiag d (T g⁻¹), by
          rw [← gradedDiag_mul (hup g) (hup g⁻¹), ← hTmul, mul_inv_cancel, hT1, gradedDiag_one],
        by rw [← gradedDiag_mul (hup g⁻¹) (hup g), ← hTmul, inv_mul_cancel, hT1, gradedDiag_one]⟩
      map_one' := Units.ext (by simp only [hT1, gradedDiag_one, Units.val_one])
      map_mul' := fun g h => Units.ext (by
        simp only [Units.val_mul]
        rw [hTmul, gradedDiag_mul (hup g) (hup h)]) }
  have hσv : ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) = gradedDiag d (T g) := fun g => rfl
  have hgd : Continuous (gradedDiag d : Matrix (Fin r) (Fin r) K → Matrix (Fin r) (Fin r) K) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun T : Matrix (Fin r) (Fin r) K => if d i = d j then T i j else 0
    split_ifs
    · exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const
  have hσc : Continuous fun g => (σ' g : Matrix (Fin r) (Fin r) K) := by
    refine hgd.comp ?_
    exact (continuous_const.matrix_mul (((Units.continuous_val.comp hρ).matrix_map
      (continuous_algebraMap ℚ_[ℓ] K)))).matrix_mul continuous_const
  have hstab : ∀ (Q : ℤ → Prop) [DecidablePred Q] (g : Γ), (σ' g : Matrix (Fin r) (Fin r) K) ∈
      stabilizerSubalgebra (coordSubspace (K := K) fun i => Q (d i)) := fun Q _ g =>
    mem_stabilizerSubalgebra_coordSubspace (fun i j h => by rw [hσv]; exact ite_eq_right h) Q
  set S : Set (Module.End K (Fin r → K)) :=
    Set.range fun g => Matrix.toLin' (σ' g : Matrix (Fin r) (Fin r) K) with hS_def
  have hSiff : ∀ X : Submodule K (Fin r → K), IsStableUnder S X ↔
      ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra X := fun _ =>
    ⟨fun h g => le_comap_toLin'_iff.mp (h _ ⟨g, rfl⟩), by
      rintro h _ ⟨g, rfl⟩
      exact le_comap_toLin'_iff.mpr (h g)⟩
  have htop : sSup {X | IsIrreducibleUnder S X} = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    rw [pi_eq_sum_univ v]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hmem : (fun j => if i = j then (1 : K) else 0) ∈
        coordSubspace (K := K) (fun j => d j = d i) := by
      intro j hj
      have : i ≠ j := fun e => hj (by rw [e])
      simp [this]
    refine Submodule.mem_sSup_of_mem ?_ hmem
    refine ⟨fun h => ?_, (hSiff _).mpr (hstab (· = d i)), fun W' hle hW' => ?_⟩
    · have := (Submodule.mem_bot K).mp (h ▸ hmem)
      simpa using congrFun this i
    · by_cases h : W' = ⊥
      · exact Or.inl h
      · exact Or.inr (hirr (d i) W' hle h fun g v hv => (hSiff W').mp hW' g v hv)
  have hss : ∀ W : Submodule K (Fin r → K),
      (∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (Fin r → K), IsCompl W W' ∧
        ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W' := by
    intro W hW
    obtain ⟨W', hc, hW'⟩ := exists_isCompl_of_sSup_eq_top htop ((hSiff W).mpr hW)
    exact ⟨W', hc, (hSiff W').mp hW'⟩
  obtain ⟨β, hβ, h⟩ := exists_norm_eq_pow_of_isRoot_toSquareBlock ι H φ hcomm hD1 Fr deg hFr
    hdeg hfin hq htf ρ hρ hreal P₀ d σ' hup hσv hσc hss
    (fun t W' hle hne hW' => hirr t W' hle hne fun g v hv => hW' g v hv) t
  refine ⟨β, hβ, fun y c hc => h y c ?_⟩
  rwa [hσv, toSquareBlock_gradedDiag]

end Purity

end Stacks.EtaleCohomology

end
