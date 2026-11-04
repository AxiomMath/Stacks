module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Discriminant
public import StacksFrontier.RingTheory.Polynomial.MatrixCokernelDimension

/-!
# A `k[s]`-lattice and a `k[s⁻¹]`-lattice with constant discriminants

Let `k ⊆ F` be fields, `s ∈ F` transcendental over `k`, and `L` a finite-dimensional `F`-vector
space with two bases `b`, `c`. Think of `b` as a basis of a `k[s]`-lattice and of `c` as a basis of
a `k[s⁻¹]`-lattice in `L`, that is, of a vector bundle on `𝐏¹_k` glued from its two charts. If both
discriminants (for a fixed algebra structure of `L` over `F`) are nonzero constants and the
change-of-basis matrices have entries in `k[s, s⁻¹]`, then the vectors whose `b`-coordinates lie in
`k[s]` and whose `c`-coordinates lie in `k[s⁻¹]` (the global sections of the bundle) form a
`k`-vector space of dimension at least `rank L`.

This is the Riemann–Roch inequality `h⁰(E) ≥ χ(E) = rank E + deg E` for a bundle of degree zero
on `𝐏¹`.

## Main definitions

* `Polynomial.coordLattice k b R`: the vectors whose `b`-coordinates lie in a subalgebra `R`.

## Main results

* `Polynomial.card_le_finrank_of_coordLattice_inf_le`: the inequality above, for any
  finite-dimensional subspace containing the global sections.
-/

@[expose] public noncomputable section

open Module Polynomial Matrix

namespace Polynomial

variable (k : Type*) {F L : Type*} [Field k] [Field F] [Algebra k F] [Field L] [Algebra F L]
  [Algebra k L] [IsScalarTower k F L] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `k`-subspace of vectors of `L` whose coordinates in the basis `b` lie in the subalgebra
`R` of `F`. -/
def coordLattice (b : Basis ι F L) (R : Subalgebra k F) : Submodule k L :=
  (Submodule.pi Set.univ fun _ : ι ↦ Subalgebra.toSubmodule R).comap
    (b.equivFun.toLinearMap.restrictScalars k)

variable {k}

omit [DecidableEq ι] in
/-- A vector lies in `coordLattice k b R` if and only if each of its `b`-coordinates lies in
`R`. -/
theorem mem_coordLattice {b : Basis ι F L} {R : Subalgebra k F} {x : L} :
    x ∈ coordLattice k b R ↔ ∀ i, b.equivFun x i ∈ R :=
  ⟨fun h i ↦ h i trivial, fun h i _ ↦ h i⟩

/-- Multiplying an element of `k[s⁻¹]` by a power of `s⁻¹` stays in `k[s⁻¹]`. -/
private theorem inv_pow_mul_mem_adjoin_inv {s x : F} (n : ℕ) (h : x ∈ Algebra.adjoin k {s⁻¹}) :
    s⁻¹ ^ n * x ∈ Algebra.adjoin k {s⁻¹} :=
  Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton k _) _) h

/-- An element of `k[s, s⁻¹]` becomes an element of `k[s⁻¹]` after multiplication by a power of
`s⁻¹`. -/
theorem exists_inv_pow_mul_mem_adjoin {s : F} (hs : s ≠ 0) {x : F}
    (hx : x ∈ Algebra.adjoin k {s, s⁻¹}) : ∃ N : ℕ, s⁻¹ ^ N * x ∈ Algebra.adjoin k {s⁻¹} := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hs]; exact Subalgebra.one_mem _⟩
    · exact ⟨0, by rw [pow_zero, one_mul]; exact Algebra.self_mem_adjoin_singleton k _⟩
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hy
    refine ⟨N + M, ?_⟩
    rw [mul_add]
    refine Subalgebra.add_mem _ ?_ ?_
    · rw [pow_add, mul_comm (s⁻¹ ^ N), mul_assoc]
      exact inv_pow_mul_mem_adjoin_inv _ hN
    · rw [pow_add, mul_assoc]
      exact inv_pow_mul_mem_adjoin_inv _ hM
  | mul x y _ _ hx hy =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hy
    refine ⟨N + M, ?_⟩
    rw [pow_add, show s⁻¹ ^ N * s⁻¹ ^ M * (x * y) = (s⁻¹ ^ N * x) * (s⁻¹ ^ M * y) by ring]
    exact Subalgebra.mul_mem _ hN hM

/-- If `s⁻¹ ^ N * x` lies in `k[s⁻¹]` and `N ≤ M`, then so does `s⁻¹ ^ M * x`. -/
theorem inv_pow_mul_mem_adjoin_of_le {s : F} {x : F} {N M : ℕ} (hNM : N ≤ M)
    (h : s⁻¹ ^ N * x ∈ Algebra.adjoin k {s⁻¹}) : s⁻¹ ^ M * x ∈ Algebra.adjoin k {s⁻¹} := by
  rw [← Nat.sub_add_cancel hNM, pow_add, mul_assoc]
  exact inv_pow_mul_mem_adjoin_inv _ h

/-- `s^m p(s⁻¹)` is a polynomial in `s` when `deg p ≤ m`. -/
theorem pow_mul_aeval_inv_mem_adjoin {s : F} (hs : s ≠ 0) {m : ℕ} {p : k[X]}
    (hp : p.natDegree ≤ m) : s ^ m * aeval s⁻¹ p ∈ Algebra.adjoin k {s} := by
  let : Invertible s := invertibleOfNonzero hs
  have h := eval₂_reflect_mul_pow (algebraMap k F) s m (reflect m p)
    (natDegree_reflect_le.trans (max_le le_rfl hp))
  rw [reflect_reflect, invOf_eq_inv] at h
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  refine ⟨reflect m p, ?_⟩
  show aeval s (reflect m p) = s ^ m * aeval s⁻¹ p
  rw [aeval_def, aeval_def, ← h, mul_comm]

/-- **Global sections of a degree-zero bundle on `𝐏¹`.** Let `s ∈ F` be transcendental over `k`
and `b`, `c` two bases of `L` over `F` with discriminants nonzero constants of `k` and with both
change-of-basis matrices having entries in `k[s, s⁻¹]`. Then the vectors with `b`-coordinates in
`k[s]` and `c`-coordinates in `k[s⁻¹]` span at least `#ι` dimensions over `k`. -/
theorem card_le_finrank_of_coordLattice_inf_le {s : F} (hs : Transcendental k s) (b c : Basis ι F L)
    {α β : k} (hα : α ≠ 0) (hb : Algebra.discr F b = algebraMap k F α)
    (hc : Algebra.discr F c = algebraMap k F β)
    (hG : ∀ i j, b.toMatrix c i j ∈ Algebra.adjoin k {s, s⁻¹})
    (hH : ∀ i j, c.toMatrix b i j ∈ Algebra.adjoin k {s, s⁻¹})
    (W : Submodule k L) [FiniteDimensional k W]
    (hW : coordLattice k b (Algebra.adjoin k {s}) ⊓ coordLattice k c (Algebra.adjoin k {s⁻¹}) ≤ W) :
    Fintype.card ι ≤ finrank k W := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs isAlgebraic_zero
  set u := s⁻¹ with hu
  have hut : Transcendental k u := fun h ↦ hs (IsAlgebraic.inv_iff.mp h)
  let φ : k[X] →ₐ[k] F := aeval u
  have hφ : Function.Injective φ := transcendental_iff_injective.mp hut
  let G := b.toMatrix c
  let H := c.toMatrix b
  choose NG hNG using fun i j ↦ exists_inv_pow_mul_mem_adjoin hs0 (hG i j)
  choose NH hNH using fun i j ↦ exists_inv_pow_mul_mem_adjoin hs0 (hH i j)
  obtain ⟨N, hN⟩ := Finite.exists_le fun p : ι × ι ↦ NG p.1 p.2 + NH p.1 p.2
  set m := N + 1 with hm
  have hmem : ∀ i j, u ^ m * G i j ∈ Algebra.adjoin k {u} ∧
      u ^ m * H i j ∈ Algebra.adjoin k {u} := fun i j ↦
    have h : NG i j + NH i j ≤ N := hN (i, j)
    ⟨inv_pow_mul_mem_adjoin_of_le (by omega) (hNG i j),
      inv_pow_mul_mem_adjoin_of_le (by omega) (hNH i j)⟩
  simp only [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  choose T hT using fun i j ↦ (hmem i j).1
  choose T₂ hT₂ using fun i j ↦ (hmem i j).2
  let TM : Matrix ι ι k[X] := Matrix.of T
  let TM₂ : Matrix ι ι k[X] := Matrix.of T₂
  have hTmap : TM.map φ = u ^ m • G := Matrix.ext hT
  have hT₂map : TM₂.map φ = u ^ m • H := Matrix.ext hT₂
  have hGH : G * H = 1 := Basis.toMatrix_mul_toMatrix_flip b c
  have hTT : TM * TM₂ = (X ^ (2 * m) : k[X]) • (1 : Matrix ι ι k[X]) := by
    apply Matrix.map_injective hφ
    show (TM * TM₂).map φ = ((X ^ (2 * m) : k[X]) • (1 : Matrix ι ι k[X])).map φ
    rw [Matrix.map_mul, hTmap, hT₂map, Matrix.smul_mul, Matrix.mul_smul, hGH, smul_smul,
      ← pow_add]
    ext i j
    by_cases hij : i = j <;> simp [hij, two_mul, φ]
  -- the determinant of `G` is constant
  have hcb : ⇑c = b ᵥ* G.map (algebraMap F L) := by
    funext j
    rw [Matrix.vecMul, dotProduct, ← Basis.sum_toMatrix_smul_self b c j]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Matrix.map_apply, Algebra.smul_def, mul_comm]
  have hdisc : algebraMap k F β = G.det ^ 2 * algebraMap k F α := by
    rw [← hc, ← hb, hcb, Algebra.discr_of_matrix_vecMul]
  have hdetT : TM.det ^ 2 = C (β / α) * X ^ (2 * (m * Fintype.card ι)) := by
    apply hφ
    have hd : φ TM.det = (TM.map φ).det := RingHom.map_det φ.toRingHom TM
    rw [map_pow, hd, hTmap, Matrix.det_smul]
    simp only [φ, map_mul, map_pow, aeval_X, aeval_C, map_div₀]
    rw [hdisc, mul_div_assoc,
      div_self ((map_ne_zero_iff _ (algebraMap k F).injective).mpr hα), mul_one]
    ring
  have hdeg : TM.det.natDegree = m * Fintype.card ι := by
    have hβ : β ≠ 0 := by
      rintro rfl
      have h0 : G.det ^ 2 * algebraMap k F α = 0 := by rw [← hdisc, map_zero]
      rcases mul_eq_zero.mp h0 with h | h
      · have : G.det * H.det = 1 := by rw [← Matrix.det_mul, hGH, Matrix.det_one]
        rw [pow_eq_zero_iff two_ne_zero] at h
        rw [h, zero_mul] at this
        exact zero_ne_one this
      · exact hα ((map_eq_zero_iff _ (algebraMap k F).injective).mp h)
    have h2 := congrArg natDegree hdetT
    rw [natDegree_pow, natDegree_C_mul_X_pow _ _ (div_ne_zero hβ hα)] at h2
    omega
  -- the injective map from the polynomial count into the lattice intersection
  let P : Submodule k (ι → k[X]) := Submodule.pi Set.univ (fun _ : ι ↦ degreeLT k (m + 1)) ⊓
    (LinearMap.range TM.mulVecLin).restrictScalars k
  let Ψ₀ : (ι → k[X]) →ₗ[k] L :=
    (b.equivFun.symm.toLinearMap.restrictScalars k) ∘ₗ
      (LinearMap.pi fun i ↦ (LinearMap.mulLeft k (s ^ m)) ∘ₗ φ.toLinearMap ∘ₗ LinearMap.proj i)
  have hΨ₀ : ∀ v, b.equivFun (Ψ₀ v) = fun i ↦ s ^ m * φ (v i) := by
    intro v
    show b.equivFun (b.equivFun.symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hΨinj : Function.Injective Ψ₀ := by
    intro v w h
    have := congrArg b.equivFun h
    rw [hΨ₀, hΨ₀] at this
    funext i
    exact hφ (mul_left_cancel₀ (pow_ne_zero _ hs0) (congrFun this i))
  have hΨmem : ∀ v ∈ P, Ψ₀ v ∈ coordLattice k b (Algebra.adjoin k {s}) ⊓
      coordLattice k c (Algebra.adjoin k {s⁻¹}) := by
    rintro v ⟨hvP, z, hz⟩
    refine ⟨mem_coordLattice.mpr fun i ↦ ?_, mem_coordLattice.mpr fun i ↦ ?_⟩
    · rw [hΨ₀]
      exact pow_mul_aeval_inv_mem_adjoin hs0 (natDegree_le_of_degree_le (Order.le_of_lt_succ
        (by exact_mod_cast mem_degreeLT.mp (hvP i (Set.mem_univ i)))))
    · have hzv : ∀ i, φ (v i) = (u ^ m • (G *ᵥ fun j ↦ φ (z j))) i := by
        intro i
        rw [← hz]
        show φ ((TM *ᵥ z) i) = _
        rw [← AlgHom.coe_toRingHom, RingHom.map_mulVec, AlgHom.coe_toRingHom]
        show (TM.map φ *ᵥ fun j ↦ φ (z j)) i = _
        rw [hTmap, Matrix.smul_mulVec]
      have hb' : b.equivFun (Ψ₀ v) = G *ᵥ fun j ↦ φ (z j) := by
        rw [hΨ₀]
        funext i
        rw [hzv, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← mul_pow, hu,
          mul_inv_cancel₀ hs0, one_pow, one_mul]
      have hc' : c.equivFun (Ψ₀ v) = fun j ↦ φ (z j) := by
        rw [Basis.equivFun_apply, ← Basis.toMatrix_mulVec_repr b c, ← Basis.equivFun_apply, hb',
          Matrix.mulVec_mulVec, Basis.toMatrix_mul_toMatrix_flip c b, Matrix.one_mulVec]
      rw [hc', ← hu, Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨z i, rfl⟩
  calc Fintype.card ι ≤ finrank k P :=
        card_le_finrank_pi_degreeLT_inf_range TM TM₂ (by omega) hTT hdeg
    _ = finrank k (P.map Ψ₀) := LinearEquiv.finrank_eq (P.equivMapOfInjective Ψ₀ hΨinj)
    _ ≤ finrank k W := Submodule.finrank_mono
      (Submodule.map_le_iff_le_comap.mpr fun v hv ↦ hW (hΨmem v hv))

end Polynomial

end
