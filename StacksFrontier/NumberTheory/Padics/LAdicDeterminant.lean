module

public import StacksFrontier.NumberTheory.Padics.LAdicOuterAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerCharpoly
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Projection

/-!
# Determinant of the `ℓ`-adic exponential on invariant subspaces

For a matrix `M` over a complete, algebraically closed, ultrametric normed field `K` over `ℚ_ℓ`
with `‖M‖ < ℓ⁻¹`, and a subspace `S ⊆ K^n` stable under `M`, we prove
`det (exp M |_S) = exp (tr (M |_S))` and `‖tr (M |_S)‖ ≤ ‖M‖`.  The proof triangularizes `M |_S`
in some basis of `S`; the norm of that matrix is not controlled, but its diagonal entries are
eigenvalues of `M`, which have norm at most `‖M‖`, and the exponential series of the triangular
matrix converges, being the image of the exponential series of `M` under a continuous linear map.

Consequently, if a matrix `g` in the disc `‖g - 1‖ < ℓ⁻¹` preserves `S` and `det (g |_S)` is a root
of unity, then `tr (log g |_S) = 0`.  These are the inputs relating determinants of Frobenius on
constituents to the decomposition `u ^ ℓ ^ N = exp A * exp B` of
`Stacks.LAdic.exists_pow_eq_exp_mul_exp_of_normalizes` (Weil II, 1.3.9–1.3.12).

## Main results

* `Stacks.LAdic.norm_le_of_mulVec_eq_smul`: eigenvalues are bounded by the sup norm.
* `Stacks.LAdic.det_restrict_exp`: `det (exp M |_S) = exp (tr (M |_S))`.
* `Stacks.LAdic.trace_restrict_ladicLog_eq_zero`: `tr (log g |_S) = 0` when `det (g |_S)` has
  finite order.
-/

@[expose] public noncomputable section

open Filter Topology NormedSpace Matrix

namespace Stacks.LAdic

variable {ℓ : ℕ} [Fact ℓ.Prime]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist Matrix.completeSpace_of_ultra

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K] {n : Type*} [Fintype n] [DecidableEq n]

omit [Fact ℓ.Prime] [CharZero K] [NormedAlgebra ℚ_[ℓ] K] in
/-- An eigenvalue of a matrix over an ultrametric field is bounded by its sup norm. -/
theorem norm_le_of_mulVec_eq_smul {M : Matrix n n K} {v : n → K} (hv : v ≠ 0) {μ : K}
    (h : M *ᵥ v = μ • v) : ‖μ‖ ≤ ‖M‖ := by
  obtain ⟨i, hi⟩ : ∃ i, ∀ j, ‖v j‖ ≤ ‖v i‖ := by
    have : Nonempty n := by
      by_contra hn
      exact hv (funext fun j => absurd ⟨j⟩ hn)
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) Finset.univ_nonempty
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  have hvi : 0 < ‖v i‖ := by
    by_contra h0
    refine hv (funext fun j => ?_)
    have := (hi j).trans (not_lt.mp h0)
    exact norm_le_zero_iff.mp this
  have hrow : ‖μ * v i‖ ≤ ‖M‖ * ‖v i‖ := by
    have e : μ * v i = (M *ᵥ v) i := by rw [h]; rfl
    rw [e, mulVec, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
    rw [norm_mul]
    exact mul_le_mul (norm_entry_le_entrywise_sup_norm M) (hi j) (norm_nonneg _) (norm_nonneg _)
  rw [norm_mul] at hrow
  exact le_of_mul_le_mul_right hrow hvi

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K] in
/-- The diagonal of a power of an upper triangular matrix. -/
theorem pow_apply_self_of_isUpperTriangular {d : ℕ} {T : Matrix (Fin d) (Fin d) K}
    (hT : T.IsUpperTriangular) (k : ℕ) (i : Fin d) : (T ^ k) i i = T i i ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i, ih, pow_succ]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with h | h
      · rw [(hT.pow k) h, zero_mul]
      · rw [hT h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

variable [CompleteSpace K]

omit [CharZero K] in
/-- **The determinant of a triangular exponential series.**  If the exponential series of an upper
triangular matrix `T` with diagonal entries in the disc `‖t‖ < ℓ⁻¹` sums to `E`, then
`det E = exp (tr T)`. -/
theorem det_eq_exp_trace_of_hasSum {d : ℕ} {T E : Matrix (Fin d) (Fin d) K}
    (hT : T.IsUpperTriangular) (hdiag : ∀ i, ‖T i i‖ < (ℓ : ℝ)⁻¹)
    (hE : HasSum (fun k => (((k.factorial : ℕ) : ℚ_[ℓ])⁻¹) • T ^ k) E) :
    E.det = exp T.trace := by
  have hentry : ∀ i j, HasSum (fun k => ((((k.factorial : ℕ) : ℚ_[ℓ])⁻¹) • T ^ k) i j) (E i j) :=
    fun i j => Pi.hasSum.mp (Pi.hasSum.mp hE i) j
  have hEup : E.IsUpperTriangular := by
    intro i j hij
    refine (hentry i j).unique ?_
    simp [Matrix.smul_apply, (hT.pow _) hij]
  have hEdiag : ∀ i, E i i = exp (T i i) := by
    intro i
    refine (hentry i i).unique ?_
    have := hasSum_exp (ℓ := ℓ) (𝔸 := K) (hdiag i)
    simpa [Matrix.smul_apply, pow_apply_self_of_isUpperTriangular hT] using this
  rw [det_of_isUpperTriangular hEup, Matrix.trace]
  simp only [Matrix.diag, hEdiag]
  have key : ∀ s : Finset (Fin d), ‖∑ i ∈ s, T i i‖ < (ℓ : ℝ)⁻¹ ∧
      ∏ i ∈ s, exp (T i i) = exp (∑ i ∈ s, T i i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨?_, by simp⟩
      have : (0 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
      simpa using this
    | insert a s ha ih =>
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_insert ha]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hdiag a) ih.1)
      · rw [Finset.prod_insert ha, Finset.sum_insert ha, ih.2,
          exp_add_of_commute_of_mem_ball (𝕂 := ℚ_[ℓ]) (Commute.all _ _)
            (mem_eball_expSeries (hdiag a)) (mem_eball_expSeries ih.1)]
  exact (key Finset.univ).2

omit [Fact ℓ.Prime] [CharZero K] [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] in
/-- In an ultrametric normed group, a finite sum of terms of norm `< r` has norm `< r`. -/
theorem norm_sum_lt_of_forall_lt {ι : Type*} (s : Finset ι) (f : ι → K) {r : ℝ} (hr : 0 < r)
    (h : ∀ i ∈ s, ‖f i‖ < r) : ‖∑ i ∈ s, f i‖ < r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

omit [CharZero K] [CompleteSpace K] in
/-- The restriction to `S` of a matrix preserving `S`. -/
def stabRestrict {S : Submodule K (n → K)} (X : Matrix n n K) (hX : X ∈ stabilizerSubalgebra S) :
    Module.End K S :=
  (Matrix.toLin' X).restrict fun x hx => by rw [Matrix.toLin'_apply]; exact hX x hx

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- The restriction of `X` to `S` acts on `w ∈ S` as `X *ᵥ w`. -/
theorem stabRestrict_apply {S : Submodule K (n → K)} {X : Matrix n n K}
    (hX : X ∈ stabilizerSubalgebra S) (w : S) : ((stabRestrict X hX w : S) : n → K) = X *ᵥ w := by
  simp [stabRestrict, LinearMap.restrict_apply, Matrix.toLin'_apply]

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- The restriction of `X ^ k` to `S` is the `k`-th power of the restriction of `X`. -/
theorem stabRestrict_pow {S : Submodule K (n → K)} {X : Matrix n n K}
    (hX : X ∈ stabilizerSubalgebra S) (k : ℕ) :
    stabRestrict (X ^ k) (Subalgebra.pow_mem _ hX k) = stabRestrict X hX ^ k := by
  induction k with
  | zero => ext w; simp [stabRestrict_apply]
  | succ k ih =>
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [stabRestrict_apply, pow_succ' (stabRestrict X hX), Module.End.mul_apply,
      stabRestrict_apply, ← ih, stabRestrict_apply, Matrix.mulVec_mulVec, ← pow_succ']

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- The restriction of `X * Y` to `S` is the product of the restrictions of `X` and `Y`. -/
theorem stabRestrict_mul {S : Submodule K (n → K)} {X Y : Matrix n n K}
    (hX : X ∈ stabilizerSubalgebra S) (hY : Y ∈ stabilizerSubalgebra S) :
    stabRestrict (X * Y) (Subalgebra.mul_mem _ hX hY) = stabRestrict X hX * stabRestrict Y hY :=
  LinearMap.ext fun w => Subtype.ext (by
    rw [stabRestrict_apply, Module.End.mul_apply, stabRestrict_apply, stabRestrict_apply,
      Matrix.mulVec_mulVec])

omit [Fact ℓ.Prime] [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- Equal matrices preserving `S` have the same restriction to `S`. -/
theorem stabRestrict_congr {S : Submodule K (n → K)} {X Y : Matrix n n K} (h : X = Y)
    (hX : X ∈ stabilizerSubalgebra S) (hY : Y ∈ stabilizerSubalgebra S) :
    stabRestrict X hX = stabRestrict Y hY := by
  subst h; rfl

omit [CharZero K] [CompleteSpace K] in
/-- The eigenvalues of the restriction of `M` to an invariant subspace are bounded by `‖M‖`. -/
theorem norm_le_of_hasEigenvalue_stabRestrict {S : Submodule K (n → K)} {M : Matrix n n K}
    (hM : M ∈ stabilizerSubalgebra S) {μ : K} (h : (stabRestrict M hM).HasEigenvalue μ) :
    ‖μ‖ ≤ ‖M‖ := by
  obtain ⟨w, hw⟩ := h.exists_hasEigenvector
  refine norm_le_of_mulVec_eq_smul (v := (w : n → K)) ?_ ?_
  · exact fun h0 => hw.2 (Subtype.ext h0)
  · rw [← stabRestrict_apply hM, hw.apply_eq_smul]
    rfl

omit [CharZero K] in
/-- **`det (exp M |_S) = exp (tr (M |_S))`**, and `‖tr (M |_S)‖ < ℓ⁻¹`, for `‖M‖ < ℓ⁻¹`. -/
theorem det_stabRestrict_exp [IsAlgClosed K] {S : Submodule K (n → K)} {M : Matrix n n K}
    (hMn : ‖M‖ < (ℓ : ℝ)⁻¹) (hM : M ∈ stabilizerSubalgebra S)
    (hE : exp M ∈ stabilizerSubalgebra S) :
    ‖LinearMap.trace K S (stabRestrict M hM)‖ < (ℓ : ℝ)⁻¹ ∧
      LinearMap.det (stabRestrict (exp M) hE) = exp (LinearMap.trace K S (stabRestrict M hM)) := by
  classical
  set f := stabRestrict M hM
  obtain ⟨b, hb⟩ := Stacks.EtaleCohomology.exists_basis_isUpperTriangular_toMatrix f
  set T := LinearMap.toMatrix b b f with hTdef
  have hdiag : ∀ i, ‖T i i‖ < (ℓ : ℝ)⁻¹ := by
    intro i
    refine lt_of_le_of_lt (norm_le_of_hasEigenvalue_stabRestrict hM ?_) hMn
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, ← LinearMap.charpoly_toMatrix f b,
      ← hTdef, Matrix.charpoly_of_isUpperTriangular T hb, Polynomial.IsRoot,
      Polynomial.eval_prod, Finset.prod_eq_zero_iff]
    exact ⟨i, Finset.mem_univ _, by simp⟩
  have htr : LinearMap.trace K S f = T.trace := LinearMap.trace_eq_matrix_trace K b f
  refine ⟨?_, ?_⟩
  · rw [htr, Matrix.trace]
    have : (0 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
    exact norm_sum_lt_of_forall_lt _ _ (by positivity) fun i _ => hdiag i
  · obtain ⟨C, hC⟩ := S.exists_isCompl
    let Φ : Matrix n n K →ₗ[K] Matrix (Fin (Module.finrank K S)) (Fin (Module.finrank K S)) K :=
      { toFun := fun X =>
          LinearMap.toMatrix b b (S.projectionOnto C hC ∘ₗ Matrix.toLin' X ∘ₗ S.subtype)
        map_add' := fun X Y => by simp [LinearMap.add_comp, LinearMap.comp_add]
        map_smul' := fun c X => by simp [LinearMap.smul_comp, LinearMap.comp_smul] }
    have hΦ : ∀ (X : Matrix n n K) (hX : X ∈ stabilizerSubalgebra S),
        Φ X = LinearMap.toMatrix b b (stabRestrict X hX) := by
      intro X hX
      change LinearMap.toMatrix b b _ = _
      congr 1
      refine LinearMap.ext fun w => ?_
      have hw : ((stabRestrict X hX w : S) : n → K) = X *ᵥ w := stabRestrict_apply hX w
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, Matrix.toLin'_apply]
      rw [← hw, Submodule.projectionOnto_apply_left]
    have hsum := (hasSum_exp (ℓ := ℓ) hMn).map Φ.toAddMonoidHom
      (LinearMap.continuous_of_finiteDimensional Φ)
    have hterm : ∀ k : ℕ, Φ.toAddMonoidHom ((((k.factorial : ℕ) : ℚ_[ℓ])⁻¹) • M ^ k) =
        (((k.factorial : ℕ) : ℚ_[ℓ])⁻¹) • T ^ k := by
      intro k
      rw [LinearMap.toAddMonoidHom_coe, LinearMap.map_smul_of_tower,
        hΦ _ (Subalgebra.pow_mem _ hM k), stabRestrict_pow, LinearMap.toMatrix_pow]
    simp only [Function.comp_def, hterm] at hsum
    have hdet := det_eq_exp_trace_of_hasSum hb hdiag hsum
    rw [LinearMap.toAddMonoidHom_coe] at hdet
    exact (LinearMap.det_toMatrix b _).symm.trans ((congrArg Matrix.det (hΦ _ hE)).symm.trans
      (hdet.trans (by rw [htr])))

/-- **Trace of the logarithm on an invariant subspace.**  If `g` lies in the disc
`‖g - 1‖ < ℓ⁻¹`, preserves `S`, and `det (g |_S)` has finite order, then `tr (log g |_S) = 0`. -/
theorem trace_stabRestrict_ladicLog_eq_zero [IsAlgClosed K] {S : Submodule K (n → K)}
    {g : Matrix n n K} (hg1 : ‖g - 1‖ < (ℓ : ℝ)⁻¹) (hg : g ∈ stabilizerSubalgebra S)
    (hL : ladicLog ℓ g ∈ stabilizerSubalgebra S) {m : ℕ} (hm : 0 < m)
    (hdet : LinearMap.det (stabRestrict g hg) ^ m = 1) :
    LinearMap.trace K S (stabRestrict (ladicLog ℓ g) hL) = 0 := by
  set L := ladicLog ℓ g
  have hLn : ‖L‖ < (ℓ : ℝ)⁻¹ := (norm_ladicLog_le hg1.le).trans_lt hg1
  have hEL : exp L = g := exp_ladicLog hg1
  have hE : exp L ∈ stabilizerSubalgebra S := hEL ▸ hg
  obtain ⟨ht, hdt⟩ := det_stabRestrict_exp hLn hL hE
  set t := LinearMap.trace K S (stabRestrict L hL)
  have key : ∀ (x y : Matrix n n K) (_ : x = y) (hx : x ∈ stabilizerSubalgebra S)
      (hy : y ∈ stabilizerSubalgebra S), stabRestrict x hx = stabRestrict y hy := by
    rintro x _ rfl hx hy; rfl
  have hdet' : exp t ^ m = 1 := by
    rw [← hdt, key _ _ hEL hE hg]
    exact hdet
  have hmt : ‖m • t‖ < (ℓ : ℝ)⁻¹ := (norm_nsmul_le_of_ultrametric m t).trans_lt ht
  have h0 : m • t = 0 := by
    rw [← ladicLog_exp hmt, exp_nsmul_of_norm_lt ht, hdet']
    refine ladicLog_eq_of_tendsto ?_
    have : logSeq ℓ (1 : K) = fun _ => 0 := funext fun m => by simp [logSeq]
    rw [this]
    exact tendsto_const_nhds
  rw [nsmul_eq_mul] at h0
  exact (mul_eq_zero.mp h0).resolve_left (Nat.cast_ne_zero.mpr hm.ne')

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Elements of the Lie algebra of the monodromy have determinant `1` on invariant subspaces.**
If `det (g |_S)` has finite order for every `g ∈ G`, then for `A` in the Lie algebra spanned by
`log G` (and `‖A‖ < ℓ⁻¹`), `det (exp A |_S) = 1`. -/
theorem det_stabRestrict_exp_eq_one [IsAlgClosed K] {G : Subgroup (Matrix n n K)ˣ}
    (hG : ∀ g ∈ G, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹) {S : Submodule K (n → K)}
    (hGS : ∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra S)
    (hdetG : ∀ g ∈ G, ∃ m : ℕ, 0 < m ∧ ∀ hg : (g : Matrix n n K) ∈ stabilizerSubalgebra S,
      LinearMap.det (stabRestrict (g : Matrix n n K) hg) ^ m = 1)
    {A : Matrix n n K} (hA : Matrix.toLinAlgEquiv' A ∈ logLieSpan ℓ G) (hAn : ‖A‖ < (ℓ : ℝ)⁻¹)
    (hAS : A ∈ stabilizerSubalgebra S) (hE : exp A ∈ stabilizerSubalgebra S) :
    LinearMap.det (stabRestrict (exp A) hE) = 1 := by
  have hstab : ∀ x ∈ logLieSpan ℓ G, ∀ v ∈ S, x v ∈ S := fun x hx =>
    apply_mem_of_mem_logLieSpan hG hGS hx
  have htr : ∀ x (hx : x ∈ logLieSpan ℓ G), LinearMap.trace K S (x.restrict (hstab x hx)) = 0 := by
    intro x hx
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      obtain ⟨m, hm, hdet⟩ := hdetG g hg
      have hL : ladicLog ℓ (g : Matrix n n K) ∈ stabilizerSubalgebra S :=
        (ladicLog_mem_stabilizerSubalgebra_iff (hG g hg)).mpr (hGS g hg)
      have e : (Matrix.toLinAlgEquiv' (ladicLog ℓ (g : Matrix n n K))).restrict
          (hstab _ (LieSubalgebra.subset_lieSpan ⟨g, hg, rfl⟩)) =
          stabRestrict (ladicLog ℓ (g : Matrix n n K)) hL :=
        LinearMap.ext fun w => Subtype.ext (by
          rw [stabRestrict_apply, LinearMap.coe_restrict_apply, Matrix.toLinAlgEquiv'_apply])
      rw [e]
      exact trace_stabRestrict_ladicLog_eq_zero (hG g hg) (hGS g hg) hL hm (hdet _)
    | zero =>
      have e : (0 : Module.End K (n → K)).restrict (hstab 0 (LieSubalgebra.zero_mem _)) = 0 :=
        LinearMap.ext fun w => Subtype.ext (by simp)
      rw [e, map_zero]
    | add x y hx hy ihx ihy =>
      have e : (x + y).restrict (hstab _ (LieSubalgebra.add_mem _ hx hy)) =
          x.restrict (hstab x hx) + y.restrict (hstab y hy) :=
        LinearMap.ext fun w => Subtype.ext (by simp)
      rw [e, map_add, ihx, ihy, add_zero]
    | smul a x hx ihx =>
      have e : (a • x).restrict (hstab _ (LieSubalgebra.smul_mem _ a hx)) =
          a • x.restrict (hstab x hx) :=
        LinearMap.ext fun w => Subtype.ext (by simp)
      rw [e, map_smul, ihx, smul_zero]
    | lie x y hx hy _ _ =>
      have e : ⁅x, y⁆.restrict (hstab _ (LieSubalgebra.lie_mem _ hx hy)) =
          x.restrict (hstab x hx) * y.restrict (hstab y hy) -
            y.restrict (hstab y hy) * x.restrict (hstab x hx) :=
        LinearMap.ext fun w => Subtype.ext (by
          simp [LieRing.of_associative_ring_bracket])
      rw [e, map_sub, LinearMap.trace_mul_comm, sub_self]
  have eA : (Matrix.toLinAlgEquiv' A).restrict (hstab _ hA) = stabRestrict A hAS :=
    LinearMap.ext fun w => Subtype.ext (by
      rw [stabRestrict_apply, LinearMap.coe_restrict_apply, Matrix.toLinAlgEquiv'_apply])
  have h0 := htr _ hA
  rw [eA] at h0
  rw [(det_stabRestrict_exp hAn hAS hE).2, h0, exp_zero]

/-- **Determinantal weights through the centralizing element** (Kedlaya, Proposition 6.1.4, for
subspaces).  In the situation of `Stacks.LAdic.exists_pow_eq_exp_mul_exp_of_normalizes`, assume
moreover that `det (g |_S)` has finite order for every `G`-stable subspace `S` and `g ∈ G` (the
finiteness of determinants on the geometric monodromy, Weil II 1.3.4).  Then there are `N` and an
invertible `z` commuting with `G` and with `u` such that every subspace `S` stable under `G` and
`u` is `z`-stable and `det (u ^ ℓ ^ N |_S) = det (z |_S)`. -/
theorem exists_det_stabRestrict_pow_eq [IsAlgClosed K] {G : Subgroup (Matrix n n K)ˣ}
    (hG : ∀ g ∈ G, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹)
    (hss : ∀ W : Submodule K (n → K), (∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (n → K), IsCompl W W' ∧
        ∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra W')
    {u : (Matrix n n K)ˣ} (hu : ‖(u : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹)
    (hnorm : ∀ g ∈ G, u * g * u⁻¹ ∈ G)
    (hdetG : ∀ S : Submodule K (n → K), (∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra S) →
      ∀ g ∈ G, ∃ m : ℕ, 0 < m ∧ ∀ hg : (g : Matrix n n K) ∈ stabilizerSubalgebra S,
        LinearMap.det (stabRestrict (g : Matrix n n K) hg) ^ m = 1) :
    ∃ N : ℕ, ∃ z : Matrix n n K, IsUnit z ∧ (∀ g ∈ G, Commute z (g : Matrix n n K)) ∧
      Commute z (u : Matrix n n K) ∧
      ∀ S : Submodule K (n → K), (∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra S) →
        (u : Matrix n n K) ∈ stabilizerSubalgebra S →
        ∃ hz : z ∈ stabilizerSubalgebra S, ∃ hu' : (u : Matrix n n K) ^ (ℓ ^ N) ∈
          stabilizerSubalgebra S,
          LinearMap.det (stabRestrict _ hu') = LinearMap.det (stabRestrict z hz) := by
  obtain ⟨N, A, B, hA, hAn, hBn, hBG, hBu, hAB, hsum, heq⟩ :=
    exists_pow_eq_exp_mul_exp_of_normalizes hG hss hu hnorm
  refine ⟨N, exp B, isUnit_exp_of_mem_ball (𝕂 := ℚ_[ℓ]) (mem_eball_expSeries hBn),
    fun g hg => (hBG g hg).exp_left, hBu.exp_left, fun S hGS huS => ?_⟩
  have hX : ladicLog ℓ (u : Matrix n n K) ∈ stabilizerSubalgebra S :=
    (ladicLog_mem_stabilizerSubalgebra_iff hu).mpr huS
  have hAS : A ∈ stabilizerSubalgebra S := fun v hv => by
    have := apply_mem_of_mem_logLieSpan hG hGS hA v hv
    rwa [Matrix.toLinAlgEquiv'_apply] at this
  have hBS : B ∈ stabilizerSubalgebra S := by
    have hB : B = (ℓ ^ N : ℕ) • ladicLog ℓ (u : Matrix n n K) - A := by rw [hsum]; abel
    rw [hB]
    exact Subalgebra.sub_mem _ (Subalgebra.nsmul_mem _ hX _) hAS
  have hEA : exp A ∈ stabilizerSubalgebra S := NormedSpace.exp_mem (R := K)
    (isClosed_stabilizerSubalgebra S) hAS
  have hEB : exp B ∈ stabilizerSubalgebra S := NormedSpace.exp_mem (R := K)
    (isClosed_stabilizerSubalgebra S) hBS
  have huN : (u : Matrix n n K) ^ (ℓ ^ N) ∈ stabilizerSubalgebra S := Subalgebra.pow_mem _ huS _
  refine ⟨hEB, huN, ?_⟩
  rw [stabRestrict_congr heq huN (Subalgebra.mul_mem _ hEA hEB), stabRestrict_mul hEA hEB,
    map_mul, det_stabRestrict_exp_eq_one hG hGS (hdetG S hGS) hA hAn hAS hEA, one_mul]

end Stacks.LAdic
