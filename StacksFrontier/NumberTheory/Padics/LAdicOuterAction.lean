module

public import StacksFrontier.NumberTheory.Padics.LAdicExpLog
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SemisimpleLieNormalizer
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.Pi

/-!
# Frobenius acts on the `ℓ`-adic monodromy by an inner automorphism, up to the centralizer

Let `K` be a complete, algebraically closed, ultrametric normed field over `ℚ_ℓ` (for instance
`ℂ_ℓ`), let `G` be a group of invertible `r × r` matrices over `K` close to `1`, acting
semisimply on `K^r`, and let `u` be a matrix close to `1` normalizing `G`.  Then a power of `u`
is `exp A · z` where `A` lies in the Lie algebra spanned by the logarithms of `G` and `z`
commutes with `G` and with `u`.

This is the `ℓ`-adic form of Deligne's finiteness of the outer action of Frobenius on the
geometric monodromy (Weil II, 1.3.9; Kedlaya, *Fourier transforms and p-adic Weil II*,
Proposition 6.1.3).  Instead of the Zariski closure of the monodromy group and the dimension
theory of algebraic groups, the argument uses the `ℓ`-adic logarithm
(`Stacks.LAdic.ladicLog`): the Lie algebra `𝔤` spanned by `log G` has the same invariant
subspaces as `G`, `log u` normalizes `𝔤` because conjugation by `u` permutes `log G`, and the
Lie-algebra normalizer lemma
(`Stacks.EtaleCohomology.exists_mem_centralizer_sub_mem_of_mem_normalizer`) splits `log u` as an
element of `𝔤` plus an element of its centralizer.

## Main results

* `Matrix.ultraNormedRing`, `Matrix.ultraNormedAlgebra`: the sup norm on square matrices over an
  ultrametric normed ring is submultiplicative.
* `Stacks.LAdic.exists_pow_eq_exp_mul_of_normalizes`: the decomposition of a power of `u`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.3.9.
* K. S. Kedlaya, *Fourier transforms and p-adic "Weil II"*, Compos. Math. 142 (2006), 6.1.
-/

@[expose] public noncomputable section

open Filter Topology NormedSpace

namespace Matrix

variable {n α : Type*} [Fintype n] [DecidableEq n]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

omit [DecidableEq n] in
/-- The sup norm of a product of matrices over an ultrametric normed ring is at most the product
of the sup norms. -/
theorem norm_mul_le_of_ultrametric [NormedRing α] [IsUltrametricDist α] (A B : Matrix n n α) :
    ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  rw [norm_le_iff (by positivity)]
  intro i j
  rw [mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  exact (norm_mul_le _ _).trans (mul_le_mul (norm_entry_le_entrywise_sup_norm A)
    (norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _))

/-- The normed ring structure on square matrices over an ultrametric normed ring given by the
entrywise sup norm.  Not an instance, as there are several natural norms on matrices. -/
@[instance_reducible]
protected def ultraNormedRing [NormedRing α] [IsUltrametricDist α] : NormedRing (Matrix n n α) :=
  { Matrix.normedAddCommGroup, Matrix.instRing with
    norm_mul_le := norm_mul_le_of_ultrametric }

attribute [local instance] Matrix.ultraNormedRing

/-- The normed algebra structure on square matrices over an ultrametric normed algebra given by
the entrywise sup norm. -/
@[instance_reducible]
protected def ultraNormedAlgebra {R : Type*} [NormedField R] [NormedRing α] [IsUltrametricDist α]
    [NormedAlgebra R α] : NormedAlgebra R (Matrix n n α) :=
  { Matrix.normedSpace, Matrix.instAlgebra with }

/-- The entrywise sup distance on square matrices over an ultrametric normed ring is itself
ultrametric. -/
theorem isUltrametricDist [NormedRing α] [IsUltrametricDist α] :
    IsUltrametricDist (Matrix n n α) :=
  Pi.instIsUltrametricDist (X := fun _ : n => n → α)

omit [DecidableEq n] in
/-- Square matrices over a complete normed ring form a complete space for the entrywise sup
norm. -/
theorem completeSpace_of_ultra [NormedRing α] [CompleteSpace α] :
    CompleteSpace (Matrix n n α) :=
  inferInstanceAs (CompleteSpace (n → n → α))

end Matrix

namespace Stacks.LAdic

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Abstract

/-- `ℓ⁻¹ < 1` as a real number. -/
private theorem inv_ell_lt_one : (ℓ : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt)

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ_[ℓ] 𝔸] [IsUltrametricDist 𝔸]

omit [Fact ℓ.Prime] [NormedAlgebra ℚ_[ℓ] 𝔸] in
/-- `‖u⁻¹ - 1‖ ≤ ‖u - 1‖` for a unit with `‖u - 1‖ < 1`. -/
theorem norm_inv_sub_one_le {u : 𝔸ˣ} (hu : ‖(u : 𝔸) - 1‖ < 1) :
    ‖((u⁻¹ : 𝔸ˣ) : 𝔸) - 1‖ ≤ ‖(u : 𝔸) - 1‖ := by
  have h : ((u⁻¹ : 𝔸ˣ) : 𝔸) * (u : 𝔸) = 1 := u.inv_mul
  have key : ((u⁻¹ : 𝔸ˣ) : 𝔸) - 1 =
      -((((u⁻¹ : 𝔸ˣ) : 𝔸) - 1) * ((u : 𝔸) - 1)) - ((u : 𝔸) - 1) := by
    simp only [sub_mul, mul_sub, h, mul_one, one_mul]
    abel
  set a := ‖((u⁻¹ : 𝔸ˣ) : 𝔸) - 1‖
  set e := ‖(u : 𝔸) - 1‖
  have hle : a ≤ max (a * e) e := by
    calc a = ‖-((((u⁻¹ : 𝔸ˣ) : 𝔸) - 1) * ((u : 𝔸) - 1)) - ((u : 𝔸) - 1)‖ := by rw [← key]
      _ ≤ max ‖-((((u⁻¹ : 𝔸ˣ) : 𝔸) - 1) * ((u : 𝔸) - 1))‖ ‖(u : 𝔸) - 1‖ := by
          rw [sub_eq_add_neg, ← norm_neg ((u : 𝔸) - 1)]
          exact IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max (a * e) e := by
          rw [norm_neg]
          exact max_le_max (norm_mul_le _ _) le_rfl
  by_contra! hlt
  have ha0 : 0 < a := (norm_nonneg _).trans_lt hlt
  rcases le_max_iff.mp hle with h1 | h1 <;> linarith [mul_lt_of_lt_one_right ha0 hu]

omit [Fact ℓ.Prime] [NormedAlgebra ℚ_[ℓ] 𝔸] in
/-- `‖u ^ N - 1‖ ≤ ‖u - 1‖` for `‖u - 1‖ ≤ 1`. -/
theorem norm_pow_sub_one_le {u : 𝔸} (hu : ‖u - 1‖ ≤ 1) (N : ℕ) : ‖u ^ N - 1‖ ≤ ‖u - 1‖ := by
  have hb := norm_one_add_pow_sub_le hu N
  rw [add_sub_cancel] at hb
  calc ‖u ^ N - 1‖ = ‖(u ^ N - 1 - N • (u - 1)) + N • (u - 1)‖ := by rw [sub_add_cancel]
    _ ≤ max ‖u ^ N - 1 - N • (u - 1)‖ ‖N • (u - 1)‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ ‖u - 1‖ := max_le (hb.trans (sq_le (norm_nonneg _) hu)) (norm_nsmul_le_of_ultrametric N _)

variable [CompleteSpace 𝔸]

/-- **The logarithm commutes with conjugation.** -/
theorem ladicLog_conj (a : 𝔸ˣ) {u : 𝔸} (hu : ‖u - 1‖ ≤ (ℓ : ℝ)⁻¹) :
    ladicLog ℓ ((a : 𝔸) * u * ((a⁻¹ : 𝔸ˣ) : 𝔸)) = a * ladicLog ℓ u * ((a⁻¹ : 𝔸ˣ) : 𝔸) := by
  refine ladicLog_eq_of_tendsto ?_
  have hseq : logSeq ℓ ((a : 𝔸) * u * ((a⁻¹ : 𝔸ˣ) : 𝔸)) =
      fun m => (a : 𝔸) * logSeq ℓ u m * ((a⁻¹ : 𝔸ˣ) : 𝔸) := by
    funext m
    have hp : ((a : 𝔸) * u * ((a⁻¹ : 𝔸ˣ) : 𝔸)) ^ (ℓ ^ m) =
        (a : 𝔸) * u ^ (ℓ ^ m) * ((a⁻¹ : 𝔸ˣ) : 𝔸) := by
      induction ℓ ^ m with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [logSeq, logSeq, hp, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one,
      Units.mul_inv]
  rw [hseq]
  exact ((tendsto_logSeq hu).const_mul _).mul_const _

/-- **The bracket with `log u` as a limit of conjugations.**  If every conjugate `uᵏ Y u⁻ᵏ`
lies in a closed `ℚ_ℓ`-subspace `T`, so does `[log u, Y]`: it is the limit of
`ℓ^{-m} (u^{ℓ^m} Y u^{-ℓ^m} - Y)`. -/
theorem lie_mem_of_forall_conj_mem {T : Submodule ℚ_[ℓ] 𝔸} (hT : IsClosed (T : Set 𝔸))
    {u : 𝔸ˣ} (hu : ‖(u : 𝔸) - 1‖ ≤ (ℓ : ℝ)⁻¹) (hu' : ‖((u⁻¹ : 𝔸ˣ) : 𝔸) - 1‖ ≤ (ℓ : ℝ)⁻¹)
    {Y : 𝔸} (hY : ∀ k : ℕ, ((u ^ k : 𝔸ˣ) : 𝔸) * Y * (((u ^ k)⁻¹ : 𝔸ˣ) : 𝔸) ∈ T) :
    ladicLog ℓ (u : 𝔸) * Y - Y * ladicLog ℓ (u : 𝔸) ∈ T := by
  have hc : (ℓ : ℚ_[ℓ]) ≠ 0 := ell_ne_zero
  have hY0 : Y ∈ T := by simpa using hY 0
  set f : ℕ → 𝔸 := fun m => ((ℓ : ℚ_[ℓ]) ^ m)⁻¹ •
    (((u ^ (ℓ ^ m) : 𝔸ˣ) : 𝔸) * Y * (((u ^ (ℓ ^ m))⁻¹ : 𝔸ˣ) : 𝔸) - Y) with hf
  have hfT : ∀ m, f m ∈ T := fun m => T.smul_mem _ (T.sub_mem (hY _) hY0)
  have hwinv : ∀ m, (((u ^ (ℓ ^ m))⁻¹ : 𝔸ˣ) : 𝔸) = ((u⁻¹ : 𝔸ˣ) : 𝔸) ^ (ℓ ^ m) := fun m => by
    rw [← inv_pow, Units.val_pow_eq_pow_val]
  have hkey : ∀ m, f m = (logSeq ℓ (u : 𝔸) m * Y - Y * logSeq ℓ (u : 𝔸) m) *
      ((u⁻¹ : 𝔸ˣ) : 𝔸) ^ (ℓ ^ m) := by
    intro m
    have hw : ((u ^ (ℓ ^ m) : 𝔸ˣ) : 𝔸) = 1 + ((ℓ : ℚ_[ℓ]) ^ m) • logSeq ℓ (u : 𝔸) m := by
      rw [← pow_sub_one_eq_smul_logSeq, Units.val_pow_eq_pow_val, add_sub_cancel]
    have hww : ((u ^ (ℓ ^ m) : 𝔸ˣ) : 𝔸) * (((u ^ (ℓ ^ m))⁻¹ : 𝔸ˣ) : 𝔸) = 1 := Units.mul_inv _
    have h1 : ((u ^ (ℓ ^ m) : 𝔸ˣ) : 𝔸) * Y * (((u ^ (ℓ ^ m))⁻¹ : 𝔸ˣ) : 𝔸) - Y =
        (((u ^ (ℓ ^ m) : 𝔸ˣ) : 𝔸) * Y - Y * ((u ^ (ℓ ^ m) : 𝔸ˣ) : 𝔸)) *
          (((u ^ (ℓ ^ m))⁻¹ : 𝔸ˣ) : 𝔸) := by
      rw [sub_mul, mul_assoc Y, hww, mul_one]
    rw [hf]
    dsimp only
    rw [h1, hw, hwinv]
    simp only [add_mul, mul_add, one_mul, mul_one, add_sub_add_left_eq_sub, smul_mul_assoc,
      mul_smul_comm, ← smul_sub, smul_mul_assoc, inv_smul_smul₀ (pow_ne_zero _ hc)]
  have hinv : Tendsto (fun m => ((u⁻¹ : 𝔸ˣ) : 𝔸) ^ (ℓ ^ m)) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun m : ℕ => ((ℓ : ℝ)⁻¹) ^ m * ‖((u⁻¹ : 𝔸ˣ) : 𝔸) - 1‖) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        inv_ell_lt_one).mul_const ‖((u⁻¹ : 𝔸ˣ) : 𝔸) - 1‖
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) h0
    rw [pow_sub_one_eq_smul_logSeq, norm_smul, norm_ell_pow]
    exact mul_le_mul_of_nonneg_left (norm_logSeq_le hu' m) (by positivity)
  have hlim : Tendsto f atTop (𝓝 ((ladicLog ℓ (u : 𝔸) * Y - Y * ladicLog ℓ (u : 𝔸)) * 1)) := by
    rw [show f = _ from funext hkey]
    exact ((((tendsto_logSeq hu).mul_const Y).sub ((tendsto_logSeq hu).const_mul Y)).mul hinv)
  rw [mul_one] at hlim
  exact hT.mem_of_tendsto hlim (Eventually.of_forall hfT)

end Abstract

section Matrix

open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist Matrix.completeSpace_of_ultra

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrices preserving a subspace `W ⊆ K^n`. -/
def stabilizerSubalgebra (W : Submodule K (n → K)) : Subalgebra K (Matrix n n K) where
  carrier := {M | ∀ w ∈ W, M *ᵥ w ∈ W}
  mul_mem' {M N} hM hN w hw := by
    rw [← Matrix.mulVec_mulVec]
    exact hM _ (hN w hw)
  add_mem' {M N} hM hN w hw := by
    rw [Matrix.add_mulVec]
    exact W.add_mem (hM w hw) (hN w hw)
  algebraMap_mem' c w hw := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem c hw

omit [CharZero K] [IsUltrametricDist K] in
/-- A matrix lies in `stabilizerSubalgebra W` if and only if it maps every vector of `W` into
`W`. -/
theorem mem_stabilizerSubalgebra {W : Submodule K (n → K)} {M : Matrix n n K} :
    M ∈ stabilizerSubalgebra W ↔ ∀ w ∈ W, M *ᵥ w ∈ W := Iff.rfl

variable [CompleteSpace K]

omit [CharZero K] in
/-- Over a complete field, the subalgebra of matrices stabilizing a subspace `W` is a closed
set. -/
theorem isClosed_stabilizerSubalgebra (W : Submodule K (n → K)) :
    IsClosed ((stabilizerSubalgebra W : Subalgebra K (Matrix n n K)) : Set (Matrix n n K)) :=
  (stabilizerSubalgebra W).toSubmodule.closed_of_finiteDimensional

/-- A matrix close to `1` and its logarithm preserve the same subspaces. -/
theorem ladicLog_mem_stabilizerSubalgebra_iff {W : Submodule K (n → K)} {u : Matrix n n K}
    (hu : ‖u - 1‖ < (ℓ : ℝ)⁻¹) :
    ladicLog ℓ u ∈ stabilizerSubalgebra W ↔ u ∈ stabilizerSubalgebra W := by
  refine ⟨fun h => ?_, fun h => ladicLog_mem (S := (stabilizerSubalgebra W).restrictScalars ℚ_[ℓ])
    (isClosed_stabilizerSubalgebra W) h hu.le⟩
  rw [← exp_ladicLog hu]
  exact NormedSpace.exp_mem (R := K) (isClosed_stabilizerSubalgebra W) h

attribute [local instance 100] LieRing.ofAssociativeRing

variable (ℓ) in
/-- The Lie algebra `𝔤 ⊆ 𝔤𝔩(K^n)` spanned by the logarithms of a group of matrices. -/
def logLieSpan (G : Subgroup (Matrix n n K)ˣ) : LieSubalgebra K (Module.End K (n → K)) :=
  LieSubalgebra.lieSpan K (Module.End K (n → K))
    {x | ∃ g ∈ G, x = Matrix.toLinAlgEquiv' (ladicLog ℓ (g : Matrix n n K))}

variable {G : Subgroup (Matrix n n K)ˣ}

/-- The Lie algebra spanned by `log G` preserves every `G`-stable subspace. -/
theorem apply_mem_of_mem_logLieSpan (hG : ∀ g ∈ G, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹)
    {W : Submodule K (n → K)} (hGW : ∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra W)
    {x : Module.End K (n → K)} (hx : x ∈ logLieSpan ℓ G) : ∀ w ∈ W, x w ∈ W := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    intro w hw
    rw [Matrix.toLinAlgEquiv'_apply]
    exact ((ladicLog_mem_stabilizerSubalgebra_iff (hG g hg)).mpr (hGW g hg)) w hw
  | zero => exact fun _ _ => by simp
  | add x y _ _ hx hy => exact fun w hw => W.add_mem (hx w hw) (hy w hw)
  | smul a x _ hx => exact fun w hw => W.smul_mem a (hx w hw)
  | lie x y _ _ hx hy =>
    intro w hw
    rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply]
    exact W.sub_mem (hx _ (hy w hw)) (hy _ (hx w hw))

/-- Conversely, a subspace preserved by the Lie algebra spanned by `log G` is `G`-stable. -/
theorem mem_stabilizerSubalgebra_of_logLieSpan
    (hG : ∀ g ∈ G, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹) {W : Submodule K (n → K)}
    (hW : ∀ x ∈ logLieSpan ℓ G, ∀ w ∈ W, x w ∈ W) {g : (Matrix n n K)ˣ} (hg : g ∈ G) :
    (g : Matrix n n K) ∈ stabilizerSubalgebra W := by
  rw [← ladicLog_mem_stabilizerSubalgebra_iff (hG g hg)]
  intro w hw
  simpa only [Matrix.toLinAlgEquiv'_apply] using
    hW _ (LieSubalgebra.subset_lieSpan ⟨g, hg, rfl⟩) w hw

/-- If `K^n` is a semisimple `G`-module, it is a semisimple module over the Lie algebra spanned
by `log G`. -/
theorem sSup_atoms_logLieSpan (hG : ∀ g ∈ G, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹)
    (hss : ∀ W : Submodule K (n → K), (∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (n → K), IsCompl W W' ∧
        ∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra W') :
    sSup {W : LieSubmodule K (logLieSpan ℓ G) (n → K) | IsAtom W} = ⊤ := by
  have : ComplementedLattice (LieSubmodule K (logLieSpan ℓ G) (n → K)) := by
    refine ⟨fun M => ?_⟩
    obtain ⟨W', hc, hW'⟩ := hss (M : Submodule K (n → K)) fun g hg =>
      mem_stabilizerSubalgebra_of_logLieSpan hG (fun x hx w hw => M.lie_mem (x := ⟨x, hx⟩) hw) hg
    let M' : LieSubmodule K (logLieSpan ℓ G) (n → K) :=
      { W' with
        lie_mem := fun {x w} hw => apply_mem_of_mem_logLieSpan hG hW' x.2 w hw }
    refine ⟨M', ?_⟩
    rw [← LieSubmodule.isCompl_toSubmodule]
    exact hc
  exact sSup_atoms_eq_top

omit [CharZero K] in
/-- `log u` normalizes the Lie algebra spanned by `log G` when `u` normalizes `G`. -/
theorem toLinAlgEquiv'_ladicLog_mem_normalizer
    (hG : ∀ g ∈ G, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹) {u : (Matrix n n K)ˣ}
    (hu : ‖(u : Matrix n n K) - 1‖ ≤ (ℓ : ℝ)⁻¹)
    (hu' : ‖((u⁻¹ : (Matrix n n K)ˣ) : Matrix n n K) - 1‖ ≤ (ℓ : ℝ)⁻¹)
    (hnorm : ∀ g ∈ G, u * g * u⁻¹ ∈ G) :
    Matrix.toLinAlgEquiv' (ladicLog ℓ (u : Matrix n n K)) ∈ (logLieSpan ℓ G).normalizer := by
  set X := ladicLog ℓ (u : Matrix n n K)
  let T : Submodule K (Matrix n n K) := (logLieSpan ℓ G).toSubmodule.comap
    (Matrix.toLinAlgEquiv' : Matrix n n K ≃ₐ[K] _).toLinearMap
  have hT : IsClosed ((T.restrictScalars ℚ_[ℓ] : Submodule ℚ_[ℓ] (Matrix n n K)) :
      Set (Matrix n n K)) := T.closed_of_finiteDimensional
  have hconj : ∀ k : ℕ, ∀ g ∈ G, u ^ k * g * (u ^ k)⁻¹ ∈ G := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro g hg
      have e : u ^ (k + 1) * g * (u ^ (k + 1))⁻¹ = u * (u ^ k * g * (u ^ k)⁻¹) * u⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact hnorm _ (ih g hg)
  have hgen : ∀ g ∈ G, X * ladicLog ℓ (g : Matrix n n K) - ladicLog ℓ (g : Matrix n n K) * X ∈
      T := by
    intro g hg
    refine lie_mem_of_forall_conj_mem (T := T.restrictScalars ℚ_[ℓ]) hT hu hu' fun k => ?_
    rw [← ladicLog_conj (u ^ k) (hG g hg).le]
    change Matrix.toLinAlgEquiv' _ ∈ logLieSpan ℓ G
    exact LieSubalgebra.subset_lieSpan ⟨u ^ k * g * (u ^ k)⁻¹, hconj k g hg, by
      simp only [Units.val_mul]⟩
  rw [LieSubalgebra.mem_normalizer_iff]
  intro y hy
  induction hy using LieSubalgebra.lieSpan_induction with
  | mem y hy =>
    obtain ⟨g, hg, rfl⟩ := hy
    have := hgen g hg
    simp only [T, Submodule.mem_comap, AlgEquiv.toLinearMap_apply, map_sub, map_mul] at this
    rw [LieRing.of_associative_ring_bracket]
    exact this
  | zero => simpa only [lie_zero] using LieSubalgebra.zero_mem _
  | add y z _ _ hy hz => simpa only [lie_add] using LieSubalgebra.add_mem _ hy hz
  | smul a y _ hy => simpa only [lie_smul] using LieSubalgebra.smul_mem _ a hy
  | lie y z hy' hz' hy hz =>
    rw [leibniz_lie]
    exact LieSubalgebra.add_mem _ (LieSubalgebra.lie_mem _ hy hz')
      (LieSubalgebra.lie_mem _ hy' hz)

omit [CharZero K] [IsUltrametricDist K] [CompleteSpace K] in
/-- If an endomorphism `z` of `K^n` centralizes a set `S` of endomorphisms and the endomorphism
of a matrix `M` lies in `S`, then the matrix of `z` commutes with `M`. -/
theorem commute_of_toLinAlgEquiv'_mem_centralizer {S : Set (Module.End K (n → K))}
    {z : Module.End K (n → K)} (hz : z ∈ Subalgebra.centralizer K S) {M : Matrix n n K}
    (hM : Matrix.toLinAlgEquiv' M ∈ S) : Commute (Matrix.toLinAlgEquiv'.symm z) M := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [map_mul, AlgEquiv.apply_symm_apply]
  exact ((Subalgebra.mem_centralizer_iff K).mp hz _ hM).symm

omit [CompleteSpace K] in
/-- **Frobenius acts on the `ℓ`-adic monodromy by an inner automorphism up to the centralizer**
(the `ℓ`-adic form of Weil II, 1.3.9).  Let `K` be a complete, algebraically closed, ultrametric
normed field over `ℚ_ℓ`, `G` a group of matrices in the disc `‖g - 1‖ < ℓ⁻¹` for which `K^n` is
a semisimple module, and `u` a matrix in the same disc normalizing `G`.  Then
`u ^ ℓ ^ N = exp A * exp B` for some `N`, where `A` lies in the Lie algebra spanned by `log G`,
`B` commutes with `A`, with `u` and with every element of `G`, and `ℓ ^ N • log u = A + B`. -/
theorem exists_pow_eq_exp_mul_exp_of_normalizes [CompleteSpace K] [IsAlgClosed K]
    (hG : ∀ g ∈ G, ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹)
    (hss : ∀ W : Submodule K (n → K), (∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (n → K), IsCompl W W' ∧
        ∀ g ∈ G, (g : Matrix n n K) ∈ stabilizerSubalgebra W')
    {u : (Matrix n n K)ˣ} (hu : ‖(u : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹)
    (hnorm : ∀ g ∈ G, u * g * u⁻¹ ∈ G) :
    ∃ N : ℕ, ∃ A B : Matrix n n K,
      Matrix.toLinAlgEquiv' A ∈ logLieSpan ℓ G ∧ ‖A‖ < (ℓ : ℝ)⁻¹ ∧ ‖B‖ < (ℓ : ℝ)⁻¹ ∧
      (∀ g ∈ G, Commute B (g : Matrix n n K)) ∧ Commute B (u : Matrix n n K) ∧ Commute A B ∧
      (ℓ ^ N : ℕ) • ladicLog ℓ (u : Matrix n n K) = A + B ∧
      (u : Matrix n n K) ^ (ℓ ^ N) = exp A * exp B := by
  have hℓ0 : (0 : ℝ) < ℓ := Nat.cast_pos.2 (Fact.out : ℓ.Prime).pos
  have hu1 : ‖(u : Matrix n n K) - 1‖ < 1 := hu.trans inv_ell_lt_one
  have hu' := (norm_inv_sub_one_le hu1).trans hu.le
  set X := ladicLog ℓ (u : Matrix n n K) with hXdef
  have hX : ‖X‖ < (ℓ : ℝ)⁻¹ := (norm_ladicLog_le hu.le).trans_lt hu
  have hnor := toLinAlgEquiv'_ladicLog_mem_normalizer hG hu.le hu' hnorm
  obtain ⟨z', hz', hXz⟩ := Stacks.EtaleCohomology.exists_mem_centralizer_sub_mem_of_mem_normalizer
    (sSup_atoms_logLieSpan hG hss) hnor
  set Z := Matrix.toLinAlgEquiv'.symm z' with hZ
  set A₀ := X - Z with hA₀
  have hA₀mem : Matrix.toLinAlgEquiv' A₀ ∈ logLieSpan ℓ G := by
    rw [hA₀, map_sub, hZ, AlgEquiv.apply_symm_apply]
    exact hXz
  have hZA : Commute Z A₀ := commute_of_toLinAlgEquiv'_mem_centralizer hz' hA₀mem
  have hZg : ∀ g ∈ G, Commute Z (g : Matrix n n K) := by
    intro g hg
    rw [← exp_ladicLog (hG g hg)]
    exact (commute_of_toLinAlgEquiv'_mem_centralizer hz'
      (LieSubalgebra.subset_lieSpan ⟨g, hg, rfl⟩)).exp_right
  have hXsum : X = A₀ + Z := (sub_add_cancel X Z).symm
  have hZX : Commute Z X := by
    rw [hXsum]
    exact hZA.add_right (Commute.refl Z)
  have hZu : Commute Z (u : Matrix n n K) := by
    rw [← exp_ladicLog hu]
    exact hZX.exp_right
  set M := max ‖A₀‖ ‖Z‖
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < (ℓ : ℝ)⁻¹ / (M + 1) by positivity)
    (inv_ell_lt_one (ℓ := ℓ))
  have hsmall : ∀ x : Matrix n n K, ‖x‖ ≤ M → ‖(ℓ ^ N : ℕ) • x‖ < (ℓ : ℝ)⁻¹ := by
    intro x hx
    rw [← Nat.cast_smul_eq_nsmul ℚ_[ℓ], norm_smul, Nat.cast_pow, norm_ell_pow]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (le_max_left _ _)
    calc ((ℓ : ℝ)⁻¹) ^ N * ‖x‖ ≤ ((ℓ : ℝ)⁻¹) ^ N * (M + 1) := by gcongr; linarith
      _ < (ℓ : ℝ)⁻¹ / (M + 1) * (M + 1) := by gcongr
      _ = (ℓ : ℝ)⁻¹ := div_mul_cancel₀ _ (by positivity)
  have hA := hsmall A₀ (le_max_left _ _)
  have hB := hsmall Z (le_max_right _ _)
  refine ⟨N, (ℓ ^ N : ℕ) • A₀, (ℓ ^ N : ℕ) • Z, ?_, hA, hB, fun g hg => (hZg g hg).smul_left _,
    hZu.smul_left _, (hZA.symm.smul_left _).smul_right _, by rw [hXsum, nsmul_add], ?_⟩
  · rw [← Nat.cast_smul_eq_nsmul K, map_smul]
    exact LieSubalgebra.smul_mem _ _ hA₀mem
  · rw [← exp_ladicLog hu, ← hXdef, ← exp_nsmul_of_norm_lt hX, hXsum, nsmul_add,
      exp_add_of_commute_of_mem_ball (𝕂 := ℚ_[ℓ]) ((hZA.symm.smul_left _).smul_right _)
        (mem_eball_expSeries hA) (mem_eball_expSeries hB)]
    rfl

end Matrix

end Stacks.LAdic
