module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The cokernel of a square polynomial matrix

Let `k` be a field and `T` a square matrix over `k[X]` with nonzero determinant. The cokernel
`k[X]^ι / T k[X]^ι` is a finite-dimensional `k`-vector space of dimension `deg det T`; this is the
analogue for `k[X]` of the formula `#(ℤ^n / T ℤ^n) = |det T|`.

As a consequence we prove a lattice-point count, the only input from the geometry of `𝐏¹` needed
to show that `𝐏¹` has no nontrivial connected finite étale covers: if `T T₂ = X^{2m}` and
`deg det T = m · #ι` (with `m ≥ 1`), then the vectors of polynomials of degree `≤ m` lying in the
image of `T` form a `k`-vector space of dimension at least `#ι`.

## Main results

* `Polynomial.finrank_quotient_range_mulVecLin`: `dim_k (k[X]^ι / T k[X]^ι) = deg det T`.
* `Polynomial.card_le_finrank_pi_degreeLT_inf_range`: the lattice-point count.
-/

@[expose] public noncomputable section

open Module Submodule Polynomial

namespace Polynomial

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The cokernel of a polynomial matrix.** For a square matrix `T` over `k[X]` with nonzero
determinant, `dim_k (k[X]^ι / T k[X]^ι) = deg det T`. -/
theorem finrank_quotient_range_mulVecLin (T : Matrix ι ι k[X]) (hT : T.det ≠ 0) :
    finrank k ((ι → k[X]) ⧸ LinearMap.range T.mulVecLin) = T.det.natDegree := by
  classical
  let N : Submodule k[X] (ι → k[X]) := LinearMap.range T.mulVecLin
  have hinj : Function.Injective T.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    exact hT (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hv⟩)
  let e : (ι → k[X]) ≃ₗ[k[X]] N := LinearEquiv.ofInjective _ hinj
  let b := Pi.basisFun k[X] ι
  have h : finrank k[X] N = finrank k[X] (ι → k[X]) := e.finrank_eq.symm
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  let e' : (ι → k[X]) ≃ₗ[k[X]] N := b'.equiv ab (Equiv.refl _)
  let f : (ι → k[X]) →ₗ[k[X]] (ι → k[X]) := N.subtype.comp (e' : (ι → k[X]) →ₗ[k[X]] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change N.subtype (b'.equiv ab (Equiv.refl _) (b' i)) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact smithNormalFormBotBasis_def b h i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have : LinearMap.toMatrix b' b' f = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one]
      by_cases hij : i = j
      · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
      · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
    rw [this, Matrix.det_diagonal]
  have hdetT : LinearMap.det (N.subtype ∘ₗ (e : (ι → k[X]) →ₗ[k[X]] N)) = T.det := by
    rw [show N.subtype ∘ₗ (e : (ι → k[X]) →ₗ[k[X]] N) = T.mulVecLin from
      LinearMap.ext fun _ ↦ rfl, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  have hassoc : Associated T.det (∏ i, a i) := by
    rw [← hdetT, ← hdetf]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have ha0 : ∀ i, a i ≠ 0 := smithNormalFormCoeffs_ne_zero b h
  have : ∀ i, Module.Finite k (k[X] ⧸ Ideal.span {a i}) := fun i ↦
    (AdjoinRoot.powerBasis (ha0 i)).finite
  rw [((quotientEquivPiSpan N b h).restrictScalars k).finrank_eq, Module.finrank_pi_fintype]
  simp_rw [finrank_quotient_span_eq_natDegree]
  rw [← natDegree_prod _ _ (fun i _ ↦ ha0 i)]
  exact (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)).symm

omit [DecidableEq ι] in
/-- The `k`-subspace of vectors of polynomials of degree `≤ m` is `(m + 1) · #ι`-dimensional. -/
theorem finrank_pi_degreeLT (n : ℕ) :
    finrank k ↥(Submodule.pi Set.univ (fun _ : ι ↦ degreeLT k n)) = Fintype.card ι * n := by
  let e : ↥(Submodule.pi Set.univ (fun _ : ι ↦ degreeLT k n)) ≃ₗ[k] (ι → Fin n → k) :=
    { toFun := fun v i ↦ degreeLTEquiv k n ⟨v.1 i, v.2 i (Set.mem_univ i)⟩
      invFun := fun w ↦ ⟨fun i ↦ ((degreeLTEquiv k n).symm (w i)).1,
        fun i _ ↦ ((degreeLTEquiv k n).symm (w i)).2⟩
      map_add' := fun v w ↦ by
        funext i
        rw [Pi.add_apply, ← map_add]
        rfl
      map_smul' := fun a v ↦ by
        funext i
        rw [Pi.smul_apply, RingHom.id_apply, ← map_smul]
        rfl
      left_inv := fun v ↦ by
        apply Subtype.ext
        funext i
        simp
      right_inv := fun w ↦ by
        funext i
        simp }
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  simp

/-- **The lattice-point count.** Let `T T₂` be square matrices over `k[X]` with
`T T₂ = X^{2m}` and `deg det T = m · #ι`, where `m ≥ 1`. Then the vectors of polynomials of
degree `≤ m` which lie in `T k[X]^ι` form a `k`-vector space of dimension at least `#ι`.

The proof counts in `Q = k[X]^ι / X^{2m} k[X]^ι`, of dimension `2m · #ι`: the vectors of degree
`≤ m` inject into `Q`, spanning `(m + 1) · #ι` dimensions, and `T k[X]^ι` contains `X^{2m} k[X]^ι`
with image of dimension `2m · #ι - m · #ι` by `Polynomial.finrank_quotient_range_mulVecLin`. -/
theorem card_le_finrank_pi_degreeLT_inf_range (T T₂ : Matrix ι ι k[X]) {m : ℕ} (hm : 1 ≤ m)
    (hTT : T * T₂ = (X ^ (2 * m) : k[X]) • (1 : Matrix ι ι k[X]))
    (hdet : T.det.natDegree = m * Fintype.card ι) :
    Fintype.card ι ≤ finrank k ↥(Submodule.pi Set.univ (fun _ : ι ↦ degreeLT k (m + 1)) ⊓
      (LinearMap.range T.mulVecLin).restrictScalars k) := by
  classical
  set c := Fintype.card ι with hc_def
  let D : Matrix ι ι k[X] := (X ^ (2 * m) : k[X]) • (1 : Matrix ι ι k[X])
  have hdetD : D.det = X ^ (2 * m * c) := by
    simp only [D, Matrix.det_smul, Matrix.det_one, mul_one, ← pow_mul, hc_def]
  have hD0 : D.det ≠ 0 := by rw [hdetD]; exact pow_ne_zero _ X_ne_zero
  have hT0 : T.det ≠ 0 := fun h ↦ hD0 <| by
    rw [show D = T * T₂ from hTT.symm, Matrix.det_mul, h, zero_mul]
  let U : Submodule k (ι → k[X]) := (LinearMap.range D.mulVecLin).restrictScalars k
  let V : Submodule k (ι → k[X]) := (LinearMap.range T.mulVecLin).restrictScalars k
  let P : Submodule k (ι → k[X]) := Submodule.pi Set.univ (fun _ : ι ↦ degreeLT k (m + 1))
  change c ≤ finrank k ↥(P ⊓ V)
  have hUV : U ≤ V := by
    rintro _ ⟨w, rfl⟩
    refine ⟨T₂.mulVec w, ?_⟩
    change T.mulVec (T₂.mulVec w) = D.mulVec w
    rw [Matrix.mulVec_mulVec, hTT]
  have hQU : finrank k ((ι → k[X]) ⧸ U) = 2 * m * c := by
    rw [(Submodule.Quotient.restrictScalarsEquiv k _).finrank_eq,
      finrank_quotient_range_mulVecLin D hD0, hdetD, natDegree_X_pow]
  have hQV : finrank k ((ι → k[X]) ⧸ V) = m * c := by
    rw [(Submodule.Quotient.restrictScalarsEquiv k _).finrank_eq,
      finrank_quotient_range_mulVecLin T hT0, hdet]
  rcases Nat.eq_zero_or_pos c with hc | hc
  · omega
  have : FiniteDimensional k ((ι → k[X]) ⧸ U) :=
    Module.finite_of_finrank_pos (by rw [hQU]; positivity)
  have hP : finrank k P = c * (m + 1) := finrank_pi_degreeLT (m + 1)
  have : FiniteDimensional k P := Module.finite_of_finrank_pos (by rw [hP]; positivity)
  have hVU : finrank k (V.map U.mkQ) = m * c := by
    have h1 := Submodule.finrank_quotient_add_finrank (V.map U.mkQ)
    rw [(Submodule.quotientQuotientEquivQuotient U V hUV).finrank_eq, hQV, hQU] at h1
    have : 2 * m * c = m * c + m * c := by ring
    omega
  have hPinj : Function.Injective (U.mkQ.domRestrict P) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨v, hv⟩ h0
    obtain ⟨w, rfl⟩ : v ∈ U := by simpa [Submodule.Quotient.mk_eq_zero] using h0
    apply Subtype.ext
    funext i
    refine eq_zero_of_dvd_of_degree_lt (p := X ^ (2 * m)) ⟨w i, ?_⟩ ?_
    · simp [D]
    · rw [degree_X_pow]
      exact (mem_degreeLT.mp (hv i trivial)).trans_le
        (by exact_mod_cast (show m + 1 ≤ 2 * m by omega))
  have hPmap : finrank k (P.map U.mkQ) = c * (m + 1) := by
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hPinj, hP]
  have hinf := Submodule.finrank_sup_add_finrank_inf_eq (P.map U.mkQ) (V.map U.mkQ)
  have hsup := Submodule.finrank_le (P.map U.mkQ ⊔ V.map U.mkQ)
  rw [hPmap, hVU] at hinf
  rw [hQU] at hsup
  have hle : P.map U.mkQ ⊓ V.map U.mkQ ≤ (P ⊓ V).map U.mkQ := by
    rw [Submodule.map_inf_eq_map_inf_comap, Submodule.comap_map_mkQ, sup_eq_right.mpr hUV]
  have h3 := Submodule.finrank_mono hle
  have h4 := Submodule.finrank_map_le U.mkQ (P ⊓ V)
  have : c * (m + 1) + m * c = 2 * m * c + c := by ring
  omega

end Polynomial

end
