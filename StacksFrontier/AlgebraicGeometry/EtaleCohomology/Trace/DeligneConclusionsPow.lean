module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPoincarePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyBlockRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyTracePowers
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTracePow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConjectureConclusions
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# Purity and the conclusions of Deligne's conjecture under powers of the Frobenius

Two pieces of linear algebra behind the reduction, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), of purity to a scheme with a rational
point, by base change to a finite extension `k'` of degree `e` of the finite field `k`:

* the Frobenius of `X ×_k k'` acts on cohomology as the `e`-th power of the Frobenius of `X`, and
  its eigenvalues are weighed against `q ^ e`: purity of weight `w` for `f ^ e` against `q ^ e` is
  purity of weight `w` for `f` against `q`
  (`Stacks.EtaleCohomology.IsCharpolyPureOfWeight.of_pow`);
* the geometric Frobenius element of `X ×_k k'` at a closed point `y'` over `y` maps to a conjugate
  of the `[κ(y') : κ(y)]`-th power of that of `X` at `y`, so a representation `ρ` of `π₁(X)`
  satisfying the conclusions of Deligne's conjecture restricts to one of `π₁(X ×_k k')` satisfying
  them (`Stacks.EtaleCohomology.HasDeligneConclusions.comp_of_conj_pow`): the characteristic
  polynomial of `A ^ e` is a function of that of `A`
  (`Stacks.EtaleCohomology.charpoly_pow_eq_map`).
-/

@[expose] public noncomputable section

open Polynomial IsDedekindDomain

namespace Stacks.EtaleCohomology

/-! ### Purity from a power -/

section Pure

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Purity from a power.**  If the characteristic roots of `f ^ m` (`m ≠ 0`) are `q ^ m`-Weil
numbers of weight `w`, then those of `f` are `q`-Weil numbers of weight `w`. -/
public theorem IsCharpolyPureOfWeight.of_pow {q : ℕ} {ι : K →+* ℂ} {w : ℤ}
    {f : Module.End K V} {m : ℕ} (hm : m ≠ 0)
    (h : IsCharpolyPureOfWeight (q ^ m) ι w (f ^ m)) : IsCharpolyPureOfWeight q ι w f := by
  intro z hz
  have hzm := h (z ^ m) (isRoot_charpoly_map_pow ι hz m)
  refine ⟨hzm.isAlgebraic.of_pow (Nat.pos_of_ne_zero hm), ?_⟩
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hrhs : ((q ^ m : ℕ) : ℝ) ^ ((w : ℝ) / 2) = ((q : ℝ) ^ ((w : ℝ) / 2)) ^ m := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0,
      ← Real.rpow_mul hq0, mul_comm]
  have hn := hzm.norm_eq
  rw [norm_pow, hrhs] at hn
  exact (pow_left_inj₀ (norm_nonneg z) (Real.rpow_nonneg hq0 _) hm).1 hn

end Pure

/-! ### The characteristic polynomial of a power -/

section CharpolyPow

/-- A matrix over a field with a prescribed monic characteristic polynomial `Q`: multiplication by
the root of `Q` on `K[X]/(Q)`, in the power basis. -/
public def charpolyRealization {E : Type*} [Field E] (Q : E[X]) (hQ : Q.Monic) :
    Matrix (Fin Q.natDegree) (Fin Q.natDegree) E :=
  Algebra.leftMulMatrix (AdjoinRoot.powerBasis hQ.ne_zero).basis
    (AdjoinRoot.powerBasis hQ.ne_zero).gen

/-- The matrix `Stacks.EtaleCohomology.charpolyRealization` has characteristic polynomial `Q`. -/
public theorem charpoly_charpolyRealization {E : Type*} [Field E] (Q : E[X]) (hQ : Q.Monic) :
    (charpolyRealization Q hQ).charpoly = Q := by
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis hQ.ne_zero)
  rwa [AdjoinRoot.minpoly_powerBasis_gen_of_monic hQ] at h

/-- Two square matrices with the same characteristic polynomial have powers with the same
traces. -/
public theorem trace_pow_eq_of_matrix_charpoly_eq {L : Type*} [Field L] {n m : Type*} [Fintype n]
    [DecidableEq n] [Fintype m] [DecidableEq m] (A : Matrix n n L) (B : Matrix m m L)
    (h : A.charpoly = B.charpoly) (k : ℕ) : (A ^ k).trace = (B ^ k).trace := by
  have h' := trace_pow_eq_of_charpoly_eq (Matrix.toLin' A) B
    ((Matrix.charpoly_toLin' A).trans h) k
  rwa [← Matrix.toLin'_pow, Matrix.trace_toLin'_eq] at h'

/-- **The characteristic polynomial of a power is a function of the characteristic polynomial**:
over a field `L` of characteristic zero, if `A` has characteristic polynomial `Q.map φ` for a monic
`Q` over a field `E` and `φ : E →+* L`, then `A ^ e` has characteristic polynomial the image of
that of `C ^ e`, for the realization `C` of `Q` over `E`. -/
public theorem charpoly_pow_eq_map {E L : Type*} [Field E] [Field L] [CharZero L] (φ : E →+* L)
    (Q : E[X]) (hQ : Q.Monic) {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n L)
    (hA : A.charpoly = Q.map φ) (e : ℕ) :
    (A ^ e).charpoly = ((charpolyRealization Q hQ ^ e).charpoly).map φ := by
  set C := charpolyRealization Q hQ
  have hC : (C.map φ).charpoly = A.charpoly := by
    rw [Matrix.charpoly_map, charpoly_charpolyRealization, hA]
  have hcard : Fintype.card n = Fintype.card (Fin Q.natDegree) := by
    rw [Fintype.card_fin, ← Matrix.charpoly_natDegree_eq_dim A, hA, natDegree_map]
  rw [← Matrix.charpoly_map, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply]
  refine matrix_charpoly_eq_of_trace_pow_eq _ _ hcard fun k _ => ?_
  rw [← pow_mul, ← pow_mul]
  exact trace_pow_eq_of_matrix_charpoly_eq A (C.map φ) hC.symm (e * k)

end CharpolyPow

/-! ### The conclusions of Deligne's conjecture under restriction -/

section Deligne

variable {G : Type*} [Group G] [TopologicalSpace G] {G' : Type*} [Group G'] [TopologicalSpace G']
  {P P' : Type*} {K : Type*} [Field K] [CharZero K]

/-- Conjugation does not change the characteristic polynomial of the image of a group element. -/
public theorem charpoly_conj_val {L : Type*} [Field L] {r : ℕ} (c a : GL (Fin r) L) :
    ((c * a * c⁻¹ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L).charpoly =
      (a : Matrix (Fin r) (Fin r) L).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

omit [TopologicalSpace G] [TopologicalSpace G'] in
/-- Under `φ (Fr' y') = c * Fr (π y') ^ e y' * c⁻¹`, the characteristic polynomial of
`σ (φ (Fr' y'))` is that of `σ (Fr (π y')) ^ e y'`. -/
public theorem charpoly_comp_of_conj_pow {Fr : P → G} {Fr' : P' → G'} (φ : G' →* G) (π : P' → P)
    (e : P' → ℕ) (hFr : ∀ y', ∃ c : G, φ (Fr' y') = c * Fr (π y') ^ e y' * c⁻¹) {L : Type*}
    [Field L] {r : ℕ} (σ : G →* GL (Fin r) L) (y' : P') :
    ((σ.comp φ (Fr' y') : GL (Fin r) L) : Matrix (Fin r) (Fin r) L).charpoly =
      (((σ (Fr (π y')) : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) ^ e y').charpoly := by
  obtain ⟨c, hc⟩ := hFr y'
  rw [MonoidHom.comp_apply, hc, map_mul, map_mul, map_inv, charpoly_conj_val, map_pow,
    Units.val_pow_eq_pow_val]

/-- Under `φ (Fr' y') = c * Fr (π y') ^ e y' * c⁻¹`, if `σ (Fr (π y'))` has characteristic
polynomial `Q.map ψ`, then `σ (φ (Fr' y'))` has that of the realization of `Q` to the power
`e y'`, mapped by `ψ`. -/
private theorem charpoly_comp_eq_map_of_conj_pow {H H' Y Y' : Type*} [Group H] [Group H']
    {Fr : Y → H} {Fr' : Y' → H'} (φ : H' →* H) (π : Y' → Y) (e : Y' → ℕ)
    (hFr : ∀ y', ∃ c : H, φ (Fr' y') = c * Fr (π y') ^ e y' * c⁻¹)
    {E L : Type*} [Field E] [Field L] [CharZero L] (ψ : E →+* L) {r : ℕ}
    (σ : H →* GL (Fin r) L) (y' : Y') (Q : E[X]) (hQ : Q.Monic)
    (h : ((σ (Fr (π y')) : GL (Fin r) L) : Matrix (Fin r) (Fin r) L).charpoly = Q.map ψ) :
    ((σ.comp φ (Fr' y') : GL (Fin r) L) : Matrix (Fin r) (Fin r) L).charpoly =
      ((charpolyRealization Q hQ ^ e y').charpoly).map ψ :=
  (charpoly_comp_of_conj_pow φ π e hFr σ y').trans (charpoly_pow_eq_map ψ Q hQ _ h _)

omit [TopologicalSpace G'] in
/-- Under `φ (Fr' y') = c * Fr (π y') ^ e y' * c⁻¹` with `e y' ≠ 0`, the eigenvalues of
`ρ (φ (Fr' y'))` have absolute value `1` if those of the `ρ (Fr y)` do. -/
public theorem norm_eq_one_of_conj_pow {Fr : P → G} {Fr' : P' → G'} (φ : G' →* G) (π : P' → P)
    (e : P' → ℕ) (he : ∀ y', e y' ≠ 0)
    (hFr : ∀ y', ∃ c : G, φ (Fr' y') = c * Fr (π y') ^ e y' * c⁻¹) {p : ℕ} {ι : K →+* ℂ}
    {r : ℕ} {ρ : G →* GL (Fin r) K} (h : HasDeligneConclusions Fr p ι ρ) (y' : P') (z : ℂ)
    (hz : (((ρ.comp φ (Fr' y') : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).charpoly.map
      ι).IsRoot z) : ‖z‖ = 1 := by
  rw [charpoly_comp_of_conj_pow φ π e hFr ρ y', ← Matrix.charpoly_toLin', Matrix.toLin'_pow] at hz
  obtain ⟨w, hw, rfl⟩ := exists_isRoot_charpoly_map_pow_eq ι _ (he y') hz
  rw [Matrix.charpoly_toLin'] at hw
  rw [norm_pow, h.norm_eq_one (π y') w hw, one_pow]

/-- **The conclusions of Deligne's conjecture restrict along a map carrying Frobenius elements to
conjugates of powers of Frobenius elements.**  Let `φ : G' →* G` be continuous, and suppose that
for every `y'` the element `φ (Fr' y')` is conjugate to `Fr (π y') ^ e y'` with `e y' ≠ 0` (for
`φ : π₁(X ×_k k') → π₁(X)`, the geometric Frobenius at `y'` and the geometric Frobenius at its
image, to the power of the residue degree).  If `ρ` satisfies the conclusions of Deligne's
conjecture for `Fr`, then `ρ ∘ φ` satisfies them for `Fr'`, with the same number field. -/
public theorem HasDeligneConclusions.comp_of_conj_pow {Fr : P → G} {Fr' : P' → G'} (φ : G' →* G)
    (hφ : Continuous φ) (π : P' → P) (e : P' → ℕ) (he : ∀ y', e y' ≠ 0)
    (hFr : ∀ y', ∃ c : G, φ (Fr' y') = c * Fr (π y') ^ e y' * c⁻¹) {p : ℕ} {ι : K →+* ℂ}
    {r : ℕ} {ρ : G →* GL (Fin r) K} (h : HasDeligneConclusions Fr p ι ρ) :
    HasDeligneConclusions Fr' p ι (ρ.comp φ) := by
  classical
  obtain ⟨E, hE, Q, hQ, hcomp⟩ := h.exists_companions
  have hQm : ∀ y, (Q y).Monic := fun y =>
    Polynomial.monic_of_injective (algebraMap E K).injective
      ((hQ y).symm ▸ Matrix.charpoly_monic _)
  have hK := fun y' => charpoly_comp_eq_map_of_conj_pow φ π e hFr _ ρ y' _ (hQm (π y'))
    (hQ (π y')).symm
  refine ⟨⟨E, inferInstance, fun y' n => ?_⟩, fun y' z hz => ?_, ⟨E, hE, fun y' =>
    (charpolyRealization (Q (π y')) (hQm (π y')) ^ e y').charpoly, fun y' => (hK y').symm,
    fun v hv => ?_⟩⟩
  · rw [hK y', coeff_map]
    exact Subtype.mem _
  · exact norm_eq_one_of_conj_pow φ π e he hFr h y' z hz
  · obtain ⟨ρv, hρv, hρvQ⟩ := hcomp v hv
    have : CharZero (v.adicCompletion E) :=
      charZero_of_injective_algebraMap (algebraMap E (v.adicCompletion E)).injective
    exact ⟨ρv.comp φ, hρv.comp hφ, fun y' =>
      charpoly_comp_eq_map_of_conj_pow φ π e hFr _ ρv y' _ _ (hρvQ (π y'))⟩

end Deligne

end Stacks.EtaleCohomology

end
