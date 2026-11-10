module

public import StacksFrontier.Algebra.Polynomial.TorsionCharpoly
public import StacksFrontier.AlgebraicGeometry.Picard.WeilPairing
public import Mathlib.LinearAlgebra.Trace

/-!
# The characteristic polynomial of an endomorphism on `ℓ^n`-torsion, from kernel counts

Let `P` be an abelian group with `P[ℓ^N] ≅ (ℤ/ℓ^N)^r` for every `N` (in the application, `Pic⁰`
of a curve, or the points of an abelian variety, with `ℓ` invertible), `u` an endomorphism of
`P`, `p ≠ ℓ` primes and `χ ∈ ℤ[X]` monic of degree `r`. Suppose that for every `R ∈ ℤ[X]` with
`p ∤ R(0)` and `Res(χ, R) ≠ 0` the kernel of `R(u)` on `P` has `|Res(χ, R)|` elements (for an
endomorphism `F` of an abelian variety with `dF = 0`, `R(F)` is then étale and
`#ker R(F) = deg R(F) = Res(χ_F, R)`). Then the characteristic polynomial of `u` on `P[ℓ^n]` is
`χ mod ℓ^n` (`Stacks.Picard.charpoly_levelMatrix_eq`), so its trace is `-χ_{r-1} mod ℓ^n`
([Mumford, *Abelian varieties*, §19, Theorem 4]).

The proof: the characteristic polynomials `c_N` of `u` on `P[ℓ^N]` are compatible
(`Stacks.Picard.charpoly_levelMatrix_map`, by multiplication by `ℓ^{N-n}`), with a limit
`F ∈ ℤ_ℓ[X]`. For `R` as above and `N > v_ℓ(Res(χ, R))`, the kernel of `R(u)` on `P[ℓ^N]` has
`ℓ^{v_ℓ(Res(χ, R))}` elements, so an integer lift `B` of the matrix of `u` has
`v_ℓ(det R(B)) = v_ℓ(Res(χ, R))` (`Stacks.TorsionCount.natCard_ker_mulVecMod_of_lt`), and
`det R(B) = Res(χ_B, R) ≡ Res(F, R) mod ℓ^N`. Hence `‖Res(F, R)‖ = ‖Res(χ, R)‖`, and
`F = χ` by Mumford's lemma (`Stacks.Polynomial.eq_of_norm_resultant_intPoly_eq`).

## Main definitions

* `Stacks.Picard.levelMap`, `Stacks.Picard.levelMatrix` — `u` on `P[ℓ^n]`, and its matrix in the
  basis given by `P[ℓ^n] ≅ (ℤ/ℓ^n)^r`.

## Main results

* `Stacks.Picard.charpoly_levelMatrix_map` — compatibility of the characteristic polynomials.
* `Stacks.Picard.charpoly_levelMatrix_eq` — the characteristic polynomial is `χ mod ℓ^n`.
* `Stacks.Picard.trace_levelMap` — the trace of `u` on `P[ℓ^n]` is that of its matrix.
-/

@[expose] public noncomputable section

open Polynomial Stacks.TorsionCount

namespace Stacks.Picard

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {P : Type*} [AddCommGroup P] (u : P →+ P) {r : ℕ}
  [∀ n : ℕ, Module (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n))]

/-- An additive endomorphism, as an element of the ring `AddMonoid.End P`. -/
abbrev asEnd (f : P →+ P) : AddMonoid.End P := f

/-- An additive equivalence of `ℤ/n`-modules is `ℤ/n`-linear. -/
def zmodLinearEquiv (n : ℕ) {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    [Module (ZMod n) M] [Module (ZMod n) M'] (e : M ≃+ M') : M ≃ₗ[ZMod n] M' :=
  e.toLinearEquiv fun c x => (e.toAddMonoidHom.toZModLinearMap n).map_smul c x

/-- The basis of `P[ℓ^n]` transported from the standard basis of `(ℤ/ℓ^n)^r`. -/
def levelBasis (n : ℕ) (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n) ≃+ (Fin r → ZMod (ℓ ^ n))) :
    Module.Basis (Fin r) (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n)) :=
  (Pi.basisFun (ZMod (ℓ ^ n)) (Fin r)).map (zmodLinearEquiv (ℓ ^ n) E.symm)

/-- `u` on `P[ℓ^n]` as a `ℤ/ℓ^n`-linear map. -/
def levelMap (n : ℕ) : Module.End (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n)) :=
  (torsionByRestrict u ((ℓ : ℤ) ^ n)).toZModLinearMap (ℓ ^ n)

/-- The matrix of `u` on `P[ℓ^n] ≅ (ℤ/ℓ^n)^r`. -/
def levelMatrix (n : ℕ) (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n) ≃+ (Fin r → ZMod (ℓ ^ n))) :
    Matrix (Fin r) (Fin r) (ZMod (ℓ ^ n)) :=
  LinearMap.toMatrix (levelBasis n E) (levelBasis n E) (levelMap u n)

omit hℓ in
/-- The coordinates of `x ∈ P[ℓ^n]` in `levelBasis n E` are `E x`. -/
theorem levelBasis_repr (n : ℕ)
    (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n) ≃+ (Fin r → ZMod (ℓ ^ n)))
    (x : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n)) : ⇑((levelBasis n E).repr x) = E x := by
  ext i
  simp only [levelBasis, zmodLinearEquiv, Module.Basis.map_repr, LinearEquiv.trans_apply,
    Pi.basisFun_repr]
  rfl

omit hℓ in
/-- Under `E : P[ℓ^n] ≅ (ℤ/ℓ^n)^r`, the matrix of `u` acts on `(ℤ/ℓ^n)^r` as `u` does on
`P[ℓ^n]`. -/
theorem levelMatrix_mulVec (n : ℕ)
    (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n) ≃+ (Fin r → ZMod (ℓ ^ n)))
    (z : Fin r → ZMod (ℓ ^ n)) :
    (levelMatrix u n E).mulVec z = E (torsionByRestrict u _ (E.symm z)) := by
  have h := LinearMap.toMatrix_mulVec_repr (levelBasis n E) (levelBasis n E) (levelMap u n)
    (E.symm z)
  rwa [levelBasis_repr, levelBasis_repr, AddEquiv.apply_symm_apply] at h

omit hℓ in
/-- The trace of `u` on `P[ℓ^n]` is the trace of its matrix. -/
theorem trace_levelMap (n : ℕ)
    (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n) ≃+ (Fin r → ZMod (ℓ ^ n))) :
    LinearMap.trace (ZMod (ℓ ^ n)) _ (levelMap u n) = (levelMatrix u n E).trace :=
  LinearMap.trace_eq_matrix_trace _ (levelBasis n E) _

omit hℓ in
/-- The point of `P` corresponding to `(levelMatrix u N E).mulVec z` is `u` of the point
corresponding to `z`. -/
theorem coe_levelMatrix_mulVec (N : ℕ)
    (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N)))
    (z : Fin r → ZMod (ℓ ^ N)) :
    (E.symm ((levelMatrix u N E).mulVec z) : P) = u (E.symm z : P) := by
  rw [levelMatrix_mulVec, AddEquiv.symm_apply_apply, torsionByRestrict_apply]

/-- `ℓ^{N-n}` times a lift, `(ℤ/ℓ^n)^r → P[ℓ^n] ⊆ P[ℓ^N] ≅ (ℤ/ℓ^N)^r`. -/
def levelEmb (N : ℕ) (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N)))
    {n : ℕ} (h : n ≤ N) : (Fin r → ZMod (ℓ ^ n)) →+ Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n) where
  toFun y := ⟨(E.symm (fun i => scaleEmb (ℓ := ℓ) h (y i)) : P), by
    rw [Submodule.mem_torsionBy_iff, ← Submodule.coe_smul, ← map_zsmul]
    have : ((ℓ : ℤ) ^ n) • (fun i => scaleEmb (ℓ := ℓ) h (y i)) = 0 := by
      funext i
      rw [Pi.smul_apply, Pi.zero_apply, ← map_zsmul]
      have : ((ℓ : ℤ) ^ n) • y i = 0 := by
        rw [zsmul_eq_mul]
        push_cast
        rw [show ((ℓ : ZMod (ℓ ^ n)) ^ n) = ((ℓ ^ n : ℕ) : ZMod (ℓ ^ n)) by push_cast; rfl,
          ZMod.natCast_self, zero_mul]
      rw [this, map_zero]
    rw [this, map_zero, Submodule.coe_zero]⟩
  map_zero' := by
    ext
    simp only [Pi.zero_apply, map_zero]
    rw [show (fun _ : Fin r => (0 : ZMod (ℓ ^ N))) = 0 from rfl, map_zero]
    rfl
  map_add' y y' := by
    ext
    simp only [Pi.add_apply, map_add]
    rw [show (fun i => scaleEmb (ℓ := ℓ) h (y i) + scaleEmb h (y' i)) =
      (fun i => scaleEmb (ℓ := ℓ) h (y i)) + (fun i => scaleEmb h (y' i)) from rfl, map_add]
    rfl

omit hℓ [∀ n : ℕ, Module (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n))] in
/-- The point of `P` underlying `levelEmb N E h y`. -/
theorem coe_levelEmb (N : ℕ) (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N)))
    {n : ℕ} (h : n ≤ N) (y : Fin r → ZMod (ℓ ^ n)) :
    (levelEmb N E h y : P) = (E.symm (fun i => scaleEmb (ℓ := ℓ) h (y i)) : P) := rfl

omit [∀ n : ℕ, Module (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n))] in
/-- `levelEmb N E h` is a bijection `(ℤ/ℓ^n)^r → P[ℓ^n]`. -/
theorem levelEmb_bijective (N : ℕ)
    (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N))) {n : ℕ} (h : n ≤ N) :
    Function.Bijective (levelEmb N E h) := by
  refine ⟨fun y y' hyy => ?_, fun x => ?_⟩
  · have h1 := congrArg Subtype.val hyy
    simp only [coe_levelEmb] at h1
    exact funext fun i => scaleEmb_injective h (congrFun (E.symm.injective (Subtype.ext h1)) i)
  · have hxN : (x : P) ∈ Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) := by
      rw [Submodule.mem_torsionBy_iff, ← Nat.sub_add_cancel h, pow_add, mul_smul,
        (Submodule.mem_torsionBy_iff _ _).1 x.2, smul_zero]
    set z := E ⟨x, hxN⟩
    have hz : ∀ i, (ℓ ^ n) • z i = 0 := fun i => by
      have : ((ℓ : ℤ) ^ n) • z = 0 := by
        rw [← map_zsmul,
          show ((ℓ : ℤ) ^ n) • (⟨x, hxN⟩ : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N)) = 0 from
            Subtype.ext ((Submodule.mem_torsionBy_iff _ _).1 x.2), map_zero]
      have := congrFun this i
      rw [Pi.smul_apply, Pi.zero_apply] at this
      rw [← this, ← natCast_zsmul]
      push_cast
      rfl
    choose a ha using fun i => mem_range_scaleEmb h (z i) (hz i)
    refine ⟨a, Subtype.ext ?_⟩
    rw [coe_levelEmb, show (fun i => scaleEmb (ℓ := ℓ) h (a i)) = z from funext ha,
      AddEquiv.symm_apply_apply]

/-- **The characteristic polynomial of `u` on `P[ℓ^n]`, `n ≤ N`, is the reduction of that of its
matrix on `P[ℓ^N] ≅ (ℤ/ℓ^N)^r`.** Multiplication by `ℓ^{N-n}` identifies `(ℤ/ℓ^n)^r` with the
`ℓ^n`-torsion of `(ℤ/ℓ^N)^r`, compatibly with the matrix. -/
theorem levelMatrix_map_castHom (N : ℕ)
    (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N))) {n : ℕ} (h : n ≤ N) :
    ∃ b : Module.Basis (Fin r) (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n)),
      LinearMap.toMatrix b b (levelMap u n) =
        (levelMatrix u N E).map (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ n))) := by
  set Φ := LinearEquiv.ofBijective ((levelEmb N E h).toZModLinearMap (ℓ ^ n))
    (levelEmb_bijective N E h)
  have hΦ : ∀ y, (Φ y : P) = (E.symm (fun i => scaleEmb (ℓ := ℓ) h (y i)) : P) := fun y => rfl
  set b := (Pi.basisFun (ZMod (ℓ ^ n)) (Fin r)).map Φ
  refine ⟨b, ?_⟩
  set A' := (levelMatrix u N E).map (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ n)))
  have hrepr : ∀ x, ⇑(b.repr x) = Φ.symm x := fun x => by
    ext i
    simp [b]
  have key : ∀ y, levelMap u n (Φ y) = Φ (A'.mulVec y) := fun y => by
    apply Subtype.ext
    change u (Φ y : P) = _
    rw [hΦ, hΦ, ← coe_levelMatrix_mulVec]
    congr 3
    funext i
    simp only [A', Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, scaleEmb_mul]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have := LinearMap.toMatrix_mulVec_repr b b (levelMap u n) (Φ y)
  rwa [hrepr, hrepr, LinearEquiv.symm_apply_apply, key, LinearEquiv.symm_apply_apply] at this

omit hℓ in
/-- `u^k` on `P[ℓ^N]` is the restriction of `u^k` on `P`. -/
theorem coe_levelMap_pow_apply (N k : ℕ) (x : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N)) :
    (((levelMap u N) ^ k) x : P) = ((asEnd u) ^ k) (x : P) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ]
    rfl

omit hℓ in
/-- `R(u)` on `P[ℓ^N]` is the restriction of `R(u)` on `P`. -/
theorem coe_aeval_levelMap_apply (N : ℕ) (R : ℤ[X]) (x : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N)) :
    ((aeval (levelMap u N) R) x : P) = (aeval (asEnd u) R) (x : P) := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
    rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, hR, hS]
    rfl
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply]
    change _ = (algebraMap ℤ (AddMonoid.End P) a) (((asEnd u) ^ k) (x : P))
    rw [← coe_levelMap_pow_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, Submodule.coe_smul_of_tower]
    rfl

omit hℓ in
/-- The matrix of `R(u)` on `P[ℓ^N]` is `R` of the matrix of `u`. -/
theorem aeval_levelMatrix_mulVec (N : ℕ)
    (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N))) (R : ℤ[X])
    (z : Fin r → ZMod (ℓ ^ N)) :
    (E.symm ((aeval (levelMatrix u N E) R).mulVec z) : P) =
      (aeval (asEnd u) R) (E.symm z : P) := by
  have hR : aeval (levelMatrix u N E) R = LinearMap.toMatrix (levelBasis N E) (levelBasis N E)
      (aeval (levelMap u N) R) := by
    change aeval ((LinearMap.toMatrixAlgEquiv (levelBasis N E)) (levelMap u N)) R =
      (LinearMap.toMatrixAlgEquiv (levelBasis N E)) (aeval (levelMap u N) R)
    exact aeval_algHom_apply
      ((LinearMap.toMatrixAlgEquiv (levelBasis N E)).toAlgHom.restrictScalars ℤ) (levelMap u N) R
  have h := LinearMap.toMatrix_mulVec_repr (levelBasis N E) (levelBasis N E)
    (aeval (levelMap u N) R) (E.symm z)
  rw [levelBasis_repr, levelBasis_repr, AddEquiv.apply_symm_apply, ← hR] at h
  rw [h, AddEquiv.symm_apply_apply, coe_aeval_levelMap_apply]

omit [∀ n : ℕ, Module (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n))] in
/-- Ultrametric: `‖x‖ = ‖y‖` if `‖x - y‖ < ‖y‖`, in `ℤ_ℓ`. -/
theorem padicInt_norm_eq_of_norm_sub_lt {x y : ℤ_[ℓ]} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  rw [← PadicInt.norm_coe, ← PadicInt.norm_coe] at h ⊢
  rw [PadicInt.coe_sub] at h
  have := Padic.add_eq_max_of_ne h.ne'
  rw [add_sub_cancel] at this
  rw [this, max_eq_left h.le]

omit [∀ n : ℕ, Module (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n))] in
/-- The norm of a nonzero integer in `ℤ_ℓ` is determined by its `ℓ`-adic valuation. -/
theorem padicInt_norm_intCast_eq {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a.natAbs.factorization ℓ = b.natAbs.factorization ℓ) :
    ‖(a : ℤ_[ℓ])‖ = ‖(b : ℤ_[ℓ])‖ := by
  have key : ∀ c : ℤ, c ≠ 0 → ‖(c : ℤ_[ℓ])‖ = ‖((ℓ : ℤ_[ℓ]) ^ c.natAbs.factorization ℓ)‖ := by
    intro c hc
    have hm : ¬ ℓ ∣ c.natAbs / ℓ ^ c.natAbs.factorization ℓ :=
      Nat.not_dvd_ordCompl hℓ.out (Int.natAbs_ne_zero.2 hc)
    have hnorm_abs : ‖(c : ℤ_[ℓ])‖ = ‖((c.natAbs : ℤ) : ℤ_[ℓ])‖ := by
      rcases Int.natAbs_eq c with h | h
      · rw [← h]
      · conv_lhs => rw [h]
        rw [Int.cast_neg, norm_neg]
    rw [hnorm_abs]
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self c.natAbs ℓ]
    rw [Nat.cast_mul, Int.cast_mul, norm_mul, Nat.cast_pow, Int.cast_pow]
    have h1 : ‖(((c.natAbs / ℓ ^ c.natAbs.factorization ℓ : ℕ) : ℤ) : ℤ_[ℓ])‖ = 1 :=
      le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt =>
        hm (by exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd _).1 hlt))
    rw [h1, mul_one]
    norm_cast
  rw [key a ha, key b hb, hab]

omit hℓ in
/-- The characteristic polynomial of the matrix of `u` on `P[ℓ^n]` does not depend on the chosen
identification `P[ℓ^n] ≅ (ℤ/ℓ^n)^r`. -/
theorem charpoly_toMatrix_eq (n : ℕ)
    (b b' : Module.Basis (Fin r) (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n))) :
    (LinearMap.toMatrix b b (levelMap u n)).charpoly =
      (LinearMap.toMatrix b' b' (levelMap u n)).charpoly := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  rw [LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

/-- Compatibility of the characteristic polynomials of `u` on `P[ℓ^N]` and on `P[ℓ^n]`. -/
theorem charpoly_levelMatrix_map (N : ℕ)
    (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N))) {n : ℕ} (h : n ≤ N)
    (E' : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n) ≃+ (Fin r → ZMod (ℓ ^ n))) :
    (levelMatrix u N E).charpoly.map (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ n))) =
      (levelMatrix u n E').charpoly := by
  obtain ⟨b, hb⟩ := levelMatrix_map_castHom u N E h
  rw [← Matrix.charpoly_map, ← hb, levelMatrix, charpoly_toMatrix_eq]

omit [∀ n : ℕ, Module (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n))] in
/-- The characteristic polynomial of an `r × r` matrix over `ℤ/ℓ^N` has degree at most `r`. -/
theorem natDegree_charpoly_le {N : ℕ} (A : Matrix (Fin r) (Fin r) (ZMod (ℓ ^ N))) :
    A.charpoly.natDegree ≤ r := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (ZMod (ℓ ^ 0)) := by
      rw [pow_zero]
      infer_instance
    rw [Subsingleton.elim A.charpoly 0, natDegree_zero]
    exact Nat.zero_le _
  · have : Fact (1 < ℓ ^ N) := ⟨Nat.one_lt_pow hN.ne' hℓ.out.one_lt⟩
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- For an integer lift `B` of the matrix of `R(u)` on `P[ℓ^N] ≅ (ℤ/ℓ^N)^r`, the kernel of `B` on
`(ℤ/ℓ^N)^r` is the `ℓ^N`-torsion of the kernel of `R(u)` on `P`. -/
private def kerMulVecModEquivTors (N : ℕ)
    (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N))) (R : ℤ[X])
    (B : Matrix (Fin r) (Fin r) ℤ)
    (hB : (Int.castRingHom (ZMod (ℓ ^ N))).mapMatrix B = aeval (levelMatrix u N E) R) :
    (mulVecMod (ℓ := ℓ) B N).ker ≃ tors (aeval (asEnd u) R).ker (ℓ ^ N) where
  toFun z := ⟨⟨E.symm z.1, by
    change (aeval (asEnd u) R) _ = 0
    rw [← aeval_levelMatrix_mulVec]
    have hz := z.2
    rw [AddMonoidHom.mem_ker] at hz
    change (B.map (Int.castRingHom (ZMod (ℓ ^ N)))).mulVec z.1 = 0 at hz
    rw [← RingHom.mapMatrix_apply, hB] at hz
    rw [hz, map_zero]
    rfl⟩, by
      rw [mem_tors]
      apply Subtype.ext
      have := (E.symm z.1).2
      rw [Submodule.mem_torsionBy_iff] at this
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, ← natCast_zsmul]
      push_cast
      exact this⟩
  invFun x := ⟨E ⟨x.1.1, by
      rw [Submodule.mem_torsionBy_iff]
      have h' := congrArg Subtype.val (mem_tors.1 x.2)
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, ← natCast_zsmul] at h'
      push_cast at h'
      exact h'⟩, by
      rw [AddMonoidHom.mem_ker]
      change (B.map (Int.castRingHom (ZMod (ℓ ^ N)))).mulVec _ = 0
      rw [← RingHom.mapMatrix_apply, hB]
      apply E.symm.injective
      apply Subtype.ext
      rw [map_zero, Submodule.coe_zero, aeval_levelMatrix_mulVec, AddEquiv.symm_apply_apply]
      exact x.1.2⟩
  left_inv z := Subtype.ext (E.apply_symm_apply z.1)
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [AddEquiv.symm_apply_apply]

/-- If the kernel of `R(u)` on `P` has `|d|` elements, `d ≠ 0`, then the resultant of the `ℓ`-adic
limit `F` of the characteristic polynomials of `u` on `P[ℓ^N]` with `R` has the norm of `d`. -/
private theorem norm_resultant_eq_of_natCard_ker
    (E' : ∀ N, Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N)))
    (F : ℤ_[ℓ][X]) (hF : ∀ N, F.map (PadicInt.toZModPow N) = (levelMatrix u N (E' N)).charpoly)
    (R : ℤ[X]) {d : ℤ} (hd : d ≠ 0) (hK : Nat.card (aeval (asEnd u) R).ker = d.natAbs) :
    ‖F.resultant (R.map (Int.castRingHom ℤ_[ℓ])) r R.natDegree‖ = ‖(d : ℤ_[ℓ])‖ := by
  classical
  set ιZ := Int.castRingHom ℤ_[ℓ]
  have : Finite (aeval (asEnd u) R).ker :=
    Nat.finite_of_card_ne_zero (hK.trans_ne (Int.natAbs_ne_zero.2 hd))
  set e := d.natAbs.factorization ℓ
  set N := e + 1
  set A := levelMatrix u N (E' N)
  set B : Matrix (Fin r) (Fin r) ℤ := A.map fun x => ((x.val : ℕ) : ℤ)
  have hB : B.map (Int.castRingHom (ZMod (ℓ ^ N))) = A := by
    ext i j
    simp [B]
  set BR := aeval B R
  have hBR : (Int.castRingHom (ZMod (ℓ ^ N))).mapMatrix BR = aeval A R := by
    rw [Stacks.Polynomial.mapMatrix_aeval, RingHom.mapMatrix_apply, hB,
      show Int.castRingHom (ZMod (ℓ ^ N)) = algebraMap ℤ (ZMod (ℓ ^ N)) from RingHom.ext_int _ _,
      aeval_map_algebraMap]
  have hcard : Nat.card (mulVecMod (ℓ := ℓ) BR N).ker = ℓ ^ e := by
    rw [Nat.card_congr (kerMulVecModEquivTors u N (E' N) R BR hBR),
      natCard_tors_pow_eq N (by rw [hK]; omega), hK]
  have hlt : Nat.card (mulVecMod (ℓ := ℓ) BR N).ker < ℓ ^ N :=
    hcard.trans_lt (Nat.pow_lt_pow_right hℓ.out.one_lt (Nat.lt_succ_self e))
  obtain ⟨hdet0, -, hdetcard⟩ := natCard_ker_mulVecMod_of_lt BR N hlt
  have hv : BR.det.natAbs.factorization ℓ = e :=
    Nat.pow_right_injective hℓ.out.two_le (hdetcard.symm.trans hcard)
  have hmod : PadicInt.toZModPow N (F.resultant (R.map ιZ) r R.natDegree) =
      PadicInt.toZModPow N (BR.det : ℤ_[ℓ]) := by
    rw [← resultant_map_map, hF N, Polynomial.map_map, map_intCast,
      Stacks.Polynomial.det_aeval_eq_resultant_charpoly_int,
      show (PadicInt.toZModPow N).comp ιZ = Int.castRingHom (ZMod (ℓ ^ N)) from
        RingHom.ext_int _ _]
    change A.charpoly.resultant _ r R.natDegree = _
    rw [← hB, Matrix.charpoly_map, resultant_map_map, eq_intCast]
  have hsub : ‖F.resultant (R.map ιZ) r R.natDegree - (BR.det : ℤ_[ℓ])‖ ≤
      (ℓ : ℝ) ^ (-(N : ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
      map_sub, hmod, sub_self]
  have hDnorm : (ℓ : ℝ) ^ (-(N : ℤ)) < ‖(BR.det : ℤ_[ℓ])‖ := by
    refine lt_of_not_ge fun hle => ?_
    have := PadicInt.norm_int_le_pow_iff_dvd.1 hle
    have hdvd : ℓ ^ (e + 1) ∣ BR.det.natAbs := by
      rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs]
      exact_mod_cast this
    exact Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.2 hdet0) hℓ.out (hv ▸ hdvd)
  rw [padicInt_norm_eq_of_norm_sub_lt (hsub.trans_lt hDnorm),
    padicInt_norm_intCast_eq hdet0 hd hv]

/-- **The `ℓ`-adic characteristic polynomial of an endomorphism with known kernel counts**
([Mumford, *Abelian varieties*, §19, Theorem 4]). Let `P` be an abelian group with
`P[ℓ^N] ≅ (ℤ/ℓ^N)^r` for all `N`, `u` an endomorphism of `P`, `p ≠ ℓ` primes and `χ ∈ ℤ[X]`
monic of degree `r` such that for every `R ∈ ℤ[X]` with `p ∤ R(0)` and `Res(χ, R) ≠ 0` the
kernel of `R(u)` on `P` has `|Res(χ, R)|` elements. Then the characteristic polynomial of `u`
on `P[ℓ^n]` is `χ mod ℓ^n`, for every `n`. -/
theorem charpoly_levelMatrix_eq (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hP : ∀ N, Nonempty (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N))))
    (χ : ℤ[X]) (hχ : χ.Monic) (hχr : χ.natDegree = r)
    (hker : ∀ R : ℤ[X], ¬ (p : ℤ) ∣ R.coeff 0 → χ.resultant R ≠ 0 →
      Nat.card (aeval (asEnd u) R).ker = (χ.resultant R).natAbs)
    (n : ℕ) (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n) ≃+ (Fin r → ZMod (ℓ ^ n))) :
    (levelMatrix u n E).charpoly = χ.map (Int.castRingHom (ZMod (ℓ ^ n))) := by
  classical
  have E' : ∀ N, Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N)) :=
    fun N => (hP N).some
  set c : ∀ N : ℕ, (ZMod (ℓ ^ N))[X] := fun N => (levelMatrix u N (E' N)).charpoly
  obtain ⟨F, hFdeg, hF⟩ := exists_map_toZModPow_eq (ℓ := ℓ) c r
    (fun N => natDegree_charpoly_le _)
    (fun n N h => charpoly_levelMatrix_map u N (E' N) h (E' n))
  have hFr : F.coeff r = 1 := PadicInt.ext_of_toZModPow.1 fun N => by
    rw [map_one, ← coeff_map, hF N]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have : Subsingleton (ZMod (ℓ ^ 0)) := by
        rw [pow_zero]
        infer_instance
      exact Subsingleton.elim _ _
    · have : Fact (1 < ℓ ^ N) := ⟨Nat.one_lt_pow hN.ne' hℓ.out.one_lt⟩
      have := (Matrix.charpoly_monic (levelMatrix u N (E' N))).coeff_natDegree
      rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  have hFm : F.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one r hFdeg hFr
  have hFn : F.natDegree = r := natDegree_eq_of_le_of_coeff_ne_zero hFdeg (by simp [hFr])
  set ιZ := Int.castRingHom ℤ_[ℓ]
  set ιQ := Int.castRingHom ℚ_[ℓ]
  have hinj : Function.Injective (PadicInt.Coe.ringHom (p := ℓ)) := Subtype.val_injective
  have hcomp : (PadicInt.Coe.ringHom (p := ℓ)).comp ιZ = ιQ := RingHom.ext_int _ _
  have hFχ : F = χ.map ιZ := by
    apply Polynomial.map_injective _ hinj
    rw [Polynomial.map_map, hcomp]
    refine Stacks.Polynomial.eq_of_norm_resultant_intPoly_eq p hp hpℓ (χ.map ιQ)
      (F.map PadicInt.Coe.ringHom) 1 (hχ.map _) (hFm.map _) ?_ one_ne_zero fun R hR0 hres => ?_
    · rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective
        (RingHom.injective_int ιQ), hFn, hχr]
    have hRQ : R.map ιQ = (R.map ιZ).map PadicInt.Coe.ringHom := by rw [Polynomial.map_map, hcomp]
    have hdR : (R.map ιQ).natDegree = R.natDegree :=
      natDegree_map_eq_of_injective (RingHom.injective_int ιQ) R
    have hχres : (χ.map ιQ).resultant (R.map ιQ) = ιQ (χ.resultant R) := by
      rw [hdR, natDegree_map_eq_of_injective (RingHom.injective_int ιQ), resultant_map_map]
    have hFres : (F.map PadicInt.Coe.ringHom).resultant (R.map ιQ) =
        PadicInt.Coe.ringHom (F.resultant (R.map ιZ) r R.natDegree) := by
      rw [hdR, natDegree_map_eq_of_injective hinj, hFn, hRQ, resultant_map_map]
    rw [one_mul, hχres] at hres
    have hres' : χ.resultant R ≠ 0 := fun h0 => hres (by rw [h0, map_zero])
    rw [hχres, hFres]
    change ‖((F.resultant (R.map ιZ) r R.natDegree : ℤ_[ℓ]) : ℚ_[ℓ])‖ =
      ‖((χ.resultant R : ℤ) : ℚ_[ℓ])‖
    rw [PadicInt.norm_coe,
      norm_resultant_eq_of_natCard_ker u E' F hF R hres' (hker R hR0 hres'),
      ← PadicInt.norm_coe, PadicInt.coe_intCast]
  rw [← charpoly_levelMatrix_map u n (E' n) (le_refl n) E,
    show ZMod.castHom (pow_dvd_pow ℓ (le_refl n)) (ZMod (ℓ ^ n)) = RingHom.id _ from
      ZMod.castHom_self, Polynomial.map_id]
  change c n = _
  rw [← hF n, hFχ, Polynomial.map_map,
    show (PadicInt.toZModPow n).comp ιZ = Int.castRingHom (ZMod (ℓ ^ n)) from RingHom.ext_int _ _]

end Stacks.Picard
