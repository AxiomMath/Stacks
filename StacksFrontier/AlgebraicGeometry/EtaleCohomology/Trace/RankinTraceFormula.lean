module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PositiveExponentialSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeightsFromTraceGrowth
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Rankin's bound from the trace formula on a curve

Deligne's Lemme 1.5.2 of Weil II (Kedlaya, *Fourier transforms and p-adic Weil II*, Lemma 6.5.1)
bounds the Frobenius eigenvalues of an `ι`-real lisse sheaf `ℰ` on a smooth affine curve `U` over
a finite field with `q` elements: the trace formula for `ℰ^{⊗ 2i}` has nonnegative local terms
`Tr(F_y^n, ℰ^{⊗ 2i}) = Tr(F_y^n, ℰ)^{2i}`, so the cohomological side dominates every single local
term, and the cohomological side is controlled by `H²_c(U_k̄, ℰ^{⊗ 2i})`, the geometric
coinvariants twisted by `(-1)`.

This file isolates the group-theoretic content.  A group `Γ` (the arithmetic fundamental group)
with a normal subgroup `H` (the geometric fundamental group), an element `φ` (a geometric
Frobenius), and a family `Fr : Y → Γ` of Frobenius elements at the closed points `y`, of degrees
`deg y`, are fixed.  A representation `τ : Γ → GL_m(F)` *satisfies the Frobenius trace formula*
(`Stacks.EtaleCohomology.SatisfiesFrobeniusTraceFormula`) when, along `ι : F →+* ℂ`, the local
sums `∑_{deg y ∣ n} deg y · Tr(τ(Fr y)^{n / deg y})` are `∑_{a ∈ A} a^n - ∑_{b ∈ B} b^n` for
finite families `A` (the eigenvalues on `H²_c`) and `B` (those on `H¹_c`), every `a ∈ A` being `q`
times an eigenvalue of `φ` on the `H`-coinvariants of `τ`.  For the lisse sheaf `ℱ_τ` on a smooth
affine curve this is the Grothendieck–Lefschetz trace formula together with
`H⁰_c(U_k̄, ℱ_τ) = 0` and `H²_c(U_k̄, ℱ_τ) = (ℱ_τ)_{π₁(U_k̄)}(-1)`.

## Main definitions

* `Stacks.EtaleCohomology.matrixRepresentation`: a matrix representation as a `Representation`.
* `Stacks.EtaleCohomology.coinvariantsFrobenius`: the action of `φ` on the `H`-coinvariants.
* `Stacks.EtaleCohomology.SatisfiesFrobeniusTraceFormula`.
* `Stacks.EtaleCohomology.tensorPowerRepresentation`: `τ^{⊗ k}`.

## Main results

* `Stacks.EtaleCohomology.trace_tensorPowerRepresentation`: `Tr τ^{⊗ k}(g) = (Tr τ(g))^k`.
* `Stacks.EtaleCohomology.norm_le_of_satisfiesFrobeniusTraceFormula`: Rankin's bound.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), Lemme 1.5.2.
* K. S. Kedlaya, *Fourier transforms and p-adic "Weil II"*, Compos. Math. 142 (2006), 6.5.
-/

@[expose] public noncomputable section

open Polynomial Filter

namespace Stacks.EtaleCohomology

section Representation

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R] {m : ℕ}

/-- A matrix representation `τ : Γ → GL_m(R)` as a representation on `R^m`. -/
public def matrixRepresentation (τ : Γ →* GL (Fin m) R) : Representation R Γ (Fin m → R) :=
  (Matrix.toLinAlgEquiv' (R := R) (n := Fin m)).toRingEquiv.toMonoidHom.comp
    ((Units.coeHom _).comp τ)

/-- `matrixRepresentation τ g v` is the matrix-vector product `τ g *ᵥ v`. -/
public theorem matrixRepresentation_apply (τ : Γ →* GL (Fin m) R) (g : Γ) (v : Fin m → R) :
    matrixRepresentation τ g v = Matrix.mulVec (τ g : Matrix (Fin m) (Fin m) R) v :=
  rfl

variable (H : Subgroup Γ) [H.Normal]

/-- **The action of `φ` on the `H`-coinvariants** of a representation `τ` of `Γ`, for `H` normal
in `Γ`: `ρ(φ)` preserves the span of the `ρ(h) v - v`. -/
public def coinvariantsFrobenius (τ : Γ →* GL (Fin m) R) (φ : Γ) :
    Module.End R (Representation.Coinvariants
      ((matrixRepresentation τ).comp H.subtype : Representation R H (Fin m → R))) :=
  Representation.Coinvariants.lift _
    (Representation.Coinvariants.mk _ ∘ₗ matrixRepresentation τ φ) fun h => by
      refine LinearMap.ext fun v => ?_
      change Representation.Coinvariants.mk _ (matrixRepresentation τ φ
          (matrixRepresentation τ h v)) =
        Representation.Coinvariants.mk _ (matrixRepresentation τ φ v)
      rw [← Module.End.mul_apply, ← map_mul, show φ * (h : Γ) = (φ * h * φ⁻¹) * φ by group,
        map_mul, Module.End.mul_apply]
      exact Representation.Coinvariants.mk_self_apply _
        (⟨φ * h * φ⁻¹, Subgroup.Normal.conj_mem inferInstance _ h.2 φ⟩ : H) _

/-- **`τ^{⊗ k}`**, the `k`-th Kronecker power of a matrix representation. -/
public def tensorPowerRepresentation (τ : Γ →* GL (Fin m) R) : (k : ℕ) → Γ →* GL (Fin (m ^ k)) R
  | 0 => 1
  | k + 1 => kroneckerRepresentation (tensorPowerRepresentation τ k) τ

/-- **The trace of `τ^{⊗ k}` is the `k`-th power of the trace.** -/
public theorem trace_tensorPowerRepresentation (τ : Γ →* GL (Fin m) R) (k : ℕ) (g : Γ) :
    (tensorPowerRepresentation τ k g : Matrix (Fin (m ^ k)) (Fin (m ^ k)) R).trace =
      (τ g : Matrix (Fin m) (Fin m) R).trace ^ k := by
  induction k with
  | zero =>
    change (1 : Matrix (Fin (m ^ 0)) (Fin (m ^ 0)) R).trace = _
    rw [Matrix.trace_one, Fintype.card_fin, pow_zero, Nat.cast_one, pow_zero]
  | succ k ih =>
    change (kroneckerRepresentation (tensorPowerRepresentation τ k) τ g).val.trace = _
    rw [trace_kroneckerRepresentation, ih, pow_succ]

/-- The tensor powers of a continuous matrix representation are continuous. -/
public theorem continuous_tensorPowerRepresentation [TopologicalSpace Γ] [TopologicalSpace R]
    [IsTopologicalRing R] {τ : Γ →* GL (Fin m) R} (hτ : Continuous τ) (k : ℕ) :
    Continuous (tensorPowerRepresentation τ k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih => exact continuous_kroneckerRepresentation _ _ ih hτ

end Representation

section TraceFormula

variable {Γ : Type*} [Group Γ] {F : Type*} [Field F] {m : ℕ}

/-- **The Frobenius trace formula with `H²` the coinvariants** for a representation
`τ : Γ → GL_m(F)`, read along `ι : F →+* ℂ`: there are finite families `A`, `B` of complex
numbers with
`ι (∑_{deg y ∣ n} deg y · Tr(τ(Fr y)^{n / deg y})) = ∑_{a ∈ A} a ^ n - ∑_{b ∈ B} b ^ n`
for every `n ≥ 1`, every `a ∈ A` being `q` times a root, along `ι`, of the characteristic
polynomial of `φ` on the `H`-coinvariants of `τ`.  For the lisse sheaf of `τ` on a smooth affine
curve over a finite field with `q` elements, `H` the geometric fundamental group, `φ` a
geometric Frobenius and `Fr y` the Frobenius elements at the closed points, `A` and `B` are the
eigenvalues of `π^*` on `H²_c = (ℱ_τ)_H(-1)` and on `H¹_c`. -/
public def SatisfiesFrobeniusTraceFormula (q : ℝ) (ι : F →+* ℂ) (H : Subgroup Γ) [H.Normal]
    (φ : Γ) {Y : Type*} (Fr : Y → Γ) (deg : Y → ℕ) (τ : Γ →* GL (Fin m) F) : Prop :=
  ∃ A B : Multiset ℂ,
    (∀ a ∈ A, ((LinearMap.charpoly (coinvariantsFrobenius H τ φ)).map ι).IsRoot (a / q)) ∧
    ∀ n : ℕ, 0 < n →
      ι (∑ᶠ (y : Y) (_ : deg y ∣ n),
          (deg y : F) * ((τ (Fr y) : Matrix (Fin m) (Fin m) F) ^ (n / deg y)).trace) =
        (A.map (· ^ n)).sum - (B.map (· ^ n)).sum

/-- Along `ι`, the trace of the `e`-th power of a matrix is the sum of the `e`-th powers of the
complex roots of its characteristic polynomial read along `ι`. -/
public theorem map_trace_pow_eq_sum_roots (ι : F →+* ℂ) (M : Matrix (Fin m) (Fin m) F) (e : ℕ) :
    ι (M ^ e).trace = (((M.charpoly.map ι).roots).map (· ^ e)).sum := by
  have h := map_trace_pow_eq_sum_roots_map_pow ι (Matrix.toLin' M) e
  have hp : (Matrix.toLin' M) ^ e = Matrix.toLin' (M ^ e) :=
    (map_pow (Matrix.toLinAlgEquiv' (R := F) (n := Fin m)) M e).symm
  rwa [hp, Matrix.trace_toLin'_eq, Matrix.charpoly_toLin'] at h

/-- If the coefficients of the characteristic polynomial of `M` are real along `ι`, then so is the
trace of every power of `M`: it is fixed by complex conjugation. -/
public theorem conj_map_trace_pow (ι : F →+* ℂ) (M : Matrix (Fin m) (Fin m) F)
    (hreal : ∀ n, ι (M.charpoly.coeff n) ∈ Set.range ((↑) : ℝ → ℂ)) (e : ℕ) :
    starRingEnd ℂ (ι (M ^ e).trace) = ι (M ^ e).trace := by
  set P := M.charpoly.map ι
  have hPc : P.map (starRingEnd ℂ) = P := by
    ext n
    rw [coeff_map]
    obtain ⟨c, hc⟩ := hreal n
    rw [show P.coeff n = ι (M.charpoly.coeff n) from coeff_map _ _, ← hc, Complex.conj_ofReal]
  have hroots : P.roots.map (starRingEnd ℂ) = P.roots := by
    rw [(M.charpoly_monic.map ι).roots_map_of_card_eq_natDegree (starRingEnd ℂ)
      IsAlgClosed.card_roots_eq_natDegree, hPc]
  rw [map_trace_pow_eq_sum_roots, map_multiset_sum, Multiset.map_map]
  conv_rhs => rw [← hroots, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun z _ => ?_
  simp [map_pow]

/-- The real part of an even power of a real complex number is nonnegative. -/
theorem re_pow_two_mul_nonneg {c : ℂ} (hc : starRingEnd ℂ c = c) (i : ℕ) :
    0 ≤ (c ^ (2 * i)).re := by
  have hc' : (c.re : ℂ) = c := Complex.conj_eq_iff_re.mp hc
  rw [← hc', ← Complex.ofReal_pow, Complex.ofReal_re, pow_mul]
  exact pow_nonneg (sq_nonneg _) _

/-- The trace of a power of `τ^{⊗ k}(g)` is the `k`-th power of the trace of the same power of
`τ(g)`. -/
public theorem trace_pow_tensorPowerRepresentation {Γ : Type*} [Group Γ] {R : Type*} [CommRing R]
    {m : ℕ} (τ : Γ →* GL (Fin m) R) (k : ℕ) (g : Γ) (e : ℕ) :
    ((tensorPowerRepresentation τ k g : Matrix (Fin (m ^ k)) (Fin (m ^ k)) R) ^ e).trace =
      ((τ g : Matrix (Fin m) (Fin m) R) ^ e).trace ^ k := by
  rw [← Units.val_pow_eq_pow_val, ← map_pow, trace_tensorPowerRepresentation, map_pow,
    Units.val_pow_eq_pow_val]

variable {Y : Type*}

/-- **Rankin's bound at a closed point** (Weil II, Lemme 1.5.2; Kedlaya, Lemma 6.5.1).  Let
`τ : Γ → GL_m(F)` have `ι`-real Frobenius characteristic polynomials, let every `τ^{⊗ 2i}`
(`i ≥ 1`) satisfy the Frobenius trace formula, and let the roots along `ι` of the characteristic
polynomial of `φ` on the `H`-coinvariants of `τ^{⊗ 2i}` have absolute value at most `q ^ (i w)`.
Then every complex root of the characteristic polynomial of `τ(Fr y)`, read along `ι`, has
absolute value at most `q ^ (deg y · w / 2)`. -/
public theorem norm_le_of_satisfiesFrobeniusTraceFormula {q : ℝ} (hq : 1 ≤ q) (ι : F →+* ℂ)
    (H : Subgroup Γ) [H.Normal] (φ : Γ) (Fr : Y → Γ) (deg : Y → ℕ)
    (hfin : ∀ n : ℕ, 0 < n → {y : Y | deg y ∣ n}.Finite) (τ : Γ →* GL (Fin m) F)
    (hreal : ∀ (y : Y) (n : ℕ),
      ι ((τ (Fr y) : Matrix (Fin m) (Fin m) F).charpoly.coeff n) ∈ Set.range ((↑) : ℝ → ℂ))
    (w : ℝ)
    (htf : ∀ i : ℕ, 0 < i →
      SatisfiesFrobeniusTraceFormula q ι H φ Fr deg (tensorPowerRepresentation τ (2 * i)))
    (hcoinv : ∀ i : ℕ, 0 < i → ∀ z : ℂ,
      ((LinearMap.charpoly (coinvariantsFrobenius H (tensorPowerRepresentation τ (2 * i)) φ)).map
        ι).IsRoot z → ‖z‖ ≤ q ^ (i * w))
    (y : Y) (hy : 0 < deg y) (α : ℂ)
    (hα : ((τ (Fr y) : Matrix (Fin m) (Fin m) F).charpoly.map ι).IsRoot α) :
    ‖α‖ ≤ q ^ (deg y * w / 2) := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  set s := ((τ (Fr y) : Matrix (Fin m) (Fin m) F).charpoly.map ι).roots with hs
  have hαs : α ∈ s := (Polynomial.mem_roots ((Matrix.charpoly_monic _).map ι).ne_zero).2 hα
  let A : ℕ → Multiset ℂ := fun i => if h : 0 < i then (htf i h).choose else 0
  let B : ℕ → Multiset ℂ := fun i => if h : 0 < i then (htf i h).choose_spec.choose else 0
  have hA : ∀ i, ∀ a ∈ A i, ‖a‖ ≤ q ^ (1 + i * w) := by
    intro i a ha
    by_cases hi : 0 < i
    · simp only [A, dite_eq_left hi] at ha
      have hb := hcoinv i hi _ ((htf i hi).choose_spec.choose_spec.1 a ha)
      rw [norm_div, Complex.norm_of_nonneg hq0.le, div_le_iff₀ hq0] at hb
      rwa [Real.rpow_add hq0, Real.rpow_one, mul_comm]
    · simp [A, dite_eq_right hi] at ha
  have hsum : ∀ (C : Multiset ℂ) (n : ℕ), (C.map (· ^ n)).sum = ∑ x : C, (x : ℂ) ^ n :=
    fun C n => by
      rw [Finset.sum_eq_multiset_sum]
      exact (congrArg Multiset.sum (Multiset.map_univ C (· ^ n))).symm
  have hdom : ∀ i, 0 < i → ∀ᶠ n : ℕ in atTop, (deg y : ℝ) * ((∑ x : s, (x : ℂ) ^ n) ^ (2 * i)).re ≤
      (((A i).map (· ^ (deg y * n))).sum - ((B i).map (· ^ (deg y * n))).sum).re := by
    intro i hi
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hdn : 0 < deg y * n := Nat.mul_pos hy hn
    have htr := (htf i hi).choose_spec.choose_spec.2 (deg y * n) hdn
    simp only [A, B, dite_eq_left hi]
    have hfs : ∀ f : Y → F, (∑ᶠ (y' : Y) (_ : deg y' ∣ deg y * n), f y') =
        ∑ y' ∈ (hfin (deg y * n) hdn).toFinset, f y' := fun f =>
      finsum_mem_eq_finite_toFinset_sum f (hfin (deg y * n) hdn)
    rw [← htr, hfs, map_sum, Complex.re_sum]
    have hterm : ∀ y' : Y,
        (ι ((deg y' : F) * ((tensorPowerRepresentation τ (2 * i) (Fr y') :
          Matrix (Fin (m ^ (2 * i))) (Fin (m ^ (2 * i))) F) ^ (deg y * n / deg y')).trace)).re =
        deg y' * ((ι (((τ (Fr y') : Matrix (Fin m) (Fin m) F) ^
          (deg y * n / deg y')).trace)) ^ (2 * i)).re := by
      intro y'
      rw [trace_pow_tensorPowerRepresentation, map_mul, map_pow, map_natCast,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    have hmem : y ∈ (hfin (deg y * n) hdn).toFinset :=
      (Set.Finite.mem_toFinset _).2 (Dvd.intro n rfl)
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun y' _ => ?_) hmem)
    swap
    · rw [hterm]
      exact mul_nonneg (Nat.cast_nonneg _) (re_pow_two_mul_nonneg
        (conj_map_trace_pow ι _ (hreal y') _) i)
    rw [hterm, Nat.mul_div_cancel_left n hy, map_trace_pow_eq_sum_roots, hsum]
  simpa [Multiset.coe_mk] using norm_le_of_forall_rankin (α := fun x : s => (x : ℂ)) hy hq A B hA
    hdom (s.mkToType α ⟨0, Multiset.count_pos.mpr hαs⟩)

end TraceFormula

end Stacks.EtaleCohomology

end
