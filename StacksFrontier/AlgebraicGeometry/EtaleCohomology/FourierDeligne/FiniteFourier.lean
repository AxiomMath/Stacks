module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.RingTheory.Trace.Basic

/-!
# The finite Fourier transform on `𝔽_q`

For a finite field `k`, a commutative domain `R` and a nontrivial additive character
`ψ : k → R`, the Fourier transform of `f : k → R` is `F_ψ(f)(t) = ∑_x f(x) ψ(x t)`.  This is the
transform of trace functions that the Fourier–Deligne transform of ℓ-adic sheaves on `𝔸¹`
categorifies [Laumon, 1.2]: the trace function of the Fourier transform of a sheaf is (up to sign)
the Fourier transform of its trace function.

## Main definitions

* `Stacks.FourierDeligne.finiteFourier ψ f`.
* `Stacks.FourierDeligne.traceChar ψ k'`: `ψ ∘ Tr_{k'/k}` on a finite extension `k'`.

## Main results

* `Stacks.FourierDeligne.finiteFourier_finiteFourier`: **involutivity up to a twist**,
  `F_ψ(F_ψ f)(x) = q f(-x)`.
* `Stacks.FourierDeligne.sum_finiteFourier_mul`: **Plancherel**,
  `∑_t F_ψ f(t) F_{ψ⁻¹} g(t) = q ∑_x f(x) g(x)`.
* `Stacks.FourierDeligne.isPrimitive_traceChar`: `ψ ∘ Tr` is again nontrivial, so the above hold
  over every finite extension of `k`.

## References

* [G. Laumon, Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil, Publ. Math. IHÉS 65 (1987), 1.1–1.2]
-/

@[expose] public noncomputable section

open Finset

namespace Stacks.FourierDeligne

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {R : Type*} [CommRing R] [IsDomain R]

/-- **The finite Fourier transform** `F_ψ(f)(t) = ∑_x f(x) ψ(x t)`. -/
public def finiteFourier (ψ : AddChar k R) (f : k → R) (t : k) : R :=
  ∑ x, f x * ψ (x * t)

omit [DecidableEq k] [IsDomain R] in
public theorem finiteFourier_add (ψ : AddChar k R) (f g : k → R) :
    finiteFourier ψ (f + g) = finiteFourier ψ f + finiteFourier ψ g := by
  funext t
  simp [finiteFourier, add_mul, sum_add_distrib]

omit [DecidableEq k] [IsDomain R] in
public theorem finiteFourier_smul (ψ : AddChar k R) (c : R) (f : k → R) :
    finiteFourier ψ (c • f) = c • finiteFourier ψ f := by
  funext t
  simp [finiteFourier, mul_sum, mul_assoc]

/-- Orthogonality: `∑_t ψ(a t) = q [a = 0]` for a nontrivial `ψ`. -/
public theorem sum_apply_mul (ψ : AddChar k R) (hψ : ψ ≠ 1) (a : k) :
    ∑ t, ψ (a * t) = if a = 0 then (Fintype.card k : R) else 0 := by
  calc ∑ t, ψ (a * t) = ∑ t, ψ (t * a) := sum_congr rfl fun t _ => by rw [mul_comm]
    _ = _ := AddChar.sum_mulShift a (AddChar.IsPrimitive.of_ne_one hψ)
    _ = _ := by split_ifs <;> simp

omit [DecidableEq k] in
/-- **The Fourier transform is involutive up to the twist `x ↦ -x` and the factor `q`**:
`F_ψ(F_ψ f)(x) = q f(-x)` (Laumon 1.2.2.1 on trace functions). -/
public theorem finiteFourier_finiteFourier (ψ : AddChar k R) (hψ : ψ ≠ 1) (f : k → R) (x : k) :
    finiteFourier ψ (finiteFourier ψ f) x = Fintype.card k * f (-x) := by
  classical
  unfold finiteFourier
  calc ∑ t, (∑ y, f y * ψ (y * t)) * ψ (t * x) = ∑ y, f y * ∑ t, ψ ((y + x) * t) := by
        simp_rw [sum_mul, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun y _ => sum_congr rfl fun t _ => ?_
        rw [mul_assoc, ← AddChar.map_add_eq_mul, add_mul, mul_comm t x]
    _ = ∑ y, if y = -x then f y * Fintype.card k else 0 := by
        refine sum_congr rfl fun y _ => ?_
        rw [sum_apply_mul ψ hψ]
        by_cases h : y = -x
        · rw [ite_eq_left (by rw [h, neg_add_cancel]), ite_eq_left h]
        · rw [ite_eq_right (fun h' => h (eq_neg_of_add_eq_zero_left h')), ite_eq_right h, mul_zero]
    _ = Fintype.card k * f (-x) := by
        rw [sum_ite_eq' univ (-x) (fun y => f y * Fintype.card k), ite_eq_left (mem_univ _),
          mul_comm]

omit [DecidableEq k] in
/-- **Plancherel**: `∑_t F_ψ f(t) F_{ψ⁻¹} g(t) = q ∑_x f(x) g(x)`. -/
public theorem sum_finiteFourier_mul (ψ : AddChar k R) (hψ : ψ ≠ 1) (f g : k → R) :
    ∑ t, finiteFourier ψ f t * finiteFourier ψ⁻¹ g t = Fintype.card k * ∑ x, f x * g x := by
  classical
  unfold finiteFourier
  calc ∑ t, (∑ x, f x * ψ (x * t)) * (∑ y, g y * ψ⁻¹ (y * t)) =
      ∑ x, ∑ y, f x * g y * ∑ t, ψ ((x - y) * t) := by
        simp_rw [sum_mul, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun x _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun y _ => sum_congr rfl fun t _ => ?_
        rw [AddChar.inv_apply, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, ← neg_mul]
        ring
    _ = ∑ x, f x * g x * Fintype.card k := by
        refine sum_congr rfl fun x _ => ?_
        simp_rw [sum_apply_mul ψ hψ, sub_eq_zero, mul_ite, mul_zero]
        rw [sum_ite_eq univ x (fun y => f x * g y * Fintype.card k), ite_eq_left (mem_univ _)]
    _ = Fintype.card k * ∑ x, f x * g x := by
        rw [mul_sum]
        exact sum_congr rfl fun x _ => mul_comm _ _

/-! ### Extension of the base field -/

variable (ψ : AddChar k R) (k' : Type*) [Field k'] [Fintype k'] [Algebra k k']

/-- `ψ ∘ Tr_{k'/k}`, the character of `k'` by which `ψ` extends to the finite extension `k'`. -/
public def traceChar : AddChar k' R :=
  ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom

omit [Fintype k] [DecidableEq k] [IsDomain R] [Fintype k'] in
public theorem traceChar_apply (x : k') : traceChar ψ k' x = ψ (Algebra.trace k k' x) :=
  rfl

omit [Fintype k] [DecidableEq k] [IsDomain R] [Fintype k'] in
/-- **`ψ ∘ Tr_{k'/k}` is nontrivial when `ψ` is**, the trace of a finite extension of finite fields
being surjective. -/
public theorem traceChar_ne_one [Finite k] [Finite k'] (hψ : ψ ≠ 1) : traceChar ψ k' ≠ 1 := by
  intro h
  apply hψ
  ext c
  obtain ⟨z, hz⟩ := Algebra.trace_surjective k k' c
  have := congrArg (fun φ : AddChar k' R => φ z) h
  simpa [traceChar_apply, hz] using this

end Stacks.FourierDeligne
