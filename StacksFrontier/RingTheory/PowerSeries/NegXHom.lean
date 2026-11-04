module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# The substitution `X ↦ -X` in power series over a noncommutative ring

For a ring `R`, not necessarily commutative, the map `f(X) ↦ f(-X)` on `R⟦X⟧`, which multiplies
the coefficient of `X^n` by `(-1)^n`, is a ring endomorphism, because `-1` is central. Over a
commutative ring it is `PowerSeries.evalNegHom`.

Written on a total Chern class `c(ℰ) = ∑ c_n(ℰ) X^n`, with the degree recorded by the power of
`X`, it is the endomorphism multiplying the degree `n` part by `(-1)^n`, which carries `c(ℰ)` to
`c(ℰ^∨)` (Stacks 0ESD).

## Main definitions

* `PowerSeries.negXHom`: the ring endomorphism `f(X) ↦ f(-X)` of `R⟦X⟧`.

## Main results

* `PowerSeries.coeff_negXHom`: the coefficient of `X^n` is multiplied by `(-1)^n`.
* `PowerSeries.negXHom_eq_evalNegHom`: over a commutative ring it is `PowerSeries.evalNegHom`.
* `PowerSeries.negXHom_one_add_C_mul_X`: `1 + a X ↦ 1 - a X`.
* `PowerSeries.commute_mk`: power series whose coefficients commute pairwise commute.

## References

* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
-/

@[expose] public noncomputable section

namespace PowerSeries

variable (R : Type*) [Ring R]

/-- The ring endomorphism `f(X) ↦ f(-X)` of the power series over a ring, multiplying the
coefficient of `X^n` by `(-1)^n`. -/
def negXHom : R⟦X⟧ →+* R⟦X⟧ where
  toFun f := mk fun n => (-1 : R) ^ n * coeff n f
  map_one' := by
    ext n
    rcases n with _ | n <;> simp [coeff_one]
  map_mul' f g := by
    ext n
    simp only [coeff_mk, coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [← hp, pow_add, mul_assoc, mul_assoc, ← mul_assoc (coeff p.1 f),
      ((Commute.neg_one_left _).pow_left p.2).eq.symm, mul_assoc]
  map_zero' := by ext; simp
  map_add' f g := by ext; simp [mul_add]

variable {R}

/-- The coefficient of `X^n` in `negXHom R f` is `(-1)^n` times that of `f`. -/
@[simp]
theorem coeff_negXHom (f : R⟦X⟧) (n : ℕ) : coeff n (negXHom R f) = (-1) ^ n * coeff n f :=
  coeff_mk n (fun n => (-1 : R) ^ n * coeff n f)

/-- The substitution `X ↦ -X` carries `1 + a X` to `1 - a X`. -/
theorem negXHom_one_add_C_mul_X (a : R) : negXHom R (1 + C a * X) = 1 + C (-a) * X := by
  ext n
  rw [coeff_negXHom]
  rcases n with _ | _ | n <;> simp [coeff_one]

/-- Over a commutative ring, `f(X) ↦ f(-X)` is `PowerSeries.evalNegHom`. -/
theorem negXHom_eq_evalNegHom {A : Type*} [CommRing A] : negXHom A = evalNegHom := by
  ext f n
  simp [evalNegHom, coeff_rescale]

/-- Power series whose coefficients commute pairwise commute. -/
theorem commute_mk {a b : ℕ → R} (h : ∀ i j, Commute (a i) (b j)) : Commute (mk a) (mk b) := by
  ext n
  rw [coeff_mul, coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [coeff_mk, Prod.fst_swap, Prod.snd_swap]
  exact (h p.2 p.1).eq

end PowerSeries
