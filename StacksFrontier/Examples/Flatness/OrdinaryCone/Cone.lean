module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination

/-!
# The affine cone over an ordinary elliptic curve in characteristic two

Over a commutative ring `k` we consider the homogeneous cubic `z³ + (y² + xy) z + x³` in
`k[x, y, z]` and the quotient `G = k[x, y, z]/(z³ + (y² + xy) z + x³)`. Over a field of
characteristic two this is the homogeneous coordinate ring of an ordinary elliptic curve, the
affine cone over it.

Over every field the cubic is irreducible, by Eisenstein's criterion in the variable `x` at the
prime `(z)` of `k[y, z]`, so `G` is a domain.

## Main definitions

* `Stacks.Examples.OrdinaryCone.equation`: the cubic `z³ + (y² + xy) z + x³`.
* `Stacks.Examples.OrdinaryCone.Cone`: the quotient `k[x, y, z]/(z³ + (y² + xy) z + x³)`, with
  coordinates `Cone.x`, `Cone.y`, `Cone.z`.
* `Stacks.Examples.OrdinaryCone.Cone.component`: its degree `d` part, the image of the
  homogeneous polynomials of degree `d`.

## Main results

* `Stacks.Examples.OrdinaryCone.irreducible_equation`: the cubic is irreducible over a field.
* `Stacks.Examples.OrdinaryCone.isPrime_span_equation`: over a field it generates a prime ideal,
  so that the cone is a domain by `Ideal.Quotient.isDomain`.
-/

@[expose] public section

namespace Stacks.Examples.OrdinaryCone

open MvPolynomial

variable (k : Type*) [CommRing k]

/-- The homogeneous cubic `z³ + (y² + xy) z + x³` in `k[x, y, z]`, with `x = X 0`, `y = X 1`
and `z = X 2`. -/
noncomputable def equation : MvPolynomial (Fin 3) k :=
  X 2 ^ 3 + (X 1 ^ 2 + X 0 * X 1) * X 2 + X 0 ^ 3

/-- The affine cone `k[x, y, z]/(z³ + (y² + xy) z + x³)`. -/
abbrev Cone : Type _ := MvPolynomial (Fin 3) k ⧸ Ideal.span {equation k}

namespace Cone

/-- The coordinate `x` of the cone. -/
noncomputable def x : Cone k := Ideal.Quotient.mk _ (X 0)

/-- The coordinate `y` of the cone. -/
noncomputable def y : Cone k := Ideal.Quotient.mk _ (X 1)

/-- The coordinate `z` of the cone. -/
noncomputable def z : Cone k := Ideal.Quotient.mk _ (X 2)

/-- The coordinates of the cone satisfy `z³ + (y² + xy) z + x³ = 0`. -/
theorem equation_eq_zero : z k ^ 3 + (y k ^ 2 + x k * y k) * z k + x k ^ 3 = 0 := by
  simp only [x, y, z, ← map_pow, ← map_mul, ← map_add]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

section Lift

variable {B : Type*} [CommRing B] [Algebra k B]

/-- The `k`-algebra map out of the cone sending `x`, `y` and `z` to a solution `(a, b, c)` of the
cubic `c³ + (b² + ab) c + a³ = 0`. -/
noncomputable def lift (a b c : B) (h : c ^ 3 + (b ^ 2 + a * b) * c + a ^ 3 = 0) :
    Cone k →ₐ[k] B :=
  Ideal.Quotient.liftₐ (Ideal.span {equation k}) (aeval ![a, b, c]) fun p hp => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hp
    simp [equation, h]

variable {k} (a b c : B) (h : c ^ 3 + (b ^ 2 + a * b) * c + a ^ 3 = 0)

/-- `lift k a b c h` sends the class of a polynomial `p` to its evaluation at `(a, b, c)`. -/
theorem lift_mk (p : MvPolynomial (Fin 3) k) :
    lift k a b c h (Ideal.Quotient.mk _ p) = aeval ![a, b, c] p :=
  rfl

/-- `lift k a b c h` sends the coordinate `x` to `a`. -/
@[simp]
theorem lift_x : lift k a b c h (x k) = a := by
  rw [x, lift_mk]
  simp

/-- `lift k a b c h` sends the coordinate `y` to `b`. -/
@[simp]
theorem lift_y : lift k a b c h (y k) = b := by
  rw [y, lift_mk]
  simp

/-- `lift k a b c h` sends the coordinate `z` to `c`. -/
@[simp]
theorem lift_z : lift k a b c h (z k) = c := by
  rw [z, lift_mk]
  simp

variable (k) in
/-- Two maps out of the cone agreeing on `x`, `y` and `z` are equal. -/
theorem algHom_ext {A : Type*} [Semiring A] [Algebra k A] {f g : Cone k →ₐ[k] A}
    (hx : f (x k) = g (x k)) (hy : f (y k) = g (y k)) (hz : f (z k) = g (z k)) : f = g :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i ↦ by fin_cases i; exacts [hx, hy, hz])

end Lift

/-- The degree `d` part of the cone: the image of the homogeneous polynomials of degree `d`. -/
noncomputable def component (d : ℕ) : Submodule k (Cone k) :=
  (homogeneousSubmodule (Fin 3) k d).map (Ideal.Quotient.mkₐ k _).toLinearMap

end Cone

/-- The image of the cubic under `k[x, y, z] ≃ k[y, z][x]`. -/
private theorem finSuccEquiv_equation :
    finSuccEquiv k 2 (equation k) = Polynomial.X ^ 3 + Polynomial.C (X 0 * X 1) * Polynomial.X +
      Polynomial.C (X 1 ^ 3 + X 0 ^ 2 * X 1) := by
  have h1 : (1 : Fin 3) = (0 : Fin 2).succ := rfl
  have h2 : (2 : Fin 3) = (1 : Fin 2).succ := rfl
  simp only [equation, h1, h2, map_add, map_mul, map_pow, finSuccEquiv_X_zero,
    finSuccEquiv_X_succ]
  ring

/-- Over a field the cubic `z³ + (y² + xy) z + x³` is irreducible: as a polynomial in `x` over
`k[y, z]` it is Eisenstein at the prime `(z)`. -/
theorem irreducible_equation (k : Type*) [Field k] : Irreducible (equation k) := by
  rw [← MulEquiv.irreducible_iff (finSuccEquiv k 2), finSuccEquiv_equation]
  set f : Polynomial (MvPolynomial (Fin 2) k) := Polynomial.X ^ 3 +
    Polynomial.C (X 0 * X 1) * Polynomial.X + Polynomial.C (X 1 ^ 3 + X 0 ^ 2 * X 1)
  have hmonic : f.Monic := by simp only [f]; monicity!
  have hdeg : f.degree = 3 := by simp only [f]; compute_degree!
  have hP : (Ideal.span {(X 1 : MvPolynomial (Fin 2) k)}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero 1)).mpr X_prime
  refine Polynomial.irreducible_of_eisenstein_criterion hP ?_ ?_ (by rw [hdeg]; decide) ?_
    hmonic.isPrimitive
  · rw [hmonic.leadingCoeff]
    exact (Ideal.ne_top_iff_one _).mp hP.ne_top
  · intro n hn
    rw [hdeg] at hn
    have hn : n < 3 := by exact_mod_cast hn
    interval_cases n <;>
      simp only [f, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C] <;>
      norm_num [Ideal.mem_span_singleton]
    exact Dvd.intro (X 1 ^ 2 + X 0 ^ 2) (by ring)
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨q, hq⟩
    simp only [f, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_zero] at hq
    norm_num at hq
    have h : (X 1 : MvPolynomial (Fin 2) k) * (X 1 ^ 2 + X 0 ^ 2) = X 1 * (X 1 * q) := by
      linear_combination hq
    have := congrArg (eval ![1, 0]) (mul_left_cancel₀ (X_ne_zero 1) h)
    simp at this

/-- Over a field the cubic `z³ + (y² + xy) z + x³` generates a prime ideal. -/
instance isPrime_span_equation (k : Type*) [Field k] :
    (Ideal.span {equation k}).IsPrime :=
  (Ideal.span_singleton_prime (irreducible_equation k).ne_zero).mpr
    (irreducible_equation k).prime

end Stacks.Examples.OrdinaryCone
