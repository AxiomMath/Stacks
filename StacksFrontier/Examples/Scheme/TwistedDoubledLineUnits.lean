module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# A global unit that is not a square times a unit of a twisted thickening

Work over `ℚ`.  Let `R = ℚ[t, t⁻¹]`, let `A = R[x]` and let `B = R[x, x⁻¹]` be the localisation
of `A` at `x`.  Glue two copies of `Spec A` along `Spec B` by the identity: the result is the
affine line over `R` with its origin doubled, a non-separated scheme `X` with
`Γ(X, 𝒪_X) = A`, so `t` is an invertible global function on `X`.

Now thicken.  Let `ε` be a square-zero parameter, let `A' = A[ε]`, `B' = B[ε]`, and glue the two
copies of `Spec A'` along `Spec B'` not by the identity but by the twist
`φ(b₀ + ε b₁) = b₀ + ε (b₁ + x⁻¹ δ b₀)`, where `δ` is the `ℚ`-derivation `t ∂/∂t` of `B`.  This
`φ` is a ring automorphism of `B'` because `x⁻¹ δ` is a derivation of `B` and `ε² = 0`, and it is
the identity modulo `ε`, so it glues to a first-order thickening `i : X ⟶ X'` whose ideal sheaf
is `𝒪_X`, with `X` the same doubled line as before.  Two is invertible in `𝒪_X`.

A global function on `X'` is a pair of elements of `A'` identified by `φ` over `B'`, so its
restriction to `X` is an element `p ∈ A` with `x ∣ δ̃ p`, where `δ̃` is the coefficientwise
extension of `δ` to `A`: the twist contributes `ε x⁻¹ δ̃ p`, and that lies in `A'` exactly when
`δ̃ p` is divisible by `x`.  **This file proves that no such `p` has `t = a² p`**, i.e. that the
invertible global function `t` on `X` is not a square times the restriction of an invertible
global function on `X'`.

That is the failure, for this thickening and `n = 2`, of the condition
`Stacks.Thickenings.GlobalUnitsPowerLift` which
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff` proves equivalent to the
conclusion of [Stacks, Tag 0C6S].  The 2-torsion class of `Pic(X')` that it produces is the line
bundle glued by `1 + ½ x⁻¹ ε ∈ Γ(B')ˣ`: its square is `1 + x⁻¹ε`, which is the comparison of the
two lifts of `t`, hence a coboundary, while `1 + ½x⁻¹ε` is not a coboundary and is trivial on
`X`.  See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Thickenings/PicardTorsionGeneral.lean`.

## Main definitions

* `Stacks.Examples.TwistedDoubledLine.gradeDeriv`: the derivation `δ = t ∂/∂t` of
  `ℚ[t, t⁻¹]`.
* `Stacks.Examples.TwistedDoubledLine.coeffDeriv` and
  `Stacks.Examples.TwistedDoubledLine.lcoeffDeriv`: its coefficientwise extension `δ̃` to the
  chart ring `A = ℚ[t,t⁻¹][x]` and to the overlap ring `B = ℚ[t,t⁻¹][x,x⁻¹]`.
* `Stacks.Examples.TwistedDoubledLine.twist`: **the gluing isomorphism of the thickening**,
  the map `b₀ + ε b₁ ↦ b₀ + ε (b₁ + x⁻¹ δ̃ b₀)` of `B' = B[ε]`, as a ring homomorphism.
* `Stacks.Examples.TwistedDoubledLine.dualToOverlap`: the inclusion of the chart ring
  `A' = A[ε]` of the thickening in `B'`, i.e. the localisation at `x` in each `ε`-component.

## Main results

* `Stacks.Examples.TwistedDoubledLine.gradeDeriv_mul` and
  `Stacks.Examples.TwistedDoubledLine.lcoeffDeriv_mul`: the Leibniz rule for `δ` and for `δ̃`,
  so that `x⁻¹ δ̃` is a derivation of `B`.
* `Stacks.Examples.TwistedDoubledLine.twist_bijective`: the twist is bijective, hence a ring
  automorphism of `B'`; it is the identity modulo `ε` by construction, so it is a legitimate
  gluing datum for a first-order thickening of the doubled line.
* `Stacks.Examples.TwistedDoubledLine.not_exists_sq_mul_fst_of_twist_eq`: **the
  counterexample.**  For no `a ∈ A` and no pair `(c₀, c₁)` of elements of `A'` identified by the
  twist over `B'` — that is, for no global function of `X'` — is `a² (c₀ mod ε)` equal to `t`.
* `Stacks.Examples.TwistedDoubledLine.not_exists_sq_mul_dvd_coeffDeriv`: the same statement with
  the gluing condition solved, as the divisibility `x ∣ δ̃ p` on the restriction `p`.

## Implementation notes

The scheme-level assembly of `X`, `X'` and `i : X ⟶ X'` from the rings and the twist is carried
out in `StacksFrontier/Examples/Scheme/TwistedDoubledLineThickening.lean`, which turns what is
proved here into the refutation of the tag as stated,
`Stacks.Examples.TwistedDoubledLine.not_forall_bijOn_schemePullbackClass_zsmulTorsion`.  What is
proved here is the statement that assembly reduces to, in the two-chart Čech description
recalled above.  Both charts of `X'` are copies of `Spec A'`, so a global function on
`X'` is a pair `(c₀, c₁) ∈ A' × A'` with `twist (c₀) = c₁` in `B'`, and the restriction map to
`Γ(X, 𝒪_X) = A` is `c₀ ↦ c₀ mod ε`; that is the hypothesis of
`not_exists_sq_mul_fst_of_twist_eq`.  Which of the two charts is twisted, and in which
direction, does not matter: the `ε`-free part of the gluing condition gives
`c₀ mod ε = c₁ mod ε` either way, and the `ε`-part gives the same divisibility.  Nothing is
assumed about `a` or `c₀` beyond the gluing condition — in particular they are not assumed
invertible, so the statement is stronger than the failure of `GlobalUnitsPowerLift` it is quoted
for.

The derivations are given by their coefficients — `δ` multiplies the coefficient of `tᵐ` by `m`,
and `δ̃` applies `δ` to each coefficient of a polynomial in `x` — rather than through Mathlib's
`Derivation` bundling, because the Leibniz rule is proved here by induction on monomials and
nothing downstream consumes the bundled form.

The argument is a parity count.  Taking the coefficient of `x⁰` in `a² p = t` and using
`x ∣ δ̃ p` leaves `α² P = t` in `ℚ[t,t⁻¹]` with `δ P = 0`, so `P` is a constant `c`; clearing
denominators with `LaurentPolynomial.exists_T_pow` turns this into `f² c = X^{2n+1}` in `ℚ[X]`,
which no `f` satisfies since the degree of a square is even.

## References

* [Stacks Project, Tag 0C6S](https://stacks.math.columbia.edu/tag/0C6S)
-/

@[expose] public noncomputable section

open Polynomial LaurentPolynomial

namespace Stacks.Examples.TwistedDoubledLine

/-- The coefficient ring `R = ℚ[t, t⁻¹]` of the charts: the Laurent polynomial ring in the
invertible coordinate `t`, whose unit `t` is the global function of the counterexample. -/
abbrev Coeff : Type := LaurentPolynomial ℚ

/-- The chart ring `A = ℚ[t, t⁻¹][x]`: each of the two charts of the doubled line over
`ℚ[t, t⁻¹]` is `Spec A`, and the two are glued along the basic open of `x`. -/
abbrev Chart : Type := Polynomial Coeff

/-! ### The derivation `t ∂/∂t` and its coefficientwise extension -/

/-- The `ℚ`-derivation `t ∂/∂t` of `ℚ[t, t⁻¹]`: it multiplies the coefficient of `tᵐ` by `m`. -/
def gradeDeriv (f : Coeff) : Coeff :=
  .ofCoeff (Finsupp.onFinset f.coeff.support (fun m => (m : ℚ) * f.coeff m)
    fun _ hm => Finsupp.mem_support_iff.2 fun h => hm (by rw [h, mul_zero]))

/-- The coefficient of `tᵐ` in `gradeDeriv f` is `m` times the coefficient of `tᵐ` in `f`. -/
@[simp] theorem gradeDeriv_coeff (f : Coeff) (m : ℤ) :
    (gradeDeriv f).coeff m = (m : ℚ) * f.coeff m := rfl

/-- `gradeDeriv` is additive. -/
theorem gradeDeriv_add (f g : Coeff) : gradeDeriv (f + g) = gradeDeriv f + gradeDeriv g := by
  ext m
  simp [mul_add]

/-- `gradeDeriv` as an additive homomorphism, so that it commutes with finite sums. -/
def gradeDerivHom : Coeff →+ Coeff where
  toFun := gradeDeriv
  map_zero' := by ext m; simp
  map_add' := gradeDeriv_add

/-- The additive homomorphism `gradeDerivHom` is `gradeDeriv`. -/
@[simp] theorem gradeDerivHom_apply (f : Coeff) : gradeDerivHom f = gradeDeriv f := rfl

/-- `gradeDeriv` vanishes at zero. -/
@[simp] theorem gradeDeriv_zero : gradeDeriv 0 = 0 := map_zero gradeDerivHom

/-- `t ∂/∂t` sends the monomial `a tᵐ` to `m a tᵐ`. -/
theorem gradeDeriv_C_mul_T (a : ℚ) (m : ℤ) :
    gradeDeriv (LaurentPolynomial.C a * T m) = LaurentPolynomial.C ((m : ℚ) * a) * T m := by
  ext k
  rw [gradeDeriv_coeff, ← single_eq_C_mul_T, ← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

/-- `t ∂/∂t` kills the constant `1`. -/
@[simp] theorem gradeDeriv_one : gradeDeriv (1 : Coeff) = 0 := by
  rw [show (1 : Coeff) = LaurentPolynomial.C 1 * T 0 by simp, gradeDeriv_C_mul_T]
  simp

/-- Monomials multiply by adding exponents and multiplying coefficients. -/
private theorem C_mul_T_mul_C_mul_T {R : Type*} [CommRing R] (a b : R) (m n : ℤ) :
    LaurentPolynomial.C a * T m * (LaurentPolynomial.C b * T n) =
      LaurentPolynomial.C (a * b) * T (m + n) := by
  rw [T_add, map_mul]
  ring

/-- The Leibniz rule for an additive map on Laurent polynomials that acts on monomials by
`a tᵐ ↦ e a m tᵐ`, where `e` satisfies the Leibniz rule on monomials. -/
private theorem leibniz_of_C_mul_T {R : Type*} [CommRing R] (D : LaurentPolynomial R →
    LaurentPolynomial R) (e : R → ℤ → R) (hadd : ∀ f g, D (f + g) = D f + D g)
    (hmono : ∀ a m, D (LaurentPolynomial.C a * T m) = LaurentPolynomial.C (e a m) * T m)
    (he : ∀ a b m n, e (a * b) (m + n) = a * e b n + b * e a m) (f g : LaurentPolynomial R) :
    D (f * g) = f * D g + g * D f := by
  induction f using LaurentPolynomial.induction_on' with
  | add f₁ f₂ h₁ h₂ =>
    rw [add_mul, hadd, h₁, h₂, hadd]
    ring
  | C_mul_T m a =>
    induction g using LaurentPolynomial.induction_on' with
    | add g₁ g₂ h₁ h₂ =>
      rw [mul_add, hadd, h₁, h₂, hadd]
      ring
    | C_mul_T n b =>
      rw [C_mul_T_mul_C_mul_T, hmono, hmono, hmono, C_mul_T_mul_C_mul_T, C_mul_T_mul_C_mul_T,
        add_comm n m, ← add_mul, ← map_add, he]

/-- The Leibniz rule for `t ∂/∂t`: this is what makes the twist of the thickening below a ring
automorphism. -/
theorem gradeDeriv_mul (f g : Coeff) :
    gradeDeriv (f * g) = f * gradeDeriv g + g * gradeDeriv f :=
  leibniz_of_C_mul_T gradeDeriv (fun a m => (m : ℚ) * a) gradeDeriv_add gradeDeriv_C_mul_T
    (fun a b m n => by push_cast; ring) f g

/-- The coefficientwise extension `δ̃` of `t ∂/∂t` to `ℚ[t, t⁻¹][x]`. -/
def coeffDeriv (p : Chart) : Chart :=
  ∑ j ∈ p.support, Polynomial.C (gradeDeriv (p.coeff j)) * Polynomial.X ^ j

/-- The coefficient of `xʲ` in `coeffDeriv p` is `gradeDeriv` of the coefficient of `xʲ` in
`p`. -/
@[simp] theorem coeffDeriv_coeff (p : Chart) (j : ℕ) :
    (coeffDeriv p).coeff j = gradeDeriv (p.coeff j) := by
  classical
  rw [coeffDeriv, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j (fun i _ hij => ?_) (fun hj => ?_)]
  · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hij]
  · rw [Polynomial.notMem_support_iff] at hj
    simp [hj]

/-- `coeffDeriv` is additive. -/
theorem coeffDeriv_add (p q : Chart) : coeffDeriv (p + q) = coeffDeriv p + coeffDeriv q := by
  ext j
  simp [gradeDeriv_add]

/-- The Leibniz rule for the coefficientwise extension: with it, `x⁻¹ δ̃` is a derivation of
`ℚ[t,t⁻¹][x, x⁻¹]`, which is what the twist of the thickening is built from. -/
theorem coeffDeriv_mul (p q : Chart) :
    coeffDeriv (p * q) = p * coeffDeriv q + q * coeffDeriv p := by
  rw [mul_comm q (coeffDeriv p)]
  refine Polynomial.ext fun j => ?_
  rw [coeffDeriv_coeff, Polynomial.coeff_mul, Polynomial.coeff_add, Polynomial.coeff_mul,
    Polynomial.coeff_mul, ← Finset.sum_add_distrib, ← gradeDerivHom_apply,
    map_sum gradeDerivHom]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [gradeDerivHom_apply, gradeDeriv_mul, coeffDeriv_coeff, coeffDeriv_coeff]
  ring

/-! ### The counterexample -/

/-- A Laurent polynomial killed by `t ∂/∂t` is a constant. -/
theorem eq_C_of_gradeDeriv_eq_zero {P : Coeff} (hP : gradeDeriv P = 0) :
    P = LaurentPolynomial.C (P.coeff 0) := by
  ext m
  have h : (m : ℚ) * P.coeff m = 0 := by rw [← gradeDeriv_coeff, hP]; rfl
  rw [← single_eq_C (P.coeff 0)]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rcases eq_or_ne (0 : ℤ) m with rfl | hm
  · rw [ite_eq_left rfl]
  · rw [ite_eq_right hm]
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd (Int.cast_injective (α := ℚ) (by rw [h', Int.cast_zero])) (Ne.symm hm)
    · exact h'

/-- **The counterexample to [Stacks, Tag 0C6S] as stated.**  No square times a global function
of the twisted thickening is the unit `t`: there are no `a p : ℚ[t,t⁻¹][x]` with `x ∣ δ̃ p` and
`a² p = t`.  By the module docstring, `p` ranges over exactly the restrictions to `X` of the
global functions of `X'`, so the invertible global function `t` on the doubled line `X` is not a
square times the restriction of an invertible global function on the thickening `X'`, which is
the failure of `Stacks.Thickenings.GlobalUnitsPowerLift` for `n = 2`. -/
theorem not_exists_sq_mul_dvd_coeffDeriv :
    ¬ ∃ a p : Chart, Polynomial.X ∣ coeffDeriv p ∧ a ^ 2 * p = Polynomial.C (T 1) := by
  rintro ⟨a, p, hdvd, hap⟩
  -- Take the coefficient of `x⁰`: the identity `a² p = t` becomes `α² P = t` in `ℚ[t,t⁻¹]`.
  have hcoeff : a.coeff 0 ^ 2 * p.coeff 0 = (T 1 : Coeff) := by
    have h := congrArg (fun q : Chart => q.coeff 0) hap
    simpa [pow_two, Polynomial.mul_coeff_zero] using h
  -- The twist condition says that `P` is killed by `t ∂/∂t`, hence is a constant `c`.
  have hP0 : gradeDeriv (p.coeff 0) = 0 := by
    rw [Polynomial.X_dvd_iff, coeffDeriv_coeff] at hdvd
    exact hdvd
  obtain ⟨c, hc⟩ : ∃ c : ℚ, p.coeff 0 = LaurentPolynomial.C c :=
    ⟨_, eq_C_of_gradeDeriv_eq_zero hP0⟩
  have hT : (T 1 : Coeff) ≠ 0 := fun h => by
    have hbot := LaurentPolynomial.degree_eq_bot_iff.2 h
    rw [LaurentPolynomial.degree_T] at hbot
    exact WithBot.coe_ne_bot hbot
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [hc, show (LaurentPolynomial.C (0 : ℚ) : Coeff) = 0 from map_zero _, mul_zero] at hcoeff
    exact hT hcoeff.symm
  -- Clear denominators: `α = f / tⁿ` for a polynomial `f`, and the identity becomes an identity
  -- of polynomials in which a square equals an odd power of `X`.
  obtain ⟨n, f, hf⟩ := LaurentPolynomial.exists_T_pow (a.coeff 0)
  have key : (f ^ 2 * Polynomial.C c : Polynomial ℚ) = Polynomial.X ^ (2 * n + 1) := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow, hf, mul_pow, T_pow,
      show a.coeff 0 ^ 2 * T ((2 : ℕ) * (n : ℤ)) * LaurentPolynomial.C c =
        a.coeff 0 ^ 2 * LaurentPolynomial.C c * T ((2 : ℕ) * (n : ℤ)) by ring,
      ← hc, hcoeff, ← T_add]
    push_cast
    ring_nf
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_pow (two_ne_zero), zero_mul] at key
    exact pow_ne_zero _ Polynomial.X_ne_zero key.symm
  have hdeg := congrArg Polynomial.natDegree key
  rw [Polynomial.natDegree_mul (pow_ne_zero 2 hf0) (Polynomial.C_ne_zero.2 hc0),
    Polynomial.natDegree_pow, Polynomial.natDegree_C, Polynomial.natDegree_X_pow] at hdeg
  omega

/-! ### The overlap ring, its square-zero extension and the twist -/

/-- The overlap ring `B = ℚ[t, t⁻¹][x, x⁻¹]`: the two charts of the doubled line are glued along
`Spec B`, and `Polynomial.toLaurent : A ⟶ B` is the localisation of the chart ring at `x`. -/
abbrev Overlap : Type := LaurentPolynomial Coeff

/-- The coefficientwise extension of `t ∂/∂t` to the overlap ring `B`. -/
def lcoeffDeriv (b : Overlap) : Overlap :=
  .ofCoeff (Finsupp.onFinset b.coeff.support (fun j => gradeDeriv (b.coeff j))
    fun _ hm => Finsupp.mem_support_iff.2 fun h => hm (by rw [h, gradeDeriv_zero]))

/-- The coefficient of `xʲ` in `lcoeffDeriv b` is `gradeDeriv` of the coefficient of `xʲ` in
`b`. -/
@[simp] theorem lcoeffDeriv_coeff (b : Overlap) (j : ℤ) :
    (lcoeffDeriv b).coeff j = gradeDeriv (b.coeff j) := rfl

/-- `lcoeffDeriv` is additive. -/
theorem lcoeffDeriv_add (b c : Overlap) :
    lcoeffDeriv (b + c) = lcoeffDeriv b + lcoeffDeriv c := by
  ext j
  simp [gradeDeriv_add]

/-- `lcoeffDeriv` vanishes at zero. -/
@[simp] theorem lcoeffDeriv_zero : lcoeffDeriv 0 = 0 := by ext j; simp

/-- `lcoeffDeriv` sends the monomial `a xᵐ` to `(gradeDeriv a) xᵐ`. -/
theorem lcoeffDeriv_C_mul_T (a : Coeff) (m : ℤ) :
    lcoeffDeriv (LaurentPolynomial.C a * T m) = LaurentPolynomial.C (gradeDeriv a) * T m := by
  ext k
  rw [lcoeffDeriv_coeff, ← single_eq_C_mul_T, ← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · rfl
  · rw [gradeDeriv_zero]

/-- The Leibniz rule on the overlap ring: `x⁻¹ δ̃` is therefore a derivation of `B`, which is
what makes the twist `twist` below a ring automorphism. -/
theorem lcoeffDeriv_mul (b c : Overlap) :
    lcoeffDeriv (b * c) = b * lcoeffDeriv c + c * lcoeffDeriv b :=
  leibniz_of_C_mul_T lcoeffDeriv (fun a _ => gradeDeriv a) lcoeffDeriv_add lcoeffDeriv_C_mul_T
    (fun a b _ _ => gradeDeriv_mul a b) b c

/-- `coeffDeriv` sends the monomial `a xⁿ` to `(gradeDeriv a) xⁿ`. -/
theorem coeffDeriv_C_mul_X_pow (a : Coeff) (n : ℕ) :
    coeffDeriv (Polynomial.C a * Polynomial.X ^ n) =
      Polynomial.C (gradeDeriv a) * Polynomial.X ^ n := by
  refine Polynomial.ext fun k => ?_
  rw [coeffDeriv_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with h
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, gradeDeriv_zero]

/-- The two coefficientwise derivations agree on the chart ring inside the overlap ring. -/
theorem lcoeffDeriv_toLaurent (p : Chart) :
    lcoeffDeriv (Polynomial.toLaurent p) = Polynomial.toLaurent (coeffDeriv p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, lcoeffDeriv_add, hp, hq, coeffDeriv_add, map_add]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow,
      lcoeffDeriv_C_mul_T, coeffDeriv_C_mul_X_pow, Polynomial.toLaurent_C_mul_X_pow]

/-- The square-zero extension `B' = B[ε]` of the overlap ring: the thickening `X'` is glued from
two copies of `Spec A[ε]` along `Spec B'`. -/
abbrev DualOverlap : Type := DualNumber Overlap

@[simp] private theorem fst_mk (a b : Overlap) : TrivSqZeroExt.fst ((a, b) : DualOverlap) = a :=
  rfl

@[simp] private theorem snd_mk (a b : Overlap) : TrivSqZeroExt.snd ((a, b) : DualOverlap) = b :=
  rfl

/-- `lcoeffDeriv` kills the constant `1`. -/
@[simp] theorem lcoeffDeriv_one : lcoeffDeriv (1 : Overlap) = 0 := by
  rw [show (1 : Overlap) = LaurentPolynomial.C 1 * T 0 by simp, lcoeffDeriv_C_mul_T]
  simp

/-- The twist `b₀ + ε b₁ ↦ b₀ + ε (b₁ + x⁻¹ δ̃ b₀)` of the overlap ring of the thickening: the
gluing isomorphism of `X'`, as a function. -/
def twistFun (z : DualOverlap) : DualOverlap := (z.fst, z.snd + T (-1) * lcoeffDeriv z.fst)

/-- The twist does not change the `ε`-free part. -/
@[simp] theorem twistFun_fst (z : DualOverlap) : (twistFun z).fst = z.fst := rfl

/-- The `ε`-part of the twist of `b₀ + ε b₁` is `b₁ + x⁻¹ δ̃ b₀`. -/
@[simp] theorem twistFun_snd (z : DualOverlap) :
    (twistFun z).snd = z.snd + T (-1) * lcoeffDeriv z.fst := rfl

/-- The inverse of the twist, which subtracts `x⁻¹ δ̃` instead of adding it. -/
def twistInvFun (z : DualOverlap) : DualOverlap := (z.fst, z.snd - T (-1) * lcoeffDeriv z.fst)

/-- The inverse twist does not change the `ε`-free part. -/
@[simp] theorem twistInvFun_fst (z : DualOverlap) : (twistInvFun z).fst = z.fst := rfl

/-- The `ε`-part of the inverse twist of `b₀ + ε b₁` is `b₁ - x⁻¹ δ̃ b₀`. -/
@[simp] theorem twistInvFun_snd (z : DualOverlap) :
    (twistInvFun z).snd = z.snd - T (-1) * lcoeffDeriv z.fst := rfl

/-- **The gluing isomorphism of the thickening `X'`**: the twist
`b₀ + ε b₁ ↦ b₀ + ε (b₁ + x⁻¹ δ̃ b₀)` of `B' = B[ε]` is a ring homomorphism, by the Leibniz rule
for `δ̃`; it is bijective by `Stacks.Examples.TwistedDoubledLine.twist_bijective` and the
identity modulo `ε`, so it is a gluing datum for a first-order thickening of the doubled
line. -/
def twist : DualOverlap →+* DualOverlap where
  toFun := twistFun
  map_one' := TrivSqZeroExt.ext (by simp [TrivSqZeroExt.fst_one])
    (by simp [TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one])
  map_zero' := TrivSqZeroExt.ext (by simp) (by simp)
  map_add' z w := TrivSqZeroExt.ext (by simp [TrivSqZeroExt.fst_add]) (by
    simp only [twistFun_snd, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, lcoeffDeriv_add,
      mul_add]
    ring)
  map_mul' z w := TrivSqZeroExt.ext (by simp [TrivSqZeroExt.fst_mul]) (by
    simp only [twistFun_snd, TrivSqZeroExt.fst_mul, DualNumber.snd_mul, twistFun_fst,
      lcoeffDeriv_mul, mul_add]
    ring)

/-- The ring homomorphism `twist` is the function `twistFun`. -/
@[simp] theorem twist_apply (z : DualOverlap) : twist z = twistFun z := rfl

/-- The twist is bijective, so it is an automorphism of `B'` and glues the two charts of the
thickening into a scheme. -/
theorem twist_bijective : Function.Bijective twist := by
  refine Function.bijective_iff_has_inverse.2 ⟨twistInvFun, fun z => ?_, fun z => ?_⟩
  · refine TrivSqZeroExt.ext rfl ?_
    rw [twistInvFun_snd, twist_apply, twistFun_snd, twistFun_fst]
    ring
  · refine TrivSqZeroExt.ext rfl ?_
    rw [twist_apply, twistFun_snd, twistInvFun_snd, twistInvFun_fst]
    ring

/-- The inclusion of the chart ring `A' = A[ε]` of the thickening into its overlap ring
`B' = B[ε]`, as a function: the localisation at `x` in each `ε`-component. -/
def dualToOverlapFun (c : DualNumber Chart) : DualOverlap :=
  (Polynomial.toLaurent c.fst, Polynomial.toLaurent c.snd)

/-- The `ε`-free part of `dualToOverlapFun c` is the image of the `ε`-free part of `c`. -/
@[simp] theorem dualToOverlapFun_fst (c : DualNumber Chart) :
    (dualToOverlapFun c).fst = Polynomial.toLaurent c.fst := rfl

/-- The `ε`-part of `dualToOverlapFun c` is the image of the `ε`-part of `c`. -/
@[simp] theorem dualToOverlapFun_snd (c : DualNumber Chart) :
    (dualToOverlapFun c).snd = Polynomial.toLaurent c.snd := rfl

/-- The chart ring of the thickening, `A' = A[ε]`, included in the overlap ring `B' = B[ε]` by
the localisation at `x` in each `ε`-component. -/
def dualToOverlap : DualNumber Chart →+* DualOverlap where
  toFun := dualToOverlapFun
  map_one' := TrivSqZeroExt.ext (by simp [TrivSqZeroExt.fst_one])
    (by simp [TrivSqZeroExt.snd_one])
  map_zero' := TrivSqZeroExt.ext (by simp) (by simp)
  map_add' c d := TrivSqZeroExt.ext
    (by simp [TrivSqZeroExt.fst_add]) (by simp [TrivSqZeroExt.snd_add])
  map_mul' c d := TrivSqZeroExt.ext
    (by simp [TrivSqZeroExt.fst_mul])
    (by simp [map_add, map_mul])

/-- The ring homomorphism `dualToOverlap` is the function `dualToOverlapFun`. -/
@[simp] theorem dualToOverlap_apply (c : DualNumber Chart) :
    dualToOverlap c = dualToOverlapFun c := rfl

/-- **The counterexample to [Stacks, Tag 0C6S] as stated, in the Čech description of the
thickening.**  A global function on `X'` is a pair `(c₀, c₁)` of elements of `A' = A[ε]`
identified over `B' = B[ε]` by the gluing twist, and its restriction to the doubled line `X` is
`c₀ mod ε`.  No such restriction is `t` divided by a square: the invertible global function `t`
on `X` is not a square times the restriction of an invertible global function on `X'`, which is
the failure of `Stacks.Thickenings.GlobalUnitsPowerLift` for this thickening and `n = 2`. -/
theorem not_exists_sq_mul_fst_of_twist_eq :
    ¬ ∃ (a : Chart) (c₀ c₁ : DualNumber Chart),
        twist (dualToOverlap c₀) = dualToOverlap c₁ ∧ a ^ 2 * c₀.fst = Polynomial.C (T 1) := by
  rintro ⟨a, c₀, c₁, hglue, hap⟩
  refine not_exists_sq_mul_dvd_coeffDeriv ⟨a, c₀.fst, ?_, hap⟩
  -- The `ε`-part of the gluing condition says that `x⁻¹ δ̃ (c₀ mod ε)` has no pole, i.e. that
  -- `x` divides `δ̃ (c₀ mod ε)`.
  have hsnd : Polynomial.toLaurent c₀.snd +
      T (-1) * Polynomial.toLaurent (coeffDeriv c₀.fst) = Polynomial.toLaurent c₁.snd := by
    have h : (twistFun (dualToOverlapFun c₀)).snd = (dualToOverlapFun c₁).snd := by
      have h' := congrArg TrivSqZeroExt.snd hglue
      rwa [dualToOverlap_apply, dualToOverlap_apply, twist_apply] at h'
    rwa [twistFun_snd, dualToOverlapFun_fst, dualToOverlapFun_snd, dualToOverlapFun_snd,
      lcoeffDeriv_toLaurent] at h
  refine ⟨c₁.snd - c₀.snd, Polynomial.toLaurent_injective ?_⟩
  rw [map_mul, Polynomial.toLaurent_X, map_sub, ← hsnd]
  rw [show Polynomial.toLaurent c₀.snd + T (-1) * Polynomial.toLaurent (coeffDeriv c₀.fst) -
      Polynomial.toLaurent c₀.snd = T (-1) * Polynomial.toLaurent (coeffDeriv c₀.fst) by ring,
    ← mul_assoc, ← T_add]
  simp

end Stacks.Examples.TwistedDoubledLine

end
