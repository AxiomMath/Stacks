module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Tactic.LinearCombination
public import StacksFrontier.RingTheory.Kaehler.PerfectField

/-!
# Affine forms and derivations of a polynomial ring in two variables

Auxiliary algebra for the proof that a quadratic polynomial in the square of an ideal of
colength greater than one is a scalar multiple of the square of an affine linear polynomial:
affine linear forms `a + b x + c y` in `κ[x, y]`, the identities expressing a quadratic as a
scalar multiple of the square of such a form, derivations of `κ[x, y]` mapping `I ^ 2` into `I`,
and, in characteristic two, derivations of `κ` over `ZMod 2` detecting non-squares together
with the translations of the variables.

## Main results

* `MvPolynomial.pderiv_mem_of_mem_pow_two`: a partial derivative of an element of `I ^ 2` lies
  in `I`.

## Implementation notes

The polynomial ring `κ[x, y]` is represented by `MvPolynomial (Fin 2) κ`, with variables `X 0`
and `X 1`.

## References

* [Stacks Project, Tag 0BGD](https://stacks.math.columbia.edu/tag/0BGD)
-/

@[expose] public section

open MvPolynomial

namespace MvPolynomial

/-- The affine linear polynomial `a + b x + c y` in two variables. -/
private noncomputable def affineForm {k : Type*} [Field k] (a b c : k) : MvPolynomial (Fin 2) k :=
  MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0 +
    MvPolynomial.C c * MvPolynomial.X 1

/-- If the linear parts of `affineForm a b c` and `t • affineForm d e f` agree, their difference
is a constant. -/
private theorem affineForm_sub_scaled_eq_const {k : Type*} [Field k]
    (a b c d e f t : k) (h₁ : b = t * e) (h₂ : c = t * f) :
    affineForm a b c - MvPolynomial.C t * affineForm d e f =
      MvPolynomial.C (a - t * d) := by
  have h₁' : (MvPolynomial.C (σ := Fin 2) b : MvPolynomial (Fin 2) k) =
      MvPolynomial.C t * MvPolynomial.C e := by
    rw [← map_mul, h₁]
  have h₂' : (MvPolynomial.C (σ := Fin 2) c : MvPolynomial (Fin 2) k) =
      MvPolynomial.C t * MvPolynomial.C f := by
    rw [← map_mul, h₂]
  rw [affineForm, affineForm, h₁', h₂']
  simp only [map_sub, map_mul]
  ring

/-- An affine form all of whose coefficients are `s` times those of another is `s` times that
other form. -/
private theorem affineForm_eq_scaled_gen {k : Type*} [Field k]
    (a b c s u v w : k) (ha : a = s * u) (hb : b = s * v) (hc : c = s * w) :
    affineForm a b c = MvPolynomial.C s *
      (MvPolynomial.C u + MvPolynomial.C v * MvPolynomial.X (0 : Fin 2) +
        MvPolynomial.C w * MvPolynomial.X (1 : Fin 2)) := by
  rw [affineForm, ha, hb, hc]
  simp only [map_mul]
  ring

/-- If all coefficients of a quadratic except the constant one match those of
`j • (g + h x + i y) ^ 2`, the difference of the two polynomials is a constant. -/
private theorem quad_sub_square_eq_const {k : Type*} [Field k]
    (a b c d e f j g h i : k)
    (hb : b = 2 * j * g * h) (hc : c = 2 * j * g * i)
    (hd : d = j * h ^ 2) (he : e = 2 * j * h * i) (hf : f = j * i ^ 2) :
    (MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X (0 : Fin 2) +
      MvPolynomial.C c * MvPolynomial.X (1 : Fin 2) +
      MvPolynomial.C d * MvPolynomial.X (0 : Fin 2) ^ 2 +
      MvPolynomial.C e * MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) +
      MvPolynomial.C f * MvPolynomial.X (1 : Fin 2) ^ 2) -
    MvPolynomial.C j *
      (MvPolynomial.C g + MvPolynomial.C h * MvPolynomial.X (0 : Fin 2) +
        MvPolynomial.C i * MvPolynomial.X (1 : Fin 2)) ^ 2 =
      MvPolynomial.C (a - j * g ^ 2) := by
  rw [hb, hc, hd, he, hf]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- A quadratic whose six coefficients are the expansion of `j • (g + h x + i y) ^ 2` equals that
square. -/
private theorem quad_eq_affine_square {σ : Type*} {k : Type*} [Field k]
    (x y : σ) (a b c d e f j g h i : k)
    (ha : a = j * g ^ 2) (hb : b = 2 * j * g * h)
    (hc : c = 2 * j * g * i) (hd : d = j * h ^ 2)
    (he : e = 2 * j * h * i) (hf : f = j * i ^ 2) :
    MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X x +
      MvPolynomial.C c * MvPolynomial.X y + MvPolynomial.C d * MvPolynomial.X x ^ 2 +
      MvPolynomial.C e * MvPolynomial.X x * MvPolynomial.X y +
      MvPolynomial.C f * MvPolynomial.X y ^ 2 =
    MvPolynomial.C j *
      (MvPolynomial.C g + MvPolynomial.C h * MvPolynomial.X x +
        MvPolynomial.C i * MvPolynomial.X y) ^ 2 := by
  rw [ha, hb, hc, hd, he, hf]
  simp only [map_mul, map_pow, map_ofNat]
  ring

/-- The characteristic-two form of `quad_eq_affine_square`: with the cross terms vanishing, the
quadratic is still `j • (g + h x + i y) ^ 2`. -/
private theorem quad_eq_affine_square_char_two {σ : Type*} {k : Type*} [Field k]
    (x y : σ) (a b c d e f j g h i : k) (h2 : (2 : k) = 0)
    (hb : b = 0) (hc : c = 0) (he : e = 0)
    (ha : a = j * g ^ 2) (hd : d = j * h ^ 2) (hf : f = j * i ^ 2) :
    MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X x +
      MvPolynomial.C c * MvPolynomial.X y +
      MvPolynomial.C d * MvPolynomial.X x ^ 2 +
      MvPolynomial.C e * MvPolynomial.X x * MvPolynomial.X y +
      MvPolynomial.C f * MvPolynomial.X y ^ 2 =
    MvPolynomial.C j * (MvPolynomial.C g + MvPolynomial.C h * MvPolynomial.X x +
      MvPolynomial.C i * MvPolynomial.X y) ^ 2 := by
  apply quad_eq_affine_square x y a b c d e f j g h i ha
  · rw [hb, h2]; simp
  · rw [hc, h2]; simp
  · exact hd
  · rw [he, h2]; simp
  · exact hf

/-- A derivation of the polynomial ring maps `I ^ 2` into `I`. -/
private theorem derivation_mem_of_mem_sq {R : Type*} [CommSemiring R]
    {k : Type*} [CommRing k] [Algebra R k]
    (I : Ideal (MvPolynomial (Fin 2) k))
    (D : Derivation R (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k))
    {p : MvPolynomial (Fin 2) k} (hp : p ∈ I ^ 2) : D p ∈ I := by
  rw [pow_two] at hp
  induction hp using Submodule.mul_induction_on' with
  | mem_mul_mem p hp q hq =>
      rw [D.leibniz]
      exact I.add_mem (I.mul_mem_right _ hp) (I.mul_mem_right _ hq)
  | add p hp q hq ihp ihq =>
      simpa only [map_add] using I.add_mem ihp ihq

/-- A partial derivative of an element of `I ^ 2` lies in `I`. -/
private theorem pderiv_mem_of_mem_sq
    {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 2) k))
    {p : MvPolynomial (Fin 2) k} (hp : p ∈ I ^ 2) (i : Fin 2) :
    MvPolynomial.pderiv i p ∈ I :=
  derivation_mem_of_mem_sq I (MvPolynomial.pderiv i) hp

/-- A partial derivative of an element of `I ^ 2` lies in `I`. -/
public alias pderiv_mem_of_mem_pow_two := pderiv_mem_of_mem_sq

/-- Over a field of characteristic two, an element that is not a square is detected by some
`ZMod 2`-derivation. -/
private theorem exists_derivation_detecting_nonsquare {k : Type*} [Field k] [CharP k 2]
    [Algebra (ZMod 2) k]
    (z : k) (hz : ¬ ∃ r : k, r ^ 2 = z) :
    ∃ D : Derivation (ZMod 2) k k, D z ≠ 0 := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : PerfectField (ZMod 2) := inferInstance
  have hD : KaehlerDifferential.D (ZMod 2) k z ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ :=
      (KaehlerDifferential.D_eq_zero_iff_exists_pow_eq (k := ZMod 2) 2 z).mp h
    exact hz ⟨r, hr⟩
  let B := Module.Basis.ofVectorSpace k (KaehlerDifferential (ZMod 2) k)
  have hrepr : B.repr (KaehlerDifferential.D (ZMod 2) k z) ≠ 0 :=
    fun h => hD (B.repr.injective (by simpa using h))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hrepr
  refine ⟨(B.coord i).compDer (KaehlerDifferential.D (ZMod 2) k), ?_⟩
  change B.coord i (KaehlerDifferential.D (ZMod 2) k z) ≠ 0
  simpa only [B.coord_apply, Finsupp.zero_apply] using hi

/-- Transport a derivation along an algebra equivalence of its source and target. -/
private noncomputable def transportDerivation {R S A B : Type*}
    [CommSemiring R] [CommSemiring S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B]
    [IsScalarTower R S A] [IsScalarTower R S B]
    (e : A ≃ₐ[S] B) (D : Derivation R A A) : Derivation R B B := by
  let eR := e.restrictScalars R
  refine Derivation.mk' (eR.toLinearMap.comp (D.toLinearMap.comp eR.symm.toLinearMap)) ?_
  intro x y
  change eR (D (eR.symm (x * y))) =
    x • eR (D (eR.symm y)) + y • eR (D (eR.symm x))
  simp [D.leibniz]

/-- The derivation of `k[x, y]` that applies a given derivation of `k` coefficientwise and kills
the two variables. -/
private noncomputable def mvPolynomialCoeffDerivation {k : Type*} [Field k]
    [Algebra (ZMod 2) k] (D : Derivation (ZMod 2) k k) :
    Derivation (ZMod 2) (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k) := by
  let d₁ : Derivation (ZMod 2) (Polynomial k) (Polynomial k) :=
    PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs
  let d₂ : Derivation (ZMod 2) (Polynomial (Polynomial k))
      (Polynomial (Polynomial k)) :=
    PolynomialModule.equivPolynomialSelf.compDer d₁.mapCoeffs
  exact transportDerivation (Polynomial.Bivariate.equivMvPolynomial k) d₂

/-- The coefficientwise derivation acts on constants through the given derivation of `k`. -/
private theorem mvPolynomialCoeffDerivation_C {k : Type*} [Field k]
    [Algebra (ZMod 2) k] (D : Derivation (ZMod 2) k k) (a : k) :
    mvPolynomialCoeffDerivation D (MvPolynomial.C a) = MvPolynomial.C (D a) := by
  simp [mvPolynomialCoeffDerivation, transportDerivation,
    PolynomialModule.equivPolynomialSelf_apply_eq]

/-- The coefficientwise derivation kills the variables. -/
private theorem mvPolynomialCoeffDerivation_X {k : Type*} [Field k]
    [Algebra (ZMod 2) k] (D : Derivation (ZMod 2) k k) (i : Fin 2) :
    mvPolynomialCoeffDerivation D (MvPolynomial.X i) = 0 := by
  fin_cases i <;>
    simp [mvPolynomialCoeffDerivation, transportDerivation,
      PolynomialModule.equivPolynomialSelf_apply_eq]

/-- In characteristic two a derivation kills every square. -/
private theorem derivation_sq_eq_zero_char_two {k : Type*} [Field k] [CharP k 2]
    [Algebra (ZMod 2) k] (D : Derivation (ZMod 2) k k) (z : k) : D (z ^ 2) = 0 := by
  rw [pow_two, D.leibniz]
  calc
    z • D z + z • D z = (2 : k) • (z • D z) := (two_smul k (z • D z)).symm
    _ = 0 := by
      have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
      change (2 : k) * (z * D z) = 0
      rw [htwo]
      simp

/-- The square `D ∘ D` of a derivation, which is again a derivation when `2 = 0`. -/
private noncomputable def derivationSquare {R k : Type*} [CommRing R] [Field k]
    [Algebra R k] (D : Derivation R k k) (h2 : (2 : k) = 0) : Derivation R k k := by
  refine Derivation.mk' (D.toLinearMap.comp D.toLinearMap) ?_
  intro x y
  change D (D (x * y)) = x • D (D y) + y • D (D x)
  rw [D.leibniz]
  simp only [map_add]
  simp only [smul_eq_mul, D.leibniz]
  have hcross : D x * D y + D y * D x = 0 := by
    rw [mul_comm (D y) (D x), ← two_mul, h2, zero_mul]
  linear_combination hcross

/-- Membership in `I ^ 2` of a diagonal quadratic is preserved by dividing its coefficients by a
nonzero scalar. -/
private theorem scale_quad_mem {k : Type*} [Field k]
    (I : Ideal (MvPolynomial (Fin 2) k)) (a d f t : k) (_ht : t ≠ 0)
    (hmem : MvPolynomial.C a + MvPolynomial.C d * MvPolynomial.X (0 : Fin 2) ^ 2 +
      MvPolynomial.C f * MvPolynomial.X (1 : Fin 2) ^ 2 ∈ I ^ 2) :
    MvPolynomial.C (a / t) + MvPolynomial.C (d / t) * MvPolynomial.X (0 : Fin 2) ^ 2 +
      MvPolynomial.C (f / t) * MvPolynomial.X (1 : Fin 2) ^ 2 ∈ I ^ 2 := by
  have hs := (I ^ 2).mul_mem_left (MvPolynomial.C (t⁻¹)) hmem
  have heq : MvPolynomial.C (a / t) + MvPolynomial.C (d / t) *
      MvPolynomial.X (0 : Fin 2) ^ 2 +
      MvPolynomial.C (f / t) * MvPolynomial.X (1 : Fin 2) ^ 2 =
      MvPolynomial.C (t⁻¹) * (MvPolynomial.C a + MvPolynomial.C d *
        MvPolynomial.X (0 : Fin 2) ^ 2 +
        MvPolynomial.C f * MvPolynomial.X (1 : Fin 2) ^ 2) := by
    simp only [div_eq_mul_inv, map_mul]
    ring
  rwa [heq]

/-- The coefficientwise derivation applied to a diagonal quadratic acts on its three
coefficients. -/
private theorem mvPolynomialCoeffDerivation_quad {k : Type*} [Field k]
    [Algebra (ZMod 2) k] (D : Derivation (ZMod 2) k k) (a d f : k) :
    mvPolynomialCoeffDerivation D
        (MvPolynomial.C a + MvPolynomial.C d * MvPolynomial.X (0 : Fin 2) ^ 2 +
          MvPolynomial.C f * MvPolynomial.X (1 : Fin 2) ^ 2) =
        MvPolynomial.C (D a) + MvPolynomial.C (D d) * MvPolynomial.X (0 : Fin 2) ^ 2 +
        MvPolynomial.C (D f) * MvPolynomial.X (1 : Fin 2) ^ 2 := by
  have hterm : ∀ (c : k) (i : Fin 2), mvPolynomialCoeffDerivation D
      (MvPolynomial.C c * MvPolynomial.X i ^ 2) = MvPolynomial.C (D c) * MvPolynomial.X i ^ 2 := by
    intro c i
    rw [Derivation.leibniz, pow_two (MvPolynomial.X i), Derivation.leibniz,
      mvPolynomialCoeffDerivation_X, mvPolynomialCoeffDerivation_C]
    simp [smul_eq_mul, mul_comm]
  rw [map_add, map_add, mvPolynomialCoeffDerivation_C, hterm, hterm]

/-- In characteristic two, the ring endomorphism of `k[x, y]` translating the variables by `r`
and `s`. -/
private noncomputable def translateRingHom {k : Type*} [Field k] [CharP k 2] (r s : k) :
    MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k)
    (fun i => MvPolynomial.X i + MvPolynomial.C (if i = 0 then r else s))

/-- In characteristic two, translating the variables twice is the identity. -/
private theorem translateRingHom_involutive {k : Type*} [Field k] [CharP k 2]
    (r s : k) : Function.Involutive (translateRingHom r s) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a => simp [translateRingHom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      have hX : translateRingHom r s (translateRingHom r s (MvPolynomial.X i)) =
          MvPolynomial.X i := by
        simp only [translateRingHom, map_add, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
        have hz : (if i = 0 then r else s) + (if i = 0 then r else s) = 0 := by
          rw [← two_mul, show (2 : k) = 0 from CharP.cast_eq_zero k 2, zero_mul]
        have hc : (MvPolynomial.C (if i = 0 then r else s) : MvPolynomial (Fin 2) k) +
            MvPolynomial.C (if i = 0 then r else s) = 0 := by
          simpa only [map_add, map_zero] using congrArg MvPolynomial.C hz
        change MvPolynomial.X i + MvPolynomial.C (if i = 0 then r else s) +
          MvPolynomial.C (if i = 0 then r else s) = MvPolynomial.X i
        linear_combination hc
      simp only [RingHom.map_mul, hp, hX]
/-- In characteristic two, translation of the variables as a ring equivalence. -/
private noncomputable def translateRingEquiv {k : Type*} [Field k] [CharP k 2]
    (r s : k) : MvPolynomial (Fin 2) k ≃+* MvPolynomial (Fin 2) k where
  toFun := translateRingHom r s
  invFun := translateRingHom r s
  left_inv := translateRingHom_involutive r s
  right_inv := translateRingHom_involutive r s
  map_mul' := (translateRingHom r s).map_mul
  map_add' := (translateRingHom r s).map_add

end MvPolynomial
