module

public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.TwistStalk
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheaf

/-!
# Multiplication by a homogeneous polynomial on the twists of projective space over a base

Let `S` be a scheme and `n` a natural number. The twist `𝒪(d)` of `ℙⁿ_S` is the inverse image
along the projection `ℙⁿ_S ⟶ ℙⁿ_ℤ` of the degree-`d` twisting sheaf of the integral model, and on
the integral model a homogeneous `a ∈ ℤ[T₀, …, Tₙ]` of degree `k` acts by multiplication,

`𝒪(d) ⟶ 𝒪(k + d)`

(`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftIntOf`). Taking inverse images carries
that action to `ℙⁿ_S`, together with the composition law "multiplying by `a` and then by `b` is
multiplying by `b * a`". This file records the resulting maps and that law, and specialises them
to the monomials `T^e`, where the law becomes the addition of multidegrees.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `twistOverMulLeft`: **multiplication by a homogeneous polynomial of degree `k`,
  `𝒪(d) ⟶ 𝒪(e)` on `ℙⁿ_S`**, for any integer `e` equal to `k + d`.
* `MonomialIndex.add`: the sum of two multidegrees, of the sum of their total degrees.
* `twistOverMulMonomial`: **multiplication by the monomial `T^b`**, for a multidegree `b` of
  total degree `e₁`, as `𝒪(d) ⟶ 𝒪(g)` for any integer `g` equal to `e₁ + d`.

## Main results

* `twistOverMulLeft_comp`: **the multiplication maps compose by multiplying the polynomials.**
* `twistOverMulLeft_congr`: the map depends on the polynomial alone, not on the degree in which
  it is presented as homogeneous.
* `coordMonomial_add`: the monomial of a sum of multidegrees is the product of the monomials.
* `twistOverMulMonomial_comp`: **the monomial multiplication maps compose by adding the
  multidegrees.**

## Implementation notes

The target degree is a named integer together with an equation rather than the computed sum
`k + d`, exactly as in `twistMulLeftIntOf`, so that composites need no transport along an
associativity of degrees.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistMulLeftIntOf twistMulLeftIntOf_comp)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous polynomials of degree `k` in the homogeneous coordinate ring of the integral
model `ℙⁿ_ℤ`. -/
abbrev integralHomogeneous (n k : ℕ) : Type u :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) k

/-! ### Multiplication by a homogeneous polynomial -/

/-- **Multiplication by a homogeneous polynomial `a` of degree `k`, as a morphism
`𝒪(d) ⟶ 𝒪(e)` of twists on `ℙⁿ_S`**, where `e` is any integer equal to `k + d`. The twists are
the inverse images of the twists of the integral model, and this is the inverse image of
multiplication by `a` there. -/
def twistOverMulLeft (n : ℕ) (S : Scheme.{u}) {k : ℕ} (a : integralHomogeneous.{u} n k)
    (d e : ℤ) (he : (k : ℤ) + d = e) :
    twistOver n S d ⟶ twistOver n S e :=
  (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).map
    (twistMulLeftIntOf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) a d e he)

/-- **The multiplication maps on the twists of `ℙⁿ_S` compose by multiplying the polynomials**:
multiplication by `a` of degree `k` followed by multiplication by `b` of degree `l` is
multiplication by `b * a`, of degree `l + k`. -/
theorem twistOverMulLeft_comp (n : ℕ) (S : Scheme.{u}) {k l : ℕ}
    (a : integralHomogeneous.{u} n k) (b : integralHomogeneous.{u} n l) (d e g : ℤ)
    (he : (k : ℤ) + d = e) (hg : (l : ℤ) + e = g) :
    twistOverMulLeft n S a d e he ≫ twistOverMulLeft n S b e g hg =
      twistOverMulLeft n S
        (⟨(b : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) * (a : _),
          SetLike.mul_mem_graded b.2 a.2⟩ : integralHomogeneous.{u} n (l + k))
        d g (by push_cast; omega) :=
  by
  rw [twistOverMulLeft, twistOverMulLeft, twistOverMulLeft]
  exact ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).map_comp
    _ _).symm.trans (congrArg _ (twistMulLeftIntOf_comp _ a b d e g he hg))

/-- **Multiplication by a homogeneous polynomial depends on the polynomial alone.** The degree in
which it is presented as homogeneous is determined by the source and target degrees, so two
presentations with the same underlying polynomial give the same morphism. -/
theorem twistOverMulLeft_congr (n : ℕ) (S : Scheme.{u}) {k l : ℕ}
    (a : integralHomogeneous.{u} n k) (b : integralHomogeneous.{u} n l)
    (hab : (a : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) = (b : _))
    (d e : ℤ) (ha : (k : ℤ) + d = e) (hb : (l : ℤ) + d = e) :
    twistOverMulLeft n S a d e ha = twistOverMulLeft n S b d e hb := by
  have hkl : k = l := by omega
  subst hkl
  rw [show a = b from Subtype.ext hab]

/-! ### Multiplication by a monomial -/

/-- The sum of two multidegrees, of the sum of their total degrees. -/
def MonomialIndex.add {n : ℕ} {e₁ e₂ : ℤ} (b : MonomialIndex.{u} n e₁)
    (c : MonomialIndex.{u} n e₂) : MonomialIndex.{u} n (e₁ + e₂) :=
  ⟨b.1 + c.1, by
    rw [show (b.1 + c.1).degree = b.1.degree + c.1.degree from map_add Finsupp.degree _ _]
    push_cast
    rw [b.2, c.2]⟩

/-- **The monomial of a sum of multidegrees is the product of the two monomials.** -/
theorem coordMonomial_add {n : ℕ} {e₁ e₂ : ℤ} (b : MonomialIndex.{u} n e₁)
    (c : MonomialIndex.{u} n e₂) :
    coordMonomial (MonomialIndex.add b c) = coordMonomial c * coordMonomial b := by
  rw [coordMonomial, coordMonomial, coordMonomial, MvPolynomial.monomial_mul_monomial, mul_one]
  refine congrArg (fun z => MvPolynomial.monomial z (1 : ULift.{u} ℤ)) ?_
  show Finsupp.equivMapDomain Equiv.ulift (b.1 + c.1) =
    Finsupp.equivMapDomain Equiv.ulift c.1 + Finsupp.equivMapDomain Equiv.ulift b.1
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_add]
  exact add_comm _ _

/-- **Multiplication by the monomial `T^b` of a multidegree `b` of total degree `e₁`, as a
morphism `𝒪(d) ⟶ 𝒪(g)` of twists on `ℙⁿ_S`**, where `g` is any integer equal to `e₁ + d`. -/
def twistOverMulMonomial (n : ℕ) (S : Scheme.{u}) {e₁ : ℤ} (b : MonomialIndex.{u} n e₁)
    (d g : ℤ) (hg : e₁ + d = g) :
    twistOver n S d ⟶ twistOver n S g :=
  twistOverMulLeft n S ⟨coordMonomial b, coordMonomial_mem b⟩ d g (by rw [b.2]; exact hg)

/-- **The monomial multiplication maps on the twists of `ℙⁿ_S` compose by adding the
multidegrees.** -/
theorem twistOverMulMonomial_comp (n : ℕ) (S : Scheme.{u}) {e₁ e₂ : ℤ}
    (b : MonomialIndex.{u} n e₁) (c : MonomialIndex.{u} n e₂) (d g h : ℤ)
    (hg : e₁ + d = g) (hh : e₂ + g = h) :
    twistOverMulMonomial n S b d g hg ≫ twistOverMulMonomial n S c g h hh =
      twistOverMulMonomial n S (MonomialIndex.add b c) d h (by omega) := by
  rw [twistOverMulMonomial, twistOverMulMonomial, twistOverMulMonomial, twistOverMulLeft_comp]
  exact twistOverMulLeft_congr n S _ _ (coordMonomial_add b c).symm d h _ _

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
