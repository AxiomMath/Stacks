module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TwistAcyclicRange
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TwistMultiplication

/-!
# The monomial action of the polynomial algebra on the higher direct images of the twists

Let `S` be a scheme, let `n` be a natural number and let `f : ℙⁿ_S ⟶ S` be the structure
morphism. Multiplication by the monomial `T^b` of a multidegree `b` of total degree `e₁` is a
morphism `𝒪(d) ⟶ 𝒪(d + e₁)` of `𝒪_{ℙⁿ_S}`-modules
(`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverMulMonomial`), so a higher
direct image of it is a morphism of `𝒪_S`-modules

`Rᵠ f_* 𝒪(d) ⟶ Rᵠ f_* 𝒪(d + e₁)`,

for every degree `q` and over every base scheme. This file records those morphisms and the
composition law they inherit from the monomials: multiplying by `T^b` and then by `T^c` is
multiplying by `T^{b+c}`.

In the degree `q = n` this is the pairing of the degree-`n` row of the display of
[Stacks, Tag 01XW]. That row identifies `Rⁿ f_* 𝒪(d)` with the `𝒪_S`-dual of
`(𝒪_S[T₀, …, Tₙ])_{-n-1-d}`, and the identification is the pairing

`(b, ξ) ↦ T^b · ξ ∈ Rⁿ f_* 𝒪(-n-1) = 𝒪_S`

that the morphisms below give, `(𝒪_S[T₀, …, Tₙ])_{-n-1-d}` being free on the multidegrees `b` of
total degree `-n - 1 - d` and `d + (-n - 1 - d)` being `-n - 1`. The composition law is what makes
that pairing a pairing of modules over the polynomial algebra, and
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.dualBaseDegreeSheafZeroIso` identifies
the target at `d = -n - 1` with `𝒪_S`.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `rightDerivedPlusMulMonomial`: **the action of the monomial `T^b` on the higher direct images
  of the twists**, `Rᵠ f_* 𝒪(d) ⟶ Rᵠ f_* 𝒪(g)` for any integer `g` equal to `e₁ + d`.

## Main results

* `rightDerivedPlusMulMonomial_comp`: **the monomial actions compose by adding the
  multidegrees.**

## Implementation notes

The target degree is a named integer together with an equation, as in `twistOverMulMonomial`, so
that composites need no transport along an associativity of degrees.

`CategoryTheory.HasDerivedCategory.standard` is installed as a local instance at priority `2000`,
as in the modules whose statements are composed here.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-- **The action of the monomial `T^b` on the higher direct images of the twists of `ℙⁿ_S`**: the
degree-`q` higher direct image along the structure morphism of multiplication by `T^b`,

`Rᵠ f_* 𝒪(d) ⟶ Rᵠ f_* 𝒪(g)`,

where `b` is a multidegree of total degree `e₁` and `g` is any integer equal to `e₁ + d`. -/
def rightDerivedPlusMulMonomial (n : ℕ) (S : Scheme.{u}) (q : ℤ) {e₁ : ℤ}
    (b : MonomialIndex.{u} n e₁) (d g : ℤ) (hg : e₁ + d = g) :
    ((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).rightDerivedPlus q).obj
        (twistOver n S d) ⟶
      ((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).rightDerivedPlus q).obj
        (twistOver n S g) :=
  ((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).rightDerivedPlus q).map
    (twistOverMulMonomial n S b d g hg)

/-- **The monomial actions on the higher direct images compose by adding the multidegrees.** -/
theorem rightDerivedPlusMulMonomial_comp (n : ℕ) (S : Scheme.{u}) (q : ℤ) {e₁ e₂ : ℤ}
    (b : MonomialIndex.{u} n e₁) (c : MonomialIndex.{u} n e₂) (d g h : ℤ)
    (hg : e₁ + d = g) (hh : e₂ + g = h) :
    rightDerivedPlusMulMonomial n S q b d g hg ≫ rightDerivedPlusMulMonomial n S q c g h hh =
      rightDerivedPlusMulMonomial n S q (MonomialIndex.add b c) d h (by omega) :=
  Eq.trans
    (((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).rightDerivedPlus q).map_comp
      (twistOverMulMonomial n S b d g hg) (twistOverMulMonomial n S c g h hh)).symm
    (congrArg (fun z => ((Scheme.Modules.pushforward
        (projectiveSpaceOver n S ↘ S)).rightDerivedPlus q).map z)
      (twistOverMulMonomial_comp n S b c d g h hg hh))

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
