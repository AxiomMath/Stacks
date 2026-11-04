module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleRationalFunctionUnitLocus

/-!
# The principal Weil divisor of a rational function, and Stacks 0ENQ

Let `X` be a locally Noetherian integral algebraic space over a scheme `S` and let
`f ∈ R(X)^*`. The *principal Weil divisor* of `f` is `div_X(f) = ∑ ord_Z(f) [Z]`, the sum over
the prime divisors `Z` of `X`; it is a Weil divisor because the prime divisors with
`ord_Z(f) ≠ 0` are locally finite, which is Stacks 0ENN. This is **Stacks 0ENP**. Its
additivity `div_X(fg) = div_X(f) + div_X(g)` in `Div(X)` is **Stacks 0ENQ**.

## Main definitions

* `AlgebraicGeometry.Space.divRationalFunction`: **Stacks 0ENP**, the principal Weil divisor
  `div_X(f)`, under the hypotheses of the source only.

## Main results

* `AlgebraicGeometry.Space.divRationalFunction_mul`: **Stacks 0ENQ**,
  `div_X(fg) = div_X(f) + div_X(g)` as Weil divisors on `X`.
* `AlgebraicGeometry.Space.divRationalFunction_one` and
  `AlgebraicGeometry.Space.divRationalFunction_inv`: `div_X(1) = 0` and
  `div_X(f⁻¹) = -div_X(f)`.
* `AlgebraicGeometry.Space.divRationalFunctionHom`: `div_X` as a homomorphism
  `R(X)^* → Div(X)`, whose range is the subgroup of principal Weil divisors.

## Implementation notes

The coefficient family is `AlgebraicGeometry.Space.ordRationalFunction` of Stacks 0ENL, which is
computed through the canonical embedding `AlgebraicGeometry.Space.genericFractionEmbedding` of
Stacks 0ENK, and its membership in `Div(X)` is
`AlgebraicGeometry.Space.ordRationalFunction_mem_weilDivisor`, proved from `f ∈ R(X)^*` alone.
`divRationalFunction` is kept reducible, as an `abbrev`, so that it *is*
`AlgebraicGeometry.Space.GenericFractionEmbedding.principalDivisor` at that canonical embedding
and that local finiteness, rather than a second notion with the same value. Decency is not a
further hypothesis: an integral algebraic space is decent by Stacks 0AD4.

## References

* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENN](https://stacks.math.columbia.edu/tag/0ENN)
* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0ENQ](https://stacks.math.columbia.edu/tag/0ENQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))

/-- **Stacks 0ENP.** The *principal Weil divisor* `div_X(f) = ∑ ord_Z(f) [Z]` of an invertible
rational function `f` on a locally Noetherian integral algebraic space `X`, the sum running over
the prime divisors `Z` of `X` and `ord_Z(f)` being the order of vanishing of Stacks 0ENL. It is
a Weil divisor by Stacks 0ENN, which is
`AlgebraicGeometry.Space.ordRationalFunction_mem_weilDivisor`. -/
@[stacks 0ENP "div_X(f) = ∑ ord_Z(f) [Z] as a Weil divisor, at the hypotheses of the source: \
  the order of vanishing is the canonical one of Stacks 0ENL and the local finiteness is Stacks \
  0ENN, both proved"]
abbrev divRationalFunction (f : (rationalFunctions B S hS hX)ˣ) : ↥(WeilDivisor B S hS X) :=
  (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).principalDivisor
    (ordRationalFunction_mem_weilDivisor B S hS hX hInt hN) f

/-- The coefficient family of `div_X(f)` is `Z ↦ ord_Z(f)`. -/
@[simp]
theorem coe_divRationalFunction (f : (rationalFunctions B S hS hX)ˣ) :
    ((divRationalFunction B S hS hX hInt hN f : ↥(WeilDivisor B S hS X)) :
        PrimeDivisor B S hS X → ℤ) =
      ordRationalFunction B S hS hX hInt hN f :=
  rfl

/-- The coefficient of `div_X(f)` at a prime divisor `Z` is `ord_Z(f)`. -/
theorem divRationalFunction_apply (f : (rationalFunctions B S hS hX)ˣ)
    (Z : PrimeDivisor B S hS X) :
    (divRationalFunction B S hS hX hInt hN f : PrimeDivisor B S hS X → ℤ) Z =
      ordRationalFunction B S hS hX hInt hN f Z :=
  rfl

/-- **Stacks 0ENQ.** Let `X` be a locally Noetherian integral algebraic space over `S` and let
`f, g ∈ R(X)^*`. Then `div_X(fg) = div_X(f) + div_X(g)` as Weil divisors on `X`.

As in the source this is the additivity of the order of vanishing,
`AlgebraicGeometry.Space.GenericFractionEmbedding.ord_mul_apply`, at every prime divisor. -/
@[stacks 0ENQ "div_X(fg) = div_X(f) + div_X(g) as Weil divisors on X, at the hypotheses of the \
  source only"]
theorem divRationalFunction_mul (f g : (rationalFunctions B S hS hX)ˣ) :
    divRationalFunction B S hS hX hInt hN (f * g) =
      divRationalFunction B S hS hX hInt hN f + divRationalFunction B S hS hX hInt hN g :=
  Subtype.ext <| funext fun Z =>
    (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).ord_mul_apply f g Z

/-- `div_X` as a homomorphism from `R(X)^*`, written additively, to `Div(X)`: Stacks 0ENQ
together with `div_X(1) = 0`. Its range is the subgroup of principal Weil divisors. -/
def divRationalFunctionHom : Additive (rationalFunctions B S hS hX)ˣ →+ ↥(WeilDivisor B S hS X) :=
  AddMonoidHom.mk' (fun f => divRationalFunction B S hS hX hInt hN f.toMul)
    fun f g => divRationalFunction_mul B S hS hX hInt hN f.toMul g.toMul

/-- The value of `div_X` as a homomorphism at `f` is `div_X(f)`. -/
@[simp]
theorem divRationalFunctionHom_apply (f : (rationalFunctions B S hS hX)ˣ) :
    divRationalFunctionHom B S hS hX hInt hN (Additive.ofMul f) =
      divRationalFunction B S hS hX hInt hN f :=
  rfl

/-- The coefficient family of `div_X` as a homomorphism at `f` is `Z ↦ ord_Z(f)`. -/
theorem coe_divRationalFunctionHom_apply (f : (rationalFunctions B S hS hX)ˣ) :
    ((divRationalFunctionHom B S hS hX hInt hN (Additive.ofMul f) : ↥(WeilDivisor B S hS X)) :
        PrimeDivisor B S hS X → ℤ) =
      ordRationalFunction B S hS hX hInt hN f :=
  rfl

/-- The principal Weil divisor of the constant function `1` is zero. -/
@[simp]
theorem divRationalFunction_one : divRationalFunction B S hS hX hInt hN 1 = 0 := by
  have h := divRationalFunction_mul B S hS hX hInt hN 1 1
  rw [one_mul] at h
  exact add_eq_left.mp h.symm

/-- The principal Weil divisor of `f⁻¹` is `-div_X(f)`. -/
@[simp]
theorem divRationalFunction_inv (f : (rationalFunctions B S hS hX)ˣ) :
    divRationalFunction B S hS hX hInt hN f⁻¹ = -divRationalFunction B S hS hX hInt hN f := by
  have h := divRationalFunction_mul B S hS hX hInt hN f f⁻¹
  rw [mul_inv_cancel, divRationalFunction_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The principal Weil divisor of `f / g` is `div_X(f) - div_X(g)`. -/
theorem divRationalFunction_div (f g : (rationalFunctions B S hS hX)ˣ) :
    divRationalFunction B S hS hX hInt hN (f / g) =
      divRationalFunction B S hS hX hInt hN f - divRationalFunction B S hS hX hInt hN g := by
  rw [div_eq_mul_inv, divRationalFunction_mul, divRationalFunction_inv, sub_eq_add_neg]

end AlgebraicGeometry.Space

end
