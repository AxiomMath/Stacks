module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PrincipalWeilDivisorRationalFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisorClassGroup

/-!
# The Weil divisor class group of a locally Noetherian integral algebraic space

Let `X` be a locally Noetherian integral algebraic space over a scheme `S`. **Stacks 0ENR**
defines the *Weil divisor class group* `Cl(X)` of `X` as the quotient of the group `Div(X)` of
Weil divisors by the subgroup of principal Weil divisors, the divisors `div(f)` of the
invertible rational functions `f ∈ R(X)^*`; these form a subgroup because `div` is additive,
which is Stacks 0ENQ.

This file makes that definition with the source's hypotheses and nothing else: `X` is an
algebraic space, integral and locally Noetherian. The principal divisor `div(f)` is
`AlgebraicGeometry.Space.divRationalFunction` of Stacks 0ENP, whose coefficients are the orders
of vanishing `AlgebraicGeometry.Space.ordRationalFunction` of Stacks 0ENL, read along the
canonical embedding `AlgebraicGeometry.Space.genericFractionEmbedding` of Stacks 0ENK.

## Main definitions

* `AlgebraicGeometry.Space.principalWeilDivisors`: the subgroup of principal Weil divisors, the
  range of the group homomorphism `div : R(X)^* → Div(X)`.
* `AlgebraicGeometry.Space.weilDivisorClassGroup`: **Stacks 0ENR**, `Cl(X) = Div(X) / P(X)`.

## Main results

* `AlgebraicGeometry.Space.mem_principalWeilDivisors_iff`: a Weil divisor is principal exactly
  when it is `div(f)` for some `f ∈ R(X)^*`.
* `AlgebraicGeometry.Space.weilDivisorClassGroup_mk_eq_zero_iff`: the class of a Weil divisor
  vanishes exactly when the divisor is principal.
* `AlgebraicGeometry.Space.principalWeilDivisors_eq_genericFractionEmbedding`: the subgroup of
  principal Weil divisors is the subgroup
  `AlgebraicGeometry.Space.GenericFractionEmbedding.principalWeilDivisors` at the canonical
  embedding, so `Cl(X)` is identified, by
  `AlgebraicGeometry.Space.weilDivisorClassGroupEquivGenericFractionEmbedding`, with the class
  group `AlgebraicGeometry.Space.GenericFractionEmbedding.weilDivisorClassGroup` of that
  embedding, and results stated for the latter apply to `Cl(X)`.

## Implementation notes

The subgroup of principal divisors is the range of
`AlgebraicGeometry.Space.divRationalFunctionHom`, the additive form of the homomorphism
`f ↦ div(f)` on the unit group `R(X)^*`. Its being a group homomorphism is Stacks 0ENQ, so the
range is a subgroup with no closure taken, exactly as the source observes.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0ENQ](https://stacks.math.columbia.edu/tag/0ENQ)
* [Stacks Project, Tag 0ENR](https://stacks.math.columbia.edu/tag/0ENR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))

/-- The subgroup of *principal Weil divisors* of a locally Noetherian integral algebraic space
`X`: the image of the homomorphism `div : R(X)^* → Div(X)`, `f ↦ div(f)`. -/
def principalWeilDivisors : AddSubgroup ↥(WeilDivisor B S hS X) :=
  (divRationalFunctionHom B S hS hX hInt hN).range

/-- A Weil divisor is principal exactly when it is the divisor `div(f)` of an invertible
rational function `f`. -/
theorem mem_principalWeilDivisors_iff (D : ↥(WeilDivisor B S hS X)) :
    D ∈ principalWeilDivisors B S hS hX hInt hN ↔
      ∃ f : (rationalFunctions B S hS hX)ˣ, divRationalFunction B S hS hX hInt hN f = D := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.toMul, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨Additive.ofMul f, rfl⟩

/-- The divisor of an invertible rational function is a principal Weil divisor. -/
theorem divRationalFunction_mem_principalWeilDivisors (f : (rationalFunctions B S hS hX)ˣ) :
    divRationalFunction B S hS hX hInt hN f ∈ principalWeilDivisors B S hS hX hInt hN :=
  ⟨Additive.ofMul f, rfl⟩

/-- **Stacks 0ENR.** The *Weil divisor class group* `Cl(X)` of a locally Noetherian integral
algebraic space `X` over `S`: the quotient of the group `Div(X)` of Weil divisors by the
subgroup of principal Weil divisors `div(f)`, `f ∈ R(X)^*`. -/
@[stacks 0ENR "Cl(X) = Div(X) / {div(f) : f ∈ R(X)^*}, at the source's hypotheses only: the \
  principal divisors are the range of the homomorphism div of Stacks 0ENP and 0ENQ, built from \
  the canonical order of vanishing"]
abbrev weilDivisorClassGroup : Type (u + 1) :=
  ↥(WeilDivisor B S hS X) ⧸ principalWeilDivisors B S hS hX hInt hN

/-- The class in `Cl(X)` of a Weil divisor vanishes exactly when the divisor is principal. -/
theorem weilDivisorClassGroup_mk_eq_zero_iff (D : ↥(WeilDivisor B S hS X)) :
    (D : weilDivisorClassGroup B S hS hX hInt hN) = 0 ↔
      ∃ f : (rationalFunctions B S hS hX)ˣ, divRationalFunction B S hS hX hInt hN f = D := by
  rw [QuotientAddGroup.eq_zero_iff, mem_principalWeilDivisors_iff]

/-- Two Weil divisors have the same class in `Cl(X)` exactly when they differ by a principal
divisor. -/
theorem weilDivisorClassGroup_mk_eq_mk_iff (D D' : ↥(WeilDivisor B S hS X)) :
    (D : weilDivisorClassGroup B S hS hX hInt hN) = D' ↔
      ∃ f : (rationalFunctions B S hS hX)ˣ,
        divRationalFunction B S hS hX hInt hN f = -D + D' := by
  rw [QuotientAddGroup.eq, mem_principalWeilDivisors_iff]

/-- The subgroup of principal Weil divisors is the subgroup of principal divisors of the
canonical embedding `AlgebraicGeometry.Space.genericFractionEmbedding` of Stacks 0ENK. -/
theorem principalWeilDivisors_eq_genericFractionEmbedding :
    principalWeilDivisors B S hS hX hInt hN =
      (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).principalWeilDivisors := by
  ext D
  rw [mem_principalWeilDivisors_iff, GenericFractionEmbedding.mem_principalWeilDivisors_iff]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, Subtype.ext hf.symm⟩

/-- The Weil divisor class group `Cl(X)` is the class group of the canonical embedding
`AlgebraicGeometry.Space.genericFractionEmbedding` of Stacks 0ENK: the identity of `Div(X)`
descends to an isomorphism of the quotients. -/
def weilDivisorClassGroupEquivGenericFractionEmbedding :
    weilDivisorClassGroup B S hS hX hInt hN ≃+
      (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).weilDivisorClassGroup :=
  QuotientAddGroup.quotientAddEquivOfEq
    (principalWeilDivisors_eq_genericFractionEmbedding B S hS hX hInt hN)

/-- The isomorphism with the class group of the canonical embedding sends the class of a Weil
divisor to its class. -/
@[simp]
theorem weilDivisorClassGroupEquivGenericFractionEmbedding_mk (D : ↥(WeilDivisor B S hS X)) :
    weilDivisorClassGroupEquivGenericFractionEmbedding B S hS hX hInt hN
        (D : weilDivisorClassGroup B S hS hX hInt hN) =
      (D : (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).weilDivisorClassGroup) :=
  rfl

end AlgebraicGeometry.Space

end
