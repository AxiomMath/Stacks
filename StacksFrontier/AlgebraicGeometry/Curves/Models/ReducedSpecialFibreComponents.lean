module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The reduced special fibre of the canonical decomposition of `X_k`

Let `X ⟶ Spec(R)` be a regular proper model of a smooth projective curve over the fraction
field of a discrete valuation ring. The file
`StacksFrontier/AlgebraicGeometry/Curves/Models/ReducedSpecialFibre.lean` proves
[Stacks, Tag 0C67] for an arbitrary decomposition `X_k = Σ mᵢ Cᵢ` of the special fibre into
effective Cartier divisors, carried as hypotheses. This file is the same statement at the
*canonical* decomposition, the one Situation [Stacks, Tag 0C61] actually fixes: the family
`C₁, …, Cₙ` is the family of irreducible components of `X_k` with their reduced induced
structure, and `mᵢ` is the multiplicity of `Cᵢ` in `X_k`. With `d = gcd(m₁, …, mₙ)` and
`D = Σ (mᵢ/d) Cᵢ`:

`D` is an effective Cartier divisor, `𝒪_X(D)` has order dividing `d` in `Pic(X)`, and the
conormal module `𝒞_{D/X}` is an invertible `𝒪_D`-module of order dividing `d` in `Pic(D)`.

## Main results

* `Stacks.Models.isEffectiveCartierDivisor_reducedSpecialFibre_specialFiberComponents`: `D` is
  an effective Cartier divisor on the model.
* `Stacks.Models.reducedSpecialFibre_order_dvd_gcd_specialFiberComponents`: the four
  conclusions of Tag 0C67 at the canonical decomposition.
* `Stacks.Models.addOrderOf_picardClass_reducedSpecialFibre_specialFiberComponents_dvd` and
  `Stacks.Models.addOrderOf_picardClass_immersionConormalSheaf_specialFiberComponents_dvd`: the
  two torsion clauses in the literal form "the order divides `d`".

## Implementation notes

**No hypothesis is left standing.** The general statements take a finite index set `s`, a family
`C` of effective Cartier divisors, multiplicities `m`, the effectivity hypothesis
`∀ i ∈ s, IsEffectiveCartierDivisor (C i)` and the decomposition
`X_k = ∏ i ∈ s, C i ^ m i`. Here `s = Finset.univ` on
`irreducibleComponents S.specialFiber`, which is a `Fintype` by
`Stacks.Models.RegularModelSituation.fintypeIrreducibleComponentsSpecialFiber`,
`C = Stacks.Models.RegularModelSituation.specialFiberComponentIdeal`,
`m = Stacks.Models.RegularModelSituation.specialFiberMultiplicity`, the effectivity hypothesis is
discharged by part (2) of [Stacks, Tag 0C5Z]
(`Stacks.Models.RegularModelSituation.isEffectiveCartierDivisor_specialFiberComponent`) and the
decomposition by part (3)
(`Stacks.Models.RegularModelSituation.specialFiberIdeal_eq_prod`). Nothing beyond the standing
situation is assumed.

**The effective-Cartier instance on `D`.** The general statements also carry
`[IsEffectiveCartierDivisor (reducedSpecialFibre s C m)]`, without which the Picard class of `D`
cannot be written down. Here that instance is *derived* rather than assumed: the instance
`Stacks.Models.isEffectiveCartierDivisor_specialFiberComponentIdeal` is part (2) of
[Stacks, Tag 0C5Z], and `Stacks.Divisors.IsEffectiveCartierDivisor.finsetProdPow` turns it into
the instance on the product `∏ Z, Cᵢ ^ (mᵢ/d)`; both come from
`StacksFrontier/AlgebraicGeometry/Curves/Models/PicardSequence.lean`. This is why that file is the
import rather than `ReducedSpecialFibre.lean` alone.

**Beware the notation.** On `AlgebraicGeometry.Scheme.IdealSheafData` the sum of divisors is the
product `*` and the `n`-fold sum `nD` is the power `^`; Mathlib's `Add` is `⊔`, which is
scheme-theoretic intersection and is *not* divisor addition. So `Σ mᵢ Cᵢ` is written
`∏ Z, C Z ^ m Z`.

## References

* [Stacks Project, Tag 0C67](https://stacks.math.columbia.edu/tag/0C67)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.Divisors
open Stacks.RingedSpace (structureIsSheaf)
open Stacks.SheafOfModules (IsInvertible picardClass)

universe u

namespace Stacks.Models

section CanonicalComponents

variable (S : RegularProperModelSituation.{u})

/-- **Stacks Project, Tag 0C67, at the canonical decomposition.** The reduced special fibre
`D = Σ (mᵢ/d) Cᵢ` of the decomposition of `X_k` into its irreducible components is an effective
Cartier divisor on the model: the components are effective Cartier divisors by part (2) of
[Stacks, Tag 0C5Z], and a nonnegative combination of effective Cartier divisors is one. -/
@[stacks 0C67 "D is an effective Cartier divisor, at the canonical decomposition of X_k into \
its irreducible components"]
theorem isEffectiveCartierDivisor_reducedSpecialFibre_specialFiberComponents :
    IsEffectiveCartierDivisor (reducedSpecialFibre Finset.univ
      S.specialFiberComponentIdeal S.specialFiberMultiplicity) :=
  isEffectiveCartierDivisor_reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
    S.specialFiberMultiplicity fun Z _ => S.isEffectiveCartierDivisor_specialFiberComponent Z

/-- **Stacks Project, Tag 0C67, at the canonical decomposition into irreducible components.**
Let `C₁, …, Cₙ` be the irreducible components of the special fibre `X_k` of a regular proper
model, with their reduced induced structure, let `mᵢ` be the multiplicity of `Cᵢ` in `X_k`, put
`d = gcd(m₁, …, mₙ)` and let `D = Σ (mᵢ/d) Cᵢ`. Then `D` is an effective Cartier divisor,
`𝒪_X(D)` has order dividing `d` in `Pic(X)`, and the conormal module `𝒞_{D/X}` is an invertible
`𝒪_D`-module of order dividing `d` in `Pic(D)`.

This is `Stacks.Models.reducedSpecialFibre_order_dvd_gcd` with both of its hypotheses supplied
from [Stacks, Tag 0C5Z]: effectivity of the components is part (2) and `X_k = Σ mᵢ Cᵢ` is
part (3). -/
@[stacks 0C67 "all four conclusions at the canonical decomposition of X_k into its irreducible \
components, whose two inputs are parts (2) and (3) of 0C5Z: C_i the components with their \
reduced induced structure, m_i the multiplicity of C_i in X_k, d = gcd(m_i) and D = sum \
(m_i/d)C_i"]
theorem reducedSpecialFibre_order_dvd_gcd_specialFiberComponents :
    IsEffectiveCartierDivisor (reducedSpecialFibre Finset.univ
        S.specialFiberComponentIdeal S.specialFiberMultiplicity) ∧
      ((Finset.univ.gcd S.specialFiberMultiplicity : ℕ) : ℤ) •
          picardClass (reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
            S.specialFiberMultiplicity) = 0 ∧
      IsInvertible (reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
          S.specialFiberMultiplicity).subscheme.presheaf
        (structureIsSheaf (reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
          S.specialFiberMultiplicity).subscheme.toRingedSpace)
        (Stacks.Thickenings.immersionConormalSheaf (reducedSpecialFibre Finset.univ
          S.specialFiberComponentIdeal S.specialFiberMultiplicity).subschemeι) ∧
      ((Finset.univ.gcd S.specialFiberMultiplicity : ℕ) : ℤ) •
          picardClass (reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
              S.specialFiberMultiplicity).subscheme.presheaf
            (structureIsSheaf (reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
              S.specialFiberMultiplicity).subscheme.toRingedSpace)
            (Stacks.Thickenings.immersionConormalSheaf (reducedSpecialFibre Finset.univ
              S.specialFiberComponentIdeal S.specialFiberMultiplicity).subschemeι)
            (isInvertible_immersionConormalSheaf (reducedSpecialFibre Finset.univ
              S.specialFiberComponentIdeal S.specialFiberMultiplicity)) = 0 :=
  reducedSpecialFibre_order_dvd_gcd S Finset.univ S.specialFiberComponentIdeal
    S.specialFiberMultiplicity
    (fun Z _ => S.isEffectiveCartierDivisor_specialFiberComponent Z)
    S.specialFiberIdeal_eq_prod

/-- **Stacks Project, Tag 0C67, at the canonical decomposition**, as a statement about additive
orders: the class of `𝒪_X(D)` in `Pic(X)` has order dividing `d = gcd(mᵢ)`, for `D` the reduced
special fibre of the decomposition of `X_k` into its irreducible components. -/
@[stacks 0C67 "O_X(D) has order dividing d in Pic(X), at the canonical decomposition of X_k \
into its irreducible components"]
theorem addOrderOf_picardClass_reducedSpecialFibre_specialFiberComponents_dvd :
    addOrderOf (picardClass (reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
      S.specialFiberMultiplicity)) ∣ Finset.univ.gcd S.specialFiberMultiplicity :=
  addOrderOf_picardClass_reducedSpecialFibre_dvd S Finset.univ S.specialFiberComponentIdeal
    S.specialFiberMultiplicity S.specialFiberIdeal_eq_prod

/-- **Stacks Project, Tag 0C67, at the canonical decomposition**, as a statement about additive
orders: the class of the conormal module `𝒞_{D/X}` in `Pic(D)` has order dividing
`d = gcd(mᵢ)`, for `D` the reduced special fibre of the decomposition of `X_k` into its
irreducible components. -/
@[stacks 0C67 "the conormal class of D has order dividing d in Pic(D), at the canonical \
decomposition of X_k into its irreducible components"]
theorem addOrderOf_picardClass_immersionConormalSheaf_specialFiberComponents_dvd :
    addOrderOf (picardClass (reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
        S.specialFiberMultiplicity).subscheme.presheaf
      (structureIsSheaf (reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
        S.specialFiberMultiplicity).subscheme.toRingedSpace)
      (Stacks.Thickenings.immersionConormalSheaf (reducedSpecialFibre Finset.univ
        S.specialFiberComponentIdeal S.specialFiberMultiplicity).subschemeι)
      (isInvertible_immersionConormalSheaf (reducedSpecialFibre Finset.univ
        S.specialFiberComponentIdeal S.specialFiberMultiplicity))) ∣
      Finset.univ.gcd S.specialFiberMultiplicity :=
  addOrderOf_picardClass_immersionConormalSheaf_reducedSpecialFibre_dvd S Finset.univ
    S.specialFiberComponentIdeal S.specialFiberMultiplicity S.specialFiberIdeal_eq_prod

end CanonicalComponents

end Stacks.Models

end
