module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernComm
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors

/-!
# Stacks 02TJ with both inputs discharged

`Stacks.Chow.firstChernClassCapOnChowOfInvertible_comm` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativityInvertible` proves the commutativity of
two first Chern class cap products from two inputs: Stacks 02TI, in the single reduced form
`Stacks.Chow.FirstChernCapKillsPrincipalDivisor`, and Stacks 02TH on the integral closed
subschemes of delta-dimension `k + 2`, as the class-level statement
`Stacks.Chow.FirstChernCapCommutesOnIntegralComponents`. Both are theorems of this repository:

* the reduced form of Stacks 02TI is `Stacks.Chow.firstChernCapKillsPrincipalDivisor` of
  `StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors`, out of the key formula of
  Stacks 0AYC;
* Stacks 02TH on the integral components is
  `Stacks.Chow.GenuineChern.firstChernCapCommutesOnIntegralComponents` of
  `StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernComm`, out of Stacks 02TH for the
  divisor cycles of two nonzero meromorphic sections
  (`Stacks.Chow.firstChernClassCapOfInvertible_divisorCycle_comm`) and Stacks 02SJ (2).

This file states the commutativity with both of them supplied, for the four descended operations
`Stacks.Chow.firstChernClassCapOnChowOfInvertible` themselves.

## Main results

* `Stacks.Chow.firstChernClassCapOnChowOfInvertible_comm_unconditional` — **Stacks 02TJ**.

## References

* [Stacks Project, Tag 02TJ](https://stacks.math.columbia.edu/tag/02TJ)
* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- **Stacks 02TJ.** For two invertible modules `ℒ` and `𝒩` on a scheme `X` locally of finite type
over the base, intersecting successively with the two first Chern classes is independent of the
order: `c₁(ℒ) ∩ c₁(𝒩) ∩ α = c₁(𝒩) ∩ c₁(ℒ) ∩ α` in `A_k(X)` for `α ∈ A_{k+1+1}(X)`.

The four descended operations are those of `Stacks.Chow.firstChernClassCapOnChowOfInvertible`,
whose Stacks 02TI input is supplied by `Stacks.Chow.firstChernCapKillsPrincipalDivisor` in each of
the two degrees, and Stacks 02TH enters through
`Stacks.Chow.GenuineChern.firstChernCapCommutesOnIntegralComponents`; see the implementation
notes of `StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativityInvertible`. -/
@[stacks 02TJ "the commutativity itself, with no hypotheses beyond the source's. The four \
descended cap products are `Stacks.Chow.firstChernClassCapOnChowOfInvertible`, and the Stacks \
02TI input each of them needs — the reduced form \
`Stacks.Chow.FirstChernCapKillsPrincipalDivisor`, the vanishing of the cap product on one \
principal divisor on an integral scheme, to which \
`Stacks.Chow.firstChernCapFactorsEverywhere_iff_killsPrincipalDivisor` shows Stacks 02TI is \
equivalent — is supplied in both degrees by \
`Stacks.Chow.firstChernCapKillsPrincipalDivisor`, which proves it outright. Stacks 02TH for the \
restrictions of the two modules to the integral closed subschemes of `X` of delta-dimension \
`k + 2`, as an equality of classes in `A_k(W)`, which is what the source reduces to, is \
`Stacks.Chow.GenuineChern.firstChernCapCommutesOnIntegralComponents`, which proves it out of \
the key formula of Stacks 0AYC. The four cycle-level rules of Stacks 02SO and the four \
separate instances of Stacks 02TI that `Stacks.Chow.firstChernClassCapOnChow_comm` takes as \
inputs are all theorems here, and the passage from the integral subschemes to every class is \
proved too"]
theorem firstChernClassCapOnChowOfInvertible_comm_unconditional
    (α : chowGroup C p (k + 1 + 1)) :
    firstChernClassCapOnChowOfInvertible C k (firstChernCapKillsPrincipalDivisor C k) p L
        (firstChernClassCapOnChowOfInvertible C (k + 1)
          (firstChernCapKillsPrincipalDivisor C (k + 1)) p N α) =
      firstChernClassCapOnChowOfInvertible C k (firstChernCapKillsPrincipalDivisor C k) p N
        (firstChernClassCapOnChowOfInvertible C (k + 1)
          (firstChernCapKillsPrincipalDivisor C (k + 1)) p L α) :=
  firstChernClassCapOnChowOfInvertible_comm C p k L N
    (fun j ↦ firstChernCapKillsPrincipalDivisor C j)
    (GenuineChern.firstChernCapCommutesOnIntegralComponents C p k L N) α

end Stacks.Chow

end
