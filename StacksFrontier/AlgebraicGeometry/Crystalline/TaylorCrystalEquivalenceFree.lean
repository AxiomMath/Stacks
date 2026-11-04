module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorCrystalEquivalence

/-!
# [Stacks, Tag 07JH] at the differentials of the divided power polynomial algebra

`Crystalline.taylorCrystalsToPairs_isEquivalence` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCrystalEquivalence.lean` is
[Stacks, Proposition 60.17.4, Tag 07JH] for the functor of [Stacks, Lemma 60.17.3, Tag 07JG] over
a module `Ω` of differentials with a `Module.Basis` on the chosen `d x_i`.  At the module of
divided power differentials of the divided power polynomial algebra
`P = A⟨x_w : w ∈ W⟩` that basis is a theorem rather than a datum —
`Crystalline.dividedPowerDifferentialsBasis`, whose `w`-th vector is `d x_w` by
`Crystalline.dividedPowerDifferentialsBasis_apply` — so the tag holds there with nothing about `Ω`
supplied from outside.

This is the same instantiation that
`StacksFrontier/AlgebraicGeometry/Crystalline/FreeDifferentials07JH.lean` performs for the two
algebraic hypotheses `hinj` and `hlift` separately; here it is performed once, on the equivalence
itself.

## Main results

* `Crystalline.taylorCrystalsToPairs_isEquivalence_dividedPowerDifferentials` —
  **[Stacks, Proposition 60.17.4, Tag 07JH] at `Ω = Ω¹_{P/A,δ}` with the differentials of the
  variables as the chosen `d x_w`**, for finitely many variables.

## Implementation notes

The two instance arguments are the right action of `P` on `Ω` and its agreement with the left
action.  They carry no mathematical content, `P` being commutative, but
`Crystalline.TaylorCrystal` cannot be formed without them, so they appear here exactly as they are
variables of `StacksFrontier/AlgebraicGeometry/Crystalline/FreeDifferentials07JH.lean`.

`W` is finite.  `Ω¹_{P/A,δ}` is free on the `d x_w` for any `W`, so the injectivity half of the
proof needs no finiteness; the factorisation half rests on `p`-adic precompleteness of `M ⊗_P Ω`,
which for an infinite `W` fails by
`Crystalline.not_isPrecomplete_finsupp_of_forall_pow_ne_zero`.  The asymmetry is discussed in the
module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFreeFinite.lean`.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Crystalline

open DividedPowers

attribute [local instance low] setIndexedDividedPowerPolynomialCommRing
  coefficientDividedPowerRingAlgebra setIndexedDividedPowerPolynomialAlgebra'
  setIndexedDividedPowerPolynomialDividedPowerRingAlgebra

attribute [local implicit_reducible] coefficientDividedPowerRing
  DividedPowers.setIndexedDividedPowerPolynomialDividedPowerRing

section Free

variable (A : Type u) [CommRing A] (W : Type u)
  [Module (↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W))ᵐᵒᵖ
    (dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers)]
  [IsCentralScalar (↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W))
    (dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers)]
  {g : A →+* ↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W)}
  (d : DividedPowerDerivation A
    (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) g
    (dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers))
  (p : ℕ)

/-- **The algebraic model of [Stacks, Proposition 60.17.4, Tag 07JH] at the differentials of the
divided power polynomial algebra**, which carries no `@[stacks 07JH]` attribute: the tag is about
crystals in quasi-coherent modules on `Cris(X/S)`
(`Crystalline.GlobalCrystallineSituation.SmallSite.QuasiCoherentCrystal`), not about this model.
For `P = A⟨x_w : w ∈ W⟩` with `W` finite and `Ω = Ω¹_{P/A,δ}`, the functor
of [Stacks, Lemma 60.17.3, Tag 07JG] — `Crystalline.taylorCrystalsToPairs`, the declaration this
chapter registers that lemma on — from `Crystalline.TaylorCrystal` to the pairs `(M, ∇)`
satisfying items (07JB), (07JC), (07JD) and (07JE), with its canonical crystalline connection,
**is an equivalence of categories.**

**The source category is `Crystalline.TaylorCrystal` and not the crystals in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)`**; see `Crystalline.taylorCrystalsToPairs_isEquivalence`, of
which this is the instance at `Crystalline.dividedPowerDifferentialsBasis`, the basis of
`Ω¹_{P/A,δ}` on the differentials of the variables, whose `w`-th vector is `d x_w` by
`Crystalline.dividedPowerDifferentialsBasis_apply`.  So the chosen family of differentials is the
source's own `d x_w`, and nothing about `Ω` is supplied from outside: the freeness that the
general statement takes as a datum is a theorem here.  `W` is finite, which the source does not
ask for; the general statement's docstring says why that hypothesis cannot be dropped. -/
theorem taylorCrystalsToPairs_isEquivalence_dividedPowerDifferentials [Finite W] :
    Functor.IsEquivalence
      (taylorCrystalsToPairs.{u, u, u, u, u} A
        (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) g
        (dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowerRing
            (coefficientDividedPowerRing A) W).dividedPowers) d p
        (fun w ↦ dividedPowerDifferentialsBasis A W w) (dividedPowerDifferentialsBasis A W)
        fun _ ↦ rfl) :=
  taylorCrystalsToPairs_isEquivalence A _ g _ d p _ (dividedPowerDifferentialsBasis A W) _

end Free

end Crystalline

end
