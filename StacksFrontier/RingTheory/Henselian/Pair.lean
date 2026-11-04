module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Jacobson.Ideal
public import StacksCore.Tactic.StacksAttribute

/-!
# Henselian pairs

A pair consisting of a commutative ring `A` and an ideal `I` is henselian when `I` is contained
in the Jacobson radical of `A` and every coprime factorization into monic polynomials modulo `I`
of a monic polynomial over `A` lifts to such a factorization over `A`.

## Main definitions

* `HenselianPair`: the predicate that `(A, I)` is a henselian pair.

## Implementation notes

Reduction modulo `I` is expressed by mapping polynomial coefficients along
`Ideal.Quotient.mk I`, and generation of the unit ideal is expressed by `IsCoprime`.

## References

* [The Stacks Project, Tag 09XE](https://stacks.math.columbia.edu/tag/09XE)
-/

@[expose] public section

/-- A pair `(A, I)` is henselian if `I` lies in the Jacobson radical of `A` and every
factorization modulo `I` of a monic polynomial into coprime monic factors lifts to `A`. -/
@[stacks 09XE, ega "IV 18.5.8", sga "4 VIII 4.1", sga "4 XII 6.13"]
def HenselianPair (A : Type*) [CommRing A] (I : Ideal A) : Prop :=
  I ≤ (⊥ : Ideal A).jacobson ∧
    ∀ f : Polynomial A, f.Monic →
      ∀ g₀ h₀ : Polynomial (A ⧸ I), g₀.Monic → h₀.Monic →
        f.map (Ideal.Quotient.mk I) = g₀ * h₀ → IsCoprime g₀ h₀ →
          ∃ g h : Polynomial A, g.Monic ∧ h.Monic ∧ f = g * h ∧
            g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀

namespace HenselianPair

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- In a henselian pair `(A, I)` the ideal `I` is contained in the Jacobson radical of `A`. -/
theorem le_jacobson (h : HenselianPair A I) : I ≤ (⊥ : Ideal A).jacobson := h.1

/-- In a henselian pair `(A, I)`, a factorization modulo `I` of a monic polynomial over `A` into
coprime monic factors lifts to a factorization over `A`. -/
theorem exists_monic_factorization (h : HenselianPair A I) {f : Polynomial A} (hf : f.Monic)
    {g₀ h₀ : Polynomial (A ⧸ I)} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hmap : f.map (Ideal.Quotient.mk I) = g₀ * h₀) (hcop : IsCoprime g₀ h₀) :
    ∃ g h : Polynomial A, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀ :=
  h.2 f hf g₀ h₀ hg₀ hh₀ hmap hcop

end HenselianPair

end
