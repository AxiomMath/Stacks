module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.GluingInput
public import StacksFrontier.RingTheory.LocalRing.PrepareTwoNonZeroDivisors

/-!
# Existence of a simultaneous tame-symbol preparation

Nonzerodivisors in a one-dimensional Noetherian local ring, not all of which are units, admit a
simultaneous tame-symbol preparation after a finite extension whose quotient is supported at the
maximal ideal.

## Main results

* `AlgebraicGeometry.exists_tameSymbolPreparation_of_ringKrullDim_eq_one`: the existence
  statement, with both of its ring-theoretic inputs discharged.

## References

* [Stacks Project, Tag 0EAE](https://stacks.math.columbia.edu/tag/0EAE)
* [Stacks Project, Tag 02Q7](https://stacks.math.columbia.edu/tag/02Q7)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EAG.** Nonzerodivisors in a one-dimensional Noetherian local ring, not
all of which are units, admit a simultaneous tame-symbol preparation after a finite extension
whose quotient is supported at the maximal ideal. -/
@[stacks 0EAG]
theorem exists_tameSymbolPreparation_of_ringKrullDim_eq_one {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {r : ℕ} (hr : 2 ≤ r)
    (a : Fin r → A) (ha : ∀ i, IsRegular (a i))
    (hunit : ¬ ∀ i, IsUnit (a i)) (hdim : ringKrullDim A = 1) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Nonempty (TameSymbolPreparation a B) :=
  exists_tameSymbolPreparation ringHomGluingAtMaximalIdeals
    Stacks.PrepareNonZeroDivisors.finiteExtensionPreparingTwoNonzerodivisors hr a ha hunit hdim

end AlgebraicGeometry

end
