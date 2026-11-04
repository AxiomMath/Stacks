module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapCompatible

/-!
# Intersecting with an invertible sheaf and push and pull

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `X'` be
schemes locally of finite type over `S`, let `f : X' ⟶ X` be flat of relative dimension `r`, let
`L` be an invertible module on `X` and let `α` be a `(k+1)`-cycle on `X`. Then

  `f^*(c₁(L) ∩ α) = c₁(f^*L) ∩ f^*α`

in `A_{k+r}(X')`, where the cap products are those of Stacks 02SO. The identity holds at the
level of cycles, as a rational equivalence between the two cycles representing the two sides.

## Main results

* `Stacks.Chow.flatPullback_firstChernCapOfInvertible_rationallyEquivalent`: the cycle
  representing `c₁(f^*L) ∩ f^*α` is rationally equivalent to the flat pullback of the cycle
  representing `c₁(L) ∩ α`.
* `Stacks.Chow.flatPullbackChow_firstChernClassCapOfInvertible_of_invertible`: the identity as an
  equality of Chow classes, when flat pullback `f^* : A_k(X) ⟶ A_{k+r}(X')` descends to Chow
  groups (`Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalence`).

## References

* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0EPJ](https://stacks.math.columbia.edu/tag/0EPJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X' X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (r : ℕ)
  (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- Intersecting with the first Chern class of an invertible module commutes with flat pullback:
for `f : X' ⟶ X` flat of relative dimension `r`, an invertible module `L` on `X` and a
`(k+1)`-cycle `α` on `X`, the cycle representing `c₁(f^*L) ∩ f^*α` and the flat pullback of the
cycle representing `c₁(L) ∩ α` are rationally equivalent on `X'`. -/
@[stacks 02SS]
theorem flatPullback_firstChernCapOfInvertible_rationallyEquivalent (α : CycleGroup C p (k + 1)) :
    RationallyEquivalent C (f ≫ p) (k + (r : ℤ))
      ((firstChernCapRule C (f ≫ p) (k + (r : ℤ))
          (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
            ((Scheme.Modules.pullback f).obj L))).extendCycleGroup
        ((show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ▸
          flatPullback C (f ≫ p) p f rfl r hf (k + 1) α))
      (flatPullback C (f ≫ p) p f rfl r hf k
        ((firstChernCapRule C p k (firstChernComponentCycleRule C p k L)).extendCycleGroup α)) :=
  flatPullback_firstChernCapRule_rationallyEquivalent C p f r hf k
    (firstChernComponentCycleRule C p k L)
    (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L))
    (firstChernCapRationallyCompatibleWithFlatPullback_invertible C p f r hf k L) (by omega) α

/-- The identity `f^*(c₁(L) ∩ α) = c₁(f^*L) ∩ f^*α` in `A_{k+r}(X')`, for `f : X' ⟶ X` flat of
relative dimension `r` such that flat pullback descends to Chow groups. -/
theorem flatPullbackChow_firstChernClassCapOfInvertible_of_invertible
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (f ≫ p) p f rfl r hf k)
    (α : CycleGroup C p (k + 1)) :
    flatPullbackChow C (f ≫ p) p f rfl r hf k hfac
        (firstChernClassCapOfInvertible C p k L α) =
      firstChernClassCapOfInvertible C (f ≫ p) (k + (r : ℤ))
        ((Scheme.Modules.pullback f).obj L)
        ((show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ▸
          flatPullback C (f ≫ p) p f rfl r hf (k + 1) α) :=
  flatPullbackChow_firstChernClassCapOfInvertible C p f r hf k L hfac
    (firstChernCapRationallyCompatibleWithFlatPullback_invertible C p f r hf k L) α

end Stacks.Chow

end
