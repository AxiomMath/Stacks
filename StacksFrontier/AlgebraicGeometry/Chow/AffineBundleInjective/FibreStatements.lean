module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.BundleFibre

/-!
# Fibrewise statements about Milnor K-chains along a morphism

Let `(S, δ)` be the base situation of chapter 42 and `f : X ⟶ Y` a morphism of schemes locally of
finite type over `S`. The injectivity of flat pullback along an affine-space bundle is proved by a
dévissage of a Milnor K₁-chain on `X` into its pieces over the points of `Y`. This file names the
two properties of the fibre over a point `y` that the dévissage consumes, in terms of the
restriction `Stacks.Chow.fibreRestrict` of a chain to that fibre:

* `Stacks.Chow.FibreBoundaryLift`: a K₁-chain supported on the fibre over `y` whose divisor has no
  component on that fibre is, on that fibre, the tame-symbol boundary of a K₂-chain supported on
  the fibre — unless the chain lives at the generic points of the fibres, `δ(y) = k + 1 - r`;
* `Stacks.Chow.FibreUnitDescent`: at that remaining level, such a chain consists of classes coming
  from `κ(y)`.

For an affine-space bundle `f : X ⟶ Y` of rank `r`, the fibre over `y` is `𝔸^r_{κ(y)}`, and the
two properties are the vanishing `CH^M_t(𝔸^r_{κ(y)}, 1) = 0` for `t < r` and the computation
`CH^M_r(𝔸^r_{κ(y)}, 1) = κ(y)^*` of the higher Chow groups of Stacks 0GUA of affine space over a
field, read without forming those groups.

## Main definitions

* `Stacks.Chow.fibreRestrict` — restriction of a Milnor K-chain to the fibre over a point.
* `Stacks.Chow.FibreBoundaryLift`, `Stacks.Chow.FibreUnitDescent` — the two fibrewise properties.

## References

* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
* [Stacks Project, Tag 0GUB](https://stacks.math.columbia.edu/tag/0GUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) (f : X ⟶ Y)

/-- The restriction of a locally finite Milnor K-chain on `X` to the fibre of `f` over `y`. -/
abbrev fibreRestrict (y : Y) (m : ℤ) (n : ℕ) :
    MilnorChainGroup C sX m n →+ MilnorChainGroup C sX m n :=
  milnorChainRestrict C sX (f.base ⁻¹' {y}) m n

/-- **The boundary-lifting property of the fibre over `y`**, for K₁-chains of relative dimension
`k + 1` and a morphism of fibre dimension `r`: away from the level `δ(y) = k + 1 - r` of the
generic points of the fibres, a K₁-chain supported on the fibre over `y` whose divisor has no
component on that fibre is, on that fibre, the tame-symbol boundary of a K₂-chain supported on
the fibre. -/
def FibreBoundaryLift (r : ℕ) (k : ℤ) (y : Y) : Prop :=
  relativeDimension C.dimensionFunction sY y ≠ k + 1 - r →
    ∀ a : PointwiseKOneGroup C sX k, fibreRestrict C sX f y (k + 1) 1 a = a →
      fibreRestrict C sX f y k 0 (pointwiseDivisorDifferential C sX k a) = 0 →
        ∃ η : PointwiseKTwoGroup C sX k, fibreRestrict C sX f y (k + 2) 2 η = η ∧
          fibreRestrict C sX f y (k + 1) 1 (pointwiseMilnorBoundary C sX k η) = a

/-- **The unit-descent property of the fibre over `y`**, for K₁-chains of relative dimension
`k + 1` and a morphism of fibre dimension `r`: at the level `δ(y) = k + 1 - r` of the generic
points of the fibres, every class of a K₁-chain supported on the fibre over `y` whose divisor has
no component on that fibre comes from `κ(y)`. -/
def FibreUnitDescent (r : ℕ) (k : ℤ) (y : Y) : Prop :=
  relativeDimension C.dimensionFunction sY y = k + 1 - r →
    ∀ a : PointwiseKOneGroup C sX k, fibreRestrict C sX f y (k + 1) 1 a = a →
      fibreRestrict C sX f y k 0 (pointwiseDivisorDifferential C sX k a) = 0 →
        ∀ ξ : pointsOfDimension C sX (k + 1), f.base ξ.1 = y →
          ∃ c : MilnorKTheory (Y.residueField (f.base ξ.1)) 1,
            a.1 ξ = milnorKTransport (f.residueFieldMap ξ.1).hom 1 c

end Stacks.Chow

end
