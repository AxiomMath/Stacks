module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommutingCharacterized
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible

/-!
# The fundamental-class case of Stacks 0FBY at the Gysin system of an invertible module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, with `S` the spectrum of a
field, and let `X` be integral and flat over `S` of relative dimension `d`. For a bivariant class
`c ∈ A^p(Y ⟶ Z)` at the canonical Gysin system `Stacks.Chow.gysinSystemOfInvertible`, the exterior
product with the fundamental class `[X]` commutes with capping with `c` (Stacks 0FBY for `[X]`).

## Main results

* `Stacks.Chow.commutesExteriorProductCapAt_fundamentalChowClass_of_invertible`: the
  fundamental-class case of Stacks 0FBY at that Gysin system.

## References

* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FBY](https://stacks.math.columbia.edu/tag/0FBY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Let `X` be an integral scheme, flat of relative dimension `d` over the spectrum `S` of a field.
For a bivariant class `c` at the Gysin system of an invertible module, the exterior product with
the fundamental class `[X]` commutes with capping with `c`. -/
theorem commutesExteriorProductCapAt_fundamentalChowClass_of_invertible (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Flat sX] [IsIntegral X]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (u : Y ⟶ Z) [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ) (d : ℕ) (m : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) sY sZ u hu p)
    (hfr : AlgebraicGeometry.RelativeDimension sX d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ)) :
    CommutesExteriorProductCapAt C hδ (gysinSystemOfInvertible C) sX sY sZ u hu p c (d : ℤ) m
      (fundamentalChowClass C sX (d : ℤ)) :=
  commutesExteriorProductCapAt_fundamentalChowClass_of_isBivariantFlatPullback C hδ
    (gysinSystemOfInvertible C) sX sY sZ u hu p d (flatPullbackDescends C) m c hfr hd
    (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C (pullback.snd sX sZ ≫ sZ) sZ
      (pullback.snd sX sZ) rfl d (relativeDimension_pullbackSnd sX hfr sZ))

end Stacks.Chow

end
