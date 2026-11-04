module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PrimeCycleTransport
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisorIntegral

/-!
# The generic point of the affine line over an integral base

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `Y` be integral,
locally of finite type over `S`, of delta-dimension `n`. This file records two facts about the
prime cycles of the affine line over `Y` that the fourth step of the proof of Stacks 02TT uses
to dispose of two of its cases.

The first is bookkeeping: the prime cycle of a point is the zero cycle whenever the degree it is
read in is not the relative dimension of that point. The fourth step of the source's proof fixes
a degree `k` and a prime cycle on `𝔸¹_Y` of delta-dimension `k + 1`; a point of the wrong
dimension carries no cycle in that degree and so nothing has to be proved about it.

The second is the case `W = 𝔸¹_Y` of that step — "If `W = Y × 𝔸¹`, then `[W] = f^*[Y]`". The
delta-dimension of `𝔸¹_Y` is `n + 1`, so the prime cycle of its generic point lives in degree
`n + 1`, and it is the flat pullback of the fundamental cycle of `Y`.

## Main results

* `Stacks.Chow.cycleAssociatedToClosedSubscheme_integralComponentAt_eq_zero_of_ne` — a prime
  cycle read in a degree other than the relative dimension of its point is zero.
* `Stacks.Chow.schemeDeltaDimension_affineSpaceOver` — the delta-dimension of affine `r`-space
  over an integral base exceeds that of the base by `r`.
* `Stacks.Chow.mem_range_flatPullbackChow_primeCycle_genericPoint_affineSpaceOver` — the class of
  the prime cycle of the generic point of affine `r`-space over an integral base is a flat
  pullback.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver

/-- **A prime cycle read in the wrong degree is zero.** The cycle of the integral closed
subscheme `closure {x}` in degree `k` has coefficient one at `x` and zero elsewhere, and the
coefficient at `x` is read only when the relative dimension of `x` is `k`; so if it is not, every
coefficient vanishes. -/
theorem cycleAssociatedToClosedSubscheme_integralComponentAt_eq_zero_of_ne
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (x : X) (hx : relativeDimension C.dimensionFunction p x ≠ k) :
    cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι k = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  by_cases hz : z = x
  · subst hz
    exact (cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C p
      (integralComponentAt z).subschemeι k hx).trans rfl
  · exact (cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p k x hz).trans rfl

/-- **The delta-dimension of affine `r`-space over an integral base exceeds that of the base by
`r`.** Affine space over an integral scheme is integral, and the projection is flat of relative
dimension `r`, so this is `Stacks.Chow.schemeDeltaDimension_eq_add_of_flat`. -/
theorem schemeDeltaDimension_affineSpaceOver (C : ChowSituation.{u}) {Y : Scheme.{u}}
    [IsIntegral Y] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (r : ℕ) {n : ℤ}
    (hn : schemeDeltaDimension C sY = (n : EInt)) :
    schemeDeltaDimension C ((𝔸(ULift.{u} (Fin r); Y) ↘ Y) ≫ sY) = ((n + (r : ℤ) : ℤ) : EInt) :=
  schemeDeltaDimension_eq_add_of_flat C ((𝔸(ULift.{u} (Fin r); Y) ↘ Y) ≫ sY) sY
    (𝔸(ULift.{u} (Fin r); Y) ↘ Y) rfl r (relativeDimension_affineSpaceOver Y r) hn

/-- **The case `W = 𝔸^r_Y` of the fourth step of Stacks 02TT.** The class of the prime cycle of
the generic point of affine `r`-space over an integral base of delta-dimension `n` is the flat
pullback of the fundamental class of the base: on an integral scheme the prime cycle of the
generic point is the fundamental cycle, and flat pullback carries the fundamental cycle to the
fundamental cycle. -/
theorem mem_range_flatPullbackChow_primeCycle_genericPoint_affineSpaceOver
    (C : ChowSituation.{u}) {Y : Scheme.{u}} [IsIntegral Y] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (r : ℕ) {n : ℤ} (hn : schemeDeltaDimension C sY = (n : EInt)) :
    (QuotientAddGroup.mk' (rationalEquivalences C
        ((𝔸(ULift.{u} (Fin r); Y) ↘ Y) ≫ sY) (n + (r : ℤ)))
      (cycleAssociatedToClosedSubscheme C ((𝔸(ULift.{u} (Fin r); Y) ↘ Y) ≫ sY)
        (integralComponentAt (genericPoint ↥𝔸(ULift.{u} (Fin r); Y))).subschemeι
        (n + (r : ℤ)))) ∈
    (flatPullbackChowOfRelativeDimension C ((𝔸(ULift.{u} (Fin r); Y) ↘ Y) ≫ sY) sY
      (𝔸(ULift.{u} (Fin r); Y) ↘ Y) rfl r (relativeDimension_affineSpaceOver Y r) n).range :=
  mem_range_flatPullbackChow_cycleAssociatedToClosedSubscheme_integralComponentAt_genericPoint
    C sY (𝔸(ULift.{u} (Fin r); Y) ↘ Y) r (relativeDimension_affineSpaceOver Y r) hn
    (schemeDeltaDimension_affineSpaceOver C sY r hn)

end Stacks.Chow

end
