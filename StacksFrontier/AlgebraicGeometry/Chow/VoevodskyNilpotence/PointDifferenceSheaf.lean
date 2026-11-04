module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerChow
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.ClosedPointDivisor
public import StacksFrontier.AlgebraicGeometry.Picard.CurveChowZeroDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPower

/-!
# An invertible module whose first Chern class is `[x] - [x']`

Stacks 0FH9 takes `ℒ = 𝒪_X(x - x')` on a smooth curve `X` and uses
`c₁(ℒ) ∩ [X] = [x] - [x']`. This file produces such a module on a smooth proper curve over a
field: a representative of the Picard class `[𝒪_X(x)] - [𝒪_X(x')]`. Each closed point of a
smooth curve is an effective Cartier divisor
(`AlgebraicGeometry.IsCurve.isEffectiveCartierDivisor_vanishingIdeal_closure_singleton`), and
`c₁(𝒪_X(D)) ∩ [X] = [D]` (`AlgebraicGeometry.curvePicardToChowZero_divisorPicardClass`), so the
class of the representative is `[x] - [x']` by additivity of `c₁` in the Picard group.

## Main results

* `Stacks.Chow.exists_invCap_capOnChow_fundamentalChowClass_eq_pointDifference`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **`𝒪_X(x - x')` on a smooth proper curve.** For `k`-rational points `x`, `x'` of a smooth
proper curve `X` over a field `k` there is an invertible `𝒪_X`-module `ℒ` with
`c₁(ℒ) ∩ [X] = [x] - [x']` in `CH_0(X)`. -/
theorem exists_invCap_capOnChow_fundamentalChowClass_eq_pointDifference (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [IsProper f] [IsCurve k f] [Smooth f]
    (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ∃ (L : X.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L),
      (invCap (fieldChowSituation k) f L).capOnChow (fieldChowSituation k) f 0
        (fundamentalChowClass (fieldChowSituation k) f (0 + 1)) =
          pointDifference k f x x' hx hx' := by
  have hpt : ∀ (y : (fieldChowSituation k).S ⟶ X) (hy : y ≫ f = 𝟙 _),
      ∃ (D : X.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor D),
        curvePicardToChowZero k f (Stacks.Divisors.picardClass D) =
          Stacks.WeilCohomology.rationalPointChowClass k f y hy := by
    intro y hy
    have hc := GenusOne.isClosed_point f y hy
    have hD : Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({GenusOne.point y} : Set X)) =
        Scheme.IdealSheafData.vanishingIdeal (⟨{GenusOne.point y}, hc⟩ : Closeds X) :=
      congrArg _ (Closeds.ext (by rw [Closeds.coe_closure, hc.closure_eq]; rfl))
    have hE := IsCurve.isEffectiveCartierDivisor_vanishingIdeal_closure_singleton k f hc
    rw [hD] at hE
    refine ⟨_, hE, ?_⟩
    rw [curvePicardToChowZero_divisorPicardClass k f (IsCurve.topologicalKrullDim_eq_one (f := f)),
      cycleAssociatedToClosedSubscheme_vanishingIdeal_point k f y hy]
    rfl
  obtain ⟨D, hD, hDx⟩ := hpt x hx
  obtain ⟨D', hD', hDx'⟩ := hpt x' hx'
  obtain ⟨L, hL, hcl⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace)
    (Stacks.Divisors.picardClass D - Stacks.Divisors.picardClass D')
  refine ⟨L, hL, ?_⟩
  have h := curvePicardToChowZero_picardClass k f L hL
  rw [hcl, map_sub, hDx, hDx'] at h
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    hL
  exact (invCap_capOnChow_mk _ f L 0 _).trans h.symm

end Stacks.Chow

end
