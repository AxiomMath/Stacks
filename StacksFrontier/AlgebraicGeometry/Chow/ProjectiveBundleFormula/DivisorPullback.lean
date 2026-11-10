module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Finiteness

/-!
# Stacks 02TR on every cycle

Let `p : X ⟶ Y` be flat of relative dimension `r + 1` and let `i : D ⟶ X` be a relative
effective Cartier divisor on `X/Y`, the zero scheme of a section `s` of an invertible module `L`.
[Stacks, Tag 02TR] asserts, for every `(k+1)`-cycle `α` on `Y`,

  `i^* p^* α = (p|_D)^* α`  and  `c₁(L) ∩ p^* α = i_*((p|_D)^* α)`.

`StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullback` proves both on the
fundamental cycle of an integral closed subscheme. This file proves them for every cycle, the
first even as an identity of cycles.

## Main results

* `Stacks.Chow.gysinRule_extendCycleGroup_flatPullback` — the Gysin cycle of `p^* α` is the
  cycle `(p|_D)^* α`, for every `(k+1)`-cycle `α`.
* `Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_divisor` — **Stacks 02TR, first
  equality.**
* `Stacks.Chow.firstChernClassCapOfInvertible_flatPullback_divisor` — **Stacks 02TR, second
  equality.**

## Implementation notes

No `@[stacks 02TR]` attribute is attached: as in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullback`, the relative dimension
`hq` of `D ⟶ Y` is a hypothesis, which the projective towers these results are used for supply.

The extension to arbitrary cycles is coefficientwise. At a point `y` of `D` only the components
of `p^* α` through `y` contribute to the Gysin cycle; grouping them by their image in `Y`
(`Stacks.Chow.finsum_finsum_mem_fiber`) writes the coefficient as a sum over the points `w` of
`Y`, each term being `α(w)` times the coefficient at `y` of the Gysin cycle of `p^*[closure w]`,
to which the integral case applies.

## References

* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY = sX) (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections)
    [Flat ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)]
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))))
    (hq : AlgebraicGeometry.RelativeDimension
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) r)
    (hcast : k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1)

include hD in
/-- **Stacks 02TR on an integral component, as an identity of cycles.** The Gysin cycle of
`p^*[W]` is the cycle `(p|_D)^*[W]`. -/
theorem gysinRule_extendCycleGroup_flatPullback_primeCycle (W : Y.IdealSheafData)
    (hWint : IsIntegral W.subscheme)
    (hWdim : schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt)) :
    (gysinRule C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
        (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L)).extendCycleGroup
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1)
          (cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1))) =
      flatPullback C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
        (by rw [Category.assoc, hbase]) r hq (k + 1)
        (cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1)) := by
  have hin : (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1)
        (cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1)) :
          CycleGroup C sX (k + 1 + (r : ℤ) + 1)) =
      cycleAssociatedToClosedSubscheme C sX (W.comap p).subschemeι (k + 1 + (r : ℤ) + 1) := by
    refine Subtype.ext ((val_cycleGroup_cast C sX hcast _).trans ?_)
    rw [flatPullback_cycleAssociatedToClosedSubscheme C sX sY p hbase (r + 1) hp (k + 1)
      W.subschemeι hWdim, cycleAssociatedToClosedSubscheme_pullbackFst_eq_comap C sX p W, hcast]
  have hZdim : schemeDeltaDimension C ((W.comap p).subschemeι ≫ sX) ≤
      ((k + 1 + (r : ℤ) + 1 : ℤ) : EInt) := by
    have h := schemeDeltaDimension_comap_le_of_relativeDimension C sX sY p hbase (r + 1) hp W
      (k + 1) hWdim.le
    rwa [hcast] at h
  have hDZ := isEffectiveCartierDivisor_comap_comap_subschemeι p
    (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) hD.1 W
  rw [hin, gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme C sX
    (k + 1 + (r : ℤ)) L s (W.comap p) hZdim hDZ,
    flatPullback_cycleAssociatedToClosedSubscheme C
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
      (by rw [Category.assoc, hbase]) r hq (k + 1) W.subschemeι hWdim,
    cycleAssociatedToClosedSubscheme_pullbackFst_eq_comap C
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX)
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) W,
    Scheme.IdealSheafData.comap_comp W
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι p]

open Classical in
/-- The fundamental cycle of the closure of a point of delta-dimension `m` is the indicator of
that point. -/
theorem cycleAssociatedToClosedSubscheme_integralComponentAt_apply {Z : Scheme.{u}}
    (q : Z ⟶ C.S) [LocallyOfFiniteType q] (m : ℤ) (w : Z)
    (hw : relativeDimension C.dimensionFunction q w = m) (z : Z) :
    (cycleAssociatedToClosedSubscheme C q (integralComponentAt w).subschemeι m).1 z =
      if z = w then 1 else 0 := by
  split_ifs with hz
  · subst hz
    have h := cycleAssociatedToClosedSubscheme_integral_apply C q (integralComponentAt z)
      (isIntegral_integralComponentAt z)
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C q z hw)
    rwa [genericPointOf_integralComponentAt] at h
  · exact cycleAssociatedToClosedSubscheme_integral_apply_of_ne C q (integralComponentAt w)
      (isIntegral_integralComponentAt w) m (by rwa [genericPointOf_integralComponentAt])

include hD in
/-- **Stacks 02TR, first equality, as an identity of cycles, on every cycle.** For every
`(k+1)`-cycle `α` on `Y` the Gysin cycle of `p^* α` along `D` is the cycle `(p|_D)^* α`. -/
theorem gysinRule_extendCycleGroup_flatPullback (α : CycleGroup C sY (k + 1)) :
    (gysinRule C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
        (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L)).extendCycleGroup
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1) α) =
      flatPullback C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
        (by rw [Category.assoc, hbase]) r hq (k + 1) α := by
  classical
  set i := (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι with hi
  set R := gysinRule C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
    (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L) with hR
  apply Subtype.ext
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  set β := flatPullback C sX sY p hbase (r + 1) hp (k + 1) α with hβ
  set wt := flatPullbackWeight C sX p (k + 1 + ((r + 1 : ℕ) : ℤ)) with hwt
  set F : X → ℤ := fun x ↦ β.1 x * R.toComponentRule.cycle x y with hF
  have hFfin : (Function.support F).Finite :=
    R.toComponentRule.finite_support_extendTerm β.1.locallyFiniteSupport y
  have hLHS : (R.extendCycleGroup (hcast ▸ β)).1 y = ∑ᶠ x : X, F x := by
    rw [IntegralComponentRule.extendCycleGroup_apply, ComponentRule.extend_apply,
      val_cycleGroup_cast C sX hcast β]
  -- the contribution of the fibre over a point `w` of `Y`
  have hfibre : ∀ w : Y, (∑ᶠ x ∈ p.base ⁻¹' {w}, F x) =
      if w = (i ≫ p).base y then
        α.1 w * flatPullbackWeight C (i ≫ sX) (i ≫ p) (k + 1 + (r : ℤ)) y
      else 0 := by
    intro w
    have hfib : (∑ᶠ x ∈ p.base ⁻¹' {w}, F x) =
        α.1 w * ∑ᶠ x ∈ p.base ⁻¹' {w}, wt x * R.toComponentRule.cycle x y := by
      rw [mul_finsum_mem]
      refine finsum_mem_congr rfl fun x hx ↦ ?_
      simp only [hF, hβ, flatPullback_apply, Set.mem_singleton_iff.mp hx]
      ring
    by_cases hw : relativeDimension C.dimensionFunction sY w = k + 1
    · -- the prime cycle of the closure of `w`
      have hprime := congrArg (fun c : CycleGroup C (i ≫ sX) (k + 1 + (r : ℤ)) ↦ c.1 y)
        (gysinRule_extendCycleGroup_flatPullback_primeCycle C sX sY p hbase r hp k L s hD hq
          hcast (integralComponentAt w) (isIntegral_integralComponentAt w)
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sY w hw))
      rw [IntegralComponentRule.extendCycleGroup_apply, ComponentRule.extend_apply,
        val_cycleGroup_cast, flatPullback_apply] at hprime
      rw [cycleAssociatedToClosedSubscheme_integralComponentAt_apply C sY (k + 1) w hw] at hprime
      -- the left side of `hprime` is a sum over the fibre over `w`
      have hleft : (∑ᶠ x : X, (flatPullback C sX sY p hbase (r + 1) hp (k + 1)
            (cycleAssociatedToClosedSubscheme C sY (integralComponentAt w).subschemeι
              (k + 1))).1 x * R.toComponentRule.cycle x y) =
          ∑ᶠ x ∈ p.base ⁻¹' {w}, wt x * R.toComponentRule.cycle x y := by
        rw [finsum_mem_def]
        refine finsum_congr fun x ↦ ?_
        rw [flatPullback_apply, cycleAssociatedToClosedSubscheme_integralComponentAt_apply C sY
          (k + 1) w hw]
        by_cases hx : p.base x = w
        · rw [Set.indicator_of_mem (by exact hx), ite_eq_left hx, one_mul]
        · rw [Set.indicator_of_notMem (by exact hx), ite_eq_right hx, zero_mul, zero_mul]
      rw [hleft] at hprime
      rw [hfib, hprime]
      split_ifs with h1 h2 h2
      · rw [one_mul]
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rw [zero_mul, mul_zero]
    · have hαw : α.1 w = 0 := by
        by_contra hne
        exact hw ((mem_cyclesOfDimension_iff_forall_point C sY (k + 1) α.1).1 α.2 w hne)
      rw [hfib, hαw, zero_mul, zero_mul, ite_self]
  rw [hLHS, ← finsum_finsum_mem_fiber p.base F hFfin, finsum_congr hfibre,
    finsum_eq_single _ ((i ≫ p).base y) fun w hw ↦ ite_eq_right hw,
    ite_eq_left rfl, flatPullback_apply]

include hD in
/-- **Stacks 02TR, first equality.** For every `(k+1)`-cycle `α` on `Y`,

  `i^* p^* α = (p|_D)^* α`  in  `A_{k+1+r}(D)`. -/
theorem gysinHomomorphismOfInvertible_flatPullback_divisor
    (α : CycleGroup C sY (k + 1)) :
    gysinHomomorphismOfInvertible C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1) α) =
      QuotientAddGroup.mk
        (flatPullback C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
          (by rw [Category.assoc, hbase]) r hq (k + 1) α) := by
  change QuotientAddGroup.mk ((gysinRule C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
    (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L)).extendCycleGroup _) = _
  rw [gysinRule_extendCycleGroup_flatPullback C sX sY p hbase r hp k L s hD hq hcast α]

include hD in
/-- **Stacks 02TR, second equality.** For every `(k+1)`-cycle `α` on `Y`,

  `c₁(L) ∩ p^* α = i_*((p|_D)^* α)`  in  `A_{k+1+r}(X)`. -/
theorem firstChernClassCapOfInvertible_flatPullback_divisor
    (α : CycleGroup C sY (k + 1)) :
    firstChernClassCapOfInvertible C sX (k + 1 + (r : ℤ)) L
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1) α) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sX
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι rfl (k + 1 + (r : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sX rfl
          (k + 1 + (r : ℤ)))
        (QuotientAddGroup.mk
          (flatPullback C
            ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
            ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
            (by rw [Category.assoc, hbase]) r hq (k + 1) α)) := by
  rw [← effectiveCartierIntersectionOfInvertible_eq_firstChernClassCapOfInvertible C sX
      (k + 1 + (r : ℤ)) L (s.eval (.op ⊤)) hD.1]
  exact (effectiveCartierIntersectionOfInvertible_apply C sX (k + 1 + (r : ℤ)) L
    (s.eval (.op ⊤)) hD.1 _).trans (congrArg _
      (gysinHomomorphismOfInvertible_flatPullback_divisor C sX sY p hbase r hp k L s hD hq hcast
        α))

end Stacks.Chow

end
