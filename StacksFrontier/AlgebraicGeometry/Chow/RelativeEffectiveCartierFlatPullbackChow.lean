module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Finiteness
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback and relative effective Cartier divisors on Chow groups

Let `X` and `Y` be locally of finite type over the base scheme of chapter 42 of the Stacks
Project, let `p : X ⟶ Y` be flat of relative dimension `r + 1` and let `i : D ⟶ X` be a relative
effective Cartier divisor on `X/Y` (Stacks 062T), presented as the zero scheme of a section `s`
of an invertible module `L`. Writing `q = p|_D : D ⟶ Y`, which is flat of relative dimension `r`,
Stacks 02TR asserts for **every** class `α ∈ A_{k+1}(Y)`

  `i^* p^* α = q^* α`  in  `A_{k+r}(D)`,
  `c₁(L) ∩ p^* α = i_* (q^* α)`  in  `A_{k+r}(X)`.

This file proves both identities for an arbitrary class; the first is proved already at the
level of cycles.

## Main results

* `Stacks.Chow.gysinRule_extendCycleGroup_flatPullback_cycleAssociatedToClosedSubscheme` — the
  component case at the level of cycles: the Gysin *rule* of Stacks 02T8, extended
  coefficientwise, sends the flat pullback of `[W]` to the flat pullback of `[W]` along `q`.
* `Stacks.Chow.gysinRule_extendCycleGroup_flatPullback'` — the same for an arbitrary
  `(k+1)`-cycle, still at the level of cycles.
* `Stacks.Chow.finsum_fiber_flatPullbackWeight_gysinComponentCycleAt` — the component identity on
  cycle coefficients, summed over one fibre of `p`.
* `Stacks.Chow.gysinChowOfInvertible_flatPullbackChow` — the first equality, `i^* p^* α = q^* α`,
  for an arbitrary class `α ∈ A_{k+1}(Y)`.
* `Stacks.Chow.properChowPushforward_gysinChowOfInvertible` — the identity `i_* i^* = c₁(L) ∩ −`
  on Chow groups.
* `Stacks.Chow.firstChernClassCapChow_flatPullbackChow` — the second equality,
  `c₁(L) ∩ p^* α = i_* (q^* α)`, for an arbitrary class.

## References

* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Stacks 02TR on an integral component, at the level of cycles -/

/-- The first equality of Stacks 02TR on an integral component, as an equality of cycles: for an
integral closed subscheme `W ⊆ Y` of dimension `k + 1`, the Gysin rule of Stacks 02T8 extended
coefficientwise sends `p^* [W]_{k+1}` to `(p|_D)^* [W]_{k+1}`. -/
theorem gysinRule_extendCycleGroup_flatPullback_cycleAssociatedToClosedSubscheme
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
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
    (W : Y.IdealSheafData) (hWint : IsIntegral W.subscheme)
    (hWdim : schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hcast : k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1) :
    (gysinRule C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
          (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L)).extendCycleGroup
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1)
          (cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1))) =
      flatPullback C ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
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

/-! ### The contribution of one fibre of `p` -/

/-- The prime cycle of the integral component at a point `y` of relative dimension `k + 1` has
coefficient `1` at `y` and `0` elsewhere. -/
private theorem cycleAssociatedToClosedSubscheme_integralComponentAt_apply
    (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [DecidableEq Y] (k : ℤ) (y : Y) (hy : relativeDimension C.dimensionFunction sY y = k + 1)
    (z : Y) :
    (cycleAssociatedToClosedSubscheme C sY (integralComponentAt y).subschemeι (k + 1)).1 z =
      if z = y then 1 else 0 := by
  have hgen := genericPointOf_integralComponentAt y
  split_ifs with h
  · rw [h]
    have := cycleAssociatedToClosedSubscheme_integral_apply C sY (integralComponentAt y)
      (isIntegral_integralComponentAt y)
      (show schemeDeltaDimension C ((integralComponentAt y).subschemeι ≫ sY) =
        ((k + 1 : ℤ) : EInt) by rw [schemeDeltaDimension_integralComponentAt C sY y, hy])
    rwa [hgen] at this
  · exact cycleAssociatedToClosedSubscheme_integral_apply_of_ne C sY (integralComponentAt y)
      (isIntegral_integralComponentAt y) (k + 1) (by rwa [hgen])

/-- The component identity of Stacks 02TR on cycle coefficients. Let `y ∈ Y` have relative
dimension `k + 1`. Summing, over the fibre of `p` at `y`, the flat pullback multiplicity times
the Gysin component cycle of Stacks 02T8 gives the coefficient of the flat pullback of the prime
cycle `[closure {y}]` along `p|_D`. -/
theorem finsum_fiber_flatPullbackWeight_gysinComponentCycleAt
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
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
    (y : Y) (hy : relativeDimension C.dimensionFunction sY y = k + 1)
    (y' : (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subscheme) :
    (∑ᶠ x ∈ p.base ⁻¹' {y}, flatPullbackWeight C sX p (k + 1 + ((r + 1 : ℕ) : ℤ)) x *
        (gysinComponentCycleAt C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
          (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L) x).1 y') =
      (cycleAssociatedToClosedSubscheme C sY (integralComponentAt y).subschemeι (k + 1)).1
          (((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p).base y') *
        flatPullbackWeight C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX)
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
          (k + 1 + (r : ℤ)) y' := by
  classical
  have hWint := isIntegral_integralComponentAt y
  have hWdim : schemeDeltaDimension C ((integralComponentAt y).subschemeι ≫ sY) =
      ((k + 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_integralComponentAt C sY y, hy]
  have h2 : ((gysinRule C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
          (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L)).extendCycleGroup
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1)
          (cycleAssociatedToClosedSubscheme C sY (integralComponentAt y).subschemeι (k + 1)))).1
          y' =
      (flatPullback C ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
        (by rw [Category.assoc, hbase]) r hq (k + 1)
        (cycleAssociatedToClosedSubscheme C sY (integralComponentAt y).subschemeι (k + 1))).1
          y' := by
    rw [gysinRule_extendCycleGroup_flatPullback_cycleAssociatedToClosedSubscheme C sX sY p hbase
      r hp k L s hD hq (integralComponentAt y) hWint hWdim hcast]
  rw [flatPullback_apply] at h2
  rw [← h2,
    show ((gysinRule C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
          (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L)).extendCycleGroup
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1)
          (cycleAssociatedToClosedSubscheme C sY (integralComponentAt y).subschemeι (k + 1)))).1
          y' =
        ∑ᶠ x : X, (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1)
            (cycleAssociatedToClosedSubscheme C sY (integralComponentAt y).subschemeι (k + 1)) :
              CycleGroup C sX (k + 1 + (r : ℤ) + 1)).1 x *
          (gysinComponentCycleAt C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
            (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L) x).1 y' from rfl,
    val_cycleGroup_cast C sX hcast]
  have hvanish : ∀ x : X, x ∉ p.base ⁻¹' {y} →
      (flatPullback C sX sY p hbase (r + 1) hp (k + 1)
          (cycleAssociatedToClosedSubscheme C sY (integralComponentAt y).subschemeι (k + 1))).1 x *
        (gysinComponentCycleAt C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
          (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L) x).1 y' = 0 := by
    intro x hx
    have hx' : p.base x ≠ y := hx
    rw [flatPullback_apply,
      cycleAssociatedToClosedSubscheme_integralComponentAt_apply C sY k y hy]
    simp [hx']
  have hstep₁ : (∑ᶠ x : X, (flatPullback C sX sY p hbase (r + 1) hp (k + 1)
        (cycleAssociatedToClosedSubscheme C sY (integralComponentAt y).subschemeι (k + 1))).1 x *
      (gysinComponentCycleAt C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
        (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L) x).1 y') =
      ∑ᶠ x ∈ p.base ⁻¹' {y}, (flatPullback C sX sY p hbase (r + 1) hp (k + 1)
        (cycleAssociatedToClosedSubscheme C sY (integralComponentAt y).subschemeι (k + 1))).1 x *
      (gysinComponentCycleAt C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
        (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L) x).1 y' :=
    (finsum_mem_univ _).symm.trans
      (finsum_mem_inter_support_eq' _ Set.univ (p.base ⁻¹' {y}) fun x hx ↦
        ⟨fun _ ↦ by by_contra hne; exact hx (hvanish x hne), fun _ ↦ Set.mem_univ x⟩)
  have hstep₂ : (∑ᶠ x ∈ p.base ⁻¹' {y}, (flatPullback C sX sY p hbase (r + 1) hp (k + 1)
        (cycleAssociatedToClosedSubscheme C sY (integralComponentAt y).subschemeι (k + 1))).1 x *
      (gysinComponentCycleAt C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
        (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L) x).1 y') =
      ∑ᶠ x ∈ p.base ⁻¹' {y}, flatPullbackWeight C sX p (k + 1 + ((r + 1 : ℕ) : ℤ)) x *
      (gysinComponentCycleAt C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
        (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L) x).1 y' :=
    finsum_mem_congr rfl fun x hx ↦ by
      rw [flatPullback_apply,
        cycleAssociatedToClosedSubscheme_integralComponentAt_apply C sY k y hy,
        show p.base x = y from hx]
      simp
  exact (hstep₁.trans hstep₂).symm

/-! ### Stacks 02TR for an arbitrary cycle -/

/-- The first equality of Stacks 02TR for an arbitrary cycle: for every `(k+1)`-cycle `α` on `Y`
the Gysin rule of the relative effective Cartier divisor `D = Z(s)`, extended coefficientwise,
sends `p^* α` to `(p|_D)^* α`, as an equality of cycles on `D`. -/
theorem gysinRule_extendCycleGroup_flatPullback' (C : ChowSituation.{u}) {X Y : Scheme.{u}}
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
    (α : CycleGroup C sY (k + 1)) :
    (gysinRule C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
          (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L)).extendCycleGroup
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1) α) =
      flatPullback C ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
        (by rw [Category.assoc, hbase]) r hq (k + 1) α := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y'
  set chern := firstChernComponentClass C sX (k + 1 + (r : ℤ)) L with hchern
  set R := gysinRule C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤)) chern with hR
  set β := flatPullback C sX sY p hbase (r + 1) hp (k + 1) α with hβ
  set G : X → ℤ := fun x ↦ β.1 x *
    (gysinComponentCycleAt C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤)) chern x).1 y' with hG
  have hGfin : (Function.support G).Finite := by
    refine (finite_support_inter_generalizations β.1.locallyFiniteSupport
      (isCompact_singleton (x := (Stacks.Divisors.zeroScheme X L
        (s.eval (.op ⊤))).subschemeι.base y'))).subset ?_
    intro x hx
    replace hx : β.1 x * R.toComponentRule.cycle x y' ≠ 0 := hx
    exact ⟨⟨_, rfl, R.toComponentRule.mem_closure_of_apply_ne_zero x y'
      (right_ne_zero_of_mul hx)⟩, left_ne_zero_of_mul hx⟩
  have hLHS : (R.extendCycleGroup (hcast ▸ β)).1 y' =
      ∑ᶠ y : Y, ∑ᶠ x ∈ p.base ⁻¹' {y}, G x := by
    rw [finsum_finsum_mem_fiber p.base G hGfin,
      show (R.extendCycleGroup (hcast ▸ β)).1 y' =
        R.toComponentRule.extendCoeff (hcast ▸ β : CycleGroup C sX _).1 y' from rfl,
      val_cycleGroup_cast C sX hcast β]
    rfl
  rw [hLHS, flatPullback_apply]
  have key : ∀ y : Y, (∑ᶠ x ∈ p.base ⁻¹' {y}, G x) = α.1 y *
      (if y = ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p).base y' then
        flatPullbackWeight C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX)
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
          (k + 1 + (r : ℤ)) y' else 0) := by
    intro y
    by_cases hy : α.1 y = 0
    · rw [hy, zero_mul]
      refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
      have hβx : β.1 x = 0 := by
        rw [hβ, flatPullback_apply, show p.base x = y from hx, hy, zero_mul]
      simp only [hG, hβx, zero_mul]
    have hdim : relativeDimension C.dimensionFunction sY y = k + 1 :=
      (mem_cyclesOfDimension_iff_forall_point C sY (k + 1) α.1).1 α.2 y hy
    have hfib := finsum_fiber_flatPullbackWeight_gysinComponentCycleAt C sX sY p hbase r hp k L s
      hD hq hcast y hdim y'
    have hGmul : ∀ x ∈ p.base ⁻¹' {y}, G x = α.1 y *
        (flatPullbackWeight C sX p (k + 1 + ((r + 1 : ℕ) : ℤ)) x *
          (gysinComponentCycleAt C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤)) chern x).1 y') := by
      intro x hx
      simp only [hG, hβ, flatPullback_apply, show p.base x = y from hx]
      ring
    rw [finsum_mem_congr rfl hGmul, ← mul_finsum_mem, hfib]
    rw [cycleAssociatedToClosedSubscheme_integralComponentAt_apply C sY k y hdim]
    by_cases hz : ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p).base y' = y
    · simp only [hz, eq_self, ↓reduceIte, one_mul]
    · simp only [hz, Ne.symm hz, ↓reduceIte, zero_mul, mul_zero]
  rw [finsum_congr key,
    finsum_eq_single _
      (((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p).base y')
      (fun j hj ↦ by rw [if_neg hj, mul_zero]),
    if_pos rfl]

/-! ### Stacks 02TR on Chow groups -/

/-- Transporting a Chow class along an equality of degrees commutes with taking the class of a
cycle. -/
private theorem chowGroup_cast_mk_of_cycle (C : ChowSituation.{u}) {A : Scheme.{u}}
    (q : A ⟶ C.S) [LocallyOfFiniteType q] {j j' : ℤ} (h : j = j') (c : CycleGroup C q j) :
    (h ▸ QuotientAddGroup.mk' (rationalEquivalences C q j) c : chowGroup C q j') =
      QuotientAddGroup.mk' (rationalEquivalences C q j') (h ▸ c) := by
  subst h
  rfl

/-- Let `p : X ⟶ Y` be flat of relative dimension `r + 1` over
the base scheme of chapter 42 and let `i : D ⟶ X` be a relative effective Cartier divisor on
`X/Y`, presented as the zero scheme of a section `s` of an invertible module `L`. Then for every
class `α ∈ A_{k+1}(Y)`

  `i^* p^* α = (p|_D)^* α`  in  `A_{k+r}(D)`,

for the Gysin pullback of Stacks 02TO and the flat pullbacks of Stacks 02S1 on Chow groups, `p|_D`
having relative dimension `r` by
`AlgebraicGeometry.relativeDimension_of_isRelativeEffectiveCartierDivisor`. -/
@[stacks 02TR "first equality, for an arbitrary class in A_{k+1}(Y)"]
theorem gysinChowOfInvertible_flatPullbackChow (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY = sX) (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections)
    [Flat ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)]
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))))
    (hcast : k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1)
    (α : chowGroup C sY (k + 1)) :
    gysinChowOfInvertible C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
        (hcast ▸ flatPullbackChowOfRelativeDimension C sX sY p hbase (r + 1) hp (k + 1) α) =
      flatPullbackChowOfRelativeDimension C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
        (by rw [Category.assoc, hbase]) r
        (AlgebraicGeometry.relativeDimension_of_isRelativeEffectiveCartierDivisor p r hp
          (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) hD) (k + 1) α := by
  set hq := AlgebraicGeometry.relativeDimension_of_isRelativeEffectiveCartierDivisor p r hp
    (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) hD with hqdef
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    show gysinChowOfInvertible C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
        (hcast ▸ flatPullbackChowOfRelativeDimension C sX sY p hbase (r + 1) hp (k + 1)
          (QuotientAddGroup.mk' (rationalEquivalences C sY (k + 1)) c)) =
      flatPullbackChowOfRelativeDimension C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
        (by rw [Category.assoc, hbase]) r hq (k + 1)
        (QuotientAddGroup.mk' (rationalEquivalences C sY (k + 1)) c)
    rw [flatPullbackChowOfRelativeDimension_mk, flatPullbackChowOfRelativeDimension_mk,
      chowGroup_cast_mk_of_cycle C sX hcast]
    show QuotientAddGroup.mk ((gysinRule C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
      (firstChernComponentClass C sX (k + 1 + (r : ℤ)) L)).extendCycleGroup
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1) c)) = _
    rw [gysinRule_extendCycleGroup_flatPullback' C sX sY p hbase r hp k L s hD hq hcast c]
    rfl

/-- The proper Chow pushforward of the descended Gysin map of Stacks 02TO is the descended cap
product of Stacks 02TI: `i_* i^* = c₁(L) ∩ −` on `A_{n+1}(X)`. -/
theorem properChowPushforward_gysinChowOfInvertible (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (n : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (β : chowGroup C sX (n + 1)) :
    properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX) sX
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl n
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Stacks.Divisors.zeroScheme X L s).subschemeι C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX) sX rfl n)
        (gysinChowOfInvertible C sX n L s β) =
      firstChernClassCapChow C n sX L β := by
  induction β using QuotientAddGroup.induction_on with
  | H c =>
    show properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX) sX
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl n
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Stacks.Divisors.zeroScheme X L s).subschemeι C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX) sX rfl n)
        (gysinChowOfInvertible C sX n L s
          (QuotientAddGroup.mk' (rationalEquivalences C sX (n + 1)) c)) =
      firstChernClassCapChow C n sX L (QuotientAddGroup.mk' (rationalEquivalences C sX (n + 1)) c)
    rw [gysinChowOfInvertible_mk, firstChernClassCapChow_mk]
    exact properChowPushforward_gysinHomomorphismOfInvertible C sX n L s c

/-- In the situation of
`Stacks.Chow.gysinChowOfInvertible_flatPullbackChow`, for every class `α ∈ A_{k+1}(Y)`

  `c₁(L) ∩ p^* α = i_* ((p|_D)^* α)`  in  `A_{k+r}(X)`,

the cap product being the descended operation of Stacks 02TI, with `D` the zero scheme of `s`, so
that `L` is `𝒪_X(D)`. -/
@[stacks 02TR "second equality, for an arbitrary class in A_{k+1}(Y)"]
theorem firstChernClassCapChow_flatPullbackChow (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY = sX) (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections)
    [Flat ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)]
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))))
    (hcast : k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1)
    (α : chowGroup C sY (k + 1)) :
    firstChernClassCapChow C (k + 1 + (r : ℤ)) sX L
        (hcast ▸ flatPullbackChowOfRelativeDimension C sX sY p hbase (r + 1) hp (k + 1) α) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sX
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι rfl (k + 1 + (r : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sX rfl
          (k + 1 + (r : ℤ)))
        (flatPullbackChowOfRelativeDimension C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
          (by rw [Category.assoc, hbase]) r
          (AlgebraicGeometry.relativeDimension_of_isRelativeEffectiveCartierDivisor p r hp
            (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) hD) (k + 1) α) := by
  rw [← gysinChowOfInvertible_flatPullbackChow C sX sY p hbase r hp k L s hD hcast α,
    properChowPushforward_gysinChowOfInvertible C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))]

end Stacks.Chow

end
