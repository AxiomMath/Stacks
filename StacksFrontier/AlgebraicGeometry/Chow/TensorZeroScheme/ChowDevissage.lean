module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity.ComponentRuleFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity.GradedComponentRuleRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCapInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps

/-!
# Tag 0F98 off prime cycles: both composites as rules on integral components

[Stacks, Tag 0F98] is the identity `i₁^*p^*α = p₁^*i^*α` of maps `A_{k+1}(Y) ⟶ A_{k+1}(D₁)`
attached to the diagram of [Stacks, Tag 0F97], and the source proves it by taking an integral
closed subscheme `W ⊆ Y` of delta-dimension `k+1` and computing both sides on `[W]`. This file
performs that reduction: it presents each composite as the extension of a
`Stacks.Chow.GradedIntegralComponentRule` and concludes, from
`Stacks.Chow.GradedIntegralComponentRule.extendChow_congr`, that the identity on Chow groups
follows from the identity of the two rules' values on a single `W`, up to rational equivalence
within the preimage of `W`.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.leftRule` — `W ↦ i₁^*p^*[W]`, at cycle level, as a graded rule on
  integral components.
* `Stacks.Chow.TensorZeroScheme.rightRule` — `W ↦ p₁^*i^*[W]`, likewise.

## Main results

* `Stacks.Chow.flatPullback_finsum` — flat pullback of cycles commutes with a locally finite
  coefficientwise sum.
* `Stacks.Chow.support_flatPullback_subset` — the support of a flat pullback lies over the support
  of the cycle.
* `Stacks.Chow.support_cycleAssociatedToClosedSubscheme_subset_support` — the support of the
  fundamental cycle of a closed subscheme lies in the support of the ideal cutting it out.
* `Stacks.Chow.TensorZeroScheme.leftRule_extendCycleGroup` and `rightRule_extendCycleGroup` — the
  two rules extend to the two composites at cycle level.
* `Stacks.Chow.TensorZeroScheme.gysinChowBranch₁_flatPullbackChowProj_of_primeCycle` — **the
  reduction of [Stacks, Tag 0F98] to its prime-cycle case.**

## References

* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Flat pullback through a locally finite sum -/

/-- **Flat pullback of cycles commutes with a locally finite coefficientwise sum.** If a `k`-cycle
`α` is coefficientwise the locally finite sum of the `k`-cycles `A j`, then its flat pullback is
coefficientwise the sum of their flat pullbacks. -/
theorem flatPullback_finsum (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) {J : Type*}
    (A : J → CycleGroup C sX k) (α : CycleGroup C sX k)
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, (A j).1 x) (x' : X') :
    (flatPullback C sX' sX f hbase r hf k α).1 x' =
      ∑ᶠ j : J, (flatPullback C sX' sX f hbase r hf k (A j)).1 x' := by
  rw [flatPullback_apply, hα (f.base x'), finsum_mul]
  exact finsum_congr fun _ ↦ rfl

/-- The support of a flat pullback lies over the support of the cycle. -/
theorem support_flatPullback_subset (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (α : CycleGroup C sX k) :
    Function.support (flatPullback C sX' sX f hbase r hf k α).1 ⊆
      f.base ⁻¹' Function.support α.1 := by
  intro x' hx'
  rw [Function.mem_support, flatPullback_apply] at hx'
  exact left_ne_zero_of_mul hx'

/-- **The support of the fundamental cycle of a closed subscheme lies in the support of the ideal
cutting it out.** -/
theorem support_cycleAssociatedToClosedSubscheme_subset_support (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (W : X.IdealSheafData) (d : ℤ) :
    Function.support (cycleAssociatedToClosedSubscheme C p W.subschemeι d).1 ⊆
      (W.support : Set X) := by
  refine (support_cycleAssociatedToClosedSubscheme_subset C p W.subschemeι d).trans ?_
  rw [Scheme.IdealSheafData.range_subschemeι]

end Stacks.Chow

namespace Stacks.Chow.TensorZeroScheme

variable (C : Stacks.Chow.ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (k : ℤ)

/-! ### The two Gysin rules of the diagram -/

include h₁ h₂ in
/-- The rule on integral components of `Y` whose extension is the Gysin map of `i : D ⟶ Y`: the
`Stacks.Chow.gysinRule` of Stacks 02T8 at the presentation of `D` as the zero scheme of `s`. -/
def gysinRuleZeroIdeal :
    Stacks.Chow.IntegralComponentRule C sY ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
      (zeroIdeal Y L₁ L₂ s).subschemeι k :=
  Stacks.Chow.gysinRule C sY k (Stacks.Divisors.tensorModules L₁ L₂) s
    (Stacks.Chow.firstChernComponentClass C sY k (Stacks.Divisors.tensorModules L₁ L₂))

include h₁ h₂ in
/-- The rule on integral components of `L` whose extension is the Gysin map of `i₁ : D₁ ⟶ L`: the
`Stacks.Chow.gysinRule` of Stacks 02T8 at the presentation of `D₁` as the zero scheme of `s₁`,
condition (3) of Stacks 0F97. -/
def gysinRuleBranch₁ :
    Stacks.Chow.IntegralComponentRule C (R.normalize.p ≫ sY)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      R.normalize.D₁.subschemeι (k + 1) :=
  letI : AlgebraicGeometry.SheafOfModules.IsInvertible
      R.normalize.total.sheaf.obj
      R.normalize.total.ringCatSheaf.property
      ((Scheme.Modules.pullback R.normalize.p).obj L₁) :=
    Stacks.Divisors.pullback_isInvertible _ _
  Stacks.Chow.gysinRule C (R.normalize.p ≫ sY) (k + 1)
    ((Scheme.Modules.pullback R.normalize.p).obj L₁) R.normalize.s₁
    (Stacks.Chow.firstChernComponentClass C (R.normalize.p ≫ sY) (k + 1)
      ((Scheme.Modules.pullback R.normalize.p).obj L₁))

/-! ### The carrier computations -/

include h₁ h₂ in
/-- The two routes from `D₁` to `Y` have the same preimages: the square `i₁ ≫ p = p₁ ≫ i` of the
diagram of Stacks 0F97, read on underlying sets. -/
theorem preimage_branch₁_proj (T : Set Y) :
    (R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' T =
      R.normalize.p₁.base ⁻¹' ((zeroIdeal Y L₁ L₂ s).subschemeι.base ⁻¹' T) := by
  rw [← Set.preimage_comp, R.normalize.comm₁]
  rfl

include h₁ h₂ in
/-- The preimage of a subset of `Y` in `D₁` along `i₁ ≫ p`, factored through `L`. -/
theorem preimage_branch₁_comp (T : Set Y) :
    (R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' T =
      R.normalize.D₁.subschemeι.base ⁻¹' (R.normalize.p.base ⁻¹' T) :=
  rfl

/-! ### The two rules -/

include h₁ h₂ in
/-- **The left-hand composite of Tag 0F98 as a rule on integral components.** It takes an
integral closed subscheme `W ⊆ Y` of delta-dimension `k+1` to a cycle representing
`i₁^*p^*[W]`: the flat pullback of the fundamental cycle of `W` along `p`, followed by the
cycle-level Gysin extension of `i₁`. Its value is supported over `W`. -/
def leftRule :
    Stacks.Chow.GradedIntegralComponentRule C sY
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p) (k + 1) (k + 1) where
  cycle W _ _ :=
    (gysinRuleBranch₁ C Y L₁ L₂ s R sY k).extendCycleGroup
      (Stacks.Chow.flatPullback C (R.normalize.p ≫ sY) sY R.normalize.p rfl 1
        R.normalize.p_relativeDimension (k + 1)
        (Stacks.Chow.cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1)))
  support_subset W _ _ := by
    rw [preimage_branch₁_comp]
    refine Stacks.Chow.GysinChernCap.support_extendCycleGroup_subset C
      (R.normalize.p ≫ sY) (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      R.normalize.D₁.subschemeι (gysinRuleBranch₁ C Y L₁ L₂ s R sY k)
      (W.support.isClosed.preimage R.normalize.p.continuous) _ ?_
    refine (Stacks.Chow.support_flatPullback_subset C (R.normalize.p ≫ sY) sY
      R.normalize.p rfl 1 R.normalize.p_relativeDimension (k + 1) _).trans ?_
    exact Set.preimage_mono
      (Stacks.Chow.support_cycleAssociatedToClosedSubscheme_subset_support C sY W (k + 1))

include h₁ h₂ in
/-- **The right-hand composite of Tag 0F98 as a rule on integral components.** It takes an
integral closed subscheme `W ⊆ Y` of delta-dimension `k+1` to a cycle representing
`p₁^*i^*[W]`: the cycle-level Gysin extension of `i` applied to the fundamental cycle of `W`,
followed by the flat pullback along `p₁`. Its value is supported over `W`. -/
def rightRule :
    Stacks.Chow.GradedIntegralComponentRule C sY
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p) (k + 1) (k + 1) where
  cycle W _ _ :=
    Stacks.Chow.flatPullback C (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
      (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
      ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
      ((gysinRuleZeroIdeal C Y L₁ L₂ s sY k).extendCycleGroup
        (Stacks.Chow.cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1)))
  support_subset W _ _ := by
    rw [preimage_branch₁_proj]
    refine (Stacks.Chow.support_flatPullback_subset C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
      (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
      ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k _).trans ?_
    refine Set.preimage_mono ?_
    refine Stacks.Chow.GysinChernCap.support_extendCycleGroup_subset C sY
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) (zeroIdeal Y L₁ L₂ s).subschemeι
      (gysinRuleZeroIdeal C Y L₁ L₂ s sY k) W.support.isClosed _ ?_
    exact Stacks.Chow.support_cycleAssociatedToClosedSubscheme_subset_support C sY W (k + 1)

/-! ### The two rules extend to the two composites -/

include h₁ h₂ in
/-- **The left-hand rule extends to `i₁^* ∘ p^*` at cycle level.** -/
theorem leftRule_extendCycleGroup (α : Stacks.Chow.CycleGroup C sY (k + 1)) :
    (leftRule C Y L₁ L₂ s R sY k).extendCycleGroup α =
      (gysinRuleBranch₁ C Y L₁ L₂ s R sY k).extendCycleGroup
        (Stacks.Chow.flatPullback C (R.normalize.p ≫ sY) sY R.normalize.p rfl 1
          R.normalize.p_relativeDimension (k + 1) α) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  have hE : LocallyFinite fun i : Stacks.Chow.cycleSupportIndex α ↦
      R.normalize.p.base ⁻¹'
        ((Stacks.Chow.integralComponentAt i.1).support : Set Y) :=
    Stacks.Chow.GysinChernCap.locallyFinite_preimage
      (Stacks.Chow.locallyFinite_support_integralComponentAt α) R.normalize.p.continuous
  change ((leftRule C Y L₁ L₂ s R sY k).extendCycleGroup α).1 y = _
  rw [Stacks.Chow.GradedIntegralComponentRule.extendCycleGroup_eq_finsum_cycle C sY
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p) (k + 1) (k + 1)
      (leftRule C Y L₁ L₂ s R sY k) α y,
    Stacks.Chow.IntegralComponentRule.extendCycleGroup_finsum
      (gysinRuleBranch₁ C Y L₁ L₂ s R sY k)
      (fun i : Stacks.Chow.cycleSupportIndex α ↦
        Stacks.Chow.flatPullback C (R.normalize.p ≫ sY) sY R.normalize.p rfl 1
          R.normalize.p_relativeDimension (k + 1)
          (α.1 i.1 • Stacks.Chow.cycleAssociatedToClosedSubscheme C sY
            (Stacks.Chow.integralComponentAt i.1).subschemeι (k + 1)))
      (fun i ↦ R.normalize.p.base ⁻¹'
        ((Stacks.Chow.integralComponentAt i.1).support : Set Y)) hE
      (fun i ↦ (Stacks.Chow.support_flatPullback_subset C (R.normalize.p ≫ sY) sY
          R.normalize.p rfl 1 R.normalize.p_relativeDimension (k + 1) _).trans
        (Set.preimage_mono (Stacks.Chow.support_zsmul_primeCycle_subset C sY α i)))
      _
      (fun x ↦ Stacks.Chow.flatPullback_finsum C (R.normalize.p ≫ sY) sY R.normalize.p rfl 1
        R.normalize.p_relativeDimension (k + 1)
        (fun i : Stacks.Chow.cycleSupportIndex α ↦
          α.1 i.1 • Stacks.Chow.cycleAssociatedToClosedSubscheme C sY
            (Stacks.Chow.integralComponentAt i.1).subschemeι (k + 1))
        α (fun z ↦ Stacks.Chow.cycle_eq_finsum_primeCycles α z) x) y]
  refine finsum_congr fun i ↦ ?_
  rw [map_zsmul, map_zsmul]
  rfl

include h₁ h₂ in
/-- **The right-hand rule extends to `p₁^* ∘ i^*` at cycle level.** -/
theorem rightRule_extendCycleGroup (α : Stacks.Chow.CycleGroup C sY (k + 1)) :
    (rightRule C Y L₁ L₂ s R sY k).extendCycleGroup α =
      Stacks.Chow.flatPullback C (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
        (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
        ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
        ((gysinRuleZeroIdeal C Y L₁ L₂ s sY k).extendCycleGroup α) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  have hE : LocallyFinite fun i : Stacks.Chow.cycleSupportIndex α ↦
      (zeroIdeal Y L₁ L₂ s).subschemeι.base ⁻¹'
        ((Stacks.Chow.integralComponentAt i.1).support : Set Y) :=
    Stacks.Chow.GysinChernCap.locallyFinite_preimage
      (Stacks.Chow.locallyFinite_support_integralComponentAt α)
      (zeroIdeal Y L₁ L₂ s).subschemeι.continuous
  change ((rightRule C Y L₁ L₂ s R sY k).extendCycleGroup α).1 y = _
  rw [Stacks.Chow.GradedIntegralComponentRule.extendCycleGroup_eq_finsum_cycle C sY
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p) (k + 1) (k + 1)
      (rightRule C Y L₁ L₂ s R sY k) α y,
    Stacks.Chow.flatPullback_finsum C (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
      (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
      ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
      (fun i : Stacks.Chow.cycleSupportIndex α ↦
        (gysinRuleZeroIdeal C Y L₁ L₂ s sY k).extendCycleGroup
          (α.1 i.1 • Stacks.Chow.cycleAssociatedToClosedSubscheme C sY
            (Stacks.Chow.integralComponentAt i.1).subschemeι (k + 1)))
      _
      (fun x ↦ Stacks.Chow.IntegralComponentRule.extendCycleGroup_finsum
        (gysinRuleZeroIdeal C Y L₁ L₂ s sY k)
        (fun i : Stacks.Chow.cycleSupportIndex α ↦
          α.1 i.1 • Stacks.Chow.cycleAssociatedToClosedSubscheme C sY
            (Stacks.Chow.integralComponentAt i.1).subschemeι (k + 1))
        (fun i ↦ ((Stacks.Chow.integralComponentAt i.1).support : Set Y))
        (Stacks.Chow.locallyFinite_support_integralComponentAt α)
        (fun i ↦ Stacks.Chow.support_zsmul_primeCycle_subset C sY α i) α
        (fun z ↦ Stacks.Chow.cycle_eq_finsum_primeCycles α z) x) y]
  refine finsum_congr fun i ↦ ?_
  rw [map_zsmul, map_zsmul]
  rfl

/-! ### The reduction -/

include h₁ h₂ in
/-- **[Stacks, Tag 0F98] reduced to its prime-cycle case.** If the two cycles
`i₁^*p^*[W]` and `p₁^*i^*[W]` attached to an integral closed subscheme `W ⊆ Y` of
delta-dimension `k+1` differ by a cycle rationally equivalent to zero within the preimage of `W`
in `D₁`, then

  `i₁^*p^*α = p₁^*i^*α`  in  `A_{k+1}(D₁)`  for every  `α ∈ A_{k+1}(Y)`,

which is the identity of the tag. -/
theorem gysinChowBranch₁_flatPullbackChowProj_of_primeCycle
    (hW : ∀ (W : Y.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt)),
      Stacks.Chow.IsRationallyEquivalentToZeroWithin C
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
        ((leftRule C Y L₁ L₂ s R sY k).cycle W hW hDim -
          (rightRule C Y L₁ L₂ s R sY k).cycle W hW hDim)
        ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)))
    (α : Stacks.Chow.chowGroup C sY (k + 1)) :
    gysinChowBranch₁ C Y L₁ L₂ s R sY (k + 1)
        (flatPullbackChowProj C Y L₁ L₂ s R sY (k + 1) α) =
      flatPullbackChowProj₁ C Y L₁ L₂ s R sY k (gysinChowZeroIdeal C Y L₁ L₂ s sY k α) := by
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    have hL : (leftRule C Y L₁ L₂ s R sY k).extendChow a =
        gysinChowBranch₁ C Y L₁ L₂ s R sY (k + 1)
          (flatPullbackChowProj C Y L₁ L₂ s R sY (k + 1) (QuotientAddGroup.mk a)) := by
      change QuotientAddGroup.mk' _ ((leftRule C Y L₁ L₂ s R sY k).extendCycleGroup a) = _
      rw [leftRule_extendCycleGroup]
      rfl
    have hR : (rightRule C Y L₁ L₂ s R sY k).extendChow a =
        flatPullbackChowProj₁ C Y L₁ L₂ s R sY k
          (gysinChowZeroIdeal C Y L₁ L₂ s sY k (QuotientAddGroup.mk a)) := by
      change QuotientAddGroup.mk' _ ((rightRule C Y L₁ L₂ s R sY k).extendCycleGroup a) = _
      rw [rightRule_extendCycleGroup]
      rfl
    rw [← hL, ← hR]
    exact Stacks.Chow.GradedIntegralComponentRule.extendChow_congr C sY
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p) (k + 1) (k + 1)
      (leftRule C Y L₁ L₂ s R sY k) (rightRule C Y L₁ L₂ s R sY k) hW a

end Stacks.Chow.TensorZeroScheme

end
