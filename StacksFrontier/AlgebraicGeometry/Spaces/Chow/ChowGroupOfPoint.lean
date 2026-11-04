module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCyclesInDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroCycleDegree

/-!
# The Chow group of zero cycles on a point

In Situation 0EDT let `Y/B` be a good algebraic space whose space of points `|Y|` is a single
point and on which the dimension function induced by the base vanishes — the situation of
`Y = Spec(k)` for a field `k`. Then `Y` has exactly one integral closed subspace `W`, of
δ-dimension zero, and

`CH_0(Y) ≅ ℤ`, `[W] ↦ 1`.

This is the identification of `CH_0(Spec(k))` with `ℤ` with which Stacks 0ESG composes proper
pushforward to define the degree of a zero cycle.

The proof is a count of dimensions. A zero cycle on `Y` is determined by its coefficient at `W`,
since `W` is the only integral closed subspace, so `Z_0(Y) ≅ ℤ`. A cycle rationally equivalent to
zero is a sum over a family of integral closed subspaces of δ-dimension `1`, and there are none,
the δ-dimension of every integral closed subspace of `Y` being zero; so the family is empty, the
sum is zero, and `CH_0(Y) = Z_0(Y)`.

## Main definitions

* `AlgebraicGeometry.Space.cycleGroupZeroEquivInt`: `Z_0(Y) ≅ ℤ`, the coefficient at `W`.
* `AlgebraicGeometry.Space.chowGroupZeroEquivInt`: `CH_0(Y) ≅ ℤ`, the natural isomorphism of
  Stacks 0ESG, sending the class of `[W]` to `1`.

## Main results

* `AlgebraicGeometry.Space.rationalEquivalences_zero_eq_bot`: on `Y` no nonzero zero cycle is
  rationally equivalent to zero.
* `AlgebraicGeometry.Space.chowGroupZeroEquivInt_chowClass`: the isomorphism sends the class of
  a zero cycle to its coefficient at `W`.
* `AlgebraicGeometry.Space.chowGroupZeroEquivInt_chowClass_cycleOfIntegralClosedSubspace`: it
  sends the class of `[W]` to `1`.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroCycleDegree`, `Spec(k)` is modelled by the
two properties of it that the argument uses: its space of points is a subsingleton, and the
dimension function induced on it vanishes. The integral closed subspace `W` is an argument rather
than a choice; it is unique by
`AlgebraicGeometry.Space.IntegralClosedSubspace.eq_of_subsingleton_points`, and supplying it is
how nonemptiness of `|Y|` enters.

## References

* [Stacks Project, Tag 0ESG](https://stacks.math.columbia.edu/tag/0ESG)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- When the induced dimension function of `Y` vanishes, so does the δ-dimension of every
integral closed subspace of `Y`. -/
theorem deltaDimension_eq_zero_of_deltaValue_eq_zero (sY : Y ⟶ D.space)
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) : deltaDimension D sY W = 0 :=
  hδ _

/-- When the induced dimension function of `Y` vanishes, no zero cycle on `Y` other than `0` is
rationally equivalent to zero: a cycle rationally equivalent to zero is a sum over integral
closed subspaces of δ-dimension `1`, and there are none. -/
theorem rationalEquivalences_zero_eq_bot (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0) :
    rationalEquivalences.{v} D sY hY 0 = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun α hα => ?_
  obtain ⟨J, W, hWfin, c, hWdim, -, rfl⟩ := hα
  have : IsEmpty J := ⟨fun j => by
    simpa [deltaDimension_eq_zero_of_deltaValue_eq_zero D sY hδ] using hWdim j⟩
  exact Subtype.ext (funext fun Z => by
    rw [cycleFamilySum_apply, finsum_of_isEmpty]
    rfl)

/-- **Zero cycles on a point.** If `|Y|` is a single point, a zero cycle on `Y` is its
coefficient at the integral closed subspace `W` of `Y`, which is unique, and `Z_0(Y) ≅ ℤ`. The
inverse sends `n` to `n [W]`. -/
def cycleGroupZeroEquivInt (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    CycleGroup D sY 0 ≃+ ℤ where
  toFun α := α.1 W
  invFun n :=
    n • cycleOfIntegralClosedSubspace D sY 0 W
      (deltaDimension_eq_zero_of_deltaValue_eq_zero D sY hδ W)
  left_inv α := Subtype.ext (funext fun Z => by
    rw [IntegralClosedSubspace.eq_of_subsingleton_points D.site D.base D.base_mem hY.1 hpt Z W,
      AddSubgroup.coe_zsmul, Pi.smul_apply, cycleOfIntegralClosedSubspace_coe, cycleCoeff_self,
      smul_eq_mul, mul_one])
  right_inv n := by
    change ((n • cycleOfIntegralClosedSubspace D sY 0 W
      (deltaDimension_eq_zero_of_deltaValue_eq_zero D sY hδ W) : CycleGroup D sY 0) :
        IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) W = n
    rw [AddSubgroup.coe_zsmul, Pi.smul_apply, cycleOfIntegralClosedSubspace_coe, cycleCoeff_self,
      smul_eq_mul, mul_one]
  map_add' _ _ := rfl

/-- The isomorphism `Z_0(Y) ≅ ℤ` sends a zero cycle to its coefficient at the integral closed
subspace `W`. -/
@[simp]
theorem cycleGroupZeroEquivInt_apply (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (α : CycleGroup D sY 0) :
    cycleGroupZeroEquivInt D sY hY hpt hδ W α = α.1 W :=
  rfl

/-- **The Chow group of zero cycles on a point.** If `|Y|` is a single point and the induced
dimension function of `Y` vanishes — the case `Y = Spec(k)` — then `CH_0(Y) ≅ ℤ`, by the
coefficient at the unique integral closed subspace `W` of `Y`. This is the natural isomorphism
`CH_0(Spec(k)) → ℤ` of Stacks 0ESG; it sends the class of `[W]` to `1`, by
`AlgebraicGeometry.Space.chowGroupZeroEquivInt_chowClass_cycleOfIntegralClosedSubspace`. -/
def chowGroupZeroEquivInt (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    chowGroup.{v} D sY hY 0 ≃+ ℤ :=
  ((QuotientAddGroup.quotientAddEquivOfEq
      (rationalEquivalences_zero_eq_bot.{v} D sY hY hδ)).trans
    QuotientAddGroup.quotientBot).trans (cycleGroupZeroEquivInt D sY hY hpt hδ W)

/-- The isomorphism `CH_0(Y) ≅ ℤ` sends the class of a zero cycle to its coefficient at the
integral closed subspace `W`. -/
@[simp]
theorem chowGroupZeroEquivInt_chowClass (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (α : CycleGroup D sY 0) :
    chowGroupZeroEquivInt.{v} D sY hY hpt hδ W (chowClass.{v} D sY hY 0 α) = α.1 W :=
  rfl

/-- The isomorphism `CH_0(Y) ≅ ℤ` sends the class of `[W]` to `1`. -/
theorem chowGroupZeroEquivInt_chowClass_cycleOfIntegralClosedSubspace (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    chowGroupZeroEquivInt.{v} D sY hY hpt hδ W
      (chowClass.{v} D sY hY 0 (cycleOfIntegralClosedSubspace D sY 0 W
        (deltaDimension_eq_zero_of_deltaValue_eq_zero D sY hδ W))) = 1 := by
  rw [chowGroupZeroEquivInt_chowClass, cycleOfIntegralClosedSubspace_coe, cycleCoeff_self]

end AlgebraicGeometry.Space

end
