module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ContainedComponentComparison

/-!
# Clause (5) of Stacks 0F96 at the level of cycles

Clause (5) of [Stacks, Tag 0F96] is an identity of Chow classes,

  `o_* α = - p^*(c₁(ℒ) ∩ α)`  in  `A_{k+1}(L)`,

and that is how
`Stacks.Chow.zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow` states it.
A dévissage over integral closed subschemes cannot consume a class identity: the comparison
principle it runs on (`Stacks.Chow.GradedIntegralComponentRule.extendChow_congr`) asks for a
*cycle* on the ambient scheme that is rationally equivalent to zero *within* a prescribed carrier.
This file supplies the two intermediate shapes.

## The three shapes, and what each is for

* with a cycle `α` as the argument, the clause reads `o_*α` — the class of the pushforward cycle
  — against the pullback of the cap product of [Stacks, Tag 02SO], which is already defined on
  cycles. This is the form clause (6) is stated in
  (`Stacks.Chow.zeroSectionGysinChow_zeroSectionChowPushforward_mk`), and it is obtained from the
  clause by `Stacks.Chow.firstChernClassCapChow_mk`.
* a class identity in `A_{k+1}(L)` is exactly a rational equivalence between any two cycles
  representing the two sides, and the right-hand side is a class, not a cycle: so the cycle-level
  statement takes a representative `γ` of `p^*(c₁(ℒ) ∩ α)` as a hypothesis, as
  `Stacks.Chow.gysinComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin_of_le`
  takes a representative of the value of a component rule. Every class has a representative, so
  no mathematical hypothesis is added; which representative is taken is the consumer's business.
* the carrier form on an ambient scheme: along a closed immersion `j` out of the total space the
  two pushforward cycles differ by a cycle rationally equivalent to zero *within the image of
  `j`*, by `Stacks.Chow.properPushforward_sub_isRationallyEquivalentToZeroWithin`. This is where
  the carrier comes from — it cannot be read off the class identity, which has forgotten where
  its witnesses are, but the image of a closed immersion is a bound on them.

## Main results

* `zeroSectionChowPushforward_mk_eq_neg_flatPullbackChow_firstChernClassCapOfInvertible`
  — clause (5) with a cycle as the argument.
* `Stacks.Chow.rationallyEquivalent_properPushforward_zeroSection` — **clause (5) at the level of
  cycles**: the pushforward of `α` along the zero section is rationally equivalent to minus any
  cycle representing `p^*(c₁(ℒ) ∩ α)`.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_zeroSection` — the same
  pushed into an ambient scheme along a closed immersion, with the carrier the image of that
  immersion.

## Why no declaration here carries `@[stacks 0F96]`

Clause (5) is asserted by
`Stacks.Chow.zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow`, and
every statement here is that clause read through a representative: each is deduced from it in a
line or two and none of them says anything the clause does not. The same convention is followed
at clause (6), whose cycle-level reorientation
`Stacks.Chow.TensorZeroScheme.zeroSectionGysinChow_zeroSectionChowPushforward_branchSituation`
carries no attribute either.

## References

* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase

variable (C : ChowSituation.{u}) (D : Stacks.LineBundle.Situation.{u}) (sX : D.X ⟶ C.S)
  [LocallyOfFiniteType sX]

/-- **Clause (5) of [Stacks, Tag 0F96] with a cycle as the argument.** For a cycle
`α ∈ Z_{k+1}(X)`,

  `o_*[α] = - p^*(c₁(ℒ) ∩ α)`  in  `A_{k+1}(L)`,

the cap product on the right being the one of [Stacks, Tag 02SO], which is defined on cycles.
This is the clause itself read through `Stacks.Chow.firstChernClassCapChow_mk`, which identifies
the descended cap product of [Stacks, Tag 02TI] on the class of `α` with that cap product. -/
theorem zeroSectionChowPushforward_mk_eq_neg_flatPullbackChow_firstChernClassCapOfInvertible
    (k : ℤ) (α : CycleGroup C sX (k + 1)) :
    zeroSectionChowPushforward C D sX (k + 1)
        (QuotientAddGroup.mk' (rationalEquivalences C sX (k + 1)) α) =
      -chowGroupCast C (D.totalSpaceToBase ≫ sX)
        (show k + ((1 : ℕ) : ℤ) = k + 1 from by simp)
        (flatPullbackChowOfRelativeDimension C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase
          rfl 1 D.relativeDimension_totalSpaceToBase k
          (firstChernClassCapOfInvertible C sX k D.L α)) := by
  rw [← firstChernClassCapChow_mk]
  exact zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow C D sX k _

/-- **Clause (5) of [Stacks, Tag 0F96] at the level of cycles.** Let `α ∈ Z_{k+1}(X)` be a cycle
and let `γ ∈ Z_{k+1}(L)` be any cycle representing the class `p^*(c₁(ℒ) ∩ α)`. Then the
pushforward of `α` along the zero section and `-γ` are rationally equivalent cycles on the total
space.

This is the clause with both sides read through
`Stacks.Chow.zeroSectionChowPushforward_mk`, which presents the left-hand class as the class of
the pushforward cycle, and through `hγ`; two cycles have the same class exactly when they are
rationally equivalent, by `QuotientAddGroup.eq_iff_sub_mem`. -/
theorem rationallyEquivalent_properPushforward_zeroSection (k : ℤ) (α : CycleGroup C sX (k + 1))
    (γ : CycleGroup C (D.totalSpaceToBase ≫ sX) (k + 1))
    (hγ : QuotientAddGroup.mk' (rationalEquivalences C (D.totalSpaceToBase ≫ sX) (k + 1)) γ =
      chowGroupCast C (D.totalSpaceToBase ≫ sX)
        (show k + ((1 : ℕ) : ℤ) = k + 1 from by simp)
        (flatPullbackChowOfRelativeDimension C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase
          rfl 1 D.relativeDimension_totalSpaceToBase k
          (firstChernClassCapOfInvertible C sX k D.L α))) :
    RationallyEquivalent C (D.totalSpaceToBase ≫ sX) (k + 1)
      (properPushforward C sX (D.totalSpaceToBase ≫ sX) D.zeroSection
        (zeroSection_comp_totalSpaceToBase_comp C D sX) (k + 1) α) (-γ) := by
  have h := zeroSectionChowPushforward_mk_eq_neg_flatPullbackChow_firstChernClassCapOfInvertible
    C D sX k α
  rw [zeroSectionChowPushforward_mk, ← hγ] at h
  exact QuotientAddGroup.eq_iff_sub_mem.1
    (h.trans (map_neg (QuotientAddGroup.mk'
      (rationalEquivalences C (D.totalSpaceToBase ≫ sX) (k + 1))) γ).symm)

/-- **Clause (5) of [Stacks, Tag 0F96] as a carrier on an ambient scheme.** Let `j : L ⟶ A` be a
closed immersion of the total space into a scheme over the base situation. Then the pushforwards
along `j` of the two cycles of
`Stacks.Chow.rationallyEquivalent_properPushforward_zeroSection` differ by a cycle rationally
equivalent to zero on `A` within the image of `j`.

This is `Stacks.Chow.properPushforward_sub_isRationallyEquivalentToZeroWithin` at that rational
equivalence. The carrier is what a dévissage over integral closed subschemes needs and what the
class identity of the clause does not retain: it is produced here by the immersion, not by the
clause. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_zeroSection (k : ℤ)
    (α : CycleGroup C sX (k + 1)) (γ : CycleGroup C (D.totalSpaceToBase ≫ sX) (k + 1))
    (hγ : QuotientAddGroup.mk' (rationalEquivalences C (D.totalSpaceToBase ≫ sX) (k + 1)) γ =
      chowGroupCast C (D.totalSpaceToBase ≫ sX)
        (show k + ((1 : ℕ) : ℤ) = k + 1 from by simp)
        (flatPullbackChowOfRelativeDimension C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase
          rfl 1 D.relativeDimension_totalSpaceToBase k
          (firstChernClassCapOfInvertible C sX k D.L α)))
    {A : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (j : D.totalSpace ⟶ A)
    [IsClosedImmersion j] (hj : j ≫ sA = D.totalSpaceToBase ≫ sX) :
    IsRationallyEquivalentToZeroWithin C sA (k + 1)
      (properPushforward C (D.totalSpaceToBase ≫ sX) sA j hj (k + 1)
          (properPushforward C sX (D.totalSpaceToBase ≫ sX) D.zeroSection
            (zeroSection_comp_totalSpaceToBase_comp C D sX) (k + 1) α) -
        properPushforward C (D.totalSpaceToBase ≫ sX) sA j hj (k + 1) (-γ))
      (Set.range j.base) :=
  properPushforward_sub_isRationallyEquivalentToZeroWithin C (D.totalSpaceToBase ≫ sX) sA j hj
    (k + 1) (rationallyEquivalent_properPushforward_zeroSection C D sX k α γ hγ)

end Stacks.Chow

end
