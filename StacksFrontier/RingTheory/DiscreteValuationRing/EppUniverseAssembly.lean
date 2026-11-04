module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppUniverseDescent
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppWeakSolutionBridge
public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction

/-!
# Normalising a base-change package to the canonical one

A weak solution for an arbitrary integral-closure base-change package `D` over `K₁` is turned into
a weak solution for `IsDiscreteValuationRing.canonicalBaseChange`, whose three carriers are the
reduced compositum `reducedCompositum K L K₁`, the integral closure of `A` in `K₁` and the integral
closure of `B` in the reduced compositum.

## Main results

* `Stacks.EppTheorem.algebraMap_eL₁_base`: the compositum identification `eL₁` of a package
  respects the action of `B`.
* `Stacks.EppTheorem.isWeakSolution_canonicalBaseChange_of_isWeakSolution`: a weak solution for a
  package gives a weak solution for the canonical package.

## Implementation notes

`algebraMap_eL₁_base` is stated for `B` rather than for an arbitrary ring acting through `L`. In
the general form `Algebra.TensorProduct.includeLeft` carries an implicit scalar ring, the goal
leaves `SMulCommClass K ?m L` stuck, and the tower instance cannot be matched against the binder.

The algebra structure `integralClosureCompositumMap` between the canonical package's two integral
closures is only a local instance where it is defined, so the proof of
`isWeakSolution_canonicalBaseChange_of_isWeakSolution` reinstates it.

## References

* [The Stacks Project, Tag 09EM](https://stacks.math.columbia.edu/tag/09EM)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.EppTheorem

open IsDiscreteValuationRing

-- `Algebra K₁ (L ⊗[K] K₁)` is not a global instance in Mathlib, since it would make the action of
-- `L` on `L ⊗[K] L` ambiguous.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

-- The carrier data of a package are instance-implicit structure fields; binders mentioning
-- `D.L₁`, `D.A₁` or `D.B₁` elaborate only once they are instances.
attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraKL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraK₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraAA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerAA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureB₁

universe uA uB uK uL uK₁ w₁ w₂ w₃

variable (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]

/-- The compositum identification `D.eL₁` of a base-change package, recorded as a `K`-algebra
equivalence, respects the action of `B`: it sends `algebraMap B D.L₁ b` to
`algebraMap B (reducedCompositum K L K₁) b`. -/
theorem algebraMap_eL₁_base
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, w₁, w₂, w₃} A B K L K₁) (b : B) :
    D.eL₁ (algebraMap B D.L₁ b) = algebraMap B (reducedCompositum K L K₁) b := by
  rw [IsScalarTower.algebraMap_apply B L D.L₁, D.eL₁_left]
  exact congrArg (Ideal.Quotient.mk (nilradical (L ⊗[K] K₁)))
    (IsScalarTower.algebraMap_apply B L (L ⊗[K] K₁) b).symm

/-- If the base-change package `D` over `K₁` is a weak solution, then so is the canonical
package `IsDiscreteValuationRing.canonicalBaseChange A B K L K₁`. -/
theorem isWeakSolution_canonicalBaseChange_of_isWeakSolution
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, w₁, w₂, w₃} A B K L K₁)
    (hD : D.IsWeakSolution) :
    (canonicalBaseChange A B K L K₁).IsWeakSolution := by
  classical
  let : Algebra (integralClosure A K₁) (integralClosure B (reducedCompositum K L K₁)) :=
    (integralClosureCompositumMap A B K L K₁).toAlgebra
  have hsqB : ∀ b : B, D.eL₁.toRingEquiv (algebraMap B D.L₁ b)
      = algebraMap B (reducedCompositum K L K₁) (RingEquiv.refl B b) :=
    algebraMap_eL₁_base A B K L K₁ D
  let eA : D.A₁ ≃+* integralClosure A K₁ :=
    (IsIntegralClosure.equiv A D.A₁ K₁ (integralClosure A K₁)).toRingEquiv
  let eB : D.B₁ ≃+* integralClosure B (reducedCompositum K L K₁) :=
    (IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)).toRingEquiv.trans
      (integralClosureRingEquivOfSquare (RingEquiv.refl B) D.eL₁.toRingEquiv hsqB)
  refine Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_ringEquiv_square D
    (canonicalBaseChange A B K L K₁) eA eB ?_ hD
  intro x
  show algebraMap (integralClosure A K₁) (integralClosure B (reducedCompositum K L K₁)) (eA x)
      = eB (algebraMap D.A₁ D.B₁ x)
  apply Subtype.ext
  have hleft : ∀ y : integralClosure A K₁,
      ((algebraMap (integralClosure A K₁) (integralClosure B (reducedCompositum K L K₁)) y :
          integralClosure B (reducedCompositum K L K₁)) : reducedCompositum K L K₁)
        = algebraMap K₁ (reducedCompositum K L K₁) (y : K₁) := fun _ => rfl
  have hcoeA : ((eA x : integralClosure A K₁) : K₁) = algebraMap D.A₁ K₁ x :=
    IsIntegralClosure.algebraMap_equiv A D.A₁ K₁ (integralClosure A K₁) x
  rw [hleft, hcoeA]
  have hright : ((eB (algebraMap D.A₁ D.B₁ x) :
        integralClosure B (reducedCompositum K L K₁)) : reducedCompositum K L K₁)
      = D.eL₁ (algebraMap D.B₁ D.L₁ (algebraMap D.A₁ D.B₁ x)) := by
    simp only [eB, RingEquiv.coe_trans, Function.comp_apply,
      integralClosureRingEquivOfSquare_coe]
    exact congrArg D.eL₁ (IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁
      (integralClosure B D.L₁) (algebraMap D.A₁ D.B₁ x))
  rw [hright, D.ringSquare x, D.eL₁_right]
  rfl

end Stacks.EppTheorem

end
