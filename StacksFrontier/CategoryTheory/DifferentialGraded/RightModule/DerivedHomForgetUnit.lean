module

public import StacksFrontier.Algebra.DifferentialGraded.Module.HomEvaluationDerivedIso
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomForgetInterface

/-!
# The comparison `β` in the shape step 3 of Tag 09LK records it

`DGCategory.RightModule.derivedHomForgetUnitOfLiftInterface` carries the comparison `β` of
[Stacks, Tag 09LK] as a hypothesis: it asks for a lift `V : K(A) ⥤ D(C(K, K))` of the
abelian-group-valued `Hom(K, -)` through the forgetful functor `DGCategory.endDerivedForget`,
exhibited by an isomorphism `ι : V ⋙ U ≅ Hom(K, -)`, together with a unit `η : V ⟶ Q ⋙ R̃`. The
`V` and the `η` are what steps 1 and 2 of the replacement proof deliver; the `ι` is
`CochainComplex.homDerivedLiftForgetIso`. This file feeds the two into that interface.

## The universe cost

The ambient differential graded category of the interface is a `DGCategory.{0, 0} ℤ`, a condition
inherited from step 1, which asks for `C : DGCategory.{v, v} R`. Its second universe argument is
the universe of the objects, so taking `C` to be the differential graded category of complexes in
`A` forces `A : Type 0`. Nothing else here needs it: `CochainComplex.homDerivedForgetUnit` is the
same comparison for `A` in any universe, obtained from
`CochainComplex.derivedHomForgetUnitOfLift` directly.

## Main definitions

* `DGCategory.RightModule.derivedHomForgetUnitAtReflector`: **the comparison `β`**, with `V` and
  `ι` supplied and only the unit `η` of steps 1 and 2 left as a hypothesis.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public noncomputable section

namespace DGCategory.RightModule

universe w v

open CategoryTheory CochainComplex

variable (A : Type) [Category.{0} A] [Abelian A] [HasDerivedCategory.{v} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  (Rt : DerivedCategory A ⥤
    RightModule.derivedCategory (endDGCategory (CochainComplex.dgCategory A) K))

/-- **The comparison `β` that step 3 of [Stacks, Tag 09LK] consumes, at the reflector's target.**
Step 3's interface is instantiated at the lift `CochainComplex.homDerivedLift` of the
abelian-group-valued `Hom(K, -)` and the identification
`CochainComplex.homDerivedLiftForgetIso` of that lift with `Hom(K, -)`; the only datum left is
the unit `η` that steps 1 and 2 of the replacement proof produce. -/
def derivedHomForgetUnitAtReflector
    (η : homDerivedLift A K ⟶ DerivedCategory.Qh ⋙ Rt) :
    CochainComplex.homToDerivedCategoryForget A K ⟶
      DerivedCategory.Qh ⋙ Rt ⋙ endDerivedForget (CochainComplex.dgCategory A) K :=
  derivedHomForgetUnitOfLiftInterface A K (CochainComplex.dgCategory A) K Rt
    (homDerivedLift A K) (homDerivedLiftForgetIso A K) η

end DGCategory.RightModule

end
