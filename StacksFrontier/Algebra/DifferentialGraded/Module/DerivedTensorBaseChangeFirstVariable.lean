module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorCounitDevissage

/-! # The dévissage of Stacks 0BZ5 in the first variable

Let `(A, d)`, `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`,
let `N'` be a differential graded `(B, C)`-bimodule, and let `P` be a differential graded
`(A, B)`-bimodule with property (P), that is: the right differential graded `Aᵒᵖ ⊗_R B`-module it
is by Tag 0FQJ carries a property-(P) filtration. If the comparison of Tag 0BZ2 from the derived
to the plain tensor product with `N'` is invertible at the base-change module `(A ⊗_R B)_B`, then
it is invertible at `P_B`.

This is the first half of the dévissage carried out in the proof of Stacks 0BZ5. The filtration
of `P` lives over `Aᵒᵖ ⊗_R B`; read over `B` its graded pieces are direct sums of shifts of
`(A ⊗_R B)_B`, by `DifferentialGraded.Bimodule.baseChangeDirectSumShiftsIso`, and the class of
right differential graded `B`-modules at which the comparison is invertible is closed under direct
sums, translations and admissible extensions and cokernels, by
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedTensorCounitDevissage.lean`. So the
induction of `DifferentialGradedModule.propertyPFiltration_induction` applies to the property
"invertible after restriction of scalars to `B`".

## Main results

* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_restrictScalars_of_propertyP`:
  the induction, for the restriction to `B` of any right differential graded
  `Aᵒᵖ ⊗_R B`-module with a property-(P) filtration.
* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_rightModule_of_propertyP`:
  its consequence for a differential graded `(A, B)`-bimodule with property (P), which is the
  first half of the dévissage of Tag 0BZ5.

## References

* [Stacks Project, Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5); the dévissage is in its
  proof.
* [Stacks Project, Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4), the base-change module.
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ), bimodules as modules over
  the graded tensor product.
* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), property (P).
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped DirectSum

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra R}

/-- **The dévissage of Stacks 0BZ5 in the first variable, over the graded tensor product.** If the
comparison of Tag 0BZ2 from the derived to the plain tensor product with the differential graded
`(B, C)`-bimodule `N'` is invertible at the base-change module `(A ⊗_R B)_B`, then it is invertible
at the restriction to `B` of every right differential graded `Aᵒᵖ ⊗_R B`-module carrying a
property-(P) filtration.

The property "the comparison is invertible at the restriction to `B`" has all four closure
properties the induction asks for: the graded pieces of the filtration restrict to direct sums of
shifts of `(A ⊗_R B)_B`, where the hypothesis applies; restriction commutes with direct sums and
carries an admissible short exact sequence to one. -/
theorem isIso_derivedTensorFunctorCounit_app_restrictScalars_of_propertyP (N' : Bimodule B C)
    (hbase : IsIso ((derivedTensorFunctorCounit N').app
      ((toHomotopyCategory B).obj (baseChangeModule A B))))
    {X : DifferentialGradedModule (tensorAlgebra A B)} (F : PropertyPFiltration X) :
    IsIso ((derivedTensorFunctorCounit N').app
      ((toHomotopyCategory B).obj (ofTensorRightModule A B X))) := by
  classical
  set φ := tensorIncludeRightHom (oppAlgebra A) B with hφ
  refine propertyPFiltration_induction
    (fun Y => IsIso ((derivedTensorFunctorCounit N').app
      ((toHomotopyCategory B).obj (restrictScalars φ Y))))
    (fun e h => isIso_derivedTensorFunctorCounit_app_of_iso N'
      ((restrictScalarsFunctor φ).mapIso e) h)
    (fun ι dec k => ?_) (fun N hN => ?_) (fun i p hip hK hM => ?_) (fun i p hip hK hL => ?_) F
  · refine isIso_derivedTensorFunctorCounit_app_of_iso N'
      (baseChangeDirectSumShiftsIso A B k).symm ?_
    exact isIso_derivedTensorFunctorCounit_app_directSumObj N' _
      (fun i => isIso_derivedTensorFunctorCounit_app_shiftObj N' _ (k i) hbase)
  · refine isIso_derivedTensorFunctorCounit_app_of_iso N'
      (restrictScalarsDirectSumObjIso φ (fun j : ULift.{u} ℕ => N j.down)).symm ?_
    exact isIso_derivedTensorFunctorCounit_app_directSumObj N' _ (fun j => hN j.down)
  · exact isIso_derivedTensorFunctorCounit_app_middle_of_admissible N'
      (restrictScalarsHom φ i) (restrictScalarsHom φ p)
      (restrictScalarsHom_isAdmissibleShortExact φ i p hip) hK hM
  · exact isIso_derivedTensorFunctorCounit_app_quotient_of_admissible N'
      (restrictScalarsHom φ i) (restrictScalarsHom φ p)
      (restrictScalarsHom_isAdmissibleShortExact φ i p hip) hK hL

/-- **The dévissage of Stacks 0BZ5 in the first variable.** If the comparison of Tag 0BZ2 from the
derived to the plain tensor product with the differential graded `(B, C)`-bimodule `N'` is
invertible at the base-change module `(A ⊗_R B)_B`, then it is invertible at `P_B` for every
differential graded `(A, B)`-bimodule `P` with property (P).

This is
`DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_restrictScalars_of_propertyP`
applied to the right `Aᵒᵖ ⊗_R B`-module that `P` is by Tag 0FQJ, whose restriction to `B` is
`P_B`. -/
theorem isIso_derivedTensorFunctorCounit_app_rightModule_of_propertyP (N' : Bimodule B C)
    (hbase : IsIso ((derivedTensorFunctorCounit N').app
      ((toHomotopyCategory B).obj (baseChangeModule A B))))
    (P : Bimodule A B) (hP : Nonempty (PropertyPFiltration (toTensorModule A B P))) :
    IsIso ((derivedTensorFunctorCounit N').app ((toHomotopyCategory B).obj P.rightModule)) :=
  isIso_derivedTensorFunctorCounit_app_of_iso N' (ofTensorRightModuleToTensorIso A B P)
    (isIso_derivedTensorFunctorCounit_app_restrictScalars_of_propertyP N' hbase hP.some)

end DifferentialGraded.Bimodule

end
