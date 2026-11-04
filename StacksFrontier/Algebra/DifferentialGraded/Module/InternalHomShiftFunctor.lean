module

public import StacksFrontier.Algebra.DifferentialGraded.DerivedCategory.Triangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomShift
public import StacksCore.Tactic.StacksAttribute

/-!
# The internal hom functor commutes with the shift

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. Tag 0FQR gives, for each right differential graded
`B`-module `P` and each `k`, a sign-free isomorphism
`Hom^•_B(N, P)[k] ≅ Hom^•_B(N, P[k])`, and
`DifferentialGradedModule.homPresentationShiftIso` is that isomorphism for the presentations the
internal hom functor of Tag 0FQQ actually uses. This file proves it natural in `P`, so that it is
an isomorphism of functors, and descends that to the homotopy category `K(B, d)`.

## Main definitions

* `DifferentialGradedModule.homModuleFunctorShiftIso`: the isomorphism of functors on the
  category of differential graded `B`-modules.
* `DifferentialGradedModule.homHomotopyCategoryFunctorShiftIso`: the same on `K(B, d)`.

## Main results

* `DifferentialGradedModule.homPresentationShiftIso_naturality`: the shift comparison of Tag 0FQR
  is natural in the target module.

## Implementation notes

*How naturality is proved.* The shift comparison is not given by a formula but characterized, by
`DifferentialGradedModule.HomModuleData.IsShiftComparison`: corresponding elements have
homogeneous maps taking the same values on homogeneous elements of `N`. Both composites in the
naturality square are therefore evaluated on a homogeneous element, read through
`DifferentialGradedModule.HomModuleData.homogeneousEquiv`, and compared value by value using that
characterization together with
`DifferentialGradedModule.homModuleFunctor_map_homogeneousEquiv_apply`, which says that the
internal hom functor acts by postcomposition. Both composites turn out to take a homogeneous
element `f` to the postcomposition of `h` with the homogeneous map of `f`, which is what makes the
square commute.

The two sides of the square are not literally of the form that
`DifferentialGradedModule.HomModuleData.shiftComparison_unique` compares — that uniqueness is for
two comparisons between one fixed pair of presentations, while here the source and the target
module differ — so uniqueness cannot be used and the values have to be computed.

*Why the descent to the homotopy category goes through `Quotient.natIsoLift`.* The internal hom
functor on `K(B, d)` is not defined as a lift, but it is identified with the lift of the functor
on differential graded modules by `DifferentialGradedModule.homHomotopyDescent`; and the quotient
functors to the two homotopy categories commute with the shift by
`CategoryTheory.Quotient.functor_commShift`. Composing those identifications turns the statement
on differential graded modules into the statement on homotopy categories restricted along the
quotient functor, and `CategoryTheory.Quotient.natIsoLift` lifts it.

## References

* [Stacks Project, Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR)
* [Stacks Project, Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ)
* [Stacks Project, Tag 09JL](https://stacks.math.columbia.edu/tag/09JL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A B : DifferentialGradedAlgebra R)
  (N : DifferentialGradedModule B) (L : BimoduleStructure A B N)
  {P P' : DifferentialGradedModule B}

/-- **The shift comparison of Tag 0FQR is natural in the target module.** -/
theorem homPresentationShiftIso_naturality (h : P ⟶ P') (k : ℤ) :
    (shiftFunctor A k).map ((homModuleFunctor A B N L).map h) ≫
        (homPresentationShiftIso A B N L P' k).hom =
      (homPresentationShiftIso A B N L P k).hom ≫
        (homModuleFunctor A B N L).map ((shiftFunctor B k).map h) := by
  refine Hom.ext_of_grading fun n f => ?_
  set f' : (homModulePresentation A B N L P).module.grading (n + k) := ⟨f.1, f.property⟩ with hf'
  set Wh := (homModuleFunctor A B N L).map h with hWh
  set Wsh := (homModuleFunctor A B N L).map ((shiftFunctor B k).map h) with hWsh
  set φ := (homPresentationShiftIso A B N L P k).hom with hφ
  set φ' := (homPresentationShiftIso A B N L P' k).hom with hφ'
  have hmemL : φ'.toFun (Wh.toFun f.1) ∈
      (homModulePresentation A B N L (shift P' k)).module.grading n :=
    φ'.map_grading n _ (Wh.map_grading (n + k) f.1 f'.property)
  have hmemR : Wsh.toFun (φ.toFun f.1) ∈
      (homModulePresentation A B N L (shift P' k)).module.grading n :=
    Wsh.map_grading n _ (φ.map_grading n f.1 f.property)
  have key : (⟨φ'.toFun (Wh.toFun f.1), hmemL⟩ :
        (homModulePresentation A B N L (shift P' k)).module.grading n) =
      ⟨Wsh.toFun (φ.toFun f.1), hmemR⟩ := by
    apply ((homModulePresentation A B N L (shift P' k)).homogeneousEquiv n).injective
    refine homogeneousMap_ext fun p x => ?_
    have hL : (((homModulePresentation A B N L (shift P' k)).homogeneousEquiv n
          ⟨φ'.toFun (Wh.toFun f.1), hmemL⟩).1 x : P'.M) =
        h.toFun (((((homModulePresentation A B N L P).homogeneousEquiv (n + k) f').1 x) :
          P.M)) := by
      refine (homPresentationShiftIso_apply A B N L P' k n p (Wh.gradedMap (n + k) f') x).trans ?_
      exact homModuleFunctor_map_homogeneousEquiv_apply A B N L h (n + k) f' x
    have hR : (((homModulePresentation A B N L (shift P' k)).homogeneousEquiv n
          ⟨Wsh.toFun (φ.toFun f.1), hmemR⟩).1 x : P'.M) =
        h.toFun (((((homModulePresentation A B N L P).homogeneousEquiv (n + k) f').1 x) :
          P.M)) := by
      refine (homModuleFunctor_map_homogeneousEquiv_apply A B N L ((shiftFunctor B k).map h) n
        ⟨φ.toFun f.1, φ.map_grading n f.1 f.property⟩ x).trans ?_
      exact congrArg h.toFun (homPresentationShiftIso_apply A B N L P k n p f' x)
    exact hL.trans hR.symm
  exact congrArg Subtype.val key

/-- **The internal hom functor commutes with the shift.** The `k`-shift of `Hom^•_B(N, P)` is
`Hom^•_B(N, P[k])`, naturally in `P`. -/
def homModuleFunctorShiftIso (k : ℤ) :
    homModuleFunctor A B N L ⋙ CategoryTheory.shiftFunctor (DifferentialGradedModule A) k ≅
      CategoryTheory.shiftFunctor (DifferentialGradedModule B) k ⋙ homModuleFunctor A B N L :=
  NatIso.ofComponents (fun P => homPresentationShiftIso A B N L P k)
    fun h => homPresentationShiftIso_naturality A B N L h k

/-- The restriction to differential graded modules of the shift compatibility on the homotopy
category. -/
def homHomotopyCategoryFunctorShiftRestrictedIso (k : ℤ) :
    toHomotopyCategory B ⋙ (homHomotopyCategoryFunctor A B N L ⋙
        CategoryTheory.shiftFunctor (HomotopyCategory A) k) ≅
      toHomotopyCategory B ⋙ (CategoryTheory.shiftFunctor (HomotopyCategory B) k ⋙
        homHomotopyCategoryFunctor A B N L) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (homHomotopyDescent N L)
      (CategoryTheory.shiftFunctor (HomotopyCategory A) k) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (homModuleFunctor A B N L)
      ((toHomotopyCategory A).commShiftIso k).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (homModuleFunctorShiftIso A B N L k) (toHomotopyCategory A) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.shiftFunctor (DifferentialGradedModule B) k)
      (homHomotopyDescent N L).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((toHomotopyCategory B).commShiftIso k)
      (homHomotopyCategoryFunctor A B N L) ≪≫
    Functor.associator _ _ _

/-- **The internal hom functor on homotopy categories commutes with the shift.** -/
def homHomotopyCategoryFunctorShiftIso (k : ℤ) :
    homHomotopyCategoryFunctor A B N L ⋙
        CategoryTheory.shiftFunctor (HomotopyCategory A) k ≅
      CategoryTheory.shiftFunctor (HomotopyCategory B) k ⋙
        homHomotopyCategoryFunctor A B N L :=
  CategoryTheory.Quotient.natIsoLift _ (homHomotopyCategoryFunctorShiftRestrictedIso A B N L k)

end DifferentialGradedModule

end
