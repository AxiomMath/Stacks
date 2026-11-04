module

public import Mathlib.CategoryTheory.Linear.Yoneda
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomCohomologyNatural
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Degree-zero cohomology of the internal hom is the homotopy-category Hom, naturally

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. Tag 09LC identifies, for each right differential
graded `B`-module `P`,

`H^0(Hom^•_B(N, P)) = Hom_{K(B, d)}(N, P)`,

and `DifferentialGradedModule.HomModuleData.gradedCohomologyZeroEquiv` is that identification for
a single `P`. This file upgrades it to an isomorphism of *functors*: both sides are functors of
`P`, the left one through the internal hom functor of Tag 0FQQ and the right one through the
`R`-linear co-Yoneda embedding of the homotopy category, and the identification is natural.

Naturality is the form in which the identification is used by Tag 0CS5, where it has to be
compared with a natural transformation of derived functors.

## Main definitions

* `DifferentialGradedModule.homCohomologyZeroFunctorIso`: the natural isomorphism on the category
  of differential graded `B`-modules.
* `DifferentialGradedModule.homCohomologyZeroNatIso`: the same on the homotopy category `K(B, d)`,
  where the left-hand functor is the internal hom functor of Tag 0FQQ followed by degree-zero
  cohomology of Tag 09KW.

## Implementation notes

*Why the identification is a composite of three explicit steps.* On a single module the
identification is
`DifferentialGradedModule.HomModuleData.gradedCohomologyZeroEquiv`, which composes the explicit
cohomology of the internal hom with the bijection of Tag 09LC. Rather than chase naturality
through that composite, the whole map is computed on a representative: the class of a degree-zero
cocycle of `Hom^•_B(N, P)` goes to the homotopy class of the homomorphism `N ⟶ P` with the same
underlying linear map (`DifferentialGradedModule.gradedCohomologyZeroEquiv_mk`). Naturality is
then the statement that the internal hom functor acts by postcomposition, which is Tag 0FQQ's
`DifferentialGradedModule.homPostcompHomogeneousMap_apply`.

*Why the passage to the homotopy category is a descent.* Both functors on `K(B, d)` are already
given, so there is nothing to lift: what is lifted is the natural isomorphism, by
`CategoryTheory.Quotient.natIsoLift`, which is available because every morphism of a quotient
category is the class of a morphism of the original one. The left-hand functor is identified with
the internal hom functor on differential graded modules by
`DifferentialGradedModule.homHomotopyDescent`, and degree-zero cohomology on the homotopy category
with the homology of the underlying cochain complex by
`DifferentialGradedModule.degreeZeroCohomologyOnHomotopyIso'`.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
* [Stacks Project, Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ)
* [Stacks Project, Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR)
* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A B : DifferentialGradedAlgebra R)
  (N : DifferentialGradedModule B) (L : BimoduleStructure A B N)
  {P P' : DifferentialGradedModule B}

/-! ### The identification on a single module, computed on a representative -/

/-- The degree-zero cohomology class of a cocycle of the internal hom goes to the homotopy class
of the homomorphism `N ⟶ P` that the cocycle is. -/
theorem gradedCohomologyZeroEquiv_mk {A B : DifferentialGradedAlgebra R}
    {N P : DifferentialGradedModule B} {L : BimoduleStructure A B N}
    (H : HomModuleData A B N P L) (c : H.module.gradedCocycles 0) :
    H.gradedCohomologyZeroEquiv (Submodule.Quotient.mk c) =
      (toHomotopyCategory B).map (homOfCocycle B (H.cocyclesEquiv 0 c)) := rfl

/-- The underlying linear map of the cocycle of the internal hom attached to a degree-zero
cocycle. -/
theorem cocyclesEquiv_val_val {A B : DifferentialGradedAlgebra R}
    {N P : DifferentialGradedModule B} {L : BimoduleStructure A B N}
    (H : HomModuleData A B N P L) (c : H.module.gradedCocycles 0) :
    ((H.cocyclesEquiv 0 c).1 : HomogeneousMap B N P 0).1 =
      (H.homogeneousEquiv 0 (c : H.module.grading 0)).1 := rfl

/-! ### Naturality on differential graded modules -/

/-- Reading a homogeneous element of a presentation of the internal hom as a homogeneous map does
not depend on which of two equal degrees is used. -/
theorem homogeneousEquiv_val_apply_congr {A B : DifferentialGradedAlgebra R}
    {N P : DifferentialGradedModule B} {L : BimoduleStructure A B N}
    (H : HomModuleData A B N P L) {i j : ℤ} (hij : i = j)
    (f : H.module.grading i) (g : H.module.grading j)
    (hfg : (f : H.module.M) = (g : H.module.M)) {p : ℤ} (x : N.grading p) :
    ((H.homogeneousEquiv i f).1 x : P.M) = ((H.homogeneousEquiv j g).1 x : P.M) := by
  subst hij
  obtain rfl : f = g := Subtype.ext hfg
  rfl

/-- **The internal hom functor acts by postcomposition**, on the value of the homogeneous map
attached to a homogeneous element. -/
theorem homModuleFunctor_map_homogeneousEquiv_apply (h : P ⟶ P') (q : ℤ)
    (v : ((homModuleFunctor A B N L).obj P).grading q) {p : ℤ} (x : N.grading p) :
    (((homModulePresentation A B N L P').homogeneousEquiv q
        (((homModuleFunctor A B N L).map h).gradedMap q v)).1 x : P'.M) =
      h.toFun (((((homModulePresentation A B N L P).homogeneousEquiv q v).1 x) : P.M)) := by
  have key := homPostcompHomogeneousMap_apply A B N L (homModulePresentation A B N L P)
    (homModulePresentation A B N L P') 0 q (cocycleOfHom B h).1 v
  have hv : (((homModuleFunctor A B N L).map h).gradedMap q v).val =
      (((homModulePresentation A B N L P').homogeneousEquiv (0 + q)).symm
        (homogeneousMapComp B (rfl : (0 : ℤ) + q = 0 + q) (cocycleOfHom B h).1
          ((homModulePresentation A B N L P).homogeneousEquiv q v))).val := key
  refine (homogeneousEquiv_val_apply_congr (homModulePresentation A B N L P')
    (show q = 0 + q by omega) _ _ hv x).trans ?_
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- **The internal hom functor acts by postcomposition.** -/
theorem homModuleFunctor_map_homogeneousEquiv (h : P ⟶ P') (q : ℤ)
    (v : ((homModuleFunctor A B N L).obj P).grading q) :
    (homModulePresentation A B N L P').homogeneousEquiv q
        (((homModuleFunctor A B N L).map h).gradedMap q v) =
      homogeneousMapComp B (zero_add q) (cocycleOfHom B h).1
        ((homModulePresentation A B N L P).homogeneousEquiv q v) :=
  homogeneousMap_ext fun _p x => homModuleFunctor_map_homogeneousEquiv_apply A B N L h q v x

/-- **Tag 09LC is natural in the target.** The homomorphism `N ⟶ P'` attached to the image of a
degree-zero cocycle of `Hom^•_B(N, P)` under the internal hom functor is the homomorphism attached
to the cocycle, followed by `h`. -/
theorem homOfCocycle_cocyclesEquiv_gradedCocyclesMap (h : P ⟶ P')
    (c : ((homModuleFunctor A B N L).obj P).gradedCocycles 0) :
    homOfCocycle B ((homModulePresentation A B N L P').cocyclesEquiv 0
        (gradedCocyclesMap ((homModuleFunctor A B N L).map h) 0 c)) =
      homOfCocycle B ((homModulePresentation A B N L P).cocyclesEquiv 0 c) ≫ h := by
  refine Hom.ext ?_
  have hval := homModuleFunctor_map_homogeneousEquiv A B N L h 0 (c : _)
  show ((homModulePresentation A B N L P').homogeneousEquiv 0
      (((homModuleFunctor A B N L).map h).gradedMap 0 (c : _))).1 = _
  rw [hval]
  rfl

/-! ### The natural isomorphism -/

/-- **`H^0(Hom^•_B(N, -)) ≅ Hom_{K(B,d)}(N, -)`, naturally.** The degree-zero cohomology of the
internal hom out of a differential graded `(A, B)`-bimodule is the module of morphisms out of `N`
in the homotopy category of right differential graded `B`-modules, naturally in the target. -/
def homCohomologyZeroFunctorIso :
    homModuleFunctor A B N L ⋙ gradedCohomologyFunctor A 0 ≅
      toHomotopyCategory B ⋙ (linearCoyoneda R (HomotopyCategory B)).obj
        (Opposite.op ((toHomotopyCategory B).obj N)) :=
  NatIso.ofComponents
    (fun P => (homModulePresentation A B N L P).gradedCohomologyZeroEquiv.toModuleIso)
    fun {P P'} h => by
      refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
      induction z using Submodule.Quotient.induction_on with
      | H c =>
        change (toHomotopyCategory B).map (homOfCocycle B
            ((homModulePresentation A B N L P').cocyclesEquiv 0
              (gradedCocyclesMap ((homModuleFunctor A B N L).map h) 0 c))) =
          (toHomotopyCategory B).map (homOfCocycle B
            ((homModulePresentation A B N L P).cocyclesEquiv 0 c)) ≫ (toHomotopyCategory B).map h
        rw [homOfCocycle_cocyclesEquiv_gradedCocyclesMap, Functor.map_comp]

/-- The restriction to differential graded modules of the identification on the homotopy
category. -/
def homCohomologyZeroRestrictedIso :
    toHomotopyCategory B ⋙ (homHomotopyCategoryFunctor A B N L ⋙
        degreeZeroCohomologyOnHomotopy' A) ≅
      toHomotopyCategory B ⋙ (linearCoyoneda R (HomotopyCategory B)).obj
        (Opposite.op ((toHomotopyCategory B).obj N)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (homHomotopyDescent N L) (degreeZeroCohomologyOnHomotopy' A) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (homModuleFunctor A B N L) (degreeZeroCohomologyOnHomotopyIso' A) ≪≫
    Functor.isoWhiskerLeft (homModuleFunctor A B N L) (gradedCohomologyFunctorIso A 0) ≪≫
    homCohomologyZeroFunctorIso A B N L

/-- **`H^0(Hom^•_B(N, -)) ≅ Hom_{K(B,d)}(N, -)` on the homotopy category.** Degree-zero
cohomology of the internal hom out of a differential graded `(A, B)`-bimodule, as a functor on
`K(B, d)`, is the module of morphisms out of `N` in `K(B, d)`.

This is Tag 09LC read functorially: the left-hand side is the internal hom functor of Tag 0FQQ
followed by the degree-zero cohomology functor of Tag 09KW. -/
@[stacks 09LC "degree-zero cohomology of the internal hom, functorially"]
def homCohomologyZeroNatIso :
    homHomotopyCategoryFunctor A B N L ⋙ degreeZeroCohomologyOnHomotopy' A ≅
      (linearCoyoneda R (HomotopyCategory B)).obj
        (Opposite.op ((toHomotopyCategory B).obj N)) :=
  CategoryTheory.Quotient.natIsoLift _ (homCohomologyZeroRestrictedIso A B N L)

end DifferentialGradedModule

end
