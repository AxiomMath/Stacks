module

public import StacksFrontier.Homology.HomComplex.ShiftHom
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.HomShift.DerivedShift

/-!
# Derived Hom commutes with the shift in its source

Let `A` be a commutative ring and let `Ω` be an object of the derived category of `A`-modules.
For the contravariant functor `K ↦ RHom_A(K, Ω)` of `Dualizing.dualizingDerivedHomFunctor`,
shifting the *source* shifts derived Hom the other way:

`RHom_A(K⟦n⟧, Ω) ≅ RHom_A(K, Ω)⟦-n⟧`.

This is a different statement from the identification `RHom_A(K, Ω⟦i⟧) ≅ RHom_A(K, Ω)⟦i⟧` for
the *target*, `Dualizing.dualizingDerivedHomShift`, and does not follow formally from it.

## Main definitions

* `StacksDraft.DerivedHom.HomShift.homComplexSourceShiftIso` — the cochain-level identification
  `Hom^•(L⟦n⟧, J) ≅ Hom^•(L, J)⟦-n⟧`, which is [Stacks, Tag 0FNN] at `a = 0`, `b = n` with the
  target shift by zero removed.
* `Dualizing.dualizingDerivedHomSourceShiftOfModel` — the derived identification for a source
  and a target presented by cochain complexes of `ULift A`-modules, the target K-injective.
* `Dualizing.dualizingDerivedHomSourceShift` — **`RHom_A(K⟦n⟧, Ω) ≅ RHom_A(K, Ω)⟦-n⟧`** for
  arbitrary `K` and `Ω`.

## References

* [Stacks Project, Tag 0FNN](https://stacks.math.columbia.edu/tag/0FNN)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex

namespace StacksDraft.DerivedHom.HomShift

universe u v

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- **Shifting the source of a Hom complex shifts the Hom complex the other way:**
`Hom^•(L⟦n⟧, J) ≅ Hom^•(L, J)⟦-n⟧`.

This is `CochainComplex.HomComplex.homComplexShiftIso`, [Stacks, Tag 0FNN], at `a = 0` and
`b = n`, with the target shift by zero removed. -/
def homComplexSourceShiftIso (L J : Model.Complex (ULift.{v} A)) (n : ℤ) :
    HomComplexR (ULift.{v} A) (L⟦n⟧) J ≅
      (HomComplexR (ULift.{v} A) L J)⟦-n⟧ :=
  ((CategoryTheory.shiftFunctorZero (Model.Complex (ULift.{v} A)) ℤ).app
        (HomComplexR (ULift.{v} A) (L⟦n⟧) J)).symm ≪≫
    homComplexTargetShiftIso (ULift.{v} A) (L⟦n⟧) J 0 ≪≫
    (homComplexShiftIso (ULift.{v} A) L J 0 n).1.symm ≪≫
    eqToIso (congrArg
      (fun k : ℤ => (CategoryTheory.shiftFunctor (Model.Complex (ULift.{v} A)) k).obj
        (HomComplexR (ULift.{v} A) L J))
      (zero_sub n))

end StacksDraft.DerivedHom.HomShift

namespace Dualizing

open StacksDraft.DerivedHom StacksDraft.DerivedHom.HomShift

universe u v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] StacksDraft.DerivedHom.HomShift.scalarEquivalenceCommShift

variable (A : Type u) [CommRing A]

/-- **Derived Hom commutes with the shift in its source**, for a source and a target presented
as scalar transports of cochain complexes of `ULift A`-modules, the target by a K-injective
one. -/
def dualizingDerivedHomSourceShiftOfModel
    (L J : Model.Complex (ULift.{v} A)) [J.IsKInjective] (n : ℤ)
    {K Ω : DerivedCategory (ModuleCat.{max u v} A)}
    (sigma : K ≅ (scalarLocalization.{u, v} A).obj L)
    (rho : Ω ≅ (scalarLocalization.{u, v} A).obj J) :
    (dualizingDerivedHomFunctor.{u, v} A Ω).obj
        (Opposite.op ((CategoryTheory.shiftFunctor
          (DerivedCategory (ModuleCat.{max u v} A)) n).obj K)) ≅
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) (-n)).obj
        ((dualizingDerivedHomFunctor.{u, v} A Ω).obj (Opposite.op K)) :=
  let sigmaShift :
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) n).obj K ≅
        (scalarLocalization.{u, v} A).obj (L⟦n⟧) :=
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) n).mapIso sigma ≪≫
      (((scalarLocalization.{u, v} A).commShiftIso n).app L).symm
  (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.mapIso
      (Iso.prod sigmaShift.symm.op rho) ≪≫
    derivedHomModelIso.{u, v} A (L⟦n⟧) J ≪≫
    (scalarLocalization.{u, v} A).mapIso (homComplexSourceShiftIso.{u, v} A L J n) ≪≫
    ((scalarLocalization.{u, v} A).commShiftIso (-n)).app
      (HomComplexR (ULift.{v} A) L J) ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) (-n)).mapIso
      ((derivedHomModelIso.{u, v} A L J).symm ≪≫
        ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.mapIso
          (Iso.prod sigma.symm.op rho)).symm)

/-- **Derived Hom commutes with the shift in its source:**
`RHom_A(K⟦n⟧, Ω) ≅ RHom_A(K, Ω)⟦-n⟧`, for arbitrary objects `K` and `Ω` of the derived category
of `A`-modules. -/
def dualizingDerivedHomSourceShift (Ω : DerivedCategory (ModuleCat.{max u v} A)) (n : ℤ)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    (dualizingDerivedHomFunctor.{u, v} A Ω).obj
        (Opposite.op ((CategoryTheory.shiftFunctor
          (DerivedCategory (ModuleCat.{max u v} A)) n).obj K)) ≅
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) (-n)).obj
        ((dualizingDerivedHomFunctor.{u, v} A Ω).obj (Opposite.op K)) := by
  have hK := exists_isKInjective_model ((derivedScalarEquivalence.{u, v} A).inverse.obj K)
  have hO := exists_isKInjective_model ((derivedScalarEquivalence.{u, v} A).inverse.obj Ω)
  have hJ : hO.choose.IsKInjective := hO.choose_spec.1
  exact dualizingDerivedHomSourceShiftOfModel.{u, v} A hK.choose hO.choose n
    (((derivedScalarEquivalence.{u, v} A).counitIso.app K).symm ≪≫
      (derivedScalarEquivalence.{u, v} A).functor.mapIso hK.choose_spec.2.some.symm)
    (((derivedScalarEquivalence.{u, v} A).counitIso.app Ω).symm ≪≫
      (derivedScalarEquivalence.{u, v} A).functor.mapIso hO.choose_spec.2.some.symm)

end Dualizing

end
