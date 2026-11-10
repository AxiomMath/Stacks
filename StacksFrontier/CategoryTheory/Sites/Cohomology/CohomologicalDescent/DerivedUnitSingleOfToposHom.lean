module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleCollapseViaPlus
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescentOfToposHom
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
public import StacksFrontier.Homology.CompositeCollapse

/-!
# The derived unit at a module placed in degree zero, for a morphism of ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi along which the pullback of
modules is exact, and let `N` be an `𝒪'`-module. If the unit `N ⟶ f_*f^*N` is invertible and
`Rⁿf_*(f^*N) = 0` for `n > 0`, then the unit of the derived adjunction `Lf^* ⊣ Rf_*` of
Stacks 07A6 is invertible at `N[0]`: `N[0] ≅ Rf_*Lf^*(N[0])`.

The derived unit at `N[0]`, followed by `Rf_*` of the comparison map of `Lf^*`, is the degreewise
unit followed by the comparison map of `Rf_*` at `f^*(N[0]) = (f^*N)[0]`. The comparison of
`Lf^*` is invertible because `f^*` is exact, the degreewise unit because the unit at `N` is, and
the comparison of `Rf_*` at `(f^*N)[0]` because `f^*N` is right acyclic for `f_*`.

## Main results

* `isIso_derivedPullbackComparison_app`: along a morphism with exact pullback of modules the
  comparison map of `Lf^*` is invertible.
* `isIso_derivedUnit_app_singleFunctor_obj_of_isZero_rightDerived`: the derived unit at `N[0]` is
  invertible.

## Implementation notes

The derived adjunction of Stacks 07A6 is built on the standard model of the derived categories,
`HasDerivedCategory.standard`, which is therefore passed explicitly in the statements; the
library also carries a global instance for the derived category of sheaves of modules.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0D7V](https://stacks.math.columbia.edu/tag/0D7V)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward

namespace Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom

universe w

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

section Exact

variable [PreservesFiniteLimits f.toModulesHom.pullbackModules]

/-- **Along a morphism with exact pullback of modules, the comparison map of `Lf^*` is
invertible**: `Lf^*` is identified with the functor induced by `f^*` on derived categories, whose
comparison map is invertible. -/
theorem isIso_derivedPullbackComparison_app
    (M : HomotopyCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) :
    IsIso ((DerivedPullbackOfToposHom.derivedPullbackComparison f).app M) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  let := RingedToposHom.pullbackModules_preservesFiniteColimits f
  have : f.toModulesHom.pullbackModules.mapDerivedCategory.IsLeftDerivedFunctor
      f.toModulesHom.pullbackModules.mapDerivedCategoryFactorsh.hom
      (DerivedPullbackOfToposHom.quasiIsoTarget (Y := Y)) :=
    Functor.isLeftDerivedFunctor_of_inverts
      (DerivedPullbackOfToposHom.quasiIsoTarget (Y := Y)) _
      f.toModulesHom.pullbackModules.mapDerivedCategoryFactorsh
  have h := Functor.leftDerivedNatTrans_app (DerivedPullbackOfToposHom.derivedPullback f)
    f.toModulesHom.pullbackModules.mapDerivedCategory
    (DerivedPullbackOfToposHom.derivedPullbackComparison f)
    f.toModulesHom.pullbackModules.mapDerivedCategoryFactorsh.hom
    (DerivedPullbackOfToposHom.quasiIsoTarget (Y := Y)) (𝟙 _) M
  have : IsIso ((Functor.leftDerivedNatTrans (DerivedPullbackOfToposHom.derivedPullback f)
      f.toModulesHom.pullbackModules.mapDerivedCategory
      (DerivedPullbackOfToposHom.derivedPullbackComparison f)
      f.toModulesHom.pullbackModules.mapDerivedCategoryFactorsh.hom
      (DerivedPullbackOfToposHom.quasiIsoTarget (Y := Y)) (𝟙 _)).app
        (DerivedCategory.Qh.obj M)) :=
    (inferInstance : IsIso ((derivedPullbackNatIso f).hom.app (DerivedCategory.Qh.obj M)))
  rw [NatTrans.id_app, Category.comp_id] at h
  rw [← h]
  infer_instance

variable [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **The derived unit at `N[0]`, from the vanishing of the higher direct images.** If the unit
`N ⟶ f_*f^*N` is invertible and `Rⁿf_*(f^*N) = 0` for `n > 0`, then the unit
`N[0] ⟶ Rf_*Lf^*(N[0])` of the derived adjunction is invertible. -/
theorem isIso_derivedUnit_app_singleFunctor_obj_of_isZero_rightDerived
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hN : IsIso ((RingedToposHom.pullbackAdjPushforwardModules f).unit.app N))
    (hvan : haveI := RingedToposHom.pushforwardModules_additive f
      ∀ n : ℕ, 0 < n → IsZero (((RingedToposHom.pushforwardModules f).rightDerived n).obj
        (f.toModulesHom.pullbackModules.obj N))) :
    IsIso ((derivedPullbackPushforwardAdjunctionOfToposHom f).unit.app
      ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) 0).obj N)) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  have := RingedToposHom.pushforwardModules_additive f
  have : PreservesFiniteLimits (RingedToposHom.pushforwardModules f) :=
    have : PreservesLimitsOfSize.{0, 0} (RingedToposHom.pushforwardModules f) :=
      (RingedToposHom.pullbackAdjPushforwardModules f).rightAdjoint_preservesLimits
    inferInstance
  have hM := (Stacks.RightDerivedComp.rightAcyclic_iff_acyclic
    (RingedToposHom.pushforwardModules f) (f.toModulesHom.pullbackModules.obj N)).2 hvan
  have := SheafOfModules.isGrothendieckAbelianU (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let M := (HomotopyCategory.singleFunctor
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N
  -- the degreewise unit at `N[0]` is invertible
  have hu : IsIso ((Adjunction.mapHomologicalComplexAdjunction
      (RingedToposHom.pullbackAdjPushforwardModules f) (ComplexShape.up ℤ)).unit.app
        ((CochainComplex.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)) := by
    have (n : ℤ) : IsIso (((Adjunction.mapHomologicalComplexAdjunction
        (RingedToposHom.pullbackAdjPushforwardModules f) (ComplexShape.up ℤ)).unit.app
          ((CochainComplex.singleFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)).f n) := by
      change IsIso ((RingedToposHom.pullbackAdjPushforwardModules f).unit.app
        (((CochainComplex.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N).X n))
      by_cases hn : n = 0
      · subst hn
        exact (NatTrans.isIso_app_iff_of_iso _
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).symm).1 hN
      · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N n hn
        exact hz.isIso ((RingedToposHom.pushforwardModules f).map_isZero
          (f.toModulesHom.pullbackModules.map_isZero hz)) _
    exact HomologicalComplex.Hom.isIso_of_components _
  have hkappa : IsIso (DerivedCategory.Qh.map
      ((pullbackAdjPushforwardMapHomotopy f).unit.app M)) :=
    Functor.map_isIso (HomotopyCategory.quotient
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      ((Adjunction.mapHomologicalComplexAdjunction
        (RingedToposHom.pullbackAdjPushforwardModules f) (ComplexShape.up ℤ)).unit.app
          ((CochainComplex.singleFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N))
  -- the comparison map of `Rf_*` at `f^*(N[0]) ≅ (f^*N)[0]` is invertible
  have hpush : IsIso (((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit
      DerivedCategory.Qh (sourceQuasiIso X)).app ((pullbackMapHomotopy f).obj M)) := by
    refine (NatTrans.isIso_app_iff_of_iso _
      (((HomotopyCategory.quotient
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex f.toModulesHom.pullbackModules
            (ComplexShape.up ℤ) 0).app N)).symm ≪≫
        ((f.toModulesHom.pullbackModules.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
          ((CochainComplex.singleFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)).symm)).1 ?_
    exact Functor.isIso_app_single_of_rightAcyclic
      (RingedToposHom.pushforwardModules f) (derivedPushforward (X := X) (Y := Y) f)
      ((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit
        DerivedCategory.Qh (sourceQuasiIso X))
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.exists_quasiIso_isKInjective X)
      _ hM
  have hcmp : IsIso ((leftDerivedPullbackOfKFlat f).comparison.app M) :=
    isIso_derivedPullbackComparison_app f M
  have hmid : IsIso ((derivedPullbackPushforwardAdjunctionOfToposHom f).unit.app
      (DerivedCategory.Qh.obj M)) := by
    have hprod : IsIso ((derivedPullbackPushforwardAdjunctionOfToposHom f).unit.app
        (DerivedCategory.Qh.obj M) ≫ (derivedPushforward (X := X) (Y := Y) f).map
          ((leftDerivedPullbackOfKFlat f).comparison.app M)) := by
      change IsIso ((derivedPullbackPushforwardAdjunction f (leftDerivedPullbackOfKFlat f)).unit.app
        (DerivedCategory.Qh.obj M) ≫ (derivedPushforward (X := X) (Y := Y) f).map
          ((leftDerivedPullbackOfKFlat f).comparison.app M))
      rw [derivedPullbackPushforwardAdjunction_unit_fac f (leftDerivedPullbackOfKFlat f) M]
      infer_instance
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
      ((derivedPushforward (X := X) (Y := Y) f).map
        ((leftDerivedPullbackOfKFlat f).comparison.app M))
      (Iso.isIso_hom ((derivedPushforward (X := X) (Y := Y) f).mapIso
        (@asIso _ _ _ _ ((leftDerivedPullbackOfKFlat f).comparison.app M) hcmp))) hprod
  exact (NatTrans.isIso_app_iff_of_iso (derivedPullbackPushforwardAdjunctionOfToposHom f).unit
    ((DerivedCategory.singleFunctorIsoCompQh
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).app N).symm).1 hmid

end Exact

end Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom

end
