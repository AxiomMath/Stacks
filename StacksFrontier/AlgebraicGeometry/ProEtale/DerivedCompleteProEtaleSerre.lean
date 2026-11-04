module

public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedNakayamaProEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteInverseLimit
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteWeakSerre

/-!
# Derived complete sheaves on the small pro-étale site

Let `X` be a scheme and let `𝒪` be a sheaf of commutative rings on `X_proétale` with a sheaf of
ideals `ℐ`. This file proves three properties of derived completeness along `ℐ` on this site:

1. the sheaves of `𝒪`-modules which are derived complete form a weak Serre subcategory of all
   sheaves of `𝒪`-modules;
2. the limit of an inverse system `… → ℱ₃ → ℱ₂ → ℱ₁` of derived complete sheaves of
   `𝒪`-modules is derived complete;
3. an object `K` of `D(X_proétale, 𝒪)` is derived complete if and only if each cohomology sheaf
   `Hᵖ(K)` is.

## Main results

* `AlgebraicGeometry.ProEtale.isWeakSerreClass_isDerivedComplete_proetale`: the weak Serre
  property.
* `AlgebraicGeometry.ProEtale.isDerivedComplete_limit_proetale`: limits of inverse systems.
* `AlgebraicGeometry.ProEtale.isDerivedComplete_iff_homology_proetale`: the criterion on
  cohomology sheaves.

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
* [Stacks Project, Tag 0990](https://stacks.math.columbia.edu/tag/0990)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtale.hasSheafify_proetale_addCommGrpCat_succ
  AlgebraicGeometry.ProEtale.wEqualsLocallyBijective_proetale_addCommGrpCat_succ

universe u

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (O : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (proetaleRingedSite X O).O)))

/-- The derived complete sheaves of modules on `X_proétale` form a weak Serre subcategory of all
sheaves of modules, for any sheaf of rings `𝒪` and sheaf of ideals `ℐ ⊂ 𝒪`. -/
theorem isWeakSerreClass_isDerivedComplete_proetale :
    ObjectProperty.IsWeakSerreClass
      (fun F : SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (proetaleRingedSite X O).O) =>
        RingedSite.IsDerivedComplete.{u + 1, u, u + 1, u + 1} (proetaleRingedSite X O) I
          ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  RingedSite.derivedCompleteSheaves_isWeakSerreClass_of_slicedObjectsSituation
    (proetaleRingedSite X O)
    (Scheme.ProEt.slicedObjectsSituation X
      (Stacks.SheafOfModules.Tensor.ringSheaf (proetaleRingedSite X O).O)) I

/-- The limit of an inverse system of derived complete sheaves of modules on `X_proétale` is
derived complete, for any sheaf of rings `𝒪` and sheaf of ideals `ℐ ⊂ 𝒪`. -/
theorem isDerivedComplete_limit_proetale
    (F : ℕᵒᵖ ⥤ SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (proetaleRingedSite X O).O))
    (hF : ∀ n : ℕ, RingedSite.IsDerivedComplete.{u + 1, u, u + 1, u + 1}
      (proetaleRingedSite X O) I ((DerivedCategory.singleFunctor _ 0).obj (F.obj (op n)))) :
    RingedSite.IsDerivedComplete.{u + 1, u, u + 1, u + 1} (proetaleRingedSite X O) I
      ((DerivedCategory.singleFunctor _ 0).obj (limit F)) :=
  RingedSite.isDerivedComplete_limit_of_slicedObjectsSituation (proetaleRingedSite X O)
    (Scheme.ProEt.slicedObjectsSituation X
      (Stacks.SheafOfModules.Tensor.ringSheaf (proetaleRingedSite X O).O)) I F hF

/-- An object of `D(X_proétale, 𝒪)` is derived complete if and only if each of its cohomology
sheaves is, for any sheaf of rings `𝒪` and sheaf of ideals `ℐ ⊂ 𝒪`. -/
theorem isDerivedComplete_iff_homology_proetale
    (K : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (proetaleRingedSite X O).O))) :
    RingedSite.IsDerivedComplete.{u + 1, u, u + 1, u + 1} (proetaleRingedSite X O) I K ↔
      ∀ p : ℤ, RingedSite.IsDerivedComplete.{u + 1, u, u + 1, u + 1} (proetaleRingedSite X O) I
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ p).obj K)) :=
  RingedSite.isDerivedComplete_iff_homology_of_slicedObjectsSituation (proetaleRingedSite X O) I
    (Scheme.ProEt.slicedObjectsSituation X
      (Stacks.SheafOfModules.Tensor.ringSheaf (proetaleRingedSite X O).O)) K

end AlgebraicGeometry.ProEtale

end
