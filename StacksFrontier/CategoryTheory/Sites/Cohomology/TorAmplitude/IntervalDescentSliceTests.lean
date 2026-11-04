module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent

/-!
# A Tor test vanishing on the site vanishes on every slice

A hypothesis about the derived tensor product formed on the site is read against the one formed on
a slice, the direction opposite to
`OfEssentiallySmall.isZero_homology_derivedRestriction_tensorModule`.

## Main results

* `isZero_homology_tensorModule_restriction_of_isZero_homology`: if `Hⁱ(E ⊗^L_O G[0])` vanishes
  then so does `Hⁱ(E|_U ⊗^L_{O|_U} (G|_U)[0])`, formed against an arbitrary derived tensor
  product on the slice over `U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u c d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)]
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor
  OfEssentiallySmall.sliceTensorAdditive OfEssentiallySmall.sliceTensorObjAdditive
  OfEssentiallySmall.sliceHasMapBifunctor

variable [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max c u, u, u} (X.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived
  OfEssentiallySmall.sliceHasDerivedCategory

open Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall (restriction restrictionComplex) in
/-- **A Tor test vanishing on the site is a Tor test vanishing on every slice.** If the `i`-th
cohomology sheaf of `E ⊗^L_O G[0]` vanishes, then so does the `i`-th cohomology sheaf of
`E|_U ⊗^L_{O|_U} (G|_U)[0]`, formed against an arbitrary derived tensor product `TU` on the slice
over `U`. -/
theorem isZero_homology_tensorModule_restriction_of_isZero_homology
    (T : DerivedTensorProduct.{c, u, u, d} X) (U : X.C)
    (TU : DerivedTensorProduct.{max c u, u, u, d} (X.over U))
    (E : RingedSite.DerivedModules.{c, u, u, d} X)
    (G : RingedSite.Modules.{c, u, u} X) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{c, u, u} X) i).obj
      ((T.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{c, u, u} X) 0).obj G)))) :
    IsZero ((DerivedCategory.homologyFunctor
        (RingedSite.Modules.{max c u, u, u} (X.over U)) i).obj
      ((TU.tensor.obj ((RingedSite.derivedRestriction.{c, u, u, d} X U).obj E)).obj
        ((DerivedCategory.singleFunctor
            (RingedSite.Modules.{max c u, u, u} (X.over U)) 0).obj
          ((restriction X U).obj G)))) := by
  obtain ⟨A, pr, hA, hqi⟩ := Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize
    X.O (DerivedCategory.Q.objPreimage E)
  have _ := hqi
  have eA : DerivedCategory.Q.obj A ≅ E :=
    asIso (DerivedCategory.Q.map pr) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have eR : (RingedSite.derivedRestriction.{c, u, u, d} X U).obj E ≅
      DerivedCategory.Q.obj ((restrictionComplex X U).obj A) :=
    (RingedSite.derivedRestriction.{c, u, u, d} X U).mapIso eA.symm ≪≫
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O) U).mapDerivedCategoryFactors.app A
  have hres : IsZero ((DerivedCategory.homologyFunctor
      (RingedSite.Modules.{max c u, u, u} (X.over U)) i).obj
        ((RingedSite.derivedRestriction.{c, u, u, d} X U).obj
          ((T.tensor.obj (DerivedCategory.Q.obj A)).obj
            ((DerivedCategory.singleFunctor (RingedSite.Modules.{c, u, u} X) 0).obj G)))) := by
    refine IsZero.of_iso ?_ ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O) U) i).app _)
    exact (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O) U).map_isZero
        (h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
          ((T.tensor.mapIso eA).app _)))
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso
      ((TU.tensor.mapIso eR).app _) ≪≫
    OfEssentiallySmall.torTestIso X A U TU hA ((restriction X U).obj G) i)
  exact hres.of_iso (OfEssentiallySmall.restrictTorTestIso X A U T hA G i).symm

end Stacks.SheafOfModules.DerivedTensorProduct

end
