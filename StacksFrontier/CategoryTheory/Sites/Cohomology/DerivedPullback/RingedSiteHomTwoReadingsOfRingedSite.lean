module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.RingedSiteHomTwoReadings

/-!
# The two derived readings of a morphism of ringed sites, at a morphism of ringed sites

The results of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.RingedSiteHomTwoReadings` for the two
readings `h.toRingedToposSiteHom` and `h.ringedToposHom` of a morphism of ringed sites `h`
(Stacks 03AD), whose pullbacks of sheaves of modules are identified by
`RingedSite.Hom.pullbackModulesToposIso`.

## Main results

* `Stacks.Cohomology.RingedSiteHomReadings.isIso_projectionMap_toRingedToposSiteHom_iff`: the
  projection map of the site-presented reading is invertible exactly when the map of Stacks 0B56
  of the topos reading is.
* `Stacks.Cohomology.RingedSiteHomReadings.isIso_projectionFormulaMap_toRingedToposSiteHom_iff`:
  the maps of Stacks 0B56 of the two readings are invertible at the same objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod
open Stacks.Cohomology.AbstractKunnethMap (projectionMap)

universe u

namespace Stacks.Cohomology.RingedSiteHomReadings

-- The derived pullbacks of both readings are stated for the standard model of the derived
-- category.
attribute [local instance] HasDerivedCategory.standard

/-! ### The two readings of a morphism of ringed sites -/

section RingedSite

variable {X Y : RingedSite.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (h : RingedSite.Hom X Y)

/-- The derived pullback along the site-presented reading exists (Stacks 06YY). -/
instance hasLeftDerivedFunctor_toRingedToposSiteHom :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
      h.toRingedToposSiteHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy _
    h.isMorphismOfSites_toRingedToposSiteHom

/-- The morphism of ringed topoi `modulesHomOfSiteHom` of the site-presented reading
`h.toRingedToposSiteHom` is `h.ringedToposHom.toModulesHom`. -/
theorem modulesHomOfSiteHom_eq :
    Stacks.Sheaves.DerivedPullback.modulesHomOfSiteHom h.toRingedToposSiteHom
        h.isMorphismOfSites_toRingedToposSiteHom =
      h.ringedToposHom.toModulesHom :=
  RingedToposHom.toRingedToposModulesHom_eq_toModulesHom h.ringedToposHom

/-- **The two degreewise pullbacks of sheaves of modules along `h` agree.** -/
abbrev pullbackToposIso :
    h.toRingedToposSiteHom.pullbackTopos ≅ h.ringedToposHom.toModulesHom.pullbackModules :=
  pullbackModulesSiteIsoOfEq h.toRingedToposSiteHom h.isMorphismOfSites_toRingedToposSiteHom
    h.ringedToposHom.toModulesHom (modulesHomOfSiteHom_eq h)

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]

/-- `pullbackToposIso` carries the comparison of total tensor complexes of Stacks 03EL of the
site-presented reading to that of the topos reading. -/
theorem totalTensorCompat_pullbackToposIso :
    TotalTensorCompat h.toRingedToposSiteHom h.isMorphismOfSites_toRingedToposSiteHom
      h.ringedToposHom.toModulesHom (pullbackToposIso h) :=
  totalTensorCompat_pullbackModulesSiteIsoOfEq h.toRingedToposSiteHom
    h.isMorphismOfSites_toRingedToposSiteHom h.ringedToposHom.toModulesHom
    (modulesHomOfSiteHom_eq h)

/-- **The projection maps of the two readings of a morphism of ringed sites.** The projection map
`K ⊗^L Rh_*E ⟶ Rh_*(Lh^*K ⊗^L E)` of the site-presented reading `h.toRingedToposSiteHom` is
invertible exactly when the map `Rh_*E ⊗^L K ⟶ Rh_*(E ⊗^L Lh^*K)` of Stacks 0B56 of the topos
reading `h.ringedToposHom` is. -/
theorem isIso_projectionMap_toRingedToposSiteHom_iff
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    IsIso (projectionMap
        (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O))
        (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))
        (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction h.toRingedToposSiteHom
          h.isMorphismOfSites_toRingedToposSiteHom)
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso h.toRingedToposSiteHom
          h.isMorphismOfSites_toRingedToposSiteHom).hom K E) ↔
      IsIso (Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap h.ringedToposHom
        E K) :=
  isIso_projectionMap_iff_isIso_projectionFormulaMap (totalTensorCompat_pullbackToposIso h) E K

/-- **The maps of Stacks 0B56 of the two readings of a morphism of ringed sites**,
`Rh_*E ⊗^L K ⟶ Rh_*(E ⊗^L Lh^*K)`, are invertible at the same objects. -/
theorem isIso_projectionFormulaMap_toRingedToposSiteHom_iff
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
        h.toRingedToposSiteHom h.isMorphismOfSites_toRingedToposSiteHom E K) ↔
      IsIso (Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap h.ringedToposHom
        E K) :=
  isIso_projectionFormulaMap_iff_of_totalTensorCompat (totalTensorCompat_pullbackToposIso h) E K

end RingedSite

end Stacks.Cohomology.RingedSiteHomReadings

end
