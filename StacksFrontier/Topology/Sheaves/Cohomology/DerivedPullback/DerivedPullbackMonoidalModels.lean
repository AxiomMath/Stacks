module

public import StacksFrontier.CategoryTheory.Functor.TransportBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ModelComparisonKFlat
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonPullbackKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidalKFlat

/-!
# The tensorator of `Lf^*` at the two models

For a morphism of ringed spaces `f : X ⟶ Y`, the oplax tensorator
`Lf^*(K ⊗ᴸ L) ⟶ Lf^*K ⊗ᴸ Lf^*L` of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal` at the locally small
model of [Stacks, Tag 079Q] is the comparison of [Stacks, Tag 079U] at the standard model,
`Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison`, transported along the
comparisons of the two models `StacksDraft.DerivedModel.derivedPullbackModelIso` and
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open CochainComplex.KFlatBifunctor RingedSpaceModuleAdjunction
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory
  abelianStructureSheafRing hasDerivedCategoryModulesX hasDerivedCategoryModulesY

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- `derivedPullbackModelIso` followed by the comparison `Lf^*(QK) ⟶ Q(f^*K)` at the locally
small model is the image of that comparison at the standard model. -/
private lemma derivedPullbackModelIso_hom_app_comp_derivedFunctorQComparison
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) K) :
    letI := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
      (SheafOfModules.{u} (structureSheafRing X))
    letI := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
      (SheafOfModules.{u} (structureSheafRing Y))
    (StacksDraft.DerivedModel.derivedPullbackModelIso f).hom.app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj K) ≫
      CochainComplex.KFlatMonoidal.derivedFunctorQComparison
        (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackKFlatIso f) hK =
    (Stacks.Injectives.grothendieckModelEquiv
        (SheafOfModules.{u} (structureSheafRing X))).functor.map
      ((derivedPullbackNatTrans f).app K) :=
  StacksDraft.DerivedModel.derivedPullbackModelIso_hom_app_Q_comp f K

/-- `derivedPullbackCanonicalMonoidal_δ_model` at the images of a pair of K-flat complexes. -/
private lemma derivedPullbackCanonicalMonoidal_δ_model_kFlat
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) K)
    (hL : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) L) :
    letI := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
      (SheafOfModules.{u} (structureSheafRing X))
    letI := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
      (SheafOfModules.{u} (structureSheafRing Y))
    @Functor.OplaxMonoidal.δ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal
        ((@DerivedCategory.Q _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
            (SheafOfModules.{u} (structureSheafRing Y)))).obj K)
        ((@DerivedCategory.Q _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
            (SheafOfModules.{u} (structureSheafRing Y)))).obj L) =
      Functor.transportBifunctorComparison
        (Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing Y))).functor
        (Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing X))).functor
        (StacksDraft.DerivedModel.derivedPullbackModelIso f)
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso Y.sheaf)
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso X.sheaf)
        (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj K)
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj L) := by
  let := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
    (SheafOfModules.{u} (structureSheafRing X))
  let := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
    (SheafOfModules.{u} (structureSheafRing Y))
  have hls := derivedPullbackCanonicalMonoidal_δ_comp f K L hK hL
  have hst := @derivedPullbackCanonicalMonoidal_δ_comp _ _ f (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) K L hK hL
  have hB2 := derivedPullbackCanonicalMonoidal_δ_eq_derivedPullbackTensorIso f
    ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj K)
    ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj L)
  have f₃ := Functor.map_comp_eq_of_eq
    (Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing X))).functor
    ((congrArg (· ≫ _) hB2).symm.trans hst)
  have pK := derivedPullbackModelIso_hom_app_comp_derivedFunctorQComparison f K hK
  have pL := derivedPullbackModelIso_hom_app_comp_derivedFunctorQComparison f L hL
  have pKL := derivedPullbackModelIso_hom_app_comp_derivedFunctorQComparison f _
    (CochainComplex.KFlatMonoidal.kFlat_tensor _ hK hL)
  have f₁ := (Functor.bifunctor_map_comp_map
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf) _ _ _ _).trans
    (congrArg₂ (fun a b => ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      X.sheaf).map a).app _ ≫ ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      X.sheaf).obj _).map b) pK pL)
  open Stacks.DerivedTensor.RingedSite in
  have f₂ := (Functor.whiskering_iso_inv_naturality_assoc _
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso X.sheaf)
      ((derivedPullbackNatTrans f).app K) ((derivedPullbackNatTrans f).app L) _).symm.trans
    (congrArg (_ ≫ ·)
      (derivedTensorProductFunctorModelIso_inv_app_app_comp_comparison_hom
        X.sheaf _ _ (kFlat_pullbackComplex f K hK) (kFlat_pullbackComplex f L hL)))
  have f₄ := ((StacksDraft.DerivedModel.derivedPullbackModelIso f).inv.naturality
    ((@Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparison _ _ _ Y.sheaf _ _
      (HasDerivedCategory.standard _) _ _ _
      (@Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _ _ _ Y.sheaf _ _
        (HasDerivedCategory.standard _) _ _ _) K L hK hL).hom)).symm
  have f₅ : (StacksDraft.DerivedModel.derivedPullbackModelIso f).inv.app _ ≫
      (Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing X))).functor.map
        ((derivedPullbackNatTrans f).app _) =
      (CochainComplex.KFlatMonoidal.derivedFunctorQComparison
        (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackKFlatIso f) (CochainComplex.KFlatMonoidal.kFlat_tensor _ hK hL)) :=
    (Iso.inv_comp_eq ((StacksDraft.DerivedModel.derivedPullbackModelIso f).app _)).2 pKL.symm
  open Stacks.DerivedTensor.RingedSite in
  have f₆ :=
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map_comp _ _).symm.trans
      (congrArg (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
        (derivedTensorProductFunctorModelIso_hom_app_app_comp_map_comparison_hom
          Y.sheaf K L hK hL))
  have iso := fun {M} (hM : KFlat _ M) =>
    CochainComplex.KFlatMonoidal.isIso_derivedFunctorQComparison
      (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (derivedPullbackKFlatIso f) hM
  refine Functor.eq_comp_of_squares ?_ hls f₁ f₂ f₃ f₄ f₅ f₆
  exact @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).mapIso
        (@asIso _ _ _ _ _ (iso hK))).app _ ≪≫
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj _).mapIso
        (@asIso _ _ _ _ _ (iso hL)) ≪≫
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).comparison
        ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlat_pullbackComplex f K hK) (kFlat_pullbackComplex f L hL)))

/-- **[Stacks, Tag 079U] at the two models.** For `K`, `L` in the standard model of `D(𝒪_Y)`,
the oplax tensorator of `Lf^*` at the locally small model, at the images `G K`, `G L` under the
comparison of the two models, is the comparison of [Stacks, Tag 079U] at the standard model
transported along `derivedPullbackModelIso` and `derivedTensorProductFunctorModelIso`. -/
theorem derivedPullbackCanonicalMonoidal_δ_model
    (K L : @DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) _ _
      (HasDerivedCategory.standard _)) :
    letI := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
      (SheafOfModules.{u} (structureSheafRing X))
    letI := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
      (SheafOfModules.{u} (structureSheafRing Y))
    @Functor.OplaxMonoidal.δ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal
        ((Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing Y))).functor.obj K)
        ((Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing Y))).functor.obj L) =
      Functor.transportBifunctorComparison
        (Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing Y))).functor
        (Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing X))).functor
        (StacksDraft.DerivedModel.derivedPullbackModelIso f)
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso Y.sheaf)
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso X.sheaf)
        (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f) K L := by
  refine Functor.eq_transportBifunctorComparison _ _ _ _ _ _
    (fun K L => @Functor.OplaxMonoidal.δ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback _ _ f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal K L)
    (fun u v => (@Functor.OplaxMonoidal.δ_natural _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback _ _ f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal _ _ _ _ u v).symm)
    (fun M => ∃ (P : CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
      (_ : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) P),
      M = (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj P) ?_ ?_ K L
  · intro M
    obtain ⟨P, π, hP, hπ⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso Y.sheaf
      ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).objPreimage M)
    have : IsIso ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).map π) :=
      (@DerivedCategory.isIso_Q_map_iff_quasiIso _ _ _ (HasDerivedCategory.standard _) _ _ π).2 hπ
    exact ⟨_, ⟨P, hP, rfl⟩,
      ⟨asIso ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).map π) ≪≫
        (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).objObjPreimageIso M⟩⟩
  · rintro _ _ ⟨P, hP, rfl⟩ ⟨P', hP', rfl⟩
    exact derivedPullbackCanonicalMonoidal_δ_model_kFlat f P P' hP hP'

end Stacks.Cohomology.DerivedPullbackTensor
