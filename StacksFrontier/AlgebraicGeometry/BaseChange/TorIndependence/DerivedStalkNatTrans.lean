module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkCharacterization

/-!
# The derived stalk comparison is determined as a morphism of functors

Two morphisms of functors out of a localization of `C` at `W` are equal as soon as they agree at
the images of a class of objects through which every object of `C` admits a morphism of `W`.
Applied to `DerivedCategory.Q`, the quasi-isomorphisms and the K-flat complexes of sheaves of
modules on a scheme, this shows that a morphism of functors from the derived stalk of the derived
pullback to derived extension of scalars of the derived stalk, satisfying the equation of
`AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison` at every K-flat complex, is the
derived stalk comparison `AlgebraicGeometry.derivedPullbackStalkIso` of Stacks 0098.

## Main results

* `StacksDraft.LeftResolutions.natTrans_eq_of_left_resolutions`: two morphisms of functors on a
  localization that agree on a resolving class are equal.
* `StacksDraft.LeftResolutions.natTrans_eq_of_kFlat`: two morphisms of functors on the derived
  category of sheaves of modules on a scheme that agree at every K-flat complex are equal.
* `AlgebraicGeometry.derivedPullbackStalkIso_hom_eq_of_kFlat`: a morphism of functors satisfying
  the characterizing equation of the derived stalk comparison at every K-flat complex is the
  derived stalk comparison.
* `AlgebraicGeometry.derivedPullbackStalkIso_hom_eq_of_kFlat_of_iso`: the same for a morphism
  out of a functor isomorphic to the derived stalk of the derived pullback.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u w

namespace StacksDraft.LeftResolutions

/-- If every object of `C` receives a morphism of `W` from an object satisfying `P`, then two
morphisms of functors out of the localization of `C` at `W` which agree at the images of the
objects satisfying `P` are equal. -/
theorem natTrans_eq_of_left_resolutions
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ Y : C, P Y ∧ ∃ p : Y ⟶ X, W p)
    {F G : D ⥤ H} (τ τ' : F ⟶ G)
    (hτ : ∀ X : C, P X → τ.app (Q.obj X) = τ'.app (Q.obj X)) : τ = τ' := by
  refine Localization.natTrans_ext Q W ?_
  intro X
  obtain ⟨Y, hY, p, hp⟩ := hP X
  have : IsIso (Q.map p) := Localization.inverts Q W p hp
  rw [← cancel_epi (F.map (Q.map p)), τ.naturality, τ'.naturality, hτ Y hY]

/-- Two morphisms of functors out of `DerivedCategory Y.Modules` are equal as soon as they agree
at `DerivedCategory.Q.obj P` for every K-flat complex `P`. -/
theorem natTrans_eq_of_kFlat {Y : Scheme.{u}} [HasDerivedCategory.{w} Y.Modules]
    {H : Type*} [Category* H] {F G : DerivedCategory Y.Modules ⥤ H} (τ τ' : F ⟶ G)
    (hτ : ∀ P : CochainComplex Y.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toSheafedSpace P →
      τ.app (DerivedCategory.Q.obj P) = τ'.app (DerivedCategory.Q.obj P)) : τ = τ' := by
  refine natTrans_eq_of_left_resolutions DerivedCategory.Q
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ))
    (fun P => Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toSheafedSpace P) ?_ τ τ' hτ
  intro K
  obtain ⟨P, s, hP, -, hs, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y.toSheafedSpace K
  exact ⟨P, hP, s, hs⟩

end StacksDraft.LeftResolutions

namespace AlgebraicGeometry

attribute [local instance] hasDerivedCategory_ringedSpaceModules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
  [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
  [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))]

/-- A morphism of functors from the derived stalk of the derived pullback to derived extension
of scalars of the derived stalk which satisfies the equation of
`AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison` at every K-flat complex is
`AlgebraicGeometry.derivedPullbackStalkIso`. -/
theorem derivedPullbackStalkIso_hom_eq_of_kFlat
    (τ : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom ⋙ derivedStalkFunctor x ⟶
      derivedStalkFunctor (f x) ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (f.stalkMap x).hom).functor)
    (hτ : ∀ P : CochainComplex Y.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toSheafedSpace P →
      τ.app (DerivedCategory.Q.obj P) ≫
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (f.stalkMap x).hom).functor.map
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
              (f x)).mapDerivedCategoryFactors.hom.app P) ≫
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (f.stalkMap x).hom).comparison.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
              (f x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
        (derivedStalkFunctor x).map (pullbackComparisonOnComplex f P) ≫
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
            (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso f x).symm
              (ComplexShape.up ℤ)).hom.app P)) :
    τ = (derivedPullbackStalkIso f x).hom :=
  StacksDraft.LeftResolutions.natTrans_eq_of_kFlat τ _ fun P hP =>
    derivedPullbackStalkIso_hom_app_eq_of_mono f x P _
      (have := isIso_derivedStalkExtensionComparison_of_kFlat f x P hP; inferInstance) (hτ P hP)

/-- Given an isomorphism `e : F ≅ Lf^* ⋙ (−)_x` and a morphism of functors `τ` out of `F`, if
`e.inv ≫ τ` satisfies the equation of `AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison`
at every K-flat complex, then `e.inv ≫ τ` is `AlgebraicGeometry.derivedPullbackStalkIso`. -/
theorem derivedPullbackStalkIso_hom_eq_of_kFlat_of_iso
    {F : DerivedCategory Y.Modules ⥤ DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x))}
    (e : F ≅ Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom ⋙ derivedStalkFunctor x)
    (τ : F ⟶ derivedStalkFunctor (f x) ⋙
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (f.stalkMap x).hom).functor)
    (hτ : ∀ P : CochainComplex Y.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toSheafedSpace P →
      e.inv.app (DerivedCategory.Q.obj P) ≫ τ.app (DerivedCategory.Q.obj P) ≫
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (f.stalkMap x).hom).functor.map
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
              (f x)).mapDerivedCategoryFactors.hom.app P) ≫
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (f.stalkMap x).hom).comparison.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
              (f x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
        (derivedStalkFunctor x).map (pullbackComparisonOnComplex f P) ≫
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
            (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso f x).symm
              (ComplexShape.up ℤ)).hom.app P)) :
    e.inv ≫ τ = (derivedPullbackStalkIso f x).hom :=
  derivedPullbackStalkIso_hom_eq_of_kFlat f x _ fun P hP =>
    (Category.assoc (e.inv.app (DerivedCategory.Q.obj P))
      (τ.app (DerivedCategory.Q.obj P)) _).trans (hτ P hP)

end AlgebraicGeometry

end
