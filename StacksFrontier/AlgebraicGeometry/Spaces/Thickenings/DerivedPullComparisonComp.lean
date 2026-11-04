module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivedPullComparisonCompHomotopy

/-!
# The composition comparison of derived pullbacks, read on complexes

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces and a complex `N` of
`𝒪_Z`-modules, the composition comparison `L(Y ⟶ Z)^* ⋙ L(X ⟶ Y)^* ⟶ L(X ⟶ Z)^*` of the derived
pullback datum at `N`, followed by the comparison `AlgebraicGeometry.Space.derivedPullComparison`
along the composite, is the comparison along `g` pushed along `f`, the comparison along `f`, and
the degreewise composition comparison of pullbacks of modules, read through the identifications of
the two localizations.

This is the reading on complexes, in the spelling of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/RetractionDerivedPullback.lean`, of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_compIso_inv_app_comp_α`.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory Stacks.Cohomology.DerivedPullbackOfToposHom
  Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The composition comparison of derived pullbacks, read on complexes.** At the localization
of a complex `N` of `𝒪_Z`-modules, the composition comparison of the derived pullback datum
followed by the comparison of the derived pullback along `f ≫ g` with degreewise pullback is the
comparison along `g` pushed along `f`, the comparison along `f`, and the degreewise composition
comparison of pullbacks of modules (on the homotopy category, conjugated by the identifications of
the two localizations). -/
theorem smallEtaleDerivedPullbackData_compIso_inv_app_Q_comp_derivedPullComparison
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ) :
    ((smallEtaleDerivedPullbackData B S hS).compIso f g).inv.app (DerivedCategory.Q.obj N) ≫
        (derivedPullComparison B S hS (f ≫ g)).app N =
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) f).map
          ((derivedPullComparison B S hS g).app N) ≫
        (derivedPullComparison B S hS f).app
          ((((modulePullbackDataTopos B S hS).pull g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) ≫
        (quotientCompModulePullbackIso B S hS f).inv.app
          ((((modulePullbackDataTopos B S hS).pull g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B S hS f)
            (smallEtaleRingedToposHom B S hS g) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS f g)
            (ComplexShape.up ℤ)).hom.app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
        (quotientCompModulePullbackIso B S hS (f ≫ g)).hom.app N := by
  have n₁ := ((smallEtaleDerivedPullbackData B S hS).compIso f g).inv.naturality
    ((DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS Z.1 Z.2)).inv.app N)
  have h₁ := smallEtaleDerivedPullbackData_compIso_inv_app_comp_α B S hS f g
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)
  have h₃₄ : (quotientCompModulePullbackIso B S hS g).hom.app N ≫
      (DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS Y.1 Y.2)).inv.app
        ((((modulePullbackDataTopos B S hS).pull g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) = 𝟙 _ := by
    show (DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ ≫
      (DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS Y.1 Y.2)).hom.app _) ≫ _ = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    exact Iso.hom_inv_id_app _ _
  have key := comp_chain_triangle (derivedPull B S hS (hasDerivedModulePullbacks B S hS) f)
    _ _ _ _ _ _ _ _ _ ((quotientCompModulePullbackIso B S hS f).hom.app
          ((((modulePullbackDataTopos B S hS).pull g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N)) ((quotientCompModulePullbackIso B S hS f).inv.app
          ((((modulePullbackDataTopos B S hS).pull g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) ≫ _ ≫
        (quotientCompModulePullbackIso B S hS (f ≫ g)).hom.app N)
    _ _ n₁ h₁ h₃₄ (by rw [Iso.hom_inv_id_app_assoc]; rfl)
  exact (congrArg (_ ≫ ·) (derivedPullComparison_app B S hS (f ≫ g) N)).trans key

end AlgebraicGeometry.Space

end
