module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherentAnyModel

/-!
# Sheaf Hom with exact support, derived at an arbitrary model of the derived categories

For a closed quotient morphism of ringed spaces `i : Z ⟶ X`, derived pushforward is left adjoint
to the right derived functor of sheaf Hom with exact support, `Ri_* ⊣ R ℋom(𝒪_Z, -)`
([Stacks, Tag 0A76]), where the derived categories of `𝒪_X`-modules and of `𝒪_Z`-modules are
arbitrary models `[HasDerivedCategory.{w} _]` in a common universe `w`.

The declarations are in the namespace
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

## Main definitions

* `derivedSheafHomExactSupportComparisonAtModel`: the canonical map from sheaf Hom with exact
  support to its right derived functor.
* `derivedModulePushforwardSheafHomExactSupportAdjunctionAtModel`: the adjunction
  `Ri_* ⊣ R ℋom(𝒪_Z, -)`.

## Main results

* `derivedModulePushforwardSheafHomExactSupportAdjunctionAtModel_unit_app`,
  `derivedModulePushforwardSheafHomExactSupportAdjunctionAtModel_counit_app`: the unit and the
  counit of the adjunction.

## References

* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.X))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.Z))]

/-- The canonical map from sheaf Hom with exact support to its right derived functor. -/
noncomputable abbrev derivedSheafHomExactSupportComparisonAtModel :
    S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{w} S :=
  (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))

/-- Derived pushforward along a closed quotient morphism of ringed spaces is left adjoint to the
right derived functor of sheaf Hom with exact support: `Ri_* ⊣ R ℋom(𝒪_Z, -)`. -/
noncomputable def derivedModulePushforwardSheafHomExactSupportAdjunctionAtModel :
    (modulePushforward S.i).mapDerivedCategory ⊣
      Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{w} S :=
  Stacks.DerivedFunctor.derivedAdjunction S.modulePushforwardSheafHomExactSupportAdjunction
    (Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{w} S)
    S.derivedSheafHomExactSupportComparisonAtModel
    (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K)

/-- The unit of the derived adjunction is the one induced by the unit of the adjunction of
[Stacks, Tag 0A75] and the two derived-functor comparison maps. -/
theorem derivedModulePushforwardSheafHomExactSupportAdjunctionAtModel_unit_app
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.Z)) (ComplexShape.up ℤ)) :
    S.derivedModulePushforwardSheafHomExactSupportAdjunctionAtModel.unit.app
          (DerivedCategory.Qh.obj M) ≫
        (Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{w} S).map
          ((modulePushforward S.i).mapDerivedCategoryFactorsh.hom.app M) =
      DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction
            S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).unit.app M) ≫
        S.derivedSheafHomExactSupportComparisonAtModel.app
          (((modulePushforward S.i).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  Stacks.DerivedFunctor.derivedAdjunction_unit_app _ _ _ _ M

/-- The counit of the derived adjunction is the one induced by the counit of the adjunction of
[Stacks, Tag 0A75] and the two derived-functor comparison maps. -/
theorem derivedModulePushforwardSheafHomExactSupportAdjunctionAtModel_counit_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ)) :
    (modulePushforward S.i).mapDerivedCategory.map
          (S.derivedSheafHomExactSupportComparisonAtModel.app K) ≫
        S.derivedModulePushforwardSheafHomExactSupportAdjunctionAtModel.counit.app
          (DerivedCategory.Qh.obj K) =
      (modulePushforward S.i).mapDerivedCategoryFactorsh.hom.app
          ((S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction
            S.modulePushforwardSheafHomExactSupportAdjunction
              (ComplexShape.up ℤ)).counit.app K) :=
  Stacks.DerivedFunctor.derivedAdjunction_counit_app _ _ _ _ K

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
