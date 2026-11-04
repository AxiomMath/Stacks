module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupport

/-!
# Derived sheaf Hom with exact support

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that pushforward
`i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is left adjoint to sheaf Hom with exact support
`ℰom(𝒪_Z, -) : Mod(𝒪_X) ⥤ Mod(𝒪_Z)`. The left adjoint is exact, so it induces a functor
`D(𝒪_Z) ⥤ D(𝒪_X)` of unbounded derived categories directly; the right adjoint is only left
exact and acquires a total right derived functor `R ℰom(𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_Z)`. This file
shows that the two are again adjoint.

All names below live in the namespace
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

## Main definitions

* `derivedSheafHomExactSupport` is the total right derived functor `R ℰom(𝒪_Z, -)`.
* `derivedSheafHomExactSupportComparison` is its comparison map from the underived functor.

## Main results

* `derivedModulePushforwardSheafHomExactSupportAdjunction` is the derived adjunction
  `Ri_* ⊣ R ℰom(𝒪_Z, -)`.
* `derivedModulePushforwardSheafHomExactSupportAdjunction_unit_app` and
  `derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app` say that its unit and
  counit are the ones induced by the underived adjunction of [Stacks, Tag 0A75] and the two
  derived-functor comparison maps, which is the canonicality implicit in the notation `R ℰom`.

## Implementation notes

Both derived functors are the canonical ones: `Ri_*` is `Functor.mapDerivedCategory` of the
exact functor `i_*`, and `R ℰom(𝒪_Z, -)` is `Functor.totalRightDerived`, a Kan extension along
the localization. So no choice is made and the adjunction is a definition rather than an
existence statement.

The abstract input is `Stacks.DerivedFunctor.derivedAdjunction`, which derives an adjunction
whose left adjoint is exact as soon as the source of the right adjoint has enough K-injective
complexes; here that is [Stacks, Tag 079P] for the Grothendieck abelian category of sheaves of
modules.

## References

* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- Sheaf Hom with exact support is additive: it is the right adjoint of an additive functor. -/
noncomputable instance additive_sheafHomExactSupport : S.sheafHomExactSupport.Additive :=
  S.modulePushforwardSheafHomExactSupportAdjunction.right_adjoint_additive

/-- **[Stacks, Tag 08KS].** Pushforward along a closed quotient morphism of ringed spaces is
right exact; together with left exactness, which holds for any pushforward, it is exact. -/
instance preservesFiniteColimits_modulePushforward :
    PreservesFiniteColimits (modulePushforward S.i) :=
  Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward S.i S.isClosedEmbedding

/-- Sheaf Hom with exact support has a pointwise total right derived functor: sheaves of
modules form a Grothendieck abelian category, so every complex of them admits a
quasi-isomorphism into a K-injective complex. -/
instance hasPointwiseRightDerivedFunctor_sheafHomExactSupport :
    (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X))
          (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K)

/-- The right derived functor `R ℰom(𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_Z)` of sheaf Hom with exact
support along a closed quotient morphism of ringed spaces. -/
noncomputable abbrev derivedSheafHomExactSupport :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)) :=
  (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))

/-- The canonical map from sheaf Hom with exact support to its right derived functor. -/
noncomputable abbrev derivedSheafHomExactSupportComparison :
    S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ S.derivedSheafHomExactSupport :=
  (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))

/-- **Stacks Project, Tag 0A76.** Derived pushforward along a closed quotient morphism of
ringed spaces is left adjoint to the right derived functor of sheaf Hom with exact support:
`Ri_* ⊣ R ℰom(𝒪_Z, -)`. -/
@[stacks 0A76]
noncomputable def derivedModulePushforwardSheafHomExactSupportAdjunction :
    (modulePushforward S.i).mapDerivedCategory ⊣ S.derivedSheafHomExactSupport :=
  Stacks.DerivedFunctor.derivedAdjunction S.modulePushforwardSheafHomExactSupportAdjunction
    S.derivedSheafHomExactSupport S.derivedSheafHomExactSupportComparison
    (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K)

/-- **Stacks Project, Tag 0A76.** The unit of the derived adjunction is the one induced by the
unit of the adjunction of [Stacks, Tag 0A75] and the two derived-functor comparison maps. -/
@[stacks 0A76]
theorem derivedModulePushforwardSheafHomExactSupportAdjunction_unit_app
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.Z)) (ComplexShape.up ℤ)) :
    S.derivedModulePushforwardSheafHomExactSupportAdjunction.unit.app
          (DerivedCategory.Qh.obj M) ≫
        S.derivedSheafHomExactSupport.map
          ((modulePushforward S.i).mapDerivedCategoryFactorsh.hom.app M) =
      DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction
            S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).unit.app M) ≫
        S.derivedSheafHomExactSupportComparison.app
          (((modulePushforward S.i).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  Stacks.DerivedFunctor.derivedAdjunction_unit_app _ _ _ _ M

/-- **Stacks Project, Tag 0A76.** The counit of the derived adjunction is the one induced by
the counit of the adjunction of [Stacks, Tag 0A75] and the two derived-functor comparison
maps. -/
@[stacks 0A76]
theorem derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ)) :
    (modulePushforward S.i).mapDerivedCategory.map
          (S.derivedSheafHomExactSupportComparison.app K) ≫
        S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
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
