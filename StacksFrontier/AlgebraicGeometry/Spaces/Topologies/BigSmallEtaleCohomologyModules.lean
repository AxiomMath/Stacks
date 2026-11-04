module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedBaseChange

/-!
# Étale cohomology of sheaves of modules on the big and small étale sites (Stacks 0DGB)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `f : Y ⟶ X` a morphism of
its objects. This module is the sheaf-of-modules half of Tag 0DGB, the half left open by
`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/BigSmallEtaleCohomology.lean`: étale cohomology
over `Y` of a complex of `𝒪`-modules on the big étale site of `X` is the cohomology, on the
spaces-étale site of `Y`, of the inverse image `i_f^*` of that complex.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.restrictModulesAlongDerivedIso` identifies the underlying
  complex of abelian sheaves of `i_f^*M` with `i_f⁻¹` of the underlying complex of `M`, on the
  unbounded derived categories.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.moduleBigSmallEtaleCohomologyIso` and
  `AlgebraicGeometry.BigEtaleSpaceSite.moduleBigSmallEtaleCohomologyIsoAt`: **Stacks 0DGB**,
  part (6).

## Implementation notes

As in the source, and as in Tag 0DH2 of this library, the cohomology of a complex of sheaves of
modules is the cohomology of its underlying complex of abelian sheaves; that is Tag 0D6J, whose
part (2) for sections over an object of a site is
`Stacks.Cohomology.ForgetModule.sectionsForgetComparison_isIso`.

The inverse image `i_f^*` of sheaves of `𝒪`-modules is
`AlgebraicGeometry.BigEtaleSpaceSite.restrictModulesAlong`, restriction along the inclusion
functor of Tag 0DF2 with the identity structure map — Tag 0DF9, case (1), records that
`i_f⁻¹𝒪 ≅ 𝒪_Y` is the identity in each component, which is why the source writes `i_f^*` and not
`Li_f^*`. On underlying sheaves of abelian groups that restriction of scalars *is* restriction of
abelian sheaves, by `Stacks.SheafOfModules.pushforward_comp_toSheaf`; the concrete `rfl` is not
used, because unfolding the two sites exhausts the elaborator. So part (6) is part (5) of the
sibling module whiskered with the forgetful functor along that identification, and needs no
input of its own: in particular it does not need Tag 0DG8 for sheaves of modules, which is
false, nor the unbounded derived-adjunction argument of Tag 0DD8, whose statement in this library
carries the half of Tag 0794 that is left open.

Restriction of modules is exact (`restrictModulesAlong_preservesFiniteLimits` and its colimit
companion) and so is the forgetful functor to abelian sheaves, so both act on unbounded derived
categories through `CategoryTheory.Functor.mapDerivedCategory` and no derived functor of either
intervenes.

## References

* [Stacks Project, Tag 0DGB](https://stacks.math.columbia.edu/tag/0DGB)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] bigEtaleSections_additive smallEtaleGlobalSections_additive

variable {X Y : T.Spaces} (f : Y ⟶ X)

/-! ### The underlying abelian complex of an inverse image of modules -/

/-- **The underlying abelian sheaf of `i_f^*M` is `i_f⁻¹` of the underlying abelian sheaf of
`M`.** The inverse image of sheaves of `𝒪`-modules along `i_f` has the identity structure map
(Tag 0DF9, case (1)), so on underlying sheaves of abelian groups it is restriction of abelian
sheaves along the inclusion functor of Tag 0DF2 on the nose. -/
theorem restrictModulesAlong_comp_toSheaf :
    restrictModulesAlong T f ⋙ SheafOfModules.toSheaf.{u + 1} (spacesEtaleRingSheaf T Y) =
      SheafOfModules.toSheaf.{u + 1} (bigEtaleRingSheaf T X) ⋙ smallEtaleRestriction T f :=
  Stacks.SheafOfModules.pushforward_comp_toSheaf.{u + 1} (inclusionFunctor T f)
    (restrictAlongSharp T f)

/-- The same identification on the unbounded derived categories: both restriction of sheaves of
modules along `i_f` and the forgetful functor to abelian sheaves are exact, so each acts on the
derived category degreewise. -/
noncomputable def restrictModulesAlongDerivedIso :
    (restrictModulesAlong T f).mapDerivedCategory ⋙
        (SheafOfModules.toSheaf.{u + 1} (spacesEtaleRingSheaf T Y)).mapDerivedCategory ≅
      (SheafOfModules.toSheaf.{u + 1} (bigEtaleRingSheaf T X)).mapDerivedCategory ⋙
        (smallEtaleRestriction T f).mapDerivedCategory :=
  ProEtale.derivedCompIso (eqToIso (restrictModulesAlong_comp_toSheaf T f)) ≪≫
    (ProEtale.derivedCompIso (Iso.refl (SheafOfModules.toSheaf.{u + 1} (bigEtaleRingSheaf T X) ⋙
      smallEtaleRestriction T f))).symm

/-! ### Part (6): cohomology over `Y` of a complex of modules on the big étale site of `X` -/

/-- **Stacks 0DGB, part (6).** Étale cohomology over `Y` of a complex of sheaves of
`𝒪`-modules on the big étale site of `X` is the cohomology on the spaces-étale site of `Y` of
its inverse image along `i_f`: the right-derived sections functor at `f : Y ⟶ X` is `i_f^*`
followed by derived global sections, naturally in the derived coefficient object. -/
@[stacks 0DGB "part (6), big-site cohomology over Y of a complex of modules"]
noncomputable def moduleBigSmallEtaleCohomologyIso :
    ((SheafOfModules.toSheaf.{u + 1} (bigEtaleRingSheaf T X)).mapDerivedCategory ⋙
      (((bigEtaleSections T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)))) ≅
    ((restrictModulesAlong T f).mapDerivedCategory ⋙
      (SheafOfModules.toSheaf.{u + 1} (spacesEtaleRingSheaf T Y)).mapDerivedCategory ⋙
      (((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
            (ComplexShape.up ℤ)))) :=
  Functor.isoWhiskerLeft _ (bigSmallEtaleCohomologyIso T f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictModulesAlongDerivedIso T f).symm _ ≪≫
    Functor.associator _ _ _

/-- **Stacks 0DGB, part (6).** In every degree, étale cohomology over `Y` of a complex of
sheaves of `𝒪`-modules on the big étale site of `X` agrees with the cohomology on the
spaces-étale site of `Y` of its inverse image along `i_f`. -/
@[stacks 0DGB "part (6), in each degree"]
noncomputable def moduleBigSmallEtaleCohomologyIsoAt
    (M : DerivedCategory (BigEtaleModules.{u, u + 1} T X)) (n : ℤ) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      (((SheafOfModules.toSheaf.{u + 1} (bigEtaleRingSheaf T X)).mapDerivedCategory ⋙
        (((bigEtaleSections T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)))).obj M) ≅
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      (((restrictModulesAlong T f).mapDerivedCategory ⋙
        (SheafOfModules.toSheaf.{u + 1} (spacesEtaleRingSheaf T Y)).mapDerivedCategory ⋙
        (((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
          Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
              (ComplexShape.up ℤ)))).obj M) :=
  (DerivedCategory.homologyFunctor Ab.{u + 1} n).mapIso
    ((moduleBigSmallEtaleCohomologyIso T f).app M)

end AlgebraicGeometry.BigEtaleSpaceSite

end
