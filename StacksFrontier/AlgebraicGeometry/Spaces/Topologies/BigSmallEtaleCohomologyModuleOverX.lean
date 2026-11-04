module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleCohomologyModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedPushforwardModules
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison

/-!
# Étale cohomology over `X` of a derived pullback from the small étale site (Stacks 0DGB)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `X` an object of it. This
module closes the sheaf-of-modules half of Tag 0DGB: étale cohomology over `X` itself of the
derived pullback `Lπ_X^*K` of a complex of `𝒪_X`-modules on the spaces-étale site of `X` is the
cohomology of `K` on that site.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.piRingedSiteHom` presents the comparison morphism `π_X`
  of Tag 0DF9, case (3), as a morphism of ringed sites, and
  `AlgebraicGeometry.BigEtaleSpaceSite.pullbackModulesPiIso` identifies the pullback of sheaves
  of modules along it with the left adjoint `π_X^*` of restriction.
* `AlgebraicGeometry.BigEtaleSpaceSite.modulePullbackPiRestrictIsoId` is the retraction
  `i_X^* ∘ π_X^* ≅ id` on sheaves of modules, and
  `AlgebraicGeometry.BigEtaleSpaceSite.derivedModulePullbackSmallEtaleIdIso` is the same on the
  unbounded derived categories, which is `Lf_small^* ≅ id` at `f = 𝟙 X`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_restrictModulesAdjunction_unit`: the unit of the
  adjunction `π_X^* ⊣ π_{X,*}` on sheaves of modules is an isomorphism.
* `AlgebraicGeometry.BigEtaleSpaceSite.moduleOverXSmallEtaleCohomologyIso` and
  `AlgebraicGeometry.BigEtaleSpaceSite.moduleOverXSmallEtaleCohomologyIsoAt`: **Stacks 0DGB**,
  part (2).

## Implementation notes

Part (2) is part (4) of the sibling module at `f = 𝟙 X`, so what has to be supplied is that
`Lf_small^*` becomes the identity there. By the factorization
`AlgebraicGeometry.BigEtaleSpaceSite.derivedModulePullbackFactorization` that reduces to the
retraction `i_X^* ∘ π_X^* ≅ id`, and since restriction of modules along `i_X` is `π_{X,*}` on
the nose — `inclusionFunctor T (𝟙 X)` is the inclusion of the spaces-étale site and both
structure maps are the identity — the retraction is exactly the statement that the unit of
`π_X^* ⊣ π_{X,*}` is invertible.

That unit is invertible because the inclusion of the spaces-étale site of `X` into its big
étale site is fully faithful: in the adjoint triple `π_X^* ⊣ π_{X,*} ⊣ (π_X)_∗∗` the unit of the
left-hand adjunction is invertible exactly when the counit of the right-hand one is, and the
latter is the full faithfulness of the direct image of sheaves of modules along a fully
faithful, continuous and cocontinuous functor of sites. That is
`SheafOfModules.isIso_unit_of_isIso_coefficient`, applied with the identity structure map
`AlgebraicGeometry.BigEtaleSpaceSite.restrictSharp` of Tag 0DF9, case (3); no model of the left
adjoint enters, so `AlgebraicGeometry.BigEtaleSpaceSite.restrictModulesAdjunction` may be used
as it stands.

The pullback of sheaves of modules along `π_X` is produced twice over in this development: once
from the two-field morphism of ringed topoi `bigToSmallEtaleRingedMorphism`, which is the form
the derived pullback of Tag 06YY and hence part (4) is stated over, and once from the morphism
of sites, which is the form the adjunction with restriction is stated over. The two agree by
`AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso` together with
`AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`, both read along
`piRingedSiteHom`; the comparisons of the underlying data are identities, so
`piRingedSiteHom_ringedToposHom` and `piRingedSiteHom_pullbackTopos` hold by `rfl`.

The passage to the derived categories is uniqueness of left derived functors, as in the sibling
module: the identity functor is exact and therefore its own total left derived functor, so
`CategoryTheory.Functor.leftDerivedNatIso` lifts the underived retraction. No `rfl` on the two
sites is taken concretely; each identification instantiates a generic lemma.

## References

* [Stacks Project, Tag 0DGB](https://stacks.math.columbia.edu/tag/0DGB)
* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
* [Stacks Project, Tag 0DF3](https://stacks.math.columbia.edu/tag/0DF3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackOfToposHom

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] bigEtaleSections_additive smallEtaleGlobalSections_additive

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) (X : T.Spaces)

/-! ### The unit of `π_X^* ⊣ π_{X,*}` -/

/-- The structure map of `π_X` is the identity (Tag 0DF9, case (3)), restated so that instance
search can see that it is invertible. -/
theorem restrictSharp_eq_id : restrictSharp T X = 𝟙 _ := rfl

/-- The structure map of `π_X` is an isomorphism. -/
instance isIso_restrictSharp : IsIso (restrictSharp T X) :=
  inferInstanceAs (IsIso (𝟙 (T.spacesEtaleRingSheaf X)))

/-- **`π_{X,*}π_X^* ≅ id` on sheaves of modules.** The unit of the adjunction between the
inverse and the direct image of sheaves of `𝒪`-modules along `π_X` is an isomorphism: the
inclusion of the spaces-étale site of `X` into its big étale site is fully faithful, continuous
and cocontinuous, and the structure map of `π_X` is invertible, so the adjoint-triple argument
of `SheafOfModules.isIso_unit_of_isIso_coefficient` applies. -/
theorem isIso_restrictModulesAdjunction_unit :
    IsIso (restrictModulesAdjunction T X).unit :=
  SheafOfModules.isIso_unit_of_isIso_coefficient.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X)
    (bigEtaleRingSheaf T X) (restrictSharp T X) (restrictModulesAdjunction T X)

/-- The retraction `π_{X,*}π_X^* ≅ id` itself. -/
def restrictModulesPullbackCompRestrictIsoId :
    restrictModulesPullback T X ⋙ restrictModules.{u, u + 1} T X ≅
      𝟭 (SpacesEtaleModules.{u, u + 1} T X) :=
  have := isIso_restrictModulesAdjunction_unit T X
  (asIso (restrictModulesAdjunction T X).unit).symm

/-! ### `π_X` as a morphism of ringed sites -/

/-- The comparison morphism `π_X` of Tag 0DF9, case (3), as a morphism of ringed sites: the
inclusion of the spaces-étale site of `X`, which is a morphism of sites by Tag 0DF3, with the
identity structure map. -/
def piRingedSiteHom :
    RingedSite.Hom (bigEtaleRingedTopos T X).toRingedSite
      (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X).toRingedSite :=
  RingedSite.Hom.ofRingedToposSiteHom (spacesEtaleRestrictionRingedHom T X)
    (inclusion_isMorphismOfSites T X)

/-- The two-field morphism of ringed topoi attached to `piRingedSiteHom` is the one Tag 0DF9,
case (3), builds directly: the underlying morphism of topoi is the one induced by the inclusion
as a morphism of sites in both cases, and the structure map of the first is the structure map of
the morphism of ringed sites read through the identification of the direct image of a sheaf of
commutative rings with its restriction, which is how the second is defined. -/
theorem piRingedSiteHom_ringedToposHom :
    (piRingedSiteHom T X).ringedToposHom = bigToSmallEtaleRingedMorphism T X := rfl

/-- The pullback of sheaves of modules along the site-presented form of `π_X` is the left
adjoint `π_X^*` of restriction. -/
theorem piRingedSiteHom_pullbackTopos :
    (piRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos = restrictModulesPullback T X := rfl

/-- The pullback of sheaves of modules along `π_X`, taken over the two-field morphism of ringed
topoi of Tag 01D3 that the derived pullback is stated over, is the left adjoint `π_X^*` of
restriction. -/
theorem pullbackModules_bigToSmallEtaleRingedMorphism_eq :
    (bigToSmallEtaleRingedMorphism T X).toModulesHom.pullbackModules =
      (bigToSmallEtaleRingedMorphism T X).toRingedToposModulesHom.pullbackModules :=
  congrArg
    (fun g : Stacks.Sheaves.RingedToposModules.RingedToposHom
        (bigEtaleRingedTopos T X)
        (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X) => g.pullbackModules)
    (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom
      (bigToSmallEtaleRingedMorphism T X))

/-- The same pullback, read along `piRingedSiteHom`: the two morphisms of ringed topoi are the
same by `piRingedSiteHom_ringedToposHom`. -/
theorem pullbackModules_piRingedSiteHom_eq :
    (bigToSmallEtaleRingedMorphism T X).toRingedToposModulesHom.pullbackModules =
      (piRingedSiteHom T X).ringedToposHom.toRingedToposModulesHom.pullbackModules := rfl

/-- **`π_X^*` is the left adjoint of restriction.** The pullback of sheaves of modules along the
two-field morphism of ringed topoi `π_X` is `restrictModulesPullback`. -/
def pullbackModulesPiIso :
    (bigToSmallEtaleRingedMorphism T X).toModulesHom.pullbackModules ≅
      restrictModulesPullback T X :=
  eqToIso ((pullbackModules_bigToSmallEtaleRingedMorphism_eq T X).trans
      (pullbackModules_piRingedSiteHom_eq T X)) ≪≫
    (piRingedSiteHom T X).pullbackModulesToposIso

/-! ### The retraction `i_X^* ∘ π_X^* ≅ id` -/

/-- Restriction of sheaves of modules along `i_{𝟙 X}` is restriction along `π_X`: the inclusion
functor of Tag 0DF2 at the identity of `X` is the inclusion of the spaces-étale site, and both
structure maps are the identity. -/
theorem restrictModulesAlong_id_eq :
    restrictModulesAlong T (𝟙 X) = restrictModules.{u, u + 1} T X := rfl

/-- **`i_X^* ∘ π_X^* ≅ id` on sheaves of modules**: the inverse image of modules along `π_X`,
followed by restriction to the spaces-étale site of `X` along `i_X`, is the identity. -/
def modulePullbackPiRestrictIsoId :
    (bigToSmallEtaleRingedMorphism T X).toModulesHom.pullbackModules ⋙
        restrictModulesAlong T (𝟙 X) ≅ 𝟭 (SpacesEtaleModules.{u, u + 1} T X) :=
  Functor.isoWhiskerRight (pullbackModulesPiIso T X) (restrictModulesAlong T (𝟙 X)) ≪≫
    eqToIso (congrArg (restrictModulesPullback T X ⋙ ·) (restrictModulesAlong_id_eq T X)) ≪≫
    restrictModulesPullbackCompRestrictIsoId T X

/-- The inverse image of sheaves of modules along the composite `π_X ∘ i_X` is additive. -/
instance pullbackModules_additive_composite :
    ((smallEtaleRingedToposComposite T (𝟙 X)).toModulesHom.pullbackModules).Additive :=
  RingedToposHom.pullbackModules_additive (smallEtaleRingedToposComposite T (𝟙 X))

/-- **`(π_X ∘ i_X)^* ≅ id` on sheaves of modules**, the underived form of part (2)'s input: the
pullback along the composite of Tag 0DF9 is the composite of the pullbacks, the one along `i_X`
is restriction, and the two then cancel. -/
def pullbackModulesCompositeIsoId :
    (smallEtaleRingedToposComposite T (𝟙 X)).toModulesHom.pullbackModules ≅
      𝟭 (SpacesEtaleModules.{u, u + 1} T X) :=
  RingedToposHom.pullbackModulesCompIso (smallToBigEtaleRingedMorphism T (𝟙 X))
      (bigToSmallEtaleRingedMorphism T X) ≪≫
    Functor.isoWhiskerLeft _ (pullbackModulesIsoRestrictModulesAlong T (𝟙 X)) ≪≫
    modulePullbackPiRestrictIsoId T X

/-! ### `L f_small^* ≅ id` at `f = 𝟙 X` -/

/-- The identity functor on sheaves of modules is its own total left derived functor, being
exact. -/
theorem id_mapDerivedCategory_isLeftDerivedFunctor :
    (𝟭 (SpacesEtaleModules.{u, u + 1} T X)).mapDerivedCategory.IsLeftDerivedFunctor
      (𝟭 (SpacesEtaleModules.{u, u + 1} T X)).mapDerivedCategoryFactorsh.hom
      (quasiIsoTarget (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    (𝟭 (SpacesEtaleModules.{u, u + 1} T X)).mapDerivedCategoryFactorsh

/-- **`L f_small^* ≅ id` at `f = 𝟙 X`.** The derived pullback of sheaves of modules along the
composite `π_X ∘ i_X` of Tag 0DF9 is the identity on the unbounded derived category: the
underived pullback is the identity by `pullbackModulesCompositeIsoId`, the identity functor is
its own total left derived functor, and total left derived functors are unique. -/
def derivedModulePullbackSmallEtaleIdIso :
    derivedModulePullbackSmallEtale T (𝟙 X) ≅
      𝟭 (DerivedCategory (SpacesEtaleModules.{u, u + 1} T X)) :=
  have := id_mapDerivedCategory_isLeftDerivedFunctor T X
  Functor.leftDerivedNatIso _ _
      (derivedPullbackComparison
        (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
        (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
        (smallEtaleRingedToposComposite T (𝟙 X)))
      (𝟭 (SpacesEtaleModules.{u, u + 1} T X)).mapDerivedCategoryFactorsh.hom
      (quasiIsoTarget (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X))
      (Functor.isoWhiskerRight
        (Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompositeIsoId T X)
          (ComplexShape.up ℤ))
        DerivedCategory.Qh) ≪≫
    ProEtale.derivedIdIso

/-! ### Part (2) -/

/-- **Stacks 0DGB, part (2).** Étale cohomology over `X` of the derived pullback `Lπ_X^*K` to
the big étale site of `X` of a complex of sheaves of `𝒪_X`-modules on the spaces-étale site of
`X` is the cohomology of `K` on that site, naturally in the derived coefficient object. -/
@[stacks 0DGB "part (2), cohomology over X of a derived pullback of modules from the small site"]
def moduleOverXSmallEtaleCohomologyIso :
    (derivedModulePullbackPi T X ⋙
      (SheafOfModules.toSheaf.{u + 1} (bigEtaleRingSheaf T X)).mapDerivedCategory ⋙
      (((bigEtaleSections T (𝟙 X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)))) ≅
    ((SheafOfModules.toSheaf.{u + 1} (spacesEtaleRingSheaf T X)).mapDerivedCategory ⋙
      (((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
          Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})
              (ComplexShape.up ℤ)))) :=
  modulePulledSmallEtaleCohomologyIso T (𝟙 X) ≪≫
    Functor.isoWhiskerRight (derivedModulePullbackSmallEtaleIdIso T X) _ ≪≫
    Functor.leftUnitor _

/-- **Stacks 0DGB, part (2).** In every degree, étale cohomology over `X` of the derived
pullback `Lπ_X^*K` of a complex of sheaves of `𝒪_X`-modules on the spaces-étale site of `X`
agrees with the cohomology of `K` on that site. -/
@[stacks 0DGB "part (2), in each degree"]
def moduleOverXSmallEtaleCohomologyIsoAt
    (K : DerivedCategory (SpacesEtaleModules.{u, u + 1} T X)) (n : ℤ) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      ((derivedModulePullbackPi T X ⋙
        (SheafOfModules.toSheaf.{u + 1} (bigEtaleRingSheaf T X)).mapDerivedCategory ⋙
        (((bigEtaleSections T (𝟙 X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)))).obj K) ≅
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      (((SheafOfModules.toSheaf.{u + 1} (spacesEtaleRingSheaf T X)).mapDerivedCategory ⋙
        (((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
            Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
              (HomotopyCategory.quasiIso
                (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})
                (ComplexShape.up ℤ)))).obj K) :=
  (DerivedCategory.homologyFunctor Ab.{u + 1} n).mapIso
    ((moduleOverXSmallEtaleCohomologyIso T X).app K)

end AlgebraicGeometry.BigEtaleSpaceSite

end
