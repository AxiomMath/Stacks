module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoextendScalarsComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleCohomologyModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtaleRingedComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom

/-!
# Étale cohomology of a derived pullback from the small étale site (Stacks 0DGB)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `f : Y ⟶ X` a morphism of
its objects. Étale cohomology over `Y` of the derived pullback `Lπ_X^*K` of a complex of
`𝒪_X`-modules on the spaces-étale site of `X` is the cohomology, on the spaces-étale site of `Y`,
of `Lf_small^*K`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.derivedModulePullbackPi` is `Lπ_X^*` and
  `AlgebraicGeometry.BigEtaleSpaceSite.derivedModulePullbackSmallEtale` is `Lf_small^*`, the
  derived pullbacks of sheaves of modules along the morphisms of ringed topoi `π_X` and
  `π_X ∘ i_f` of Tag 0DF9.
* `AlgebraicGeometry.BigEtaleSpaceSite.pullbackModulesIsoRestrictModulesAlong` and
  `AlgebraicGeometry.BigEtaleSpaceSite.derivedPullbackIsoRestrictModulesAlong`: the pullback of
  sheaves of modules along `i_f` is restriction, underived and on derived categories.
* `AlgebraicGeometry.BigEtaleSpaceSite.derivedModulePullbackFactorization`:
  `Lf_small^* = i_f^* ∘ Lπ_X^*`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.modulePulledSmallEtaleCohomologyIso` and
  `AlgebraicGeometry.BigEtaleSpaceSite.modulePulledSmallEtaleCohomologyIsoAt`: **Stacks 0DGB**,
  part (4).

## Implementation notes

The derived pullback of sheaves of modules along a morphism of ringed topoi is Tag 06YY, taken
in the form whose two ringed topoi have free universes and whose geometric datum is a morphism
of the underlying topoi, which is the form the spaces-étale ringed topos of an algebraic space
fits; its existence is unconditional
(`Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy`), so
`Lπ_X^*` and `Lf_small^*` carry no hypothesis. The source's identity
`Lf_small^* = i_f^* ∘ Lπ_X^*` is then Tag 0D6D, `L(g ∘ f)^* = Lf^* ∘ Lg^*`, also unconditional,
applied to `f_small = π_X ∘ i_f` — together with the fact that `i_f^*` needs no derived functor.

That last fact is the one piece of work. The structure map of `i_f` is an isomorphism (Tag 0DF9,
case (1)), so extension of scalars along it is restriction of scalars along its inverse
(`extendScalarsFSharpIsoRestrictScalarsOfIsIso`), and the inverse image of modules along a
morphism of topoi presented by restriction along a continuous functor of sites is restriction
(Tag 03D2, `Stacks.Sheaves.ToposPullback.restrictionModuleIso`); the two changes of scalars
cancel because the comparison of Tag 03D2 for sheaves of rings *is* the structure map of `i_f`
in inverse-image form. `Lf^*` is then identified with the degreewise functor by uniqueness of
left derived functors, the degreewise one being its own because restriction of modules is exact.

The cohomology of a complex of sheaves of modules is the cohomology of its underlying complex of
abelian sheaves throughout, as in Tag 0DH2.

Both sections functors part (4) speaks of — sections over `f : Y ⟶ X` on the big étale site of
`X`, and global sections on the spaces-étale site of `Y` — have total right derived functors
unconditionally: abelian sheaves on those sites are Grothendieck abelian, so K-injective
resolutions exist (Tag 079P) and `Stacks.DerivedCategory.hasRightDerivedFunctor` applies. Those
two facts are the instances
`AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleSections_hasRightDerivedFunctor` and
`.smallEtaleGlobalSections_hasRightDerivedFunctor`, so part (4) assumes nothing.

## References

* [Stacks Project, Tag 0DGB](https://stacks.math.columbia.edu/tag/0DGB)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.RingedToposModules
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom (derivedPullbackCompIso)

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] bigEtaleSections_additive smallEtaleGlobalSections_additive

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y : T.Spaces} (f : Y ⟶ X)

/-- The pullback of complexes of modules along `i_f` on homotopy categories has a total left
derived functor. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_smallToBig :
    (pullbackOnHomotopy (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
      (Y := bigEtaleRingedTopos T X)
      (smallToBigEtaleRingedMorphism T f)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := bigEtaleRingedTopos T X)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (smallToBigEtaleRingedMorphism T f)

/-- The structure map of `i_f`, in inverse-image form, is an isomorphism. -/
instance isIso_fSharpInverseImage_smallToBigEtaleRingedMorphism :
    IsIso (smallToBigEtaleRingedMorphism T f).fSharpInverseImage := by
  rw [smallToBigEtaleRingedMorphism_fSharpInverseImage]
  exact (smallToBigEtaleStructureIso T f).isIso_hom

/-- The structure map of the morphism of ringed topoi underlying `i_f`, in inverse-image form,
is an isomorphism. -/
instance isIso_toModulesHom_fSharpInverseImage :
    IsIso (smallToBigEtaleRingedMorphism T f).toModulesHom.fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImageRing (smallToBigEtaleRingedMorphism T f)

/-- The forward map of `smallToBigRestrictionStructureIso T f` is the identity. -/
theorem smallToBigRestrictionStructureIso_hom_eq_id :
    (smallToBigRestrictionStructureIso T f).hom = 𝟙 _ := rfl

/-- The comparison of restriction along `inclusionFunctor T f` for the structure sheaf of rings
is the structure map of `i_f` in inverse-image form. -/
theorem restrictionRingIso_hom_eq_fSharpInverseImageRing :
    (restrictionRingIso (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (T.bigEtaleTopology X) (inclusionFunctor T f) (bigEtaleRingSheaf T X)).hom =
      (smallToBigEtaleRingedMorphism T f).fSharpInverseImageRing := by
  rw [← RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage
      (smallToBigEtaleRingedMorphism T f),
    smallToBigEtaleRingedMorphism_fSharpInverseImage, smallToBigEtaleStructureIso]
  rfl

/-- Restriction of scalars along the comparison `restrictionRingIso` for the structure sheaf,
followed by restriction of scalars along the inverse of the structure map of `i_f`, is the
identity functor. -/
theorem restrictScalars_comp_restrictScalars_inv_fSharpInverseImage :
    SheafOfModules.restrictScalars.{u + 1}
          (restrictionRingIso (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
            (T.bigEtaleTopology X) (inclusionFunctor T f) (bigEtaleRingSheaf T X)).hom ⋙
        SheafOfModules.restrictScalars.{u + 1}
          (asIso (smallToBigEtaleRingedMorphism T f).toModulesHom.fSharpInverseImage).inv =
      𝟭 _ := by
  have h : (asIso (smallToBigEtaleRingedMorphism T f).toModulesHom.fSharpInverseImage).inv ≫
      (restrictionRingIso (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (T.bigEtaleTopology X) (inclusionFunctor T f) (bigEtaleRingSheaf T X)).hom = 𝟙 _ := by
    rw [restrictionRingIso_hom_eq_fSharpInverseImageRing]
    exact IsIso.inv_hom_id _
  have hcomp : SheafOfModules.restrictScalars.{u + 1}
          (restrictionRingIso (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
            (T.bigEtaleTopology X) (inclusionFunctor T f) (bigEtaleRingSheaf T X)).hom ⋙
        SheafOfModules.restrictScalars.{u + 1}
          (asIso (smallToBigEtaleRingedMorphism T f).toModulesHom.fSharpInverseImage).inv =
      SheafOfModules.restrictScalars.{u + 1}
        ((asIso (smallToBigEtaleRingedMorphism T f).toModulesHom.fSharpInverseImage).inv ≫
          (restrictionRingIso (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
            (T.bigEtaleTopology X) (inclusionFunctor T f) (bigEtaleRingSheaf T X)).hom) :=
    Stacks.SheafOfModules.CoextendScalars.restrictScalars_comp _ _
  rw [hcomp, h]
  exact Stacks.SheafOfModules.CoextendScalars.restrictScalars_id

/-- **`Li_f^* = i_f^*`, underived.** -/
noncomputable def pullbackModulesIsoRestrictModulesAlong :
    (smallToBigEtaleRingedMorphism T f).toModulesHom.pullbackModules ≅
      restrictModulesAlong T f :=
  Functor.isoWhiskerRight
      (restrictionModuleIso (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (T.bigEtaleTopology X) (inclusionFunctor T f) (bigEtaleRingSheaf T X))
      (extendScalarsFSharp (smallToBigEtaleRingedMorphism T f).toModulesHom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft
        (SheafOfModules.restrictScalars.{u + 1}
          (restrictionRingIso (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
            (T.bigEtaleTopology X) (inclusionFunctor T f) (bigEtaleRingSheaf T X)).hom)
        (smallToBigEtaleRingedMorphism T
            f).toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso ≪≫
        eqToIso (restrictScalars_comp_restrictScalars_inv_fSharpInverseImage T f)) ≪≫
    Functor.rightUnitor _


/-- The pullback of sheaves of modules along `i_f` is additive. -/
instance pullbackModules_additive_smallToBig :
    (smallToBigEtaleRingedMorphism T f).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (smallToBigEtaleRingedMorphism T f)

/-- The functor induced on derived categories by restriction of modules along `i_f` is a total
left derived functor of restriction of modules on homotopy categories. -/
theorem restrictModulesAlong_mapDerivedCategory_isLeftDerivedFunctor :
    (restrictModulesAlong T f).mapDerivedCategory.IsLeftDerivedFunctor
      (restrictModulesAlong T f).mapDerivedCategoryFactorsh.hom
      (quasiIsoTarget (Y := bigEtaleRingedTopos T X)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    (restrictModulesAlong T f).mapDerivedCategoryFactorsh

/-- **`Li_f^* = i_f^*`** on the unbounded derived categories. -/
noncomputable def derivedPullbackIsoRestrictModulesAlong :
    derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
        (Y := bigEtaleRingedTopos T X) (smallToBigEtaleRingedMorphism T f) ≅
      (restrictModulesAlong T f).mapDerivedCategory :=
  have := restrictModulesAlong_mapDerivedCategory_isLeftDerivedFunctor T f
  Functor.leftDerivedNatIso _ _
    (derivedPullbackComparison (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
      (Y := bigEtaleRingedTopos T X) (smallToBigEtaleRingedMorphism T f))
    (restrictModulesAlong T f).mapDerivedCategoryFactorsh.hom
    (quasiIsoTarget (Y := bigEtaleRingedTopos T X))
    (Functor.isoWhiskerRight
      (Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesIsoRestrictModulesAlong T f)
        (ComplexShape.up ℤ))
      DerivedCategory.Qh)


/-! ### `Lπ_X^*` and `L f_small^*` -/

/-- The pullback of complexes of modules along `π_X` on homotopy categories has a total left
derived functor. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_bigToSmall (X : T.Spaces) :
    (pullbackOnHomotopy (X := bigEtaleRingedTopos T X)
      (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
      (bigToSmallEtaleRingedMorphism T X)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (bigToSmallEtaleRingedMorphism T X)

/-- `π_X ∘ i_f` as a morphism of ringed topoi. -/
noncomputable abbrev smallEtaleRingedToposComposite :=
  RingedToposHom.comp
    (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
    (Y := bigEtaleRingedTopos T X)
    (Z := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
    (bigToSmallEtaleRingedMorphism T X) (smallToBigEtaleRingedMorphism T f)

/-- The pullback of complexes of modules along `π_X ∘ i_f` on homotopy categories has a total
left derived functor. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_composite :
    (pullbackOnHomotopy (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
      (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
      (smallEtaleRingedToposComposite T f)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (smallEtaleRingedToposComposite T f)

/-- The derived pullback `Lπ_X^*` of sheaves of modules along `π_X`. -/
noncomputable abbrev derivedModulePullbackPi (X : T.Spaces) :=
  derivedPullback (X := bigEtaleRingedTopos T X)
    (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
    (bigToSmallEtaleRingedMorphism T X)

/-- The derived pullback `L f_small^*` of sheaves of modules along `π_X ∘ i_f`. -/
noncomputable abbrev derivedModulePullbackSmallEtale :=
  derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
    (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
    (smallEtaleRingedToposComposite T f)

/-- **`L f_small^* = i_f^* ∘ Lπ_X^*`** on the unbounded derived categories. -/
noncomputable def derivedModulePullbackFactorization :
    derivedModulePullbackPi T X ⋙ (restrictModulesAlong T f).mapDerivedCategory ≅
      derivedModulePullbackSmallEtale T f :=
  Functor.isoWhiskerLeft _ (derivedPullbackIsoRestrictModulesAlong T f).symm ≪≫
    derivedPullbackCompIso (smallToBigEtaleRingedMorphism T f)
      (bigToSmallEtaleRingedMorphism T X)


/-! ### Part (4) -/

/-- Étale cohomology over `Y` of the derived pullback `Lπ_X^*K` of a complex of sheaves of
`𝒪_X`-modules on the spaces-étale site of `X` is naturally isomorphic to the cohomology on the
spaces-étale site of `Y` of `Lf_small^*K`, as total right derived functors. -/
@[stacks 0DGB "part (4), cohomology over Y of a derived pullback from the small site"]
noncomputable def modulePulledSmallEtaleCohomologyIso :
    (derivedModulePullbackPi T X ⋙
      (SheafOfModules.toSheaf.{u + 1} (bigEtaleRingSheaf T X)).mapDerivedCategory ⋙
      (((bigEtaleSections T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)))) ≅
    (derivedModulePullbackSmallEtale T f ⋙
      (SheafOfModules.toSheaf.{u + 1} (spacesEtaleRingSheaf T Y)).mapDerivedCategory ⋙
      (((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
          Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
              (ComplexShape.up ℤ)))) :=
  Functor.isoWhiskerLeft _ (moduleBigSmallEtaleCohomologyIso T f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedModulePullbackFactorization T f) _

/-- In every degree, étale cohomology over `Y` of the derived
pullback `Lπ_X^*K` of a complex of sheaves of `𝒪_X`-modules on the spaces-étale site of `X`
agrees with the cohomology on the spaces-étale site of `Y` of `Lf_small^*K`. -/
@[stacks 0DGB "part (4), in each degree"]
noncomputable def modulePulledSmallEtaleCohomologyIsoAt
    (K : DerivedCategory (SpacesEtaleModules.{u, u + 1} T X)) (n : ℤ) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      ((derivedModulePullbackPi T X ⋙
        (SheafOfModules.toSheaf.{u + 1} (bigEtaleRingSheaf T X)).mapDerivedCategory ⋙
        (((bigEtaleSections T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)))).obj K) ≅
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      ((derivedModulePullbackSmallEtale T f ⋙
        (SheafOfModules.toSheaf.{u + 1} (spacesEtaleRingSheaf T Y)).mapDerivedCategory ⋙
        (((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
            Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
              (HomotopyCategory.quasiIso
                (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
                (ComplexShape.up ℤ)))).obj K) :=
  (DerivedCategory.homologyFunctor Ab.{u + 1} n).mapIso
    ((modulePulledSmallEtaleCohomologyIso T f).app K)

end AlgebraicGeometry.BigEtaleSpaceSite

end
