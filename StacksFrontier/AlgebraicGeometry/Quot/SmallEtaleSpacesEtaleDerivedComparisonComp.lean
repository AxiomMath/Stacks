module

public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleSpacesEtaleDerivedComparison
public import StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedComparisonComp

/-!
# The comparison of the derived pullbacks is compatible with composition

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces, the comparisons
`ε'_f : Φ_Y ⋙ Lf_{spaces}^* ⟶ Lf^* ⋙ Φ_X` of
`AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedPullComparison` between the derived pullback
on the small étale sites (modules in `Type u`) and the derived pullback on the spaces-étale sites
(modules in `Type (u + 1)`) are compatible with the composition isomorphisms of Stacks 0D6D on
both sides. Along flat morphisms, where the `ε'` are invertible, this is the compatibility of their
inverses with the composition isomorphisms, in the form of the last clause of
`AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`.

The proof is the categorical
`Stacks.LeftDerivedComparisonComp.leftDerivedComparison_comp_app`, fed with the
characterizations of the four comparisons involved on the images of complexes: that of `ε'`
(`AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedPullComparison_fac_app`), those of the two
composition comparisons of Stacks 0D6D
(`CategoryTheory.PullbackData.LeftDerived.compCounit_app`, and
`derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app` in
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom`), and the composition law of the
intertwining of the underived pullbacks
(`AlgebraicGeometry.Space.spacesEtalePullbackToSpacesEtaleModulesHom_comp_app'`), read on homotopy
categories through `Stacks.LeftDerivedComparisonComp.mapHomotopyCategoryComparison_comp_app`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedPullComparison_comp_app`: the
  composition law of the `ε'`.
* `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedPullIso`: the inverse of `ε'_f` along a
  flat morphism, `Lf^* ⋙ Φ_X ≅ Φ_Y ⋙ Lf_{spaces}^*`.
* `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedPullIso_comp_hom_app`: the composition
  law of these isomorphisms, in the form of the last clause of
  `AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

variable {S : Scheme.{u}} {T : BigEtaleSpaceSite S}

open Stacks.Cohomology.DerivedPullbackOfToposHom
  Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

attribute [local instance] preservesFiniteLimits_toSpacesEtaleModules
  preservesFiniteColimits_toSpacesEtaleModules hasDerivedCategory_smallEtaleModules
  hasDerivedCategory_spacesEtaleModules additive_spacesEtalePullbackModules

/-- The pullback of modules along the composite of the morphisms of spaces-étale ringed topoi of
two morphisms of algebraic spaces is additive. -/
local instance additive_spacesEtaleRingedToposHomComp_pullbackModules
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (RingedToposHom.comp (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
      (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
      (Z := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g)
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)).toModulesHom.pullbackModules.Additive
    :=
  RingedToposHom.pullbackModules_additive (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
    (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
    (RingedToposHom.comp (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
      (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
      (Z := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g)
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f))

/-- The derived pullback along the composite of the morphisms of spaces-étale ringed topoi of two
morphisms of algebraic spaces exists (Stacks 06YY), as for every morphism of ringed topoi. -/
local instance hasLeftDerivedFunctor_spacesEtaleRingedToposHomComp
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Stacks.Cohomology.DerivedPushforward.pullbackOnHomotopy
      (RingedToposHom.comp (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
        (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
        (Z := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g)
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f))).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
      (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
      (Z := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g)
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f))

/-- The composition law of the intertwining of the underived pullbacks
(`AlgebraicGeometry.Space.spacesEtalePullbackToSpacesEtaleModulesHom_comp_app'`), as
`Stacks.LeftDerivedComparisonComp.UnderivedCompCompatible`. -/
theorem spacesEtalePullbackToSpacesEtaleModulesHom_underivedCompCompatible
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Stacks.LeftDerivedComparisonComp.UnderivedCompCompatible
      (Adjunction.leftAdjointCompIso (spacesEtalePullbackAdjunction g)
        (spacesEtalePullbackAdjunction f) (spacesEtalePullbackAdjunction (f ≫ g))
        (spacesEtalePushforwardModulesCompIso f g)).hom
      (Adjunction.mateOfRightIso (modulePullbackAdjunction T.fppfSite S T.fppf_mem f)
        (spacesEtalePullbackAdjunction f) (spacesEtalePushforwardToSpacesEtaleModulesIso f))
      (Adjunction.mateOfRightIso (modulePullbackAdjunction T.fppfSite S T.fppf_mem g)
        (spacesEtalePullbackAdjunction g) (spacesEtalePushforwardToSpacesEtaleModulesIso g))
      (Adjunction.mateOfRightIso (modulePullbackAdjunction T.fppfSite S T.fppf_mem (f ≫ g))
        (spacesEtalePullbackAdjunction (f ≫ g))
        (spacesEtalePushforwardToSpacesEtaleModulesIso (f ≫ g)))
      (modulePullbackCompIso T.fppfSite S T.fppf_mem f g).hom :=
  spacesEtalePullbackToSpacesEtaleModulesHom_comp_app' f g

/-- **The intertwining of the pullbacks on homotopy categories is compatible with composition**:
the isomorphisms `AlgebraicGeometry.Space.spacesEtaleMapHomotopyPullbackIso` are compatible with
the composition comparison of degreewise pullbacks on the spaces-étale sites (followed by the
2-isomorphism of Stacks 0DE7) and with that of
`AlgebraicGeometry.Space.modulePullbackDataTopos` on the small étale sites. -/
theorem spacesEtaleMapHomotopyPullbackIso_underivedCompCompatible
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Stacks.LeftDerivedComparisonComp.UnderivedCompCompatible
      (pullbackMapHomotopyCompIso (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)
          (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso
          (spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp f g)
          (ComplexShape.up ℤ)).hom
      (spacesEtaleMapHomotopyPullbackIso f).hom (spacesEtaleMapHomotopyPullbackIso g).hom
      (spacesEtaleMapHomotopyPullbackIso (f ≫ g)).hom
      ((modulePullbackDataTopos T.fppfSite S T.fppf_mem).mapHomotopyCategory.compIso f g).inv :=
  Stacks.LeftDerivedComparisonComp.mapHomotopyCategory_underivedCompCompatible
    (ComplexShape.up ℤ) (modulePullbackDataTopos_pull_eq_modulePullback f)
    (modulePullbackDataTopos_pull_eq_modulePullback g)
    (modulePullbackDataTopos_pull_eq_modulePullback (f ≫ g))
    (Adjunction.mateOfRightIso (modulePullbackAdjunction T.fppfSite S T.fppf_mem f)
      (spacesEtalePullbackAdjunction f) (spacesEtalePushforwardToSpacesEtaleModulesIso f))
    (Adjunction.mateOfRightIso (modulePullbackAdjunction T.fppfSite S T.fppf_mem g)
      (spacesEtalePullbackAdjunction g) (spacesEtalePushforwardToSpacesEtaleModulesIso g))
    (Adjunction.mateOfRightIso (modulePullbackAdjunction T.fppfSite S T.fppf_mem (f ≫ g))
      (spacesEtalePullbackAdjunction (f ≫ g))
      (spacesEtalePushforwardToSpacesEtaleModulesIso (f ≫ g)))
    (spacesEtalePullbackToSpacesEtaleModulesIso f) (spacesEtalePullbackToSpacesEtaleModulesIso g)
    (spacesEtalePullbackToSpacesEtaleModulesIso (f ≫ g))
    (spacesEtalePullbackToSpacesEtaleModulesIso_hom f)
    (spacesEtalePullbackToSpacesEtaleModulesIso_hom g)
    (spacesEtalePullbackToSpacesEtaleModulesIso_hom (f ≫ g))
    (spacesEtalePullbackModulesCompIso f g) _ (spacesEtalePullbackCompIso_eq_leftAdjointCompIso f g)
    (modulePullbackCompIso T.fppfSite S T.fppf_mem f g)
    ((modulePullbackDataTopos T.fppfSite S T.fppf_mem).compIso f g)
    (modulePullbackDataTopos_compIso_eq f g)
    (spacesEtalePullbackToSpacesEtaleModulesHom_underivedCompCompatible f g) _
    (Stacks.Homology.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso
      (RingedToposHom.pullbackModulesCompIso (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
        (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
        (Z := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g)).symm
      (spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp f g) (ComplexShape.up ℤ))

/-- The composition comparison of the derived pullback on the small étale sites is characterized
through the comparisons of Stacks 06YY by the underived one
(`CategoryTheory.PullbackData.LeftDerived.compCounit_app`). -/
theorem smallEtaleDerivedPullbackData_compCounitCompatible
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Stacks.LeftDerivedComparisonComp.CompCounitCompatible
      ((smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).compIso f g).inv
      ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).α f)
      ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).α g)
      ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).α (f ≫ g))
      ((modulePullbackDataTopos T.fppfSite S T.fppf_mem).mapHomotopyCategory.compIso f g).inv :=
  fun M =>
    ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).L (f ≫ g)).leftDerived_fac_app
    ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).α (f ≫ g))
    ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).W Z) _
    ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).compCounit f g) M

/-- The composition isomorphism of Stacks 0D6D on the spaces-étale sites is characterized through
the comparisons of Stacks 06YY by the underived compositor followed by the 2-isomorphism of Stacks
0DE7 (`derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app` in
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom`). -/
theorem spacesEtaleDerivedPull_compCounitCompatible
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Stacks.LeftDerivedComparisonComp.CompCounitCompatible
      (derivedPullbackCompComparison (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)
          (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g) ≫
        (derivedPullbackIsoOfPullbackModulesIso
          (spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp f g)).hom)
      (derivedPullbackComparison (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f))
      (derivedPullbackComparison (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g))
      (derivedPullbackComparison (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom (f ≫ g)))
      (pullbackMapHomotopyCompIso (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)
          (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso
          (spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp f g)
          (ComplexShape.up ℤ)).hom := by
  intro M
  rw [NatTrans.comp_app, Category.assoc]
  exact derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app
    (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)
    (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g)
    (spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp f g) M

/-- The comparison `ε'_f` is characterized through the comparisons of Stacks 06YY by the
intertwining `AlgebraicGeometry.Space.spacesEtaleMapHomotopyPullbackIso` of the underived
pullbacks (`AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedPullComparison_fac_app`). -/
theorem smallEtaleSpacesEtaleDerivedPullComparison_characterized
    {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) :
    Stacks.LeftDerivedComparisonComp.ComparisonCharacterized
      (QX := DerivedCategory.Qh) (QY := DerivedCategory.Qh) (Q'X := DerivedCategory.Qh)
      (Q'Y := DerivedCategory.Qh)
      (ΦX := smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X)
      (ΦY := smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem Y)
      (Lf := (smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).pull f)
      (L'f := spacesEtaleDerivedPull T.fppfSite S T.fppf_mem f)
      (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X).mapDerivedCategoryFactorsh
      (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Y).mapDerivedCategoryFactorsh
      ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).α f)
      (derivedPullbackComparison (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f))
      (spacesEtaleMapHomotopyPullbackIso f).hom (smallEtaleSpacesEtaleDerivedPullComparison f) := by
  intro P
  have h := smallEtaleSpacesEtaleDerivedPullComparison_fac_app f P
  rw [spacesEtaleSmallEtaleDerivedPullCounit_app] at h
  simp only [Category.id_comp, Category.comp_id] at h
  exact h

/-- **The comparisons of the derived pullbacks are compatible with composition**: for
`f : X ⟶ Y` and `g : Y ⟶ Z`, the composition comparison `Lg_{spaces}^* ⋙ Lf_{spaces}^* ≅
L(f ≫ g)_{spaces}^*` of Stacks 0D6D followed by `ε'_{f ≫ g}` is `Lf_{spaces}^*(ε'_g)`, then
`ε'_f`, then `Φ_X` of the composition comparison `Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*` on the small étale
sites. -/
theorem smallEtaleSpacesEtaleDerivedPullComparison_compCompatible
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Stacks.LeftDerivedComparisonComp.ComparisonCompCompatible
      (spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp f g).hom
      (smallEtaleSpacesEtaleDerivedPullComparison f) (smallEtaleSpacesEtaleDerivedPullComparison g)
      (smallEtaleSpacesEtaleDerivedPullComparison (f ≫ g))
      ((smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).compIso f g).inv :=
  Stacks.LeftDerivedComparisonComp.comparisonCompCompatible_of_characterized
    (ΦX := smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X)
    (ΦY := smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem Y)
    (ΦZ := smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem Z)
    (Lf := (smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).pull f)
    (Lg := (smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).pull g)
    (Lfg := (smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).pull (f ≫ g))
    (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X).mapDerivedCategoryFactorsh
    (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Y).mapDerivedCategoryFactorsh
    (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Z).mapDerivedCategoryFactorsh
    _ _ _ _ _ (smallEtaleDerivedPullbackData_compCounitCompatible f g)
    _ _ _ _ _ (spacesEtaleDerivedPull_compCounitCompatible f g)
    _ _ _ (spacesEtaleMapHomotopyPullbackIso_underivedCompCompatible f g)
    _ _ _ (smallEtaleSpacesEtaleDerivedPullComparison_characterized f)
    (smallEtaleSpacesEtaleDerivedPullComparison_characterized g)
    (smallEtaleSpacesEtaleDerivedPullComparison_characterized (f ≫ g))
    (HomotopyCategory.quasiIso _ _) (isLeftDerivedFunctor_smallEtaleSpacesEtaleDerivedPull (f ≫ g))

/-- **The comparison `Lf^* ⋙ Φ_X ≅ Φ_Y ⋙ Lf_{spaces}^*` along a flat morphism**: the inverse of
`ε'_f`, invertible by
`AlgebraicGeometry.Space.isIso_smallEtaleSpacesEtaleDerivedPullComparison_of_isFlat`. -/
def smallEtaleSpacesEtaleDerivedPullIso {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) (hf : IsFlat T.fppfSite S T.fppf_mem f.hom) :
    (smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).pull f ⋙
        smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X ≅
      smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem Y ⋙
        spacesEtaleDerivedPull T.fppfSite S T.fppf_mem f :=
  haveI := isIso_smallEtaleSpacesEtaleDerivedPullComparison_of_isFlat f hf
  (asIso (smallEtaleSpacesEtaleDerivedPullComparison f)).symm

/-- **The comparisons along flat morphisms are compatible with the composition isomorphisms of
Stacks 0D6D**: for flat `f : X ⟶ Y`, `g : Y ⟶ Z` (with `f ≫ g` flat), the comparison for `f ≫ g`
followed by the composition isomorphism on the spaces-étale sites is `Φ_X` of the composition
isomorphism on the small étale sites, then the comparison for `f`, then `Lf_{spaces}^*` of the
comparison for `g`: the last clause of
`AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`, as
`Stacks.LeftDerivedComparisonComp.InvComparisonCompCompatible`. -/
theorem smallEtaleSpacesEtaleDerivedPullIso_invComparisonCompCompatible
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsFlat T.fppfSite S T.fppf_mem f.hom) (hg : IsFlat T.fppfSite S T.fppf_mem g.hom)
    (hfg : IsFlat T.fppfSite S T.fppf_mem (f ≫ g).hom) :
    Stacks.LeftDerivedComparisonComp.InvComparisonCompCompatible
      (smallEtaleSpacesEtaleDerivedPullIso f hf) (smallEtaleSpacesEtaleDerivedPullIso g hg)
      (smallEtaleSpacesEtaleDerivedPullIso (f ≫ g) hfg)
      ((smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).compIso f g)
      (spacesEtaleDerivedPullComp T.fppfSite S T.fppf_mem f g) :=
  Stacks.LeftDerivedComparisonComp.invComparisonCompCompatible_of_comparisonCompCompatible
    _ _ _ _ _ (smallEtaleSpacesEtaleDerivedPullComparison_compCompatible f g)

variable (B : BigFppfSite.{u}) (hS : B.Contains S)

/-- **The last clause of `AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`** for
the comparisons `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedPullIso` along fppf
coverings (which are flat), over the big étale site of algebraic spaces
`AlgebraicGeometry.BigFppfSite.bigEtaleSpaceSite` of `B`, whose auxiliary big fppf site is `B`. -/
theorem smallEtaleSpacesEtaleDerivedPullIso_comp_hom_app {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : fppfCoveringMorphisms B S hS f)
    (hg : fppfCoveringMorphisms B S hS g) (hfg : fppfCoveringMorphisms B S hS (f ≫ g))
    (K : derivedModules B S hS Z) :
    (smallEtaleSpacesEtaleDerivedPullIso (T := B.bigEtaleSpaceSite S hS) (f ≫ g)
          (hfg.flat ())).hom.app K ≫
        (spacesEtaleDerivedPullComp B S hS f g).hom.app
          ((smallEtaleSpacesEtaleDerivedFunctor B S hS Z).obj K) =
      (smallEtaleSpacesEtaleDerivedFunctor B S hS X).map
          (((smallEtaleDerivedPullbackData B S hS).compIso f g).hom.app K) ≫
        (smallEtaleSpacesEtaleDerivedPullIso (T := B.bigEtaleSpaceSite S hS) f
          (hf.flat ())).hom.app (((smallEtaleDerivedPullbackData B S hS).pull g).obj K) ≫
        (spacesEtaleDerivedPull B S hS f).map
          ((smallEtaleSpacesEtaleDerivedPullIso (T := B.bigEtaleSpaceSite S hS) g
            (hg.flat ())).hom.app K) :=
  smallEtaleSpacesEtaleDerivedPullIso_invComparisonCompCompatible
    (T := B.bigEtaleSpaceSite S hS) f g (hf.flat ()) (hg.flat ()) (hfg.flat ()) K

end AlgebraicGeometry.Space

end
