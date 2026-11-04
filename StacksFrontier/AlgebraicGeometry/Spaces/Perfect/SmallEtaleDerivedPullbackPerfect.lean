module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPerfectPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback
public import StacksFrontier.CategoryTheory.Functor.Derived.EquivalenceConjugationIso

/-!
# Derived pullback on the small étale sites through the spaces-étale models

Let `f : X ⟶ Y` be a morphism of algebraic spaces. The derived pullback `Lf^*` of
`𝒪`-modules on the small étale sites (`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`,
along the morphism of small étale ringed topoi of Stacks 03G8) and the derived pullback along the
morphism of models of the ringed spaces-étale sites
(`AlgebraicGeometry.Space.spacesEtaleModelHom f`) are both total left derived functors of a
degreewise pullback. Under the equivalences `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`
of Stacks 03G1, a comparison of the two underived pullbacks therefore induces a comparison of the
two derived pullbacks, and Stacks 08H6 on the models (perfect objects pull back to perfect
objects) transfers to the small étale sites.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackModelIso`: given a comparison `ψ` of the
  underived pullbacks, `Lf^*_{model} ⋙ D(e_X) ≅ D(e_Y) ⋙ Lf^*`.

## Main results

* `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback_of_modelIso`: given `ψ`,
  `Lf^*` on the small étale sites sends perfect objects to perfect objects (Stacks 08H6).

## Implementation notes

The comparison of the underived pullbacks is taken as an argument `ψ` (data, an isomorphism of
functors), so that the derived statement is separated from the identification of the module
pullback of `AlgebraicGeometry.Space.smallEtaleRingedToposHom f` with the module pullback along
`AlgebraicGeometry.Space.spacesEtaleModelHom f`. The étale case of that identification is
`AlgebraicGeometry.Space.spacesEtaleModelModulesEquivPostcompIso`.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 08H6](https://stacks.math.columbia.edu/tag/08H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- An object isomorphic to a perfect object is perfect. -/
theorem isPerfect_smallEtaleRingedSite_of_iso
    {K L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    (e : K ≅ L) (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect L := by
  obtain ⟨E, hE, ⟨i⟩⟩ := hK
  exact ⟨E, hE, ⟨i ≪≫ e⟩⟩

/-- The pullback of `𝒪`-modules along the morphism of small étale ringed topoi of a morphism of
algebraic spaces, `AlgebraicGeometry.RingedToposHom.pullbackModules`, typed on the categories
`AlgebraicGeometry.Space.Modules` (the codomain of
`AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`). -/
def smallEtaleModulePullbackModules :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules

/-- The pullback of `𝒪`-modules along the small étale ringed topoi is additive. -/
instance additive_smallEtaleModulePullbackModules :
    (smallEtaleModulePullbackModules B S hS f).Additive :=
  RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS f)

section Comparison

variable [(smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
    (smallEtaleModuleQuasiIso B S hS Y)]
  (ψ : (spacesEtaleModelHom B S hS f).pullbackTopos ⋙
      (spacesEtaleModelModulesEquiv B S hS X).functor ≅
    (spacesEtaleModelModulesEquiv B S hS Y).functor ⋙ smallEtaleModulePullbackModules B S hS f)

include ψ in
/-- The comparison of the degreewise pullbacks followed by localization, induced by `ψ`. -/
def smallEtaleModulePullbackOnHomotopyModulesModelIso :
    haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)).1
    haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Y)).1
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
        (spacesEtaleModelHom B S hS f) ⋙
        (spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory ≅
      (spacesEtaleModelModulesEquiv B S hS Y).functor.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        smallEtaleModulePullbackOnHomotopy B S hS f :=
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)).2.1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)).2.2
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Y)).1
  haveI : ((spacesEtaleModelHom B S hS f).pullbackTopos ⋙
      (spacesEtaleModelModulesEquiv B S hS X).functor).Additive :=
    Functor.additive_of_preserves_binary_products _
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso ψ (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm)
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

end Comparison

/-- `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` on homotopy categories, typed on the
modules of the small étale ringed topos. -/
def spacesEtaleModelModulesHomotopyFunctor (Z : AlgebraicSpaces B S hS) :
    HomotopyCategory (spacesEtaleModelRingedTopos B S hS Z).Modules (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
        (ComplexShape.up ℤ) :=
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Z)).1
  (spacesEtaleModelModulesEquiv B S hS Z).functor.mapHomotopyCategory (ComplexShape.up ℤ)

/-- `AlgebraicGeometry.Space.spacesEtaleModelModulesHomotopyFunctor` is an equivalence. -/
instance isEquivalence_spacesEtaleModelModulesHomotopyFunctor (Z : AlgebraicSpaces B S hS) :
    (spacesEtaleModelModulesHomotopyFunctor B S hS Z).IsEquivalence :=
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Z)).1
  Stacks.DerivedFunctor.isEquivalence_mapHomotopyCategory _

/-- `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` on derived categories, typed on the
modules of the small étale ringed topos. -/
def spacesEtaleModelModulesDerivedFunctor (Z : AlgebraicSpaces B S hS) :
    DerivedCategory (spacesEtaleModelRingedTopos B S hS Z).Modules ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) :=
  (spacesEtaleModelModulesEquiv B S hS Z).functor.mapDerivedCategory

/-- `AlgebraicGeometry.Space.spacesEtaleModelModulesDerivedFunctor` is an equivalence. -/
instance isEquivalence_spacesEtaleModelModulesDerivedFunctor (Z : AlgebraicSpaces B S hS) :
    (spacesEtaleModelModulesDerivedFunctor B S hS Z).IsEquivalence :=
  Stacks.DerivedQCoh.isEquivalence_mapDerivedCategory (spacesEtaleModelModulesEquiv B S hS Z)

/-- The localization functors commute with
`AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`. -/
def spacesEtaleModelModulesFactorsh (Z : AlgebraicSpaces B S hS) :
    spacesEtaleModelModulesHomotopyFunctor B S hS Z ⋙ DerivedCategory.Qh ≅
      DerivedCategory.Qh ⋙ spacesEtaleModelModulesDerivedFunctor B S hS Z :=
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Z)).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Z)).2.1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Z)).2.2
  (spacesEtaleModelModulesEquiv B S hS Z).functor.mapDerivedCategoryFactorsh.symm

section Comparison

variable [(smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
    (smallEtaleModuleQuasiIso B S hS Y)]
  (ψ : (spacesEtaleModelHom B S hS f).pullbackTopos ⋙
      (spacesEtaleModelModulesEquiv B S hS X).functor ≅
    (spacesEtaleModelModulesEquiv B S hS Y).functor ⋙ smallEtaleModulePullbackModules B S hS f)

include ψ in
/-- `AlgebraicGeometry.Space.smallEtaleModulePullbackOnHomotopyModulesModelIso`, typed on the
modules of the small étale ringed topoi. -/
def smallEtaleModulePullbackOnHomotopyModelIso :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
        (spacesEtaleModelHom B S hS f) ⋙ spacesEtaleModelModulesDerivedFunctor B S hS X ≅
      spacesEtaleModelModulesHomotopyFunctor B S hS Y ⋙
        smallEtaleModulePullbackOnHomotopy B S hS f :=
  smallEtaleModulePullbackOnHomotopyModulesModelIso B S hS f ψ

include ψ in
/-- **The derived pullback on the small étale sites is the derived pullback on the spaces-étale
models**, under the equivalences of Stacks 03G1, once the two underived pullbacks are identified
by `ψ`. -/
def smallEtaleDerivedModulePullbackModelIso :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback
        (spacesEtaleModelHom B S hS f) ⋙ spacesEtaleModelModulesDerivedFunctor B S hS X ≅
      spacesEtaleModelModulesDerivedFunctor B S hS Y ⋙
        smallEtaleDerivedModulePullback B S hS f :=
  Functor.totalLeftDerivedConjugateIso _ DerivedCategory.Qh DerivedCategory.Qh _
    (smallEtaleModuleQuasiIso B S hS Y) _ _ (spacesEtaleModelModulesFactorsh B S hS Y)
    (smallEtaleModulePullbackOnHomotopyModelIso B S hS f ψ)

include ψ in
/-- **Stacks 08H6 on the small étale sites**, given the identification `ψ` of the underived
pullbacks: `Lf^*` sends perfect objects of `D(𝒪_Y)` to perfect objects of `D(𝒪_X)`. -/
theorem isPerfect_smallEtaleDerivedModulePullback_of_modelIso
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hK : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect
      ((smallEtaleDerivedModulePullback B S hS f).obj K) :=
  isPerfect_smallEtaleRingedSite_of_iso B S hS
    ((smallEtaleDerivedModulePullbackModelIso B S hS f ψ).app
        ((spacesEtaleModelModulesEquiv B S hS Y).inverse.mapDerivedCategory.obj K) ≪≫
      (smallEtaleDerivedModulePullback B S hS f).mapIso
        ((Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
          (spacesEtaleModelModulesEquiv B S hS Y)).counitIso.app K))
    (isPerfect_spacesEtaleModelModulesEquiv_functor B S hS X _
      (isPerfect_derivedPullback_spacesEtaleModelHom f _
        (isPerfect_spacesEtaleModelModulesEquiv_inverse B S hS Y K hK)))

end Comparison

end AlgebraicGeometry.Space
