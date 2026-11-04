module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AbelianRestrictionCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleDirectImageInclusion
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.VanishingTransfer

/-!
# `RΓ(CRIS(X/S), F) ≅ RΓ(Cris(X/S), i^{-1}F)` at module coefficients

Fix a global crystalline situation `(p, (S, I, γ), X)` and let `i : Cris(X/S) ⥤ CRIS(X/S)` be the
inclusion of the small crystalline site into the big one. For a sheaf `F` of `𝒪_{X/S}`-modules on
`CRIS(X/S)` this file constructs an isomorphism

`RΓ(CRIS(X/S), F) ≅ RΓ(Cris(X/S), i^{-1}F)`

in the bounded below derived category of modules over `A = Γ(S, 𝒪_S)`, and shows that `i^{-1}`
carries an injective sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` to a `Γ(Cris(X/S), -)`-acyclic
one.

## Main definitions

* `derivedModuleRestrictι`: `R i^{-1}` on the bounded below derived categories of sheaves of
  modules.
* `derivedBigModuleGlobalSections`: `RΓ(CRIS(X/S), F)` for a single sheaf of modules `F` on the
  big crystalline site, placed in degree zero.
* `derivedRestrictModuleGlobalSectionsFunctorIso`: the isomorphism
  `RΓ(CRIS(X/S), -) ≅ R i^{-1} ⋙ RΓ(Cris(X/S), -)` of functors on bounded below derived
  categories.
* `derivedRestrictModuleGlobalSectionsObjIso`: the isomorphism
  `RΓ(CRIS(X/S), F) ≅ RΓ(Cris(X/S), i^{-1}F)` at a single sheaf of modules `F`.

## Main results

* `toAbelianSheaf_obj_moduleRestrictι_obj`: the underlying abelian sheaf of `i^{-1}F` is the
  restriction of the underlying abelian sheaf of `F`.
* `isZero_moduleCohomology_moduleRestrictι_succ`: `H^{j+1}(Cris(X/S), i^{-1}I) = 0` as an
  `A`-module for `I` an injective sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)`.
* `rightAcyclic_moduleRestrictι_obj`: `i^{-1}` carries an injective sheaf of `𝒪_{X/S}`-modules on
  `CRIS(X/S)` to a `Γ(Cris(X/S), -)`-acyclic sheaf of modules on `Cris(X/S)`.
* `preservesFiniteColimits_moduleRestrictι`: `i^{-1}` on sheaves of modules preserves finite
  colimits.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The underlying abelian sheaf of the restriction -/

/-- The underlying abelian sheaf of `i^{-1}F` is equal to the restriction of the underlying
abelian sheaf of `F`. -/
theorem toAbelianSheaf_obj_moduleRestrictι_obj (F : BigModuleSheaf S) :
    (toAbelianSheaf S).obj ((moduleRestrictι S).obj F) =
      (smallRestriction S).obj ((bigToAbelianSheaf S).obj F) :=
  rfl

/-! ### The vanishing -/

/-- For `I` an injective sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)`,
`H^{j+1}(Cris(X/S), i^{-1}I) = 0` as an `A`-module. -/
theorem isZero_moduleCohomology_moduleRestrictι_succ (I : BigModuleSheaf S) [Injective I]
    (j : ℕ) : IsZero (moduleCohomology S ((moduleRestrictι S).obj I) (j + 1)) :=
  (isZero_moduleCohomology_iff S ((moduleRestrictι S).obj I) (j + 1)).2
    ((isZero_rightDerivedGlobalSections_smallRestriction_iff S
        ((bigToAbelianSheaf S).obj I) (j + 1)).2
      (isZero_bigRightDerived_bigToAbelianSheaf_succ S I j))

/-! ### The acyclicity and the derived comparison -/

section Derived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe v₁ v₂ v₃

variable [HasDerivedCategory.{v₁} (ModuleSheaf S)]
  [HasDerivedCategory.{v₃} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- `i^{-1}` carries an injective sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` to a
`Γ(Cris(X/S), -)`-acyclic sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)`. -/
theorem rightAcyclic_moduleRestrictι_obj (I : BigModuleSheaf S) (hI : Injective I) :
    (baseModuleGlobalSections S).rightAcyclic ((moduleRestrictι S).obj I) := by
  have : Injective I := hI
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by lia⟩
  exact isZero_moduleCohomology_moduleRestrictι_succ S I j

/-- `i^{-1}` on sheaves of `𝒪_{X/S}`-modules preserves finite colimits. -/
instance preservesFiniteColimits_moduleRestrictι :
    PreservesFiniteColimits (moduleRestrictι S) :=
  haveI : PreservesColimitsOfSize.{u + 1, u + 1} (moduleRestrictι S) :=
    (moduleDirectImageιAdjunction S).leftAdjoint_preservesColimits
  inferInstance

variable [HasDerivedCategory.{v₂} (BigModuleSheaf S)]

/-- `R i^{-1}` on sheaves of `𝒪_{X/S}`-modules: the right derived functor, on bounded below derived
categories, of restriction along the inclusion. -/
def derivedModuleRestrictι :
    DerivedCategory.Plus (BigModuleSheaf S) ⥤ DerivedCategory.Plus (ModuleSheaf S) :=
  (moduleRestrictι S).rightDerivedFunctorPlus

/-- `RΓ(CRIS(X/S), F) ∈ D⁺(Mod_A)` for a single sheaf of `𝒪_{X/S}`-modules `F` on the big
crystalline site: the derived global sections of `F` placed in degree zero. -/
def derivedBigModuleGlobalSections :
    BigModuleSheaf S ⥤ DerivedCategory.Plus (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  DerivedCategory.Plus.singleFunctor (BigModuleSheaf S) 0 ⋙
    derivedBigModuleGlobalSectionsFunctor S

/-- The isomorphism `RΓ(CRIS(X/S), -) ≅ R i^{-1} ⋙ RΓ(Cris(X/S), -)` of functors between bounded
below derived categories. -/
def derivedRestrictModuleGlobalSectionsFunctorIso :
    derivedBigModuleGlobalSectionsFunctor S ≅
      derivedModuleRestrictι S ⋙ derivedModuleGlobalSectionsFunctor S :=
  Functor.rightDerivedFunctorPlusNatIso (restrictModuleGlobalSectionsIso S) ≪≫
    Stacks.Cohomology.DerivedPushforwardSections.compIso (moduleRestrictι S)
      (baseModuleGlobalSections S) (rightAcyclic_moduleRestrictι_obj S)

/-- The isomorphism `RΓ(CRIS(X/S), F) ≅ RΓ(Cris(X/S), i^{-1}F)` for a sheaf of
`𝒪_{X/S}`-modules `F` on the big crystalline site. -/
def derivedRestrictModuleGlobalSectionsObjIso (F : BigModuleSheaf S) :
    (derivedBigModuleGlobalSections S).obj F ≅
      (derivedModuleGlobalSections S).obj ((moduleRestrictι S).obj F) :=
  (derivedRestrictModuleGlobalSectionsFunctorIso S).app
      ((DerivedCategory.Plus.singleFunctor (BigModuleSheaf S) 0).obj F) ≪≫
    (derivedModuleGlobalSectionsFunctor S).mapIso
      ((moduleRestrictι S).rightDerivedFunctorPlusObjSingleIso F)

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite

end
