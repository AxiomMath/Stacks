module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.FaithfulConservativePlus
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.InjectiveModuleGlobalSections

/-!
# Forgetting the `A`-module structure of `RΓ(Cris(X/S), -)`

Fix a global crystalline situation `(p, (S, I, γ), X)` and let `A = Γ(S, 𝒪_S)`.  The
module-valued derived global sections `RΓ(Cris(X/S), M) ∈ D⁺(Mod_A)` of a sheaf of
`𝒪_{X/S}`-modules `M`
(`Crystalline.GlobalCrystallineSituation.SmallSite.derivedModuleGlobalSections`) and the
abelian-valued derived global sections `RΓ(Cris(X/S), M_ab) ∈ D⁺(Ab)` of its underlying abelian
sheaf (`Crystalline.GlobalCrystallineSituation.SmallSite.derivedGlobalSections`) are compared:
the image of the former under the forgetful functor `D⁺(Mod_A) ⥤ D⁺(Ab)` *is* the latter,
naturally, as objects of `D⁺(Ab)` and not only degree by degree.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `rightAcyclic_toAbelianSheaf_obj_of_injective` — the underlying abelian sheaf of an injective
  sheaf of `𝒪_{X/S}`-modules is right acyclic for `Γ(Cris(X/S), -)`.
* `globalSectionsForgetIso` — `Γ(Cris(X/S), M_ab) ≅ Γ(Cris(X/S), M)` with its `A`-module structure
  forgotten, naturally in `M`.
* `derivedModuleGlobalSectionsFunctorForgetIso` — the isomorphism of functors
  `D⁺(𝒪_{X/S}) ⥤ D⁺(Ab)` between forgetting the module structure before and after
  `RΓ(Cris(X/S), -)`.
* `derivedModuleGlobalSectionsForgetIso` and `moduleULiftDerivedGlobalSectionsForgetIso` — the
  same for a single module, at the raised and at the predicates' module universe;
  `moduleULiftDerivedGlobalSectionsForgetIsoObj` is the latter at a fixed `F`:
  `forget(RΓ(Cris(X/S), F)) ≅ RΓ(Cris(X/S), abelianSheaf F)`.
* `isIso_iff_isIso_forget₂_mapDerivedCategoryPlus_map` — a morphism of `D⁺(Mod_A)` is an
  isomorphism if and only if its image in `D⁺(Ab)` is.

## Implementation notes

The comparison is `Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso` for the
exact functors `toAbelianSheaf S` and `forget₂ (ModuleCat A) Ab`; its acyclicity input is
`Stacks.Cohomology.GlobalSections.rightAcyclic_Γ_toSheaf_obj_of_injective`, at the universes of
the small crystalline site (objects in `Type (u + 1)`, morphisms and rings in `Type u`, modules
and coefficients in `Type (u + 1)`).  The per-degree comparison
`Crystalline.GlobalCrystallineSituation.SmallSite.abelianComparisonIso` of [Stacks, Tag 03FD] is
not used: what is needed downstream is an isomorphism of objects of `D⁺(Ab)`.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w₁ w₂ w₃ w₄ u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- Forgetting the module structure of sheaves of `𝒪_{X/S}`-modules preserves finite colimits. -/
instance preservesFiniteColimits_toAbelianSheaf : PreservesFiniteColimits (toAbelianSheaf S) :=
  Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{u + 1} (structureSheaf S)

/-- **`Γ(Cris(X/S), M_ab) ≅ Γ(Cris(X/S), M)` as abelian groups**, naturally in the sheaf of
`𝒪_{X/S}`-modules `M`: the global sections of the underlying abelian sheaf are the compatible
families of sections of `M`, with its `A`-module structure forgotten. -/
def globalSectionsForgetIso :
    toAbelianSheaf S ⋙ globalSections S ≅
      baseModuleGlobalSections S ⋙
        forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1} :=
  (Stacks.Cohomology.SiteModules.globalSectionsForgetAddCommGrpIso.{u + 1, u, u, u}
    (structureSheaf S)).symm

section Derived

variable [HasDerivedCategory.{w₁} (ModuleSheaf S)]
  [HasDerivedCategory.{w₂} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{w₃} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} AddCommGrpCat.{u + 1}]

omit [HasDerivedCategory (ModuleSheaf S)]
  [HasDerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))] in
/-- **The underlying abelian sheaf of an injective sheaf of `𝒪_{X/S}`-modules is right acyclic
for `Γ(Cris(X/S), -)`**: the single complex on it computes `RΓ(Cris(X/S), -)`. -/
theorem rightAcyclic_toAbelianSheaf_obj_of_injective (M : ModuleSheaf S) [Injective M] :
    (globalSections S).rightAcyclic ((toAbelianSheaf S).obj M) :=
  Stacks.Cohomology.GlobalSections.rightAcyclic_Γ_toSheaf_obj_of_injective.{w₃, w₄, u, u, u,
    u + 1} (smallTopology S) (structureSheaf S) M

/-- **Forgetting the module structure commutes with `RΓ(Cris(X/S), -)`**, as functors
`D⁺(𝒪_{X/S}) ⥤ D⁺(Ab)`: forgetting a complex of sheaves of `𝒪_{X/S}`-modules to its underlying
complex of abelian sheaves and then taking `RΓ(Cris(X/S), -)` is the same as taking the
`A`-module-valued `RΓ(Cris(X/S), -)` and then forgetting the `A`-module structure. -/
def derivedModuleGlobalSectionsFunctorForgetIso :
    (toAbelianSheaf S).mapDerivedCategoryPlus ⋙ derivedGlobalSectionsFunctor S ≅
      derivedModuleGlobalSectionsFunctor S ⋙
        (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))
          AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus :=
  Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso (toAbelianSheaf S)
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})
    (baseModuleGlobalSections S) (globalSections S) (globalSectionsForgetIso S)
    (fun I _ => rightAcyclic_toAbelianSheaf_obj_of_injective S I)

/-- **`forget(RΓ(Cris(X/S), M)) ≅ RΓ(Cris(X/S), M_ab)` in `D⁺(Ab)`**, naturally in the sheaf of
`𝒪_{X/S}`-modules `M`, each placed in degree zero. -/
def derivedModuleGlobalSectionsForgetIso :
    derivedModuleGlobalSections S ⋙
        (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))
          AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus ≅
      toAbelianSheaf S ⋙ derivedGlobalSections S :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (ModuleSheaf S) 0)
      (derivedModuleGlobalSectionsFunctorForgetIso S).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
        (X := DerivedCategory.Plus.singleFunctor (ModuleSheaf S) 0 ⋙
          (toAbelianSheaf S).mapDerivedCategoryPlus)
        (Y := toAbelianSheaf S ⋙
          DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0)
        ((toAbelianSheaf S).mapDerivedCategorySingleFunctor 0))
      (derivedGlobalSectionsFunctor S) ≪≫
    Functor.associator _ _ _

/-- **`forget(RΓ(Cris(X/S), F)) ≅ RΓ(Cris(X/S), abelianSheaf F)` in `D⁺(Ab)`** for `F` a sheaf of
`𝒪_{X/S}`-modules at the universe the chapter's crystal and quasi-coherence predicates are stated
at, naturally in `F`: the left hand side is the image of
`moduleULiftDerivedGlobalSections S F` under the forgetful functor, the right hand side the
abelian-valued derived global sections of the abelian sheaf of `F` (`toAbelianSheaf_obj_moduleULift`
identifies the two abelian sheaves by `rfl`). -/
def moduleULiftDerivedGlobalSectionsForgetIso :
    moduleULiftDerivedGlobalSectionsFunctor S ⋙
        (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))
          AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus ≅
      moduleULift S ⋙ toAbelianSheaf S ⋙ derivedGlobalSections S :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleULift S) (derivedModuleGlobalSectionsForgetIso S)

/-- `moduleULiftDerivedGlobalSectionsForgetIso` at a fixed sheaf of `𝒪_{X/S}`-modules `F`. -/
def moduleULiftDerivedGlobalSectionsForgetIsoObj
    (F : _root_.SheafOfModules.{u} (structureSheaf S)) :
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))
        AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus.obj
        (moduleULiftDerivedGlobalSections S F) ≅
      (derivedGlobalSections S).obj (abelianSheaf F) :=
  (moduleULiftDerivedGlobalSectionsForgetIso S).app F

omit [HasDerivedCategory (ModuleSheaf S)]
  [HasDerivedCategory (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})] in
/-- **A morphism of `D⁺(Mod_A)` is an isomorphism if and only if its image in `D⁺(Ab)` is.** -/
theorem isIso_iff_isIso_forget₂_mapDerivedCategoryPlus_map
    {K L : DerivedCategory.Plus (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))} (φ : K ⟶ L) :
    IsIso φ ↔ IsIso ((forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))
      AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus.map φ) :=
  (Stacks.Cohomology.isIso_forget₂_mapDerivedCategoryPlus_map_iff φ).symm

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite

end
