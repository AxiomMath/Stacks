module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionLinearDerived07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamLinear07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Equation07LP
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleDerivedGlobalSectionsForget
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject

/-!
# `RΓ(Cris(X/S), F) = RΓ_A(Cris(X/S), F ⊗ Ω^•_{X/S})` over `A`, and restriction to `T`

Fix a global crystalline situation `(p, (S, I, γ), X)`, write `A = Γ(S, 𝒪_S)`, and let `F` be a
crystal in quasi-coherent `𝒪_{X/S}`-modules, with `A`-linear de Rham complex
`K = ...SmallSite.crystalDeRhamLinearComplex hF`, a complex of sheaves of `A`-modules on
`Cris(X/S)`.  This file proves, in `D⁺(Mod_A)`:

1. `RΓ(Cris(X/S), F) ≅ RΓ_A(Cris(X/S), F[0])`: the derived global sections of the
   `𝒪_{X/S}`-module `F` are those of `F` read as a sheaf of `A`-modules
   (`moduleULiftDerivedGlobalSectionsIsoLinear`);
2. the truncation `K ⟶ F[0]` becomes an isomorphism after `RΓ_A(Cris(X/S), -)`
   (`isIso_derivedBaseLinearGlobalSections_map_linearTruncationPlus`), by [Stacks, Tag 07LM];
3. if the map of [Stacks, Equation 07LP] at an object `B` of `Cris(X/S)` is an isomorphism, so is
   the `A`-linear restriction `RΓ_A(Cris(X/S), K) ⟶ RΓ_A(T, K_T)`
   (`isIso_derivedLinearGlobalSectionsToAmbient_app_linearDeRhamPlus`).

Each statement is reduced to its abelian counterpart: forgetting the `A`-module structure is
conservative on `D⁺`, and commutes with the derived functors because the underlying abelian sheaf
of an injective sheaf of `A`-modules (or of `𝒪_{X/S}`-modules) is acyclic for global sections.

## References

* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07LP](https://stacks.math.columbia.edu/tag/07LP)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ u

noncomputable section

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### Sheaves of `𝒪_{X/S}`-modules as sheaves of `A`-modules -/

/-- Reading a sheaf of `𝒪_{X/S}`-modules as a sheaf of `A`-modules is additive. -/
instance additive_toBaseModuleSheaf : (toBaseModuleSheaf S).Additive where
  map_add {_ _ f g} := (baseForget S).map_injective (by
    rw [(baseForget S).map_add]
    exact (toAbelianSheaf S).map_add (f := f) (g := g))

/-- Forgetting the `A`-action on `Cris(X/S)` reflects finite limits. -/
instance reflectsFiniteLimits_baseForget : ReflectsFiniteLimits (baseForget S) :=
  reflectsFiniteLimits_of_reflectsIsomorphisms _

/-- Forgetting the `A`-action on `Cris(X/S)` reflects finite colimits. -/
instance reflectsFiniteColimits_baseForget : ReflectsFiniteColimits (baseForget S) where
  reflects _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

/-- Reading a sheaf of `𝒪_{X/S}`-modules as a sheaf of `A`-modules preserves finite limits. -/
instance preservesFiniteLimits_toBaseModuleSheaf : PreservesFiniteLimits (toBaseModuleSheaf S) :=
  have : PreservesFiniteLimits (toBaseModuleSheaf S ⋙ baseForget S) :=
    inferInstanceAs (PreservesFiniteLimits (toAbelianSheaf S))
  preservesFiniteLimits_of_reflects_of_preserves _ (baseForget S)

/-- Reading a sheaf of `𝒪_{X/S}`-modules as a sheaf of `A`-modules preserves finite colimits. -/
instance preservesFiniteColimits_toBaseModuleSheaf :
    PreservesFiniteColimits (toBaseModuleSheaf S) :=
  have : PreservesFiniteColimits (toBaseModuleSheaf S ⋙ baseForget S) :=
    inferInstanceAs (PreservesFiniteColimits (toAbelianSheaf S))
  preservesFiniteColimits_of_reflects_of_preserves _ (baseForget S)

section Derived

variable [HasDerivedCategory.{w₁} (ModuleSheaf S)] [HasDerivedCategory.{w₂} (BaseModuleSheaf S)]
  [HasDerivedCategory.{w₃} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{w₄} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅} AddCommGrpCat.{u + 1}]

omit [HasDerivedCategory (ModuleSheaf S)] in
/-- **A sheaf of `𝒪_{X/S}`-modules which is injective is, read as a sheaf of `A`-modules, acyclic
for `Γ_A(Cris(X/S), -)`**: its underlying abelian sheaf is acyclic for the abelian global
sections. -/
theorem rightAcyclic_baseLinearGlobalSections_toBaseModuleSheaf_obj_of_injective
    (I : ModuleSheaf S) [Injective I] :
    (baseLinearGlobalSections S).rightAcyclic ((toBaseModuleSheaf S).obj I) :=
  Stacks.Cohomology.DerivedBaseChangePlus.rightAcyclic_of_rightAcyclic_baseChange (baseForget S)
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})
    (baseLinearGlobalSections S) (globalSections S) (baseLinearGlobalSectionsForgetIso S).symm
    (fun J _ => rightAcyclic_globalSections_baseForget_obj_of_injective S J) _
    (rightAcyclic_toAbelianSheaf_obj_of_injective S I)

variable {S} {F : SheafOfModules.{u} (structureSheaf S)} (hF : F.IsQuasicoherentOnSite)

variable (F) in
/-- **`F[0]` of sheaves of `A`-modules, as an object of `D⁺(Mod_A(Cris(X/S)))`.** -/
abbrev linearSinglePlus : DerivedCategory.Plus (BaseModuleSheaf S) :=
  plusOfCochainComplex S (linearCrystalSingleComplex F)

/-- **The `A`-linear de Rham complex of `F`, as an object of `D⁺(Mod_A(Cris(X/S)))`.** -/
abbrev linearDeRhamPlus : DerivedCategory.Plus (BaseModuleSheaf S) :=
  plusOfCochainComplex S (crystalDeRhamLinearComplex hF)

omit [HasDerivedCategory (ModuleSheaf S)] [HasDerivedCategory (BaseModuleSheaf S)]
  [HasDerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory AddCommGrpCat.{u + 1}] in
/-- The `A`-linear truncation `K ⟶ F[0]`, as a morphism of bounded below complexes. -/
abbrev linearTruncationPlusHom :
    (⟨crystalDeRhamLinearComplex hF, ⟨0, inferInstance⟩⟩ : CochainComplex.Plus (BaseModuleSheaf S))
      ⟶ ⟨linearCrystalSingleComplex F, ⟨0, inferInstance⟩⟩ :=
  ObjectProperty.homMk (crystalDeRhamLinearTruncation hF)

/-- **The `A`-linear truncation `K ⟶ F[0]`, in `D⁺(Mod_A(Cris(X/S)))`.** -/
def linearTruncationPlus : linearDeRhamPlus hF ⟶ linearSinglePlus F :=
  DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient (BaseModuleSheaf S)).map
    (linearTruncationPlusHom hF))

omit [HasDerivedCategory (ModuleSheaf S)] [HasDerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory AddCommGrpCat.{u + 1}] in
variable (F) in
/-- `F[0]` of sheaves of `A`-modules placed in degree zero is the complex
`linearCrystalSingleComplex F`. -/
def singleFunctorIsoLinearSinglePlus :
    (DerivedCategory.Plus.singleFunctor (BaseModuleSheaf S) 0).obj (linearCrystalSheaf F) ≅
      linearSinglePlus F :=
  (Functor.singleFunctorPlusIsoCompQh 0).app _ ≪≫
    DerivedCategory.Plus.Qh.mapIso (ObjectProperty.isoMk _
      ((HomotopyCategory.quotient _ _).mapIso
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
          (linearCrystalSheaf F) 0 0 rfl).symm))

variable (F) in
/-- **`RΓ(Cris(X/S), F) ≅ RΓ_A(Cris(X/S), F[0])` in `D⁺(Mod_A)`**: the derived global sections of
the `𝒪_{X/S}`-module `F` are the derived `A`-linear global sections of `F` read as a sheaf of
`A`-modules.  Reading as a sheaf of `A`-modules is exact and carries injectives to objects
acyclic for `Γ_A`, so `R(Γ_A ∘ toBaseModuleSheaf) = RΓ_A ∘ toBaseModuleSheaf`, and
`Γ_A ∘ toBaseModuleSheaf` is the module-valued global sections. -/
def moduleULiftDerivedGlobalSectionsIsoLinear :
    moduleULiftDerivedGlobalSections S F ≅
      (derivedBaseLinearGlobalSectionsFunctor S).obj (linearSinglePlus F) :=
  (Functor.rightDerivedFunctorPlusNatIso (toBaseModuleSheafGlobalSectionsIso S).symm).app _ ≪≫
    (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic (toBaseModuleSheaf S)
      (baseLinearGlobalSections S)
      (fun I _ => rightAcyclic_baseLinearGlobalSections_toBaseModuleSheaf_obj_of_injective S I)).app
      _ ≪≫
    (baseLinearGlobalSections S).rightDerivedFunctorPlus.mapIso
      ((toBaseModuleSheaf S).rightDerivedFunctorPlusObjSingleIso ((moduleULift S).obj F) ≪≫
        singleFunctorIsoLinearSinglePlus F)

omit [HasDerivedCategory (ModuleSheaf S)] in
/-- **The `A`-linear truncation `K ⟶ F[0]` becomes an isomorphism after `RΓ_A(Cris(X/S), -)`.**
Forgetting the `A`-module structure carries it to the abelian `RΓ(Cris(X/S), -)` of the
truncation map of [Stacks, Tag 07LM], which is an isomorphism
(`CrystalDeRhamSheafData.isIso_derivedGlobalSections_map_truncation`); forgetting is conservative
on `D⁺`. -/
theorem isIso_derivedBaseLinearGlobalSections_map_linearTruncationPlus
    [HasDerivedCategory.{w₆} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] :
    IsIso ((derivedBaseLinearGlobalSectionsFunctor S).map (linearTruncationPlus hF)) := by
  apply (Stacks.Cohomology.isIso_forget₂_mapDerivedCategoryPlus_map_iff _).1
  let e := Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso (baseForget S)
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})
    (baseLinearGlobalSections S) (globalSections S) (baseLinearGlobalSectionsForgetIso S).symm
    (fun J _ => rightAcyclic_globalSections_baseForget_obj_of_injective S J)
  refine (NatIso.isIso_map_iff e (linearTruncationPlus hF)).1 ?_
  refine (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (baseForget S).mapDerivedCategoryPlusFactorsh (globalSections S).rightDerivedFunctorPlus)
    ((HomotopyCategory.Plus.quotient (BaseModuleSheaf S)).map (linearTruncationPlusHom hF))).2 ?_
  let a : (⟨_, ⟨0, inferInstance⟩⟩ : CochainComplex.Plus
      (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) ≅ (crystalDeRhamSheafData hF).complexPlus :=
    ObjectProperty.isoMk _ (crystalDeRhamLinearComplexForgetIso hF)
  let b : (⟨_, ⟨0, inferInstance⟩⟩ : CochainComplex.Plus
      (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) ≅
        sheafPlusComplex S (CrystalDeRhamSheafData.singleComplex (F := F)) :=
    ObjectProperty.isoMk _ (linearCrystalSingleComplexForgetIso F)
  have key : (baseForget S).mapHomotopyCategoryPlus.map
      ((HomotopyCategory.Plus.quotient (BaseModuleSheaf S)).map (linearTruncationPlusHom hF)) =
      (HomotopyCategory.Plus.quotient _).map a.hom ≫
        (HomotopyCategory.Plus.quotient _).map
          (sheafPlusTruncation S (crystalDeRhamSheafData hF).complex
            (CrystalDeRhamSheafData.singleComplex (F := F))
            (crystalDeRhamSheafData hF).truncation) ≫
        (HomotopyCategory.Plus.quotient _).map b.inv := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine ObjectProperty.hom_ext _ ?_
    refine congrArg (HomotopyCategory.quotient _ _).map ?_
    change ((baseForget S).mapHomologicalComplex _).map (crystalDeRhamLinearTruncation hF) =
      (crystalDeRhamLinearComplexForgetIso hF).hom ≫ (crystalDeRhamSheafData hF).truncation ≫
        (linearCrystalSingleComplexForgetIso F).inv
    rw [← Category.assoc, ← crystalDeRhamLinearTruncation_forget, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h2 := (crystalDeRhamSheafData hF).isIso_derivedGlobalSections_map_truncation
    (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).1
    (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).2
  change IsIso ((globalSections S).rightDerivedFunctorPlus.map
    (DerivedCategory.Plus.Qh.map ((baseForget S).mapHomotopyCategoryPlus.map
      ((HomotopyCategory.Plus.quotient (BaseModuleSheaf S)).map (linearTruncationPlusHom hF)))))
  have h3 : IsIso ((globalSections S).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
      ((HomotopyCategory.Plus.quotient _).map a.hom ≫
        (HomotopyCategory.Plus.quotient _).map
          (sheafPlusTruncation S (crystalDeRhamSheafData hF).complex
            (CrystalDeRhamSheafData.singleComplex (F := F))
            (crystalDeRhamSheafData hF).truncation) ≫
        (HomotopyCategory.Plus.quotient _).map b.inv))) := by
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
      (@IsIso.comp_isIso _ _ _ _ _ _ _ h2 inferInstance)
  rw [key]
  exact h3

variable [HasDerivedCategory.{w₆} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  (B : CrystallineThickening S)
  [HasDerivedCategory.{w₇}
    (Sheaf (Opens.grothendieckTopology B.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]

omit [HasDerivedCategory (ModuleSheaf S)]
  [HasDerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))] in
/-- **If the map of [Stacks, Equation 07LP] is an isomorphism, so is the restriction of global
cohomology classes of `F ⊗ Ω^•_{X/S}` to `T`**, at the complex of abelian sheaves underlying the
`A`-linear de Rham complex: by `truncation_comp_crystallineToAmbientDeRham` the map of 07LP is the
restriction up to the invertible image of the truncation map. -/
theorem isIso_derivedGlobalSectionsToAmbient_app_linearDeRhamPlus
    (h : IsIso (crystallineToAmbientDeRham hF B)) :
    IsIso ((CrystallineThickening.derivedGlobalSectionsToAmbient B).app
      ((baseForget S).mapDerivedCategoryPlus.obj (linearDeRhamPlus hF))) := by
  let a : (⟨_, ⟨0, inferInstance⟩⟩ : CochainComplex.Plus
      (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) ≅ (crystalDeRhamSheafData hF).complexPlus :=
    ObjectProperty.isoMk _ (crystalDeRhamLinearComplexForgetIso hF)
  let eK : (baseForget S).mapDerivedCategoryPlus.obj (linearDeRhamPlus hF) ≅
      DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
        (crystalDeRhamSheafData hF).complexPlus) :=
    (baseForget S).mapDerivedCategoryPlusFactorsh.app _ ≪≫
      DerivedCategory.Plus.Qh.mapIso ((HomotopyCategory.Plus.quotient _).mapIso a)
  rw [NatTrans.isIso_app_iff_of_iso _ eK]
  have h1 := truncation_comp_crystallineToAmbientDeRham hF B
  have h2 := (crystalDeRhamSheafData hF).isIso_derivedGlobalSections_map_truncation
    (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).1
    (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).2
  have h4 := (congrArg IsIso h1).mp (@IsIso.comp_isIso _ _ _ _ _ _ _ h2
    (@IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance h))
  exact IsIso.of_isIso_comp_right _ ((CrystallineThickening.derivedAmbientGlobalSectionsFunctor
    B).map ((crystalDeRhamSheafData hF).derivedRestrictComplexIso B).hom)

omit [HasDerivedCategory (ModuleSheaf S)] in
/-- **If the map of [Stacks, Equation 07LP] is an isomorphism, so is the `A`-linear restriction
`RΓ_A(Cris(X/S), F ⊗ Ω^•_{X/S}) ⟶ RΓ_A(T, (F ⊗ Ω^•_{X/S})_T)`.** -/
theorem isIso_derivedLinearGlobalSectionsToAmbient_app_linearDeRhamPlus
    [HasDerivedCategory.{w₈} (CrystallineThickening.AmbientModuleSheaf B)]
    (h : IsIso (crystallineToAmbientDeRham hF B)) :
    IsIso ((CrystallineThickening.derivedLinearGlobalSectionsToAmbient B).app
      (linearDeRhamPlus hF)) :=
  CrystallineThickening.isIso_derivedLinearGlobalSectionsToAmbient_app B _
    (isIso_derivedGlobalSectionsToAmbient_app_linearDeRhamPlus hF B h)

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
