module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingLinearComplex07MW

/-!
# [Stacks, Tag 07MW] part (3) in `D(A)`, from the map of [Stacks, Equation 07LP]

In the situation of [Stacks, Tag 07MW] (`...SmallSite.Situation07MW`), with `A = Γ(S, 𝒪_S)`,
`f : Y ⟶ S` the smooth lifting, `B = (X, Y, γ)` the object of `Cris(X/S)` it defines (part (1)),
and `F` a crystal in quasi-coherent `𝒪_{X/S}`-modules with its canonical integrable connection
on `F_Y` (part (2), `Situation07MW.moduleWithConnection`), this file proves part (3),

`RΓ(Cris(X/S), F) ≅ RΓ(Y, F_Y ⊗_{𝒪_Y} Ω^•_{Y/S})` in `D⁺(Mod_A)`,

**from the hypothesis that the map `RΓ(Cris(X/S), F) ⟶ RΓ(Y, F_Y ⊗ Ω^•_{Y/S})` of
[Stacks, Equation 07LP] at `B` is an isomorphism in `D⁺(Ab)`**
(`...SmallSite.crystallineToAmbientDeRham hF T.crystallineThickening`).  That hypothesis is the
abelian form of the statement; it is not discharged in this file.  It is reduced to a statement
on affine opens in `SmallSite/SmoothLiftingCrisDeRhamAbelian07MW.lean` and proved as
`Situation07MW.isIso_crystallineToAmbientDeRham` in
`SmallSite/SmoothLiftingCrisDeRhamIso07MW.lean`.

## The argument

The isomorphism is the composite, in `D⁺(Mod_A)`,

`RΓ(Cris(X/S), F) ≅ RΓ_A(Cris(X/S), F[0]) ≅ RΓ_A(Cris(X/S), K) ≅ RΓ_A(T, K_T)
  ≅ RΓ_A(Y, F_Y ⊗ Ω^•_{Y/S}) ≅ RΓ(Y, F_Y ⊗ Ω^•_{Y/S})`,

where `K = F ⊗ Ω^•_{X/S}` is the de Rham complex of [Stacks, Tag 07LM] read as a complex of
sheaves of `A`-modules, `RΓ_A` are the derived functors of `A`-linear global sections, and:

1. the first is `moduleULiftDerivedGlobalSectionsIsoLinear` (reading `𝒪_{X/S}`-modules as
   `A`-modules does not change `RΓ`);
2. the second is the inverse of the `A`-linear truncation, an isomorphism by [Stacks, Tag 07LM]
   (`isIso_derivedBaseLinearGlobalSections_map_linearTruncationPlus`);
3. the third is the `A`-linear restriction of global cohomology classes to `T`, an isomorphism
   because its abelian form is, by the hypothesis
   (`isIso_derivedLinearGlobalSectionsToAmbient_app_linearDeRhamPlus`);
4. the fourth is `RΓ_A(T, -)` of the identification of `K_T` with the twisted de Rham complex
   of the canonical connection, read as sheaves of `A`-modules
   (`Situation07MW.twistedComplexIso`);
5. the last is `Situation07MW.derivedBaseGlobalSectionsIsoLinear`.

## Main results

* `Situation07MW.nonempty_iso_derivedBaseGlobalSections_of_isIso` — **part (3) of
  [Stacks, Tag 07MW] for `F`, with the named module with connection of part (2), from the
  abelian isomorphism of [Stacks, Equation 07LP] at `(X, Y, γ)`.**
* `Situation07MW.deRhamComparison07MW_of_isIso` — `Situation07MW.DeRhamComparison07MW` from
  that abelian isomorphism for every crystal in quasi-coherent modules.

## What is and is not proved

Everything above is proved from the stated hypothesis; nothing else is assumed.  The hypothesis
itself is not proved here, and no tag attribute is placed.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07LP](https://stacks.math.columbia.edu/tag/07LP)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
-/

-- The same derived-category models as `SmallSite/SmoothLiftingComparison.lean`, so that the
-- statements below are the ones of `Situation07MW.DeRhamComparison07MW`.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MW S)
  [HasDerivedCategory.{u + 1} (ModuleSheaf S)]
  {F : SheafOfModules.{u} (structureSheaf S)} (hF : F.IsQuasicoherentOnSite)

omit [HasDerivedCategory (ModuleSheaf S)] in
/-- The twisted de Rham complex extended over `ℤ`, read as a complex of sheaves of `A`-modules, is
the restriction `K_T` of the `A`-linear de Rham complex. -/
def twistedComplexExtendIso :
    ((CrystallineThickening.linearAmbientRestriction T.crystallineThickening).mapHomologicalComplex
        _).obj (crystalDeRhamLinearComplex hF) ≅
      (T.toAmbientModuleSheaf.mapHomologicalComplex _).obj
        ((T.moduleWithConnection hF).complex.extend ComplexShape.embeddingUpNat) :=
  (HomologicalComplex.mapHomologicalComplexExtendIso
      (CrystallineThickening.linearAmbientRestriction T.crystallineThickening)
      (crystalDeRhamLinearNatComplex hF) ComplexShape.embeddingUpNat).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (T.twistedComplexIso hF) ≪≫
    HomologicalComplex.mapHomologicalComplexExtendIso T.toAmbientModuleSheaf
      (T.moduleWithConnection hF).complex ComplexShape.embeddingUpNat

omit [HasDerivedCategory (ModuleSheaf S)] in
/-- **`K_T ≅ F_Y ⊗ Ω^•_{Y/S}` in `D⁺(Mod_A(T_Zar))`**, both read as complexes of sheaves of
`A`-modules. -/
def derivedTwistedComplexIso [HasDerivedCategory (BaseModuleSheaf S)]
    [HasDerivedCategory (CrystallineThickening.AmbientModuleSheaf T.crystallineThickening)]
    [HasDerivedCategory (TwistedModules T.toBase)] :
    (CrystallineThickening.linearAmbientRestriction
        T.crystallineThickening).mapDerivedCategoryPlus.obj (linearDeRhamPlus hF) ≅
      T.toAmbientModuleSheaf.mapDerivedCategoryPlus.obj
        (plusObjectOfCochainComplex T.toBase (T.moduleWithConnection hF).complex) := by
  refine (CrystallineThickening.linearAmbientRestriction
      T.crystallineThickening).mapDerivedCategoryPlusFactorsh.app _ ≪≫ ?_ ≪≫
    (T.toAmbientModuleSheaf.mapDerivedCategoryPlusFactorsh.app _).symm
  exact DerivedCategory.Plus.Qh.mapIso (ObjectProperty.isoMk _
    ((HomotopyCategory.quotient _ _).mapIso (T.twistedComplexExtendIso hF)))

/-- **Part (3) of [Stacks, Tag 07MW] for `F`, from the abelian map of [Stacks, Equation 07LP].**
If the map `RΓ(Cris(X/S), F) ⟶ RΓ(Y, F_Y ⊗ Ω^•_{Y/S})` of [Stacks, Equation 07LP] at the object
`(X, Y, γ)` is an isomorphism in `D⁺(Ab)`, then

`RΓ(Cris(X/S), F) ≅ RΓ(Y, F_Y ⊗_{𝒪_Y} Ω^•_{Y/S})` in `D⁺(Mod_A)`,

the right hand side being formed with the canonical integrable connection of part (2),
`moduleWithConnection hF`. -/
theorem nonempty_iso_derivedBaseGlobalSections_of_isIso
    [HasDerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
    [HasDerivedCategory (TwistedModules T.toBase)]
    [HasDerivedCategory (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (Sheaf (Opens.grothendieckTopology
      T.crystallineThickening.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]
    (h : IsIso (crystallineToAmbientDeRham hF T.crystallineThickening)) :
    Nonempty (moduleULiftDerivedGlobalSections S F ≅
      derivedBaseGlobalSections T.toBase (T.moduleWithConnection hF).complex) := by
  letI := HasDerivedCategory.standard (BaseModuleSheaf S)
  letI := HasDerivedCategory.standard
    (CrystallineThickening.AmbientModuleSheaf T.crystallineThickening)
  have := isIso_derivedBaseLinearGlobalSections_map_linearTruncationPlus hF
  have := isIso_derivedLinearGlobalSectionsToAmbient_app_linearDeRhamPlus hF
    T.crystallineThickening h
  exact ⟨moduleULiftDerivedGlobalSectionsIsoLinear F ≪≫
    (asIso ((derivedBaseLinearGlobalSectionsFunctor S).map (linearTruncationPlus hF))).symm ≪≫
    asIso ((CrystallineThickening.derivedLinearGlobalSectionsToAmbient
      T.crystallineThickening).app (linearDeRhamPlus hF)) ≪≫
    (CrystallineThickening.ambientLinearGlobalSections
      T.crystallineThickening).rightDerivedFunctorPlus.mapIso (T.derivedTwistedComplexIso hF) ≪≫
    (T.derivedBaseGlobalSectionsIsoLinear _).symm⟩

/-- **`Situation07MW.DeRhamComparison07MW` from the abelian map of [Stacks, Equation 07LP].**  If
for every crystal in quasi-coherent modules `F` the map of [Stacks, Equation 07LP] at
`(X, Y, γ)` is an isomorphism in `D⁺(Ab)`, part (3) of [Stacks, Tag 07MW] holds, the module with
connection being the one of part (2). -/
theorem deRhamComparison07MW_of_isIso
    [HasDerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
    [HasDerivedCategory (TwistedModules T.toBase)]
    [HasDerivedCategory (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (Sheaf (Opens.grothendieckTopology
      T.crystallineThickening.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]
    (h : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      IsIso (crystallineToAmbientDeRham hF T.crystallineThickening)) :
    T.DeRhamComparison07MW :=
  fun F hF => ⟨T.moduleWithConnection hF,
    T.nonempty_iso_derivedBaseGlobalSections_of_isIso hF (h F hF)⟩

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

end

end
