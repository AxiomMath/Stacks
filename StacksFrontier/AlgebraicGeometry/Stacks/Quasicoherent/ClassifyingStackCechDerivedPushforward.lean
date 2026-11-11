module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ClassifyingStackCechTermsDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardOfStacksUnbounded
public import StacksFrontier.Algebra.Homology.DerivedCategory.FunctorialResolutionRightDerived

/-!
# The derived direct image of the structure sheaf of `B(ℤ/2)_S` by the Čech complex

Let `S` be a scheme of a big fppf site, `G = (ℤ/2)_S` the constant group, `𝒳 = BG` its
classifying stack and `f : 𝒳 ⟶ S` the structure morphism. This file shows that the relative Čech
complex of the atlas `π : S ⟶ BG` computes the unbounded derived direct image `Rf_*` of the
structure sheaf at module universe `u + 1`:

`Rf_*(𝒪_𝒳[0]) ≅ Q(K)`,

where `K` is the extension to `ℤ` of the alternating coface complex of the cosimplicial module
`𝒦 = f_* (n ↦ cₙ,* cₙ⁻¹ 𝒪_𝒳)`. The augmentation of a module into its relative Čech complex is a
resolution (Stacks 06XE), injective modules have injective Čech terms, and `f_* cₙ,* cₙ⁻¹` has
no higher right derived functors at `𝒪_𝒳`
(`AlgebraicGeometry.Stack.ClassifyingZModTwo.isZero_rightDerived_cechDirectImage_uliftUnit`), so
the Čech complex computes `Rf_*`
(`CategoryTheory.Functor.rightDerivedFunctorPlusSingleIsoOfFunctorialResolution`).

## Main definitions

* `AlgebraicGeometry.Stack.ClassifyingZModTwo.cechCosimplicial`: the cosimplicial module `𝒦`.
* `AlgebraicGeometry.Stack.ClassifyingZModTwo.derivedPushforwardStructureModuleIso`:
  `Rf_*(𝒪_𝒳[0]) ≅ Q(K)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicGeometry.Stack.ClassifyingAtlasCech Stacks.Examples

universe u w

namespace AlgebraicGeometry.Stack.ClassifyingZModTwo

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} (hS : C.Contains S)

/-- The direct image along the structure morphism is additive, as it preserves finite limits. -/
instance additive_fppfModuleSheafPushforwardOfStacks_structureMap :
    (fppfModuleSheafPushforwardOfStacks C S hS (structureMap.{u, w} hS)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### The cosimplicial module -/

/-- The structure sheaf of `B(ℤ/2)_S` at module universe `u + 1`. -/
abbrev structureModule : fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS) :=
  Stacks.SheafOfModules.uliftUnit.{u + 1} _

/-- The structure sheaf of the base at module universe `u + 1`. -/
abbrev baseStructureModule : fppfModulesUnivLE.{u, w, u + 1} C S hS (base.{u, w} hS) :=
  Stacks.SheafOfModules.uliftUnit.{u + 1} _

/-- **The cosimplicial module `𝒦`**: the direct image along the structure morphism of the relative
Čech cosimplicial module of the structure sheaf along the atlas. -/
abbrev cechCosimplicial :
    CosimplicialObject (fppfModulesUnivLE.{u, w, u + 1} C S hS (base.{u, w} hS)) :=
  (Stacks.RelativeCech.cechModuleEndofunctorCosimplicial.{u, u + 1, u + 1, u, u, u} C S hS
      (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.val.p
      (stack.{u, w} hS).val.val.p
      (classifyingAtlasFunctor.{u, w} _ (isSmooth_constantZModTwoGroup hS)) .fppf
      (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.isFiberedInGroupoids
      (stack.{u, w} hS).val.isFiberedInGroupoids
      (isFibredOneMorphism_classifyingAtlasFunctor.{u, w} _
        (isSmooth_constantZModTwoGroup hS))).flip.obj (structureModule.{u, w} hS) ⋙
    fppfModuleSheafPushforwardOfStacks C S hS (structureMap.{u, w} hS)

/-- The degree `n` term of `𝒦` is `f_* cₙ,* cₙ⁻¹ 𝒪_𝒳`. -/
theorem cechCosimplicial_obj (n : ℕ) :
    (cechCosimplicial.{u, w} hS).obj ⦋n⦌ =
      (cechDirectImage.{u, w} hS n).obj (structureModule.{u, w} hS) :=
  rfl

section Derived

/-- **The complex `K`**: the alternating coface complex of `𝒦`, extended by zero to `ℤ`. -/
abbrev cechComplexInt :
    CochainComplex (fppfModulesUnivLE.{u, w, u + 1} C S hS (base.{u, w} hS)) ℤ :=
  ((AlgebraicTopology.alternatingCofaceMapComplex _).obj (cechCosimplicial.{u, w} hS)).extend
    ComplexShape.embeddingUpNat

variable [HasDerivedCategory.{u + 2}
    (fppfModulesUnivLE.{u, w, u + 1} C S hS (stack.{u, w} hS))]
  [HasDerivedCategory.{u + 2}
    (fppfModulesUnivLE.{u, w, u + 1} C S hS (base.{u, w} hS))]

/-- **The derived direct image of the structure sheaf of `B(ℤ/2)_S`**:
`Rf_*(𝒪_𝒳[0]) ≅ Q(K)` in `D(𝒪_S)`, where `f : B(ℤ/2)_S ⟶ S` is the structure morphism, `Rf_*` the
unbounded derived direct image at module universe `u + 1`, and `K` the extension to `ℤ` of the
alternating coface complex of `𝒦 ≅ cochainCosimplicial 𝒪_S` (`cechCosimplicialIso`). -/
def derivedPushforwardStructureModuleIso :
    (fppfDerivedPushforwardOfStacks C S hS (structureMap.{u, w} hS)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule.{u, w} hS)) ≅
      DerivedCategory.Q.obj (cechComplexInt.{u, w} hS) :=
  letI := enoughInjectives_fppfModulesUnivLESucc C S hS (stack.{u, w} hS)
  (fppfDerivedPushforwardOfStacks C S hS (structureMap.{u, w} hS)).mapIso
      ((DerivedCategory.Plus.singleFunctorιIso _ 0).app (structureModule.{u, w} hS)).symm ≪≫
    ((fppfDerivedPushforwardPlusOfStacksCompιIso C S hS (structureMap.{u, w} hS)).app _).symm ≪≫
    (fppfModuleSheafPushforwardOfStacks C S hS
        (structureMap.{u, w} hS)).rightDerivedFunctorPlusSingleIsoOfFunctorialResolution
      (cechComplex.{u, w} hS)
      (classifyingCechAugmentation.{u, w} _ (isSmooth_constantZModTwoGroup hS))
      (fun I _ => quasiIso_classifyingCechAugmentation_app.{u, w} _ _ I)
      (fun I hI p => by
        have := hI
        exact injective_classifyingCechComplex_obj_X.{u, w} _ _ I p)
      (structureModule.{u, w} hS)
      (fun p q hq => isZero_rightDerived_cechDirectImage_uliftUnit.{u, w} hS p q hq) ≪≫
    DerivedCategory.Q.mapIso ((ComplexShape.embeddingUpNat.extendFunctor _).mapIso
      (Stacks.RelativeCech.mapAlternatingCofaceMapComplexIso
        (fppfModuleSheafPushforwardOfStacks C S hS (structureMap.{u, w} hS)) _))

end Derived

end AlgebraicGeometry.Stack.ClassifyingZModTwo

end
