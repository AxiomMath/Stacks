module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAlongASiteMorphism
public import StacksFrontier.CategoryTheory.Sites.Glueing.LowerShriekObjectNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraUnitEssentiallySmall
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The two comparisons `f^*𝒪_D ⟶ 𝒪_C` agree

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor `f.u`
of the underlying sites which is a morphism of sites. Two comparisons of the pullback of the
structure sheaf with the structure sheaf are in play:

* Mathlib's `SheafOfModules.pullbackObjUnitToUnit f.fSharpRing`, for the site-presented pullback
  `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, defined as the transpose of
  `SheafOfModules.unitToPushforwardObjUnit f.fSharpRing` — which is `f^♯` on local sections;
* this library's `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, for the
  four-field pullback of Stacks 03D6, defined by corepresentability.

This file shows that they agree, transported along
`Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso`.

## Main results

* `Stacks.Sheaves.DerivedPullback.pushforwardModulesToposIso_hom_app_val_app`: the comparison of
  the two pushforwards of sheaves of modules is the identity on local sections.
* `Stacks.Sheaves.DerivedPullback.adjunct_pullbackModulesObjUnitIso_inv_val_app_one`: the value
  on the unit section of the transpose of this library's comparison `f^*𝒪_D ⟶ 𝒪_C` is the unit
  section.
* `Stacks.Sheaves.DerivedPullback.unitToPushforwardObjUnit_eq`: **the transposes of the two
  comparisons agree**, as morphisms `𝒪_D ⟶ f_*𝒪_C`.
* `Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso_hom_app_unit_comp_pullbackObjUnitToUnit`:
  **the two comparisons `f^*𝒪_D ⟶ 𝒪_C` agree.**
* `Stacks.Sheaves.DerivedPullback.isIso_pullbackObjUnitToUnit`: **Mathlib's comparison is
  invertible for any morphism of ringed topoi presented by a morphism of the underlying sites**,
  with no finality hypothesis on the presenting functor.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.DerivedPullback

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
open Stacks.Sheaves.GradedAlgebraEssentiallySmall in
/-- The comparison of the two pushforwards of sheaves of modules — the four-field one of
Stacks 03D6 and the one attached to the presentation by a functor of the underlying sites — is
the identity on local sections. -/
theorem pushforwardModulesToposIso_hom_app_val_app
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (W : Y.Cᵒᵖ)
    (s : ((pushforwardModules (modulesHomOfSiteHom f hmos)).obj N).val.obj W) :
    (((RingedSite.Hom.ofRingedToposSiteHom f hmos).pushforwardModulesToposIso).hom.app
      N).val.app W s = s :=
  congrArg (fun k => k.hom.app W s)
    (moduleSheafFunctor_map_pushforwardModulesIso_hom_app
      (RingedSite.Hom.ofRingedToposSiteHom f hmos).ringedToposHom N)

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The transpose along Stacks 03D7 of this library's comparison `f^*𝒪_D ⟶ 𝒪_C` takes the unit
section to the unit section. -/
theorem adjunct_pullbackModulesObjUnitIso_inv_val_app_one (W : Y.Cᵒᵖ) :
    ((pullbackAdjPushforwardModules (modulesHomOfSiteHom f hmos)).homEquiv
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (pullbackModulesObjUnitIso (modulesHomOfSiteHom f hmos)).inv).val.app W
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj W) =
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (f.u.op.obj W)) :=
  pullbackModulesObjUnitIso_inv_adjunct_val_app_one (modulesHomOfSiteHom f hmos) W

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The transposes of the two comparisons `f^*𝒪_D ⟶ 𝒪_C` agree**, as morphisms
`𝒪_D ⟶ f_*𝒪_C`. -/
theorem unitToPushforwardObjUnit_eq :
    SheafOfModules.unitToPushforwardObjUnit.{u} f.fSharpRing =
      (pullbackAdjPushforwardModules (modulesHomOfSiteHom f hmos)).homEquiv
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (pullbackModulesObjUnitIso (modulesHomOfSiteHom f hmos)).inv ≫
        ((RingedSite.Hom.ofRingedToposSiteHom f hmos).pushforwardModulesToposIso).hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := by
  refine ((SheafOfModules.pushforward.{u} f.fSharpRing).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).unitHomEquiv.injective
      (PresheafOfModules.sections_ext _ _ (fun W => ?_))
  have h1 : f.fSharpRing.hom.app W (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj W) =
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (f.u.op.obj W)) := map_one _
  refine Eq.trans (SheafOfModules.unitToPushforwardObjUnit_val_app_apply f.fSharpRing
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj W)) (Eq.trans h1 ?_)
  exact ((pushforwardModulesToposIso_hom_app_val_app f hmos
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) W
        (((pullbackAdjPushforwardModules (modulesHomOfSiteHom f hmos)).homEquiv
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (pullbackModulesObjUnitIso (modulesHomOfSiteHom f hmos)).inv).val.app W
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj W))).trans
    (adjunct_pullbackModulesObjUnitIso_inv_val_app_one f hmos W)).symm

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Mathlib's comparison `f^*𝒪_D ⟶ 𝒪_C` is this library's, read through the identification of
the two pullbacks of sheaves of modules.** -/
theorem pullbackModulesSiteIso_hom_app_unit_comp_pullbackObjUnitToUnit :
    (pullbackModulesSiteIso f hmos).hom.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing =
      (pullbackModulesObjUnitIso (modulesHomOfSiteHom f hmos)).inv := by
  refine (((pullbackAdjPushforwardModules (modulesHomOfSiteHom f hmos)).ofNatIsoRight
        (RingedSite.Hom.ofRingedToposSiteHom f hmos).pushforwardModulesToposIso).homEquiv
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).injective ?_
  refine Eq.trans (Stacks.CategoryTheory.homEquiv_leftAdjointUniq_hom_app_comp _
    f.pullbackPushforwardAdjunctionTopos _ _
    (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing)) ?_
  refine Eq.trans
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u}
      f.fSharpRing) ?_
  refine Eq.trans (unitToPushforwardObjUnit_eq f hmos) ?_
  exact (Adjunction.homEquiv_ofNatIsoRight_apply _ _ _).symm

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
include hmos in
/-- **Mathlib's comparison `f^*𝒪_D ⟶ 𝒪_C` is invertible for any morphism of ringed topoi presented
by a morphism of the underlying sites**, with no finality hypothesis on the presenting functor. -/
theorem isIso_pullbackObjUnitToUnit :
    IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing) := by
  have hcomp : IsIso ((pullbackModulesSiteIso f hmos).hom.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
      SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing) := by
    rw [pullbackModulesSiteIso_hom_app_unit_comp_pullbackObjUnitToUnit f hmos]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((pullbackModulesSiteIso f hmos).hom.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) _

end Stacks.Sheaves.DerivedPullback

end
