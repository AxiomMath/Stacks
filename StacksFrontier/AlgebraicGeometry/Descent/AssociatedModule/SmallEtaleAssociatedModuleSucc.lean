module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianUniverse
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentUniverse
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleTerminalBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSiteLiftedCartesian
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.AffineSiteFinalObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonCartesianCohomology
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# The associated module of a module over an affine scheme, on the small étale site

Let `S` be a scheme with a terminal object `t` of its small étale site whose underlying scheme is
affine, and write `A = Γ(t, 𝒪)`. For an `A`-module `N` the presheaf `T ↦ Γ(T, 𝒪) ⊗_A N`
(`Stacks.TerminalBaseChange.baseChangePresheaf`), sheafified, is a sheaf of modules `Ñ` on
`S_étale` with sections in `Type (u + 1)`, and `N ↦ Ñ` is left adjoint to taking sections over
`t` (`AlgebraicGeometry.SmallEtale.sheafifiedBaseChangeAdjSucc`). This is the étale counterpart of
the associated module of Stacks 01I7.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_sheafifiedBaseChangeAdjSucc_unit_app`: the unit
  `N ⟶ Γ(t, Ñ)` is an isomorphism for every `N`.
* `AlgebraicGeometry.SmallEtale.isIso_sheafifiedBaseChangeAdjSucc_counit_app`: the counit
  `Γ(t, ℱ)^~ ⟶ ℱ` is an isomorphism for every quasi-coherent `ℱ`.
* `Stacks.Sites.bijective_toSheafify_app_of_isSheaf_comp`: sheafification does not change the
  sections over a cocontinuous subsite on which the presheaf is already a sheaf.
* `Stacks.Sites.W_of_bijective_app_of_isDenseSubsite`: a morphism of presheaves bijective over a
  dense subsite is inverted by sheafification.

## References

* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v u' v'

namespace Stacks.Sites

section Dense

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Sheafification does not change the sections over a cocontinuous subsite on which the
presheaf is already a sheaf.** If `G : C ⥤ D` is continuous and cocontinuous and `G^* P` is a
sheaf, the unit `P ⟶ P^#` is bijective on the sections over every `G X`. -/
theorem bijective_toSheafify_app_of_isSheaf_comp [G.IsCocontinuous J K] [G.IsContinuous J K]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}) (hP : Presheaf.IsSheaf J (G.op ⋙ P)) (X : C) :
    Function.Bijective ((CategoryTheory.toSheafify K P).app (op (G.obj X))) := by
  have := (K.W_toSheafify P).isLocallyInjective
  have := (K.W_toSheafify P).isLocallySurjective
  have h₁ : Presheaf.IsLocallyInjective J
      (Functor.whiskerLeft G.op (CategoryTheory.toSheafify K P)) :=
    Presheaf.isLocallyInjective_whisker J K G _
  have h₂ : Presheaf.IsLocallySurjective J
      (Functor.whiskerLeft G.op (CategoryTheory.toSheafify K P)) :=
    Presheaf.isLocallySurjective_whisker J K G _
  let f : (⟨G.op ⋙ P, hP⟩ : Sheaf J AddCommGrpCat.{w}) ⟶
      ⟨G.op ⋙ sheafify K P, G.op_comp_isSheaf J K ((presheafToSheaf K _).obj P)⟩ :=
    ObjectProperty.homMk (Functor.whiskerLeft G.op (CategoryTheory.toSheafify K P))
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).1 ⟨h₁, h₂⟩
  have : IsIso f.hom := (sheafToPresheaf J AddCommGrpCat.{w}).map_isIso f
  exact (ConcreteCategory.isIso_iff_bijective (f.hom.app (op X))).1 inferInstance

omit [HasWeakSheafify K AddCommGrpCat] in
/-- **A morphism of presheaves bijective over a dense subsite is inverted by sheafification.** -/
theorem W_of_bijective_app_of_isDenseSubsite [G.IsDenseSubsite J K]
    {P Q : Dᵒᵖ ⥤ AddCommGrpCat.{w}} (f : P ⟶ Q)
    (hf : ∀ X : C, Function.Bijective (f.app (op (G.obj X)))) : K.W f := by
  have := Functor.IsDenseSubsite.isCoverDense J K G
  have : Presheaf.IsLocallyInjective J (Functor.whiskerLeft G.op f) :=
    Presheaf.isLocallyInjective_of_injective _ _ fun X => (hf X.unop).1
  have : Presheaf.IsLocallySurjective J (Functor.whiskerLeft G.op f) :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun X => (hf X.unop).2
  exact (K.W_iff_isLocallyBijective f).2
    ⟨Presheaf.isLocallyInjective_of_whisker J K G (f := f)
        (Functor.IsDenseSubsite.coverPreserving J K G),
      Presheaf.isLocallySurjective_of_whisker J K G (f := f)
        (Functor.IsDenseSubsite.coverPreserving J K G)⟩

end Dense

end Stacks.Sites

namespace ModuleCat

/-- Extension of scalars along a ring endomorphism equal to the identity reflects isomorphisms. -/
theorem isIso_of_isIso_extendScalars_map_of_eq_id {R : Type u} [CommRing R] (g : R →+* R)
    (hg : g = RingHom.id R) {N N' : ModuleCat.{max u w} R} (f : N ⟶ N')
    (h : IsIso ((ModuleCat.extendScalars.{u, u, max u w} g).map f)) : IsIso f := by
  subst hg
  exact (NatIso.isIso_map_iff (ModuleCat.extendScalarsId R) f).1 h

end ModuleCat

namespace Stacks.TerminalBaseChange

/-- **The base-change presheaf along a terminal object is cartesian.** -/
theorem isCartesianPresheaf_baseChangePresheaf {C : Type u'} [Category.{v'} C]
    (O : Cᵒᵖ ⥤ RingCat.{u}) [CommSections O] {X : C} (hX : IsTerminal X)
    (N : ModuleCat.{max w u} (O.obj (op X))) :
    Stacks.ModulesOnACategory.ChaoticComparison.IsCartesianPresheaf
      ((baseChangePresheaf.{w} O hX).obj N) :=
  (Stacks.ModulesOnACategory.ChaoticComparison.isCartesianPresheaf_iff_isIso_restrictionBaseChange
    (R := commPresheaf O) _).2 fun _ _ f =>
      Stacks.AffineSiteBaseChange.isIso_restrictionBaseChange_baseChangePresheaf O hX N f

end Stacks.TerminalBaseChange

namespace AlgebraicGeometry.SmallEtale

open Stacks.TerminalBaseChange Stacks.ModulesOnACategory.ChaoticComparison

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Sheafification of presheaves of abelian groups in `Type (u + 1)` exists on the small étale site
of `S`. -/
local instance : HasSheafify (topology B S hS) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- On the small étale site of `S`, a morphism of presheaves of abelian groups in `Type (u + 1)`
is inverted by sheafification exactly when it is locally bijective. -/
local instance : (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _

variable {B S hS} {t : SmallEtale B S hS} (ht : IsTerminal t)

/-- **The associated sheaf of modules of a module over the sections at a terminal object**, with
sections in `Type (u + 1)`: the presheaf `T ↦ Γ(T, 𝒪) ⊗_{Γ(t, 𝒪)} N`, sheafified. -/
noncomputable def sheafifiedBaseChangeSucc :
    ModuleCat.{u + 1} ((structureSheaf B S hS).obj.obj (op t)) ⥤
      SheafOfModules.{u + 1} (structureSheaf B S hS) :=
  baseChangePresheaf.{u + 1} (structureSheaf B S hS).obj ht ⋙
    PresheafOfModules.sheafification.{u + 1} (𝟙 (structureSheaf B S hS).obj)

/-- Taking sections over `t`, written as the right adjoint of the composite adjunction. -/
noncomputable abbrev sectionsSucc :
    SheafOfModules.{u + 1} (structureSheaf B S hS) ⥤
      ModuleCat.{u + 1} ((structureSheaf B S hS).obj.obj (op t)) :=
  (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)) ⋙
    PresheafOfModules.evaluation.{u + 1} (structureSheaf B S hS).obj (op t)

/-- **The associated sheaf of modules is left adjoint to the sections over `t`.** -/
noncomputable def sheafifiedBaseChangeAdjSucc :
    sheafifiedBaseChangeSucc ht ⊣ sectionsSucc (t := t) :=
  (baseChangeAdj.{u + 1} (structureSheaf B S hS).obj ht).comp
    (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 (structureSheaf B S hS).obj))

/-- The unit of the base-change adjunction of presheaves is an isomorphism. -/
theorem isIso_baseChangeAdj_unit_app
    (N : ModuleCat.{u + 1} ((structureSheaf B S hS).obj.obj (op t))) :
    IsIso ((baseChangeAdj.{u + 1} (structureSheaf B S hS).obj ht).unit.app N) := by
  let adj := baseChangeAdj.{u + 1} (structureSheaf B S hS).obj ht
  have hc : IsIso (adj.counit.app ((baseChangePresheaf.{u + 1} _ ht).obj N)) :=
    isIso_baseChangeAdj_counit_app.{u + 1} _ ht _
      (Stacks.TerminalBaseChange.isCartesianPresheaf_baseChangePresheaf _ ht N)
  have h₁ : IsIso ((baseChangePresheaf.{u + 1} _ ht).map (adj.unit.app N) ≫
      adj.counit.app ((baseChangePresheaf.{u + 1} _ ht).obj N)) := by
    rw [adj.left_triangle_components N]
    infer_instance
  have hF : IsIso ((baseChangePresheaf.{u + 1} _ ht).map (adj.unit.app N)) :=
    IsIso.of_isIso_comp_right _ (adj.counit.app ((baseChangePresheaf.{u + 1} _ ht).obj N))
  exact ModuleCat.isIso_of_isIso_extendScalars_map_of_eq_id.{u + 1, u} (rho _ ht (op t))
    (rho_self (structureSheaf B S hS).obj ht) (adj.unit.app N)
    ((PresheafOfModules.evaluation (structureSheaf B S hS).obj (op t)).map_isIso
      ((baseChangePresheaf.{u + 1} _ ht).map (adj.unit.app N)))

/-- **The base-change presheaf is a sheaf on the affine objects**: its restriction to the small
affine étale site is a sheaf (Stacks 023M). -/
theorem isSheaf_baseChangePresheaf_affine
    (N : ModuleCat.{u + 1} ((structureSheaf B S hS).obj.obj (op t))) :
    Presheaf.IsSheaf (SmallAffineEtale.topology B S hS)
      ((SmallAffineEtale.inclusion B S hS).op ⋙
        ((baseChangePresheaf.{u + 1} (structureSheaf B S hS).obj ht).obj N).presheaf) := by
  let P' : PresheafOfModules.{u + 1} (Stacks.AffineSiteBaseChange.rings
      (SmallAffineEtale.toScheme B S hS) ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pushforward₀ (SmallAffineEtale.inclusion B S hS)
      (structureSheaf B S hS).obj).obj
        ((baseChangePresheaf.{u + 1} (structureSheaf B S hS).obj ht).obj N)
  have hc : IsCartesianPresheaf P' := fun _ _ a =>
    Stacks.TerminalBaseChange.isCartesianPresheaf_baseChangePresheaf _ ht N
      ((SmallAffineEtale.inclusion B S hS).op.map a)
  exact Stacks.AffineSiteBaseChange.isSheaf_of_isCartesianPresheaf.{u + 1}
    (SmallAffineEtale.isFlatCofinal B S hS) P' hc

/-- **The unit `N ⟶ Γ(t, Ñ)` is an isomorphism** when the scheme underlying `t` is affine. -/
theorem isIso_sheafifiedBaseChangeAdjSucc_unit_app
    (htA : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj t))
    (N : ModuleCat.{u + 1} ((structureSheaf B S hS).obj.obj (op t))) :
    IsIso ((sheafifiedBaseChangeAdjSucc ht).unit.app N) := by
  have hb := Stacks.Sites.bijective_toSheafify_app_of_isSheaf_comp
    (SmallAffineEtale.topology B S hS) (topology B S hS) (SmallAffineEtale.inclusion B S hS)
    ((baseChangePresheaf.{u + 1} (structureSheaf B S hS).obj ht).obj N).presheaf
    (isSheaf_baseChangePresheaf_affine ht N) ⟨t, htA⟩
  have h₂ : IsIso ((PresheafOfModules.evaluation (structureSheaf B S hS).obj (op t)).map
      ((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (𝟙 (structureSheaf B S hS).obj)).unit.app
          ((baseChangePresheaf.{u + 1} (structureSheaf B S hS).obj ht).obj N))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  rw [sheafifiedBaseChangeAdjSucc, Adjunction.comp_unit_app]
  exact IsIso.comp_isIso' (isIso_baseChangeAdj_unit_app ht N) h₂

/-- **The counit `Γ(t, ℱ)^~ ⟶ ℱ` is an isomorphism for a quasi-coherent `ℱ`** when the scheme
underlying `t` is affine. This uses that `ℱ` is cartesian between affine objects (Stacks 03DX). -/
theorem isIso_sheafifiedBaseChangeAdjSucc_counit_app
    (htA : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj t))
    (M : SheafOfModules.{u + 1} (structureSheaf B S hS)) (hM : M.IsQuasicoherentOnSite) :
    IsIso ((sheafifiedBaseChangeAdjSucc ht).counit.app M) := by
  have hds : (SmallAffineEtale.inclusion B S hS).IsDenseSubsite
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2
  let adj := baseChangeAdj.{u + 1} (structureSheaf B S hS).obj ht
  let κ := adj.counit.app
    ((SheafOfModules.forget.{u + 1} _ ⋙ PresheafOfModules.restrictScalars.{u + 1} (𝟙 _)).obj M)
  have hκ : ∀ V : SmallAffineEtale B S hS,
      Function.Bijective (((PresheafOfModules.toPresheaf _).map κ).app
        (op ((SmallAffineEtale.inclusion B S hS).obj V))) := fun V => by
    have e : baseChangeCounitApp.{u + 1, u, u, u + 1} (structureSheaf B S hS).obj ht M.val
        (op V.obj) =
        ((ModuleCat.extendRestrictScalarsAdj.{u + 1} (rho _ ht (op V.obj))).homEquiv _ _).symm
          (M.val.map (iota ht (op V.obj))) := by
      rw [← homEquiv_baseChangeCounitApp.{u + 1, u, u, u + 1}, Equiv.symm_apply_apply]
    have h' : IsIso (κ.app (op V.obj)) := by
      change IsIso (baseChangeCounitApp.{u + 1, u, u, u + 1} (structureSheaf B S hS).obj ht M.val
        (op V.obj))
      rw [e]
      exact isIso_restrictionBaseChange_of_isQuasicoherentOnSite_succ B S hS hM
        (ht.from V.obj) V.2 htA
    exact (ConcreteCategory.isIso_iff_bijective (κ.app (op V.obj))).1 h'
  have h₁ : IsIso ((presheafToSheaf (topology B S hS) AddCommGrpCat.{u + 1}).map
      ((PresheafOfModules.toPresheaf _).map κ)) :=
    ((topology B S hS).W_iff _).1 <| Stacks.Sites.W_of_bijective_app_of_isDenseSubsite
      (SmallAffineEtale.topology B S hS) (topology B S hS) (SmallAffineEtale.inclusion B S hS)
      ((PresheafOfModules.toPresheaf _).map κ) hκ
  have h₂ : IsIso ((SheafOfModules.toSheaf.{u + 1} _).map
      ((PresheafOfModules.sheafification.{u + 1} (𝟙 (structureSheaf B S hS).obj)).map κ)) :=
    (NatIso.isIso_map_iff (PresheafOfModules.sheafificationCompToSheaf.{u + 1}
      (𝟙 (structureSheaf B S hS).obj)) κ).2 h₁
  have h₃ : IsIso ((PresheafOfModules.sheafification.{u + 1}
      (𝟙 (structureSheaf B S hS).obj)).map κ) :=
    isIso_of_reflects_iso _ (SheafOfModules.toSheaf.{u + 1} (structureSheaf B S hS))
  rw [sheafifiedBaseChangeAdjSucc, Adjunction.comp_counit_app]
  have h₄' : IsIso ((SheafOfModules.toSheaf.{u + 1} (structureSheaf B S hS)).map
      ((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (𝟙 (structureSheaf B S hS).obj)).counit.app M)) := by
    rw [PresheafOfModules.toSheaf_map_sheafificationAdjunction_counit_app]
    exact inferInstanceAs (IsIso ((CategoryTheory.sheafificationAdjunction (topology B S hS)
      AddCommGrpCat.{u + 1}).counit.app _))
  have h₄ : IsIso ((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 (structureSheaf B S hS).obj)).counit.app M) :=
    isIso_of_reflects_iso _ (SheafOfModules.toSheaf.{u + 1} (structureSheaf B S hS))
  exact IsIso.comp_isIso' h₃ h₄

end AlgebraicGeometry.SmallEtale

end
