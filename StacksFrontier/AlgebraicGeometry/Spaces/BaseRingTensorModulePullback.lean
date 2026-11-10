module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularAlterationImpliedProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# `𝒪_T ⊗_R -` commutes with pullback along `X ⟶ T`

Let `T` be an object of the big fppf site, read as an algebraic space, with ring of global
functions `R = Γ(T, 𝒪_T)`, and let `f : X ⟶ T` be a morphism of algebraic spaces.  For an
`R`-module `M` this file constructs the identification

`f^*(𝒪_T ⊗_R M) ≅ 𝒪_X ⊗_R M`,

natural in `M`, where `𝒪_X ⊗_R -` is `AlgebraicGeometry.Space.baseRingTensorModule` for the
base-ring datum `AlgebraicGeometry.Space.baseRingHomOfMap f` of `f`.

## Main definitions

* `AlgebraicGeometry.Space.modelSectionsHomEquiv`: global sections of an `𝒪_X`-module read on
  the model of the small étale site are the morphisms out of `𝒪_X`.
* `AlgebraicGeometry.Space.pushforwardGlobalSectionsIso`: `Γ(T, f_*F) ≅ Γ(X, F)` as
  `R`-modules, naturally in `F`.
* `AlgebraicGeometry.Space.baseRingTensorModulePullbackIso`: **`f^*(𝒪_T ⊗_R M) ≅ 𝒪_X ⊗_R M`**.

## Main results

* `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_comp_map_unitModuleMul`: the identification
  `f^*𝒪_T ≅ 𝒪_X` is linear over pulling back global functions along `f`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

/-- A morphism out of the free module of rank one is determined by its value on `1`. -/
private theorem unit_hom_val_app_eq_smul {C : Type*} [Category C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] {R : Sheaf J RingCat.{u}}
    {M : SheafOfModules.{u} R} (v : SheafOfModules.unit R ⟶ M) (W : Cᵒᵖ) (c : R.obj.obj W) :
    v.val.app W c = c • v.val.app W (1 : R.obj.obj W) := by
  have h : v.val.app W (c • (1 : R.obj.obj W)) = c • v.val.app W (1 : R.obj.obj W) :=
    map_smul _ _ _
  rwa [smul_eq_mul, mul_one] at h

namespace Stacks.Cohomology.SiteModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] {R : Sheaf J RingCat.{u}}

/-- A global section of a sheaf of rings, as a global section of the free module of rank one. -/
def unitSection (a : RingCat.sectionsSubring R.obj) : (SheafOfModules.unit R).sections :=
  ⟨a.1, a.2⟩

/-- **Multiplication by a global section, as a morphism out of the free module of rank one.**
The morphism `𝒪 ⟶ M` attached to `a • s` is multiplication by `a` on `𝒪` followed by the morphism
attached to `s`. -/
theorem unitHomEquiv_symm_smul (M : SheafOfModules.{u} R) (a : RingCat.sectionsSubring R.obj)
    (s : M.sections) :
    (SheafOfModules.unitHomEquiv M).symm (a • s) =
      (SheafOfModules.unitHomEquiv _).symm (unitSection a) ≫
        (SheafOfModules.unitHomEquiv M).symm s := by
  refine (SheafOfModules.unitHomEquiv M).injective ?_
  rw [Equiv.apply_symm_apply, SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
  refine Subtype.ext (funext fun W => ?_)
  change a.1 W • s.eval W = ((SheafOfModules.unitHomEquiv M).symm s).val.app W (a.1 W)
  rw [unit_hom_val_app_eq_smul, CategoryTheory.Sheaf.unitHomEquiv_symm_val_app_one]

end Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Model

variable (X : AlgebraicSpaces B S hS) {R : Type u} [CommRing R]
  (φ : R →+* modelGlobalFunctions B S hS X)

/-- **Global sections read on the model are the morphisms out of `𝒪_X`.** -/
def modelSectionsHomEquiv (F : Modules.{u, u} B S hS X.1 X.2) :
    (baseRingGlobalSectionsModule B S hS X φ).obj F ≃ (unitModule B S hS X.2 ⟶ F) where
  toFun s := (smallEtaleModelModulesEquiv B S hS X).fullyFaithfulFunctor.preimage
    ((SheafOfModules.unitHomEquiv ((smallEtaleModelModulesEquiv B S hS X).functor.obj F)).symm s)
  invFun v := SheafOfModules.unitHomEquiv ((smallEtaleModelModulesEquiv B S hS X).functor.obj F)
    ((smallEtaleModelModulesEquiv B S hS X).functor.map v)
  left_inv _ :=
    (congrArg (SheafOfModules.unitHomEquiv _)
      ((smallEtaleModelModulesEquiv B S hS X).fullyFaithfulFunctor.map_preimage _)).trans
      (Equiv.apply_symm_apply _ _)
  right_inv v :=
    (congrArg (smallEtaleModelModulesEquiv B S hS X).fullyFaithfulFunctor.preimage
      (Equiv.symm_apply_apply _ _)).trans
      ((smallEtaleModelModulesEquiv B S hS X).fullyFaithfulFunctor.preimage_map v)

/-- A morphism out of `𝒪_X` is multiplication of its value on the unit section. -/
theorem unitModule_hom_val_app {F : Modules.{u, u} B S hS X.1 X.2} (v : unitModule B S hS X.2 ⟶ F)
    (W : SmallEtale B S hS X.1) (c : chartRing B S hS X.1 X.2 W) :
    v.val.app (op W) c = c • v.val.app (op W) (1 : chartRing B S hS X.1 X.2 W) :=
  unit_hom_val_app_eq_smul v (op W) c

/-- The inverse of `AlgebraicGeometry.Space.modelSectionsHomEquiv` is additive. -/
theorem modelSectionsHomEquiv_symm_add (F : Modules.{u, u} B S hS X.1 X.2)
    (v w : unitModule B S hS X.2 ⟶ F) :
    (modelSectionsHomEquiv B S hS X φ F).symm (v + w) =
      (modelSectionsHomEquiv B S hS X φ F).symm v + (modelSectionsHomEquiv B S hS X φ F).symm w :=
  Subtype.ext (funext fun _ => rfl)

/-- `AlgebraicGeometry.Space.modelSectionsHomEquiv` is additive. -/
theorem modelSectionsHomEquiv_add (F : Modules.{u, u} B S hS X.1 X.2)
    (s t : (baseRingGlobalSectionsModule B S hS X φ).obj F) :
    modelSectionsHomEquiv B S hS X φ F (s + t) =
      modelSectionsHomEquiv B S hS X φ F s + modelSectionsHomEquiv B S hS X φ F t := by
  refine (modelSectionsHomEquiv B S hS X φ F).symm.injective ?_
  rw [modelSectionsHomEquiv_symm_add, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

/-- Multiplication by a global function, as an endomorphism of `𝒪_X`. -/
def unitModuleMul (a : GlobalFunctionRing (structureSheaf B S hS X.1 X.2)) :
    unitModule B S hS X.2 ⟶ unitModule B S hS X.2 :=
  (SheafOfModules.unitHomEquiv _).symm (unitSection a)

/-- Multiplication by `a` sends the unit function to `a`. -/
theorem unitModuleMul_val_app_one (a : GlobalFunctionRing (structureSheaf B S hS X.1 X.2))
    (W : SmallEtale B S hS X.1) :
    (unitModuleMul B S hS X a).val.app (op W) (1 : chartRing B S hS X.1 X.2 W) = a.1 (op W) :=
  CategoryTheory.Sheaf.unitHomEquiv_symm_val_app_one _ (unitSection a) (op W)

/-- The inverse of `AlgebraicGeometry.Space.modelSectionsHomEquiv` is restriction to the model
followed by `SheafOfModules.unitHomEquiv`. -/
theorem modelSectionsHomEquiv_symm_apply (F : Modules.{u, u} B S hS X.1 X.2)
    (v : unitModule B S hS X.2 ⟶ F) :
    (modelSectionsHomEquiv B S hS X φ F).symm v =
      SheafOfModules.unitHomEquiv ((smallEtaleModelModulesEquiv B S hS X).functor.obj F)
        ((smallEtaleModelModulesEquiv B S hS X).functor.map v) :=
  rfl

/-- The value over an object of the model of the global section attached to `v : 𝒪_X ⟶ F` is the
value of `v` on the unit function there. -/
theorem modelSectionsHomEquiv_symm_val (F : Modules.{u, u} B S hS X.1 X.2)
    (v : unitModule B S hS X.2 ⟶ F) (V : (SmallModel.{u} (SmallEtale B S hS X.1))ᵒᵖ) :
    ((modelSectionsHomEquiv B S hS X φ F).symm v).val V =
      v.val.app (op ((smallEtaleModelEquiv B S hS X).inverse.obj V.unop))
        (1 : chartRing B S hS X.1 X.2 ((smallEtaleModelEquiv B S hS X).inverse.obj V.unop)) :=
  rfl

/-- Restricted to the model, multiplication by a global function of `X` is multiplication by its
restriction. -/
theorem functor_map_unitModuleMul (a : GlobalFunctionRing (structureSheaf B S hS X.1 X.2)) :
    (smallEtaleModelModulesEquiv B S hS X).functor.map (unitModuleMul B S hS X a) =
      (SheafOfModules.unitHomEquiv
        (SheafOfModules.unit
          (ringSheafOfSite.{u, u, u} (smallEtaleModelStructureSheaf B S hS X)))).symm
        (unitSection (modelGlobalFunctionsHom B S hS X a)) :=
  (SheafOfModules.unitHomEquiv _).injective (Subtype.ext (funext fun V =>
    (unitModuleMul_val_app_one B S hS X a _).trans
      (CategoryTheory.Sheaf.unitHomEquiv_symm_val_app_one _
        (unitSection (modelGlobalFunctionsHom B S hS X a)) V).symm))

/-- **The inverse of `AlgebraicGeometry.Space.modelSectionsHomEquiv` is `Γ(T, 𝒪_T)`-linear** for
the base-ring datum of `f : X ⟶ T`: precomposing with multiplication by the pullback of `r` is
multiplication by `r`. -/
theorem modelSectionsHomEquiv_symm_comp {T : BigFppfOver B S hS} (f : X ⟶ schemeSpace T)
    (F : Modules.{u, u} B S hS X.1 X.2) (r : baseRing B S hS T) (v : unitModule B S hS X.2 ⟶ F) :
    (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) F).symm
        (unitModuleMul B S hS X (globalFunctionsOfMap f r) ≫ v) =
      r • (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) F).symm v := by
  refine Eq.trans ?_ (ModuleCat.restrictScalars.smul_def (baseRingHomOfMap f)
    (M := (globalSectionsFunctor (ringSheafOfSite.{u, u, u}
      (smallEtaleModelStructureSheaf B S hS X))).obj
        ((smallEtaleModelModulesEquiv B S hS X).functor.obj F)) r _).symm
  refine (SheafOfModules.unitHomEquiv
    ((smallEtaleModelModulesEquiv B S hS X).functor.obj F)).symm.injective ?_
  refine Eq.trans ?_ (unitHomEquiv_symm_smul
    (R := ringSheafOfSite.{u, u, u} (smallEtaleModelStructureSheaf B S hS X))
    ((smallEtaleModelModulesEquiv B S hS X).functor.obj F) _ _).symm
  have h1 := (Equiv.symm_apply_apply (SheafOfModules.unitHomEquiv
      ((smallEtaleModelModulesEquiv B S hS X).functor.obj F))
      ((smallEtaleModelModulesEquiv B S hS X).functor.map
        (unitModuleMul B S hS X (globalFunctionsOfMap f r) ≫ v))).trans
    ((smallEtaleModelModulesEquiv B S hS X).functor.map_comp _ _)
  have h2 := Equiv.symm_apply_apply (SheafOfModules.unitHomEquiv
      ((smallEtaleModelModulesEquiv B S hS X).functor.obj F))
      ((smallEtaleModelModulesEquiv B S hS X).functor.map v)
  exact h1.trans (congrArg₂ (· ≫ ·)
    (functor_map_unitModuleMul B S hS X (globalFunctionsOfMap f r)) h2.symm)

/-- `AlgebraicGeometry.Space.modelSectionsHomEquiv` carries multiplication by `r` to precomposition
with multiplication by the pullback of `r`. -/
theorem modelSectionsHomEquiv_smul {T : BigFppfOver B S hS} (f : X ⟶ schemeSpace T)
    (F : Modules.{u, u} B S hS X.1 X.2) (r : baseRing B S hS T)
    (s : (baseRingGlobalSectionsModule B S hS X (baseRingHomOfMap f)).obj F) :
    modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) F (r • s) =
      unitModuleMul B S hS X (globalFunctionsOfMap f r) ≫
        modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) F s := by
  refine (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) F).symm.injective ?_
  rw [modelSectionsHomEquiv_symm_comp B S hS X f F r, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

/-- The inverse of `AlgebraicGeometry.Space.modelSectionsHomEquiv` is natural in the module. -/
theorem modelSectionsHomEquiv_symm_naturality {F G : Modules.{u, u} B S hS X.1 X.2} (g : F ⟶ G)
    (v : unitModule B S hS X.2 ⟶ F) :
    (modelSectionsHomEquiv B S hS X φ G).symm (v ≫ g) =
      (baseRingGlobalSectionsModule B S hS X φ).map g
        ((modelSectionsHomEquiv B S hS X φ F).symm v) :=
  Subtype.ext (funext fun _ => rfl)

/-- `AlgebraicGeometry.Space.modelSectionsHomEquiv` is natural in the module. -/
theorem modelSectionsHomEquiv_naturality {F G : Modules.{u, u} B S hS X.1 X.2} (g : F ⟶ G)
    (s : (baseRingGlobalSectionsModule B S hS X φ).obj F) :
    modelSectionsHomEquiv B S hS X φ G ((baseRingGlobalSectionsModule B S hS X φ).map g s) =
      modelSectionsHomEquiv B S hS X φ F s ≫ g := by
  refine (modelSectionsHomEquiv B S hS X φ G).symm.injective ?_
  rw [Equiv.symm_apply_apply, modelSectionsHomEquiv_symm_naturality, Equiv.symm_apply_apply]

end Model

section Pullback

variable {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS} (f : X ⟶ schemeSpace T)

/-- The commutative square of étale charts given by an étale chart `U` of `X` above the identity
chart of `T`, joined by the morphism `U ⟶ T` that `f` induces. -/
def chartDiagramToBase (U : SmallEtale B S hS X.1) :
    ChartDiagram B S hS X.1 (schemeSpace T).1 f.hom where
  U := U
  V := selfChart B S hS T
  g := chartToBaseOfMap f U
  comm := (yoneda_map_chartToBaseOfMap f U).symm.trans (Category.comp_id _).symm

/-- The identity of `T` induces the identity on the identity chart of `T`. -/
theorem chartToBase_id_selfChart :
    chartToBaseOfMap (𝟙 (schemeSpace T)) (selfChart B S hS T) = 𝟙 T :=
  yoneda.map_injective ((yoneda_map_chartToBaseOfMap _ _).trans
    ((Category.id_comp _).trans (yoneda.map_id T).symm))

/-- Pulling back the global function `r` of `T` along the chart square of `U` gives its pullback
along `f`. -/
theorem chartDiagramRestrict_globalFunctionsOfMap_id (U : SmallEtale B S hS X.1)
    (r : baseRing B S hS T) :
    chartDiagramRestrict B S hS f (chartDiagramToBase B S hS f U)
        (show chartRing B S hS (schemeSpace T).1 (schemeSpace T).2 (selfChart B S hS T) from
          (globalFunctionsOfMap (𝟙 (schemeSpace T)) r).1 (op (selfChart B S hS T))) =
      (show chartRing B S hS X.1 X.2 U from (globalFunctionsOfMap f r).1 (op U)) := by
  have h := chartToBase_id_selfChart B S hS (T := T)
  dsimp only [chartDiagramRestrict, chartDiagramPullback, globalFunctionsOfMap, chartDiagramToBase,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  have h2 : ∀ x, (CommRingCat.Hom.hom (Scheme.Γ.map
      ((BigFppfOver.toScheme B S hS).map (𝟙 T)).op)) x = x := fun x => by
    simp only [op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]
  rw [h]
  exact congrArg (RingCat.Hom.hom ((forget₂ CommRingCat RingCat).map
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToBaseOfMap f U)).op))) (h2 r)

/-- **The identification `f^*𝒪_T ≅ 𝒪_X` is linear over pulling back global functions.** -/
theorem modulePullbackUnitIso_inv_comp_map_unitModuleMul (r : baseRing B S hS T) :
    (modulePullbackUnitIso B S hS f).inv ≫ (modulePullback B S hS f).map
        (unitModuleMul B S hS (schemeSpace T) (globalFunctionsOfMap (𝟙 (schemeSpace T)) r)) =
      unitModuleMul B S hS X (globalFunctionsOfMap f r) ≫ (modulePullbackUnitIso B S hS f).inv := by
  refine (SheafOfModules.unitHomEquiv _).injective (Subtype.ext (funext fun W => ?_))
  obtain ⟨U⟩ := W
  let d := chartDiagramToBase B S hS f U
  let a := globalFunctionsOfMap (𝟙 (schemeSpace T)) r
  have hL : ((modulePullbackUnitIso B S hS f).inv ≫ (modulePullback B S hS f).map
      (unitModuleMul B S hS (schemeSpace T) a)).val.app (op d.U) (1 : chartRing B S hS X.1 X.2 U) =
      chartDiagramRestrict B S hS f d (show chartRing B S hS (schemeSpace T).1 (schemeSpace T).2 d.V
        from a.1 (op d.V)) •
        (modulePullbackUnitIso B S hS f).inv.val.app (op d.U) (1 : chartRing B S hS X.1 X.2 U) := by
    refine (comp_val_app_apply B S hS _ _ (op d.U) _).trans ?_
    refine (congrArg (fun z => ((modulePullback B S hS f).map
      (unitModuleMul B S hS (schemeSpace T) a)).val.app (op d.U) z)
      (modulePullbackUnitIso_inv_val_app_one B S hS f d)).trans ?_
    refine (modulePullbackChartSection_map B S hS f _ _ d _).trans ?_
    refine (congrArg (modulePullbackChartSection B S hS f _ d)
      (unitModuleMul_val_app_one B S hS (schemeSpace T) a d.V)).trans ?_
    exact modulePullbackChartSection_unit B S hS f d _
  have hR : (unitModuleMul B S hS X (globalFunctionsOfMap f r) ≫
      (modulePullbackUnitIso B S hS f).inv).val.app (op U) (1 : chartRing B S hS X.1 X.2 U) =
      (show chartRing B S hS X.1 X.2 U from (globalFunctionsOfMap f r).1 (op U)) •
        (modulePullbackUnitIso B S hS f).inv.val.app (op U) (1 : chartRing B S hS X.1 X.2 U) := by
    refine (comp_val_app_apply B S hS _ _ (op U) _).trans ?_
    refine (congrArg (fun z => (modulePullbackUnitIso B S hS f).inv.val.app (op U) z)
      (unitModuleMul_val_app_one B S hS X (globalFunctionsOfMap f r) U)).trans ?_
    exact unitModule_hom_val_app B S hS X (modulePullbackUnitIso B S hS f).inv U _
  exact hL.trans ((congrArg (· • _)
    (chartDiagramRestrict_globalFunctionsOfMap_id B S hS f U r)).trans hR.symm)

/-- Global sections of the direct image `f_*F`, read on the model of `T` as a
`Γ(T, 𝒪_T)`-module, are the morphisms `𝒪_X ⟶ F`. -/
def pushforwardSectionsHomEquiv (F : Modules.{u, u} B S hS X.1 X.2) :
    (baseRingGlobalSectionsModule B S hS (schemeSpace T)
        (baseRingHomOfMap (𝟙 (schemeSpace T)))).obj ((modulePushforward B S hS f).obj F) ≃
      (unitModule B S hS X.2 ⟶ F) :=
  (modelSectionsHomEquiv B S hS (schemeSpace T) _ _).trans
    (((modulePullbackAdjunction B S hS f).homEquiv _ _).symm.trans
      ((modulePullbackUnitIso B S hS f).homCongr (Iso.refl F)))

/-- `AlgebraicGeometry.Space.pushforwardSectionsHomEquiv`, unfolded. -/
theorem pushforwardSectionsHomEquiv_apply (F : Modules.{u, u} B S hS X.1 X.2)
    (s : (baseRingGlobalSectionsModule B S hS (schemeSpace T)
        (baseRingHomOfMap (𝟙 (schemeSpace T)))).obj ((modulePushforward B S hS f).obj F)) :
    pushforwardSectionsHomEquiv B S hS f F s =
      (modulePullbackUnitIso B S hS f).inv ≫ ((modulePullbackAdjunction B S hS f).homEquiv _ _).symm
        (modelSectionsHomEquiv B S hS (schemeSpace T) _ _ s) := by
  simp only [pushforwardSectionsHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id]

/-- `AlgebraicGeometry.Space.pushforwardSectionsHomEquiv` is additive. -/
theorem pushforwardSectionsHomEquiv_add (F : Modules.{u, u} B S hS X.1 X.2)
    (s t : (baseRingGlobalSectionsModule B S hS (schemeSpace T)
        (baseRingHomOfMap (𝟙 (schemeSpace T)))).obj ((modulePushforward B S hS f).obj F)) :
    pushforwardSectionsHomEquiv B S hS f F (s + t) =
      pushforwardSectionsHomEquiv B S hS f F s + pushforwardSectionsHomEquiv B S hS f F t := by
  have := (modulePullbackAdjunction B S hS f).left_adjoint_additive
  rw [pushforwardSectionsHomEquiv_apply, pushforwardSectionsHomEquiv_apply,
    pushforwardSectionsHomEquiv_apply, modelSectionsHomEquiv_add,
    Adjunction.homAddEquiv_symm_add, Preadditive.comp_add]

/-- `AlgebraicGeometry.Space.pushforwardSectionsHomEquiv` carries multiplication by `r` to
precomposition with multiplication by the pullback of `r` to `X`. -/
theorem pushforwardSectionsHomEquiv_smul (F : Modules.{u, u} B S hS X.1 X.2)
    (r : baseRing B S hS T)
    (s : (baseRingGlobalSectionsModule B S hS (schemeSpace T)
        (baseRingHomOfMap (𝟙 (schemeSpace T)))).obj ((modulePushforward B S hS f).obj F)) :
    pushforwardSectionsHomEquiv B S hS f F (r • s) =
      unitModuleMul B S hS X (globalFunctionsOfMap f r) ≫
        pushforwardSectionsHomEquiv B S hS f F s := by
  have hT := modelSectionsHomEquiv_smul B S hS (schemeSpace T) (𝟙 _)
    ((modulePushforward B S hS f).obj F) r s
  refine (pushforwardSectionsHomEquiv_apply B S hS f F (r • s)).trans ?_
  refine (congrArg (fun v => (modulePullbackUnitIso B S hS f).inv ≫
    ((modulePullbackAdjunction B S hS f).homEquiv _ _).symm v) hT).trans ?_
  refine (congrArg (fun v => (modulePullbackUnitIso B S hS f).inv ≫ v)
    ((modulePullbackAdjunction B S hS f).homEquiv_naturality_left_symm _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (modulePullbackUnitIso_inv_comp_map_unitModuleMul B S hS f r)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) (pushforwardSectionsHomEquiv_apply B S hS f F s).symm

/-- `AlgebraicGeometry.Space.pushforwardSectionsHomEquiv` is natural in the module. -/
theorem pushforwardSectionsHomEquiv_naturality {F G : Modules.{u, u} B S hS X.1 X.2} (g : F ⟶ G)
    (s : (baseRingGlobalSectionsModule B S hS (schemeSpace T)
        (baseRingHomOfMap (𝟙 (schemeSpace T)))).obj ((modulePushforward B S hS f).obj F)) :
    pushforwardSectionsHomEquiv B S hS f G
        ((baseRingGlobalSectionsModule B S hS (schemeSpace T)
          (baseRingHomOfMap (𝟙 (schemeSpace T)))).map ((modulePushforward B S hS f).map g) s) =
      pushforwardSectionsHomEquiv B S hS f F s ≫ g := by
  rw [pushforwardSectionsHomEquiv_apply, pushforwardSectionsHomEquiv_apply,
    modelSectionsHomEquiv_naturality, Adjunction.homEquiv_naturality_right_symm, Category.assoc]

/-- Global sections of `f_*F` over `T` are global sections of `F` over `X`, as
`Γ(T, 𝒪_T)`-modules. -/
def pushforwardSectionsLinearEquiv (F : Modules.{u, u} B S hS X.1 X.2) :
    (baseRingGlobalSectionsModule B S hS (schemeSpace T)
        (baseRingHomOfMap (𝟙 (schemeSpace T)))).obj ((modulePushforward B S hS f).obj F)
      ≃ₗ[baseRing B S hS T] (baseRingGlobalSectionsModule B S hS X (baseRingHomOfMap f)).obj F where
  toEquiv := (pushforwardSectionsHomEquiv B S hS f F).trans
    (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) F).symm
  map_add' s t := by
    simp only [Equiv.toFun_as_coe, Equiv.trans_apply, pushforwardSectionsHomEquiv_add,
      modelSectionsHomEquiv_symm_add]
  map_smul' r s := by
    simp only [Equiv.toFun_as_coe, Equiv.trans_apply, pushforwardSectionsHomEquiv_smul,
      modelSectionsHomEquiv_symm_comp, RingHom.id_apply]

/-- **Global sections of a direct image.** For `f : X ⟶ T`, global sections of `f_*F` over `T`
and global sections of `F` over `X`, both read as `Γ(T, 𝒪_T)`-modules, agree naturally in `F`. -/
def pushforwardGlobalSectionsIso :
    modulePushforward B S hS f ⋙ baseRingGlobalSectionsModule B S hS (schemeSpace T)
        (baseRingHomOfMap (𝟙 (schemeSpace T))) ≅
      baseRingGlobalSectionsModule B S hS X (baseRingHomOfMap f) :=
  NatIso.ofComponents (fun F => (pushforwardSectionsLinearEquiv B S hS f F).toModuleIso)
    (fun {F G} g => by
      ext s
      exact (congrArg (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) G).symm
        (pushforwardSectionsHomEquiv_naturality B S hS f g s)).trans
        (modelSectionsHomEquiv_symm_naturality B S hS X _ g _))

/-- **`𝒪_T ⊗_R -` commutes with pullback along `f : X ⟶ T`**, `R = Γ(T, 𝒪_T)`:
`f^*(𝒪_T ⊗_R M) ≅ 𝒪_X ⊗_R M`, naturally in the `R`-module `M`. -/
def baseRingTensorModulePullbackIso :
    baseRingTensorModule B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T))) ⋙
        modulePullback B S hS f ≅
      baseRingTensorModule B S hS X (baseRingHomOfMap f) :=
  ((baseRingTensorModuleAdjunction B S hS (schemeSpace T) _).comp
      (modulePullbackAdjunction B S hS f)).leftAdjointUniq
    ((baseRingTensorModuleAdjunction B S hS X (baseRingHomOfMap f)).ofNatIsoRight
      (pushforwardGlobalSectionsIso B S hS f).symm)

end Pullback

end AlgebraicGeometry.Space
