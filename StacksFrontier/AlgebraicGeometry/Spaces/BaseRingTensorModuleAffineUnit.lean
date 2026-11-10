module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartBijectivePropagation
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingGlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraAffineTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleChangeOfRings
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelAffinePointTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineBijective

/-!
# `Γ(T, 𝒪_T ⊗_R M) = M` on an affine object of the site

Let `T` be an object of the big fppf site with affine underlying scheme and `R = Γ(T, 𝒪_T)`.
This file proves that the canonical map `M ⟶ Γ(T, 𝒪_T ⊗_R M)` (the unit of
`AlgebraicGeometry.Space.baseRingTensorModuleAdjunction` for the base-ring datum of the identity
of `T`) is an isomorphism for every `R`-module `M`, i.e. that `M ↦ 𝒪_T ⊗_R M` is fully faithful.
This is the affine case of Stacks 01I7 / 07UZ read on the small étale site of the algebraic
space represented by `T`.

The argument is the following.

* The global functions of the algebraic space represented by `T` are `Γ(T, 𝒪_T)`: a compatible
  family of functions on the étale charts is determined by its value on the identity chart, to
  which every chart maps (`AlgebraicGeometry.Space.bijective_globalFunctionsOfMap_id`).  The
  global functions of the model of the small étale site are those of the site itself, the model
  being equivalent to it (`AlgebraicGeometry.Space.bijective_modelGlobalFunctionsHom`).  So the
  base-ring datum of the identity of `T` is bijective.
* For an algebraic space `X ≅ h_{Spec A}` the functor `M ↦ ε^*(M̃)` is fully faithful and is
  `𝒪_X ⊗_A -` for a bijective base-ring datum `φ'`
  (`AlgebraicGeometry.Space.representedTildeOfIsoBaseRingHom`).  Any other bijective datum `φ`
  factors as `φ' ∘ σ` with `σ` a ring isomorphism, and `𝒪_X ⊗_φ - ≅ 𝒪_X ⊗_{φ'} (A ⊗_σ -)`
  (`AlgebraicGeometry.Space.baseRingTensorModuleCompIso`), which is fully faithful.  A fully
  faithful left adjoint has invertible unit.

## Main results

* `AlgebraicGeometry.Space.bijective_modelGlobalFunctionsHom`.
* `AlgebraicGeometry.Space.bijective_globalFunctionsOfMap_id`.
* `AlgebraicGeometry.Space.baseRingTensorModuleFullyFaithfulOfIso` and
  `AlgebraicGeometry.Space.isIso_baseRingTensorModuleAdjunction_unit_of_isAffineSpace`.
* `AlgebraicGeometry.Space.isIso_baseRingTensorModuleAdjunction_unit_id_of_isAffine`: the case
  of the identity of an affine `T`.
* `AlgebraicGeometry.Space.pushforwardBaseRingTensorIso`: for a morphism `h : T ⟶ T₀` of affine
  objects, `𝒪_{T₀} ⊗_{R₀} M ≅ h_*(𝒪_T ⊗_R M)` naturally in the `R`-module `M` (read as an
  `R₀`-module along `Γ(h)`): both are quasi-coherent, and on global sections the comparison is
  `M ≅ M` through the two invertible units.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 07UZ](https://stacks.math.columbia.edu/tag/07UZ)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The global functions of the model of the small étale site are those of the site.** The
model is equivalent to the small étale site, so restricting a compatible family along the
inverse equivalence loses nothing. -/
theorem bijective_modelGlobalFunctionsHom (X : AlgebraicSpaces B S hS) :
    Function.Bijective (modelGlobalFunctionsHom B S hS X) := by
  let e := smallEtaleModelEquiv B S hS X
  let P := (ringSheafOfSite (structureSheaf B S hS X.1 X.2)).obj
  have key : ∀ {a b c : (SmallEtale B S hS X.1)ᵒᵖ} (g₁ : a ⟶ b) (g₂ : b ⟶ c) (x : P.obj a),
      (P.map g₂).hom ((P.map g₁).hom x) = (P.map (g₁ ≫ g₂)).hom x := fun g₁ g₂ x => by
    rw [P.map_comp]; rfl
  let t' : modelGlobalFunctions B S hS X → ∀ U : (SmallEtale B S hS X.1)ᵒᵖ,
      P.obj (op (e.inverse.obj (e.functor.obj U.unop))) :=
    fun t U => t.1 (op (e.functor.obj U.unop))
  have ht' : ∀ (t : modelGlobalFunctions B S hS X) {V W : SmallModel.{u} (SmallEtale B S hS X.1)}
      (g : W ⟶ V), (P.map (e.inverse.map g).op).hom (t.1 (op V)) = t.1 (op W) :=
    fun t _ _ g => t.2 g.op
  -- the inverse map
  let ψ : modelGlobalFunctions B S hS X → GlobalFunctionRing (structureSheaf B S hS X.1 X.2) :=
    fun t => ⟨fun U => (P.map (e.unit.app U.unop).op).hom (t' t U), fun {U V} f => by
        have hn : (e.unit.app U.unop).op ≫ f = (e.inverse.map (e.functor.map f.unop)).op ≫
            (e.unit.app V.unop).op :=
          op_comp.symm.trans ((congrArg Quiver.Hom.op (e.unit.naturality f.unop)).trans
            op_comp)
        exact (key _ _ _).trans ((congrArg (fun k => (P.map k).hom (t' t U)) hn).trans
          ((key _ _ _).symm.trans (congrArg (fun x => (P.map (e.unit.app V.unop).op).hom x)
            (ht' t (e.functor.map f.unop)))))⟩
  refine Function.bijective_iff_has_inverse.2 ⟨ψ, fun s => ?_, fun t => ?_⟩
  · refine Subtype.ext (funext fun U => ?_)
    exact s.2 (e.unit.app U.unop).op
  · refine Subtype.ext (funext fun V => ?_)
    have h1 : (e.inverse.map (e.counit.app V.unop)).op ≫ (e.unit.app (e.inverse.obj V.unop)).op =
        𝟙 _ := op_comp.symm.trans ((congrArg Quiver.Hom.op (e.unit_inverse_comp V.unop)).trans
          op_id)
    exact (congrArg (fun x => (P.map (e.unit.app (e.inverse.obj V.unop)).op).hom x)
      (ht' t (e.counit.app V.unop)).symm).trans ((key _ _ _).trans
        ((congrArg (fun k => (P.map k).hom (t.1 V)) h1).trans
          (ConcreteCategory.congr_hom (P.map_id _) (t.1 V))))

variable (T : BigFppfOver B S hS)

/-- The morphism of étale charts of `h_T` from a chart to the identity chart. -/
def schemeSpaceChartToSelfChart (U : SmallEtale B S hS (schemeSpace T).1) :
    U ⟶ selfChart B S hS T :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chartToBaseOfMap (𝟙 (schemeSpace T)) U)
    ((yoneda_map_chartToBaseOfMap _ U).trans (Category.comp_id _)))

/-- **The global functions of the algebraic space represented by `T` are `Γ(T, 𝒪_T)`**: a
compatible family of functions on the étale charts of `h_T` is determined by its value on the
identity chart, to which every chart maps. -/
theorem bijective_globalFunctionsOfMap_id :
    Function.Bijective (globalFunctionsOfMap (𝟙 (schemeSpace T))) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun s => s.1 (op (selfChart B S hS T)), fun r => ?_, fun s => ?_⟩
  · change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (chartToBaseOfMap (𝟙 (schemeSpace T)) (selfChart B S hS T))).op).hom r = r
    rw [chartToBase_id_selfChart]
    have h : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (𝟙 T)).op = 𝟙 _ := by
      rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
    exact ConcreteCategory.congr_hom h r
  · refine Subtype.ext (funext fun U => ?_)
    exact s.2 (schemeSpaceChartToSelfChart T U.unop).op

/-- **On an affine object `T` of the site, a morphism of quasi-coherent modules on `h_T` which is
bijective on the sections over the identity chart is an isomorphism**: every affine chart maps to
the identity chart, so the morphism is bijective over every affine chart
(`AlgebraicGeometry.Space.bijective_val_app_of_bijective_of_cartesian`), hence an isomorphism
(`AlgebraicGeometry.Space.isIso_of_bijective_app_of_isAffineChart`). -/
theorem isIso_of_bijective_app_selfChart (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {G₁ G₂ : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2}
    (hG₁ : G₁.IsQuasicoherentOnSite) (hG₂ : G₂.IsQuasicoherentOnSite) (φ : G₁ ⟶ G₂)
    (h : Function.Bijective (φ.val.app (op (selfChart B S hS T)))) : IsIso φ :=
  SmallEtale.isIso_of_bijective_app_of_isAffineChart B S hS (schemeSpace T).1 (schemeSpace T).2 φ
    fun Z hZ => bijective_val_app_of_bijective_of_cartesian B S hS _ _ φ
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS _ _ G₁ hG₁)
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS _ _ G₂ hG₂)
      (U := selfChart B S hS T) hT hZ
      (schemeSpaceChartToSelfChart T Z) h

section FullyFaithful

variable {X : AlgebraicSpaces B S hS} {R : Type u} [CommRing R]

/-- Extension of scalars along a ring isomorphism is fully faithful. -/
def extendScalarsFullyFaithfulOfBijective {A : Type u} [CommRing A] (σ : R →+* A)
    (hσ : Function.Bijective σ) : (ModuleCat.extendScalars.{u, u, u} σ).FullyFaithful := by
  let e : R ≃+* A := RingEquiv.ofBijective σ hσ
  have he : e.toRingHom = σ := rfl
  haveI : (ModuleCat.restrictScalars.{u} σ).IsEquivalence := by
    rw [← he]; infer_instance
  haveI :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} σ).isEquivalence_left_of_isEquivalence_right
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- **`M ↦ 𝒪_X ⊗_R M` is fully faithful on an algebraic space `X ≅ h_{Spec A}` for a bijective
base-ring datum `φ : R →+* Γ(X, 𝒪_X)`.** The datum `φ'` of `M ↦ g^*(ε^*(M̃))` is bijective, so
`φ = φ' ∘ σ` with `σ` a ring isomorphism, and `𝒪_X ⊗_φ - ≅ 𝒪_X ⊗_{φ'} (A ⊗_σ -)` is the
composite of extension of scalars along `σ` with the fully faithful `M ↦ g^*(ε^*(M̃))`. -/
def baseRingTensorModuleFullyFaithfulOfIso {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (CommRingCat.of A))) (p : Spec (CommRingCat.of A) ⟶ S)
    (g : X ≅ schemeSpace (BigFppfOver.mk B S hS hA p))
    (φ : R →+* modelGlobalFunctions B S hS X) (hφ : Function.Bijective φ) :
    (baseRingTensorModule B S hS X φ).FullyFaithful := by
  haveI : (representedTildeOfIso B S hS hA p g).Additive :=
    additive_representedTildeOfIso B S hS hA p g
  let φ' := representedTildeOfIsoBaseRingHom B S hS hA p g
  have hφ' : Function.Bijective φ' := bijective_representedTildeOfIsoBaseRingHom B S hS hA p g
  let e' : A ≃+* modelGlobalFunctions B S hS X := RingEquiv.ofBijective φ' hφ'
  let σ : R →+* A := e'.symm.toRingHom.comp φ
  have hσ : Function.Bijective σ := e'.symm.bijective.comp hφ
  have hcomp : φ'.comp σ = φ := RingHom.ext fun r => e'.apply_symm_apply (φ r)
  have h₁ : (baseRingTensorModule B S hS X φ').FullyFaithful :=
    (representedTildeOfIsoFullyFaithful B S hS hA p g).ofIso
      (baseRingTensorModuleIsoOfUnitIso (representedTildeOfIso B S hS hA p g)
        (representedTildeOfIsoUnitIso B S hS hA p g)
        (representedTildeOfIsoAdjunction B S hS hA p g)).symm
  have h₂ : (baseRingTensorModule B S hS X (φ'.comp σ)).FullyFaithful :=
    ((extendScalarsFullyFaithfulOfBijective σ hσ).comp h₁).ofIso
      (baseRingTensorModuleCompIso B S hS X σ φ')
  exact hcomp ▸ h₂

/-- **`M ⟶ Γ(X, 𝒪_X ⊗_R M)` is an isomorphism on an affine algebraic space for a bijective
base-ring datum.** -/
theorem isIso_baseRingTensorModuleAdjunction_unit_of_isAffineSpace
    (hX : IsAffineSpace B S hS X.1) (φ : R →+* modelGlobalFunctions B S hS X)
    (hφ : Function.Bijective φ) :
    IsIso (baseRingTensorModuleAdjunction B S hS X φ).unit := by
  obtain ⟨T, hT, ⟨eT⟩⟩ := hX
  obtain ⟨A, _, hA, p, ⟨eA⟩⟩ := exists_iso_mk_spec B S hS T hT
  let g : X ≅ ⟨yoneda.obj (BigFppfOver.mk B S hS hA p), isAlgebraicSpace_yoneda B S hS _⟩ :=
    ObjectProperty.isoMk _ (eT ≪≫ yoneda.mapIso eA)
  have hff := baseRingTensorModuleFullyFaithfulOfIso hA p g φ hφ
  have := hff.full
  have := hff.faithful
  infer_instance

end FullyFaithful

/-- **`M ⟶ Γ(T, 𝒪_T ⊗_R M)` is an isomorphism for an affine `T`**, `R = Γ(T, 𝒪_T)`, the base
ring acting through the identity of `T`: Stacks 07UZ for the algebraic space represented by an
affine object of the site. -/
theorem isIso_baseRingTensorModuleAdjunction_unit_id_of_isAffine
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsIso (baseRingTensorModuleAdjunction B S hS (schemeSpace T)
      (baseRingHomOfMap (𝟙 (schemeSpace T)))).unit :=
  isIso_baseRingTensorModuleAdjunction_unit_of_isAffineSpace
    ⟨T, hT, ⟨Iso.refl _⟩⟩ _
    ((bijective_modelGlobalFunctionsHom (schemeSpace T)).comp (bijective_globalFunctionsOfMap_id T))

/-! ### Direct image of `𝒪_T ⊗_R M` along a morphism of affine objects -/

section AffinePushforward

/-- The identity chart of `h_T` is a terminal object of its small étale site. -/
def isTerminalSelfChart : IsTerminal (selfChart B S hS T) :=
  isTerminal_isoChart B S hS (Iso.refl (yoneda.obj T))

/-- **Over a space with a terminal chart `U`, bijectivity on global sections is bijectivity on
the sections over `U`**: global sections read on the model are the morphisms out of `𝒪_X`, which
are the sections over a terminal chart, naturally. -/
theorem bijective_app_of_bijective_baseRingGlobalSectionsModule_map {X : AlgebraicSpaces B S hS}
    {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)
    {U : SmallEtale B S hS X.1} (hU : IsTerminal U) {F₁ F₂ : Modules.{u, u} B S hS X.1 X.2}
    (c : F₁ ⟶ F₂) (h : Function.Bijective ((baseRingGlobalSectionsModule B S hS X φ).map c)) :
    Function.Bijective (c.val.app (op U)) := by
  let e : ∀ F : Modules.{u, u} B S hS X.1 X.2,
      (baseRingGlobalSectionsModule B S hS X φ).obj F ≃ F.val.obj (op U) := fun F =>
    (modelSectionsHomEquiv B S hS X φ F).trans ((SheafOfModules.unitHomEquiv F).trans
      (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal F hU))
  have he : ∀ x, e F₂ ((baseRingGlobalSectionsModule B S hS X φ).map c x) =
      c.val.app (op U) (e F₁ x) := fun x => by
    change (modelSectionsHomEquiv B S hS X φ F₂
        ((baseRingGlobalSectionsModule B S hS X φ).map c x)).val.app (op U)
          (1 : chartRing B S hS X.1 X.2 U) = _
    rw [modelSectionsHomEquiv_naturality]
    rfl
  have hc : ⇑(c.val.app (op U)) = e F₂ ∘ (baseRingGlobalSectionsModule B S hS X φ).map c ∘
      (e F₁).symm := funext fun y => by
    simp only [Function.comp_apply, he, Equiv.apply_symm_apply]
  rw [hc]
  exact (e F₂).bijective.comp (h.comp (e F₁).symm.bijective)

variable {T₀ : BigFppfOver B S hS} (h : T ⟶ T₀)

/-- The ring map `Γ(T₀, 𝒪_{T₀}) ⟶ Γ(T, 𝒪_T)` of a morphism `h : T ⟶ T₀` of the site. -/
abbrev baseRingMapOfHom : baseRing B S hS T₀ →+* baseRing B S hS T :=
  (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h).op).hom

/-- `Γ(T₀, h_* -) ≅ Res_α Γ(T, -)` as `Γ(T₀)`-modules, for `h : T ⟶ T₀` and `α = Γ(h)`. -/
def pushforwardGlobalSectionsRestrictScalarsIso :
    modulePushforward B S hS (schemeSpaceMap h) ⋙ baseRingGlobalSectionsModule B S hS
        (schemeSpace T₀) (baseRingHomOfMap (𝟙 (schemeSpace T₀))) ≅
      baseRingGlobalSectionsModule B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T))) ⋙
        ModuleCat.restrictScalars.{u} (baseRingMapOfHom T h) :=
  pushforwardGlobalSectionsIso B S hS (schemeSpaceMap h) ≪≫
    eqToIso (congrArg (baseRingGlobalSectionsModule B S hS (schemeSpace T))
      ((congrArg baseRingHomOfMap (Category.id_comp (schemeSpaceMap h)).symm).trans
        (baseRingHomOfMap_comp B S hS (𝟙 (schemeSpace T)) h))) ≪≫
    baseRingGlobalSectionsModuleCompIso B S hS (schemeSpace T) (baseRingMapOfHom T h)
      (baseRingHomOfMap (𝟙 (schemeSpace T)))

/-- The transformation `Res_α ⟶ Γ(T₀, h_*(𝒪_T ⊗_R -))`: the unit of `𝒪_T ⊗_R -` followed by
`Res_α Γ(T, -) ≅ Γ(T₀, h_* -)`. -/
def pushforwardBaseRingTensorUnit :
    ModuleCat.restrictScalars.{u} (baseRingMapOfHom T h) ⟶
      (baseRingTensorModule B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T))) ⋙
        modulePushforward B S hS (schemeSpaceMap h)) ⋙ baseRingGlobalSectionsModule B S hS
          (schemeSpace T₀) (baseRingHomOfMap (𝟙 (schemeSpace T₀))) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (baseRingTensorModuleAdjunction B S hS (schemeSpace T)
      (baseRingHomOfMap (𝟙 (schemeSpace T)))).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (pushforwardGlobalSectionsRestrictScalarsIso T h).inv ≫
    (Functor.associator _ _ _).inv

/-- The comparison `𝒪_{T₀} ⊗_{R₀} Res_α M ⟶ h_*(𝒪_T ⊗_R M)`, adjoint to
`AlgebraicGeometry.Space.pushforwardBaseRingTensorUnit`. -/
def pushforwardBaseRingTensorMap :
    ModuleCat.restrictScalars.{u} (baseRingMapOfHom T h) ⋙
        baseRingTensorModule B S hS (schemeSpace T₀) (baseRingHomOfMap (𝟙 (schemeSpace T₀))) ⟶
      baseRingTensorModule B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T))) ⋙
        modulePushforward B S hS (schemeSpaceMap h) :=
  Functor.whiskerRight (pushforwardBaseRingTensorUnit T h) _ ≫ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (baseRingTensorModuleAdjunction B S hS (schemeSpace T₀)
      (baseRingHomOfMap (𝟙 (schemeSpace T₀)))).counit ≫ (Functor.rightUnitor _).hom

/-- The component at `M` of `AlgebraicGeometry.Space.pushforwardBaseRingTensorMap` is the
adjoint, for `𝒪_{T₀} ⊗_{R₀} - ⊣ Γ(T₀, -)`, of the component at `M` of
`AlgebraicGeometry.Space.pushforwardBaseRingTensorUnit`. -/
theorem pushforwardBaseRingTensorMap_app (M : ModuleCat.{u} (baseRing B S hS T)) :
    (pushforwardBaseRingTensorMap T h).app M =
      ((baseRingTensorModuleAdjunction B S hS (schemeSpace T₀)
        (baseRingHomOfMap (𝟙 (schemeSpace T₀)))).homEquiv _ _).symm
        ((pushforwardBaseRingTensorUnit T h).app M) := by
  simp [pushforwardBaseRingTensorMap, Adjunction.homEquiv_counit]

/-- **The direct image of `𝒪_T ⊗_R M` along a morphism `h : T ⟶ T₀` of affine objects of the
site is `𝒪_{T₀} ⊗_{R₀} M`, `M` read as an `R₀`-module along `Γ(h)`.** Both sides are
quasi-coherent on the affine `h_{T₀}`, so it suffices that the comparison is bijective over the
identity chart, that is on global sections; there it is the composite of the inverse of the unit
`Res M ⟶ Γ(T₀, 𝒪_{T₀} ⊗ Res M)` with `Res M ≅ Res Γ(T, 𝒪_T ⊗ M) ≅ Γ(T₀, h_*(𝒪_T ⊗ M))`, the
units being invertible on affines. -/
theorem isIso_pushforwardBaseRingTensorMap
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    IsIso (pushforwardBaseRingTensorMap T h) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun M => ?_
  let adj₀ := baseRingTensorModuleAdjunction B S hS (schemeSpace T₀)
    (baseRingHomOfMap (𝟙 (schemeSpace T₀)))
  have := isIso_baseRingTensorModuleAdjunction_unit_id_of_isAffine T hT
  have := isIso_baseRingTensorModuleAdjunction_unit_id_of_isAffine T₀ hT₀
  have : IsIso ((pushforwardBaseRingTensorUnit T h).app M) := by
    simp only [pushforwardBaseRingTensorUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance
  have hcomp : adj₀.unit.app _ ≫ (baseRingGlobalSectionsModule B S hS (schemeSpace T₀)
      (baseRingHomOfMap (𝟙 (schemeSpace T₀)))).map ((pushforwardBaseRingTensorMap T h).app M) =
        (pushforwardBaseRingTensorUnit T h).app M := by
    rw [pushforwardBaseRingTensorMap_app]
    exact (adj₀.homEquiv_unit _ _ _).symm.trans ((adj₀.homEquiv _ _).apply_symm_apply _)
  have := IsIso.of_isIso_fac_left hcomp
  have h₁ : ((baseRingTensorModule B S hS (schemeSpace T₀)
      (baseRingHomOfMap (𝟙 (schemeSpace T₀)))).obj
      ((ModuleCat.restrictScalars.{u} (baseRingMapOfHom T h)).obj M)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_baseRingTensorModule B S hS (schemeSpace T₀) _ _
  have h₂ : ((modulePushforward B S hS (schemeSpaceMap h)).obj
      ((baseRingTensorModule B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T)))).obj
        M)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_isAffineHom' (schemeSpaceMap h)
      (isAffineHom_yoneda_map B S hS h)
      (isQuasicoherentOnSite_baseRingTensorModule B S hS (schemeSpace T) _ M)
  exact isIso_of_bijective_app_selfChart T₀ hT₀ h₁ h₂ ((pushforwardBaseRingTensorMap T h).app M)
    (bijective_app_of_bijective_baseRingGlobalSectionsModule_map
      (baseRingHomOfMap (𝟙 (schemeSpace T₀))) (isTerminalSelfChart T₀)
      ((pushforwardBaseRingTensorMap T h).app M) (ConcreteCategory.bijective_of_isIso _))

/-- `𝒪_{T₀} ⊗_{R₀} Res_α M ≅ h_*(𝒪_T ⊗_R M)` naturally in `M`, for `h : T ⟶ T₀` of affine
objects. -/
def pushforwardBaseRingTensorIso
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    ModuleCat.restrictScalars.{u} (baseRingMapOfHom T h) ⋙
        baseRingTensorModule B S hS (schemeSpace T₀) (baseRingHomOfMap (𝟙 (schemeSpace T₀))) ≅
      baseRingTensorModule B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T))) ⋙
        modulePushforward B S hS (schemeSpaceMap h) :=
  haveI := isIso_pushforwardBaseRingTensorMap T h hT hT₀
  asIso (pushforwardBaseRingTensorMap T h)

end AffinePushforward

end AlgebraicGeometry.Space

end
