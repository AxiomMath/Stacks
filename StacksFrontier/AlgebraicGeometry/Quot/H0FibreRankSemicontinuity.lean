module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatDerivedPushforwardFieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BettiNumbersOnPointsPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyDegreeZero
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsFiniteOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomChartFormula

/-!
# `dim_k H⁰(X_k, 𝒪)` is upper semicontinuous (Stacks 0E0R at `i = 0`)

Let `f : X ⟶ U` be a proper, flat morphism of finite presentation from an algebraic space to a
scheme `U` of the site. For a field-valued point `Spec k ⟶ U` let
`AlgebraicGeometry.Space.h0FibreRank` be `dim_k H⁰(X_k, 𝒪_{X_k})`, the dimension of the global
regular functions on the fibre `X_k = X ×_U Spec k`. This file proves that it is the value at the
image point of one upper semicontinuous function on `U`: this is parts (1) and (2) of Stacks 0E0R
for `i = 0` and `𝓕 = 𝒪_X`, in the form that
`AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank` consumes.

## Main results

* `AlgebraicGeometry.Space.derivedFibreBettiAt_zero_eq_finrank_globalSectionRing`: the `0`-th
  derived-fibre Betti number of `Rf_*𝒪_X` at `Spec k ⟶ U` is `dim_k Γ(X_k, 𝒪)`.
* `AlgebraicGeometry.Space.moduleFinite_h0Fibre`: `Γ(X_k, 𝒪)` is finite over `k`.
* `AlgebraicGeometry.Space.h0FibreRank_eq_derivedFibreBettiAt`: `dim_k H⁰(X_k, 𝒪)` is that Betti
  number.
* `AlgebraicGeometry.Space.exists_upperSemicontinuous_h0FibreRank`: **Stacks 0E0R at `i = 0`**.

## Implementation notes

The proof is the source's. By cohomology and base change (Stacks 0CTM, part (1),
`AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat`)
`K = Rf_*𝒪_X` is perfect and `Lp^*K = Rf_{k,*}𝒪_{X_k}` at every field-valued point `p`; on
`Spec k` the Leray spectral sequence degenerates
(`AlgebraicGeometry.Space.finrank_globalSectionsHomologyDerivedModulePushforward_eq`), so the
degree-zero derived fibre of `K` is `H⁰(X_k, 𝒪) = Γ(X_k, 𝒪)`
(`Stacks.Cohomology.SiteModules.globalModuleCohomologyZeroIso`). The Betti numbers of the perfect
object `K` are upper semicontinuous (Stacks 0D1Y,
`AlgebraicGeometry.Space.upperSemicontinuous_geometricFibreBettiFunction`).

The derived-fibre Betti number reads the fibre on the identity chart of `Spec k`, while the Leray
comparison reads global sections; the identity chart is terminal, and
`Stacks.Cohomology.SiteModules.finrank_globalSections_eq_finrank_eval_of_isInitial` compares the
two, at the universes of the small étale site.

## References

* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0D1Y](https://stacks.math.columbia.edu/tag/0D1Y)
* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.SiteModules

universe u' v' r' w'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{r'})

/-- Evaluation at an initial object `X` of `Cᵒᵖ` is a bijection from the compatible families of
sections of an `O`-module to its sections at `X` (any universes). -/
def sectionsEquivEvalOfIsInitial (M : SheafOfModules.{w'} O) (X : Cᵒᵖ) (hX : IsInitial X) :
    M.sections ≃ M.val.obj X := by
  refine Equiv.ofBijective (fun s => s.eval X) ⟨fun s t hst => Subtype.ext <| funext fun Y =>
    (s.2 (hX.to Y)).symm.trans ((congrArg (M.val.map (hX.to Y)) hst).trans (t.2 (hX.to Y))),
    fun a => ⟨⟨fun Y => M.val.map (hX.to Y) a, ?_⟩, ?_⟩⟩
  · intro Y Z f
    change M.val.map f (M.val.map (hX.to Y) a) = _
    rw [← PresheafOfModules.map_comp_apply, hX.hom_ext (hX.to Y ≫ f) (hX.to Z)]
  · change M.val.map (hX.to X) a = a
    rw [hX.hom_ext (hX.to X) (𝟙 X)]
    simp only [PresheafOfModules.map_id]
    rfl

/-- **`dim Γ(C, M) = dim M(X)` at an initial object of `Cᵒᵖ`**, over a field `A` acting on the
compatible families through `ρ` and on the sections at `X` through `σ`, compatibly. -/
theorem finrank_globalSections_eq_finrank_eval_of_isInitial {A : Type*} [Field A]
    (M : SheafOfModules.{w'} O) (X : Cᵒᵖ) (hX : IsInitial X)
    (ρ : A →+* ↥(GlobalSectionRing O)) (σ : A →+* O.obj.obj X)
    (hρσ : (globalSectionEval O X).comp ρ = σ) :
    Module.finrank A ((ModuleCat.restrictScalars ρ).obj
        ((globalSectionsFunctor.{u', v', r', w'} O).obj M)) =
      Module.finrank A ((ModuleCat.restrictScalars σ).obj
        ((_root_.SheafOfModules.evaluation O X).obj M)) := by
  let e : (ModuleCat.restrictScalars ρ).obj ((globalSectionsFunctor.{u', v', r', w'} O).obj M) ≃ₗ[A]
      (ModuleCat.restrictScalars σ).obj ((_root_.SheafOfModules.evaluation O X).obj M) :=
    { (show ((globalSectionsFunctor.{u', v', r', w'} O).obj M : Type _) ≃ M.val.obj X from
        sectionsEquivEvalOfIsInitial O M X hX) with
      map_add' := fun _ _ => rfl
      map_smul' := fun a s => by
        change (ρ a • s).eval X = σ a • s.eval X
        rw [← hρσ]
        rfl }
  exact e.finrank_eq

end Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The `0`-th derived-fibre Betti number of `Rf_*𝒪_X` at a field-valued point**, read through
cohomology and base change (Stacks 0CTM): it is the dimension over `k` of the global sections of
`H⁰(Rf_{k,*}𝒪_{X_k})` on `Spec k`, for the fibre `f_k : X_k ⟶ Spec k`. -/
theorem derivedFibreBettiAt_zero_derivedModulePushforward_eq (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (p : FieldValuedPoint B S hS Y.1) :
    derivedFibreBettiAt Y ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))) 0 p =
      Module.finrank p.carrier ((ModuleCat.restrictScalars
        ((globalSectionsRingHom B S hS (schemeSpace p.siteObject).1 (schemeSpace p.siteObject).2
          (𝟙 _)).comp (Scheme.ΓSpecIso (.of p.carrier)).inv.hom)).obj
        ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (schemeSpace p.siteObject).1 (schemeSpace p.siteObject).2).O)).obj
          ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (schemeSpace p.siteObject).1 (schemeSpace p.siteObject).2) 0).obj
            ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS
              (ObjectProperty.homMk (pullback.snd f.hom p.toSpace.hom) :
                AlgebraicSpaces.fiberProduct B S hS f p.toSpace ⟶ schemeSpace p.siteObject))).obj
              ((DerivedCategory.singleFunctor _ 0).obj (structureSheafModule B S hS
                (AlgebraicSpaces.fiberProduct B S hS f p.toSpace))))))) := by
  let V := p.siteObject
  let g : schemeSpace V ⟶ Y := p.toSpace
  let X' := AlgebraicSpaces.fiberProduct B S hS f g
  let f' : X' ⟶ schemeSpace V := ObjectProperty.homMk (pullback.snd f.hom g.hom)
  let g' : X' ⟶ X := ObjectProperty.homMk (pullback.fst f.hom g.hom)
  have sq : IsPullback g' f' f g := AlgebraicSpaces.isPullback_fiberProduct B S hS f g
  let E := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj (SheafOfModules.unit _)
  have hbc := (isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp E
    (isPerfect_unit X)).2 g f' g' sq
  let e₁ := @asIso _ _ _ _ _ hbc ≪≫
    (derivedModulePushforward B S hS f').mapIso (smallEtaleDerivedModulePullbackUnitIso g') ≪≫
    (smallEtaleDerivedModulePushforwardIso B S hS f').app _
  have hρσ : (Stacks.Cohomology.SiteModules.globalSectionEval _ (op (idChart B S hS V))).comp
      ((globalSectionsRingHom B S hS (schemeSpace V).1 (schemeSpace V).2 (𝟙 _)).comp
        (Scheme.ΓSpecIso (.of p.carrier)).inv.hom) = p.fieldToSections.hom := by
    ext a
    rfl
  have h1 := Stacks.Cohomology.SiteModules.finrank_globalSections_eq_finrank_eval_of_isInitial
    (A := p.carrier) (ringedToposStructureRingSheaf B S hS (schemeSpace V))
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (schemeSpace V))) 0).obj
      ((smallEtaleDerivedModulePullback B S hS g).obj ((derivedModulePushforward B S hS f).obj E)))
    (op (idChart B S hS V)) (isTerminal_idChart B S hS V).op _ p.fieldToSections.hom hρσ
  exact h1.symm.trans ((ModuleCat.restrictScalars _).mapIso
    ((Stacks.Cohomology.SiteModules.globalSectionsFunctor _).mapIso
      ((DerivedCategory.homologyFunctor _ 0).mapIso e₁))).toLinearEquiv.finrank_eq

/-- The global sections of the universe lift of the structure sheaf of an algebraic space are its
ring of global sections, as a module over itself. -/
def uliftStructureSheafModuleSectionsLinearEquiv (Z : AlgebraicSpaces B S hS) :
    (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (structureSheafModule B S hS Z)).sections ≃ₗ[Stacks.Cohomology.SiteModules.GlobalSectionRing
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)]
      Stacks.Cohomology.SiteModules.GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O) where
  toFun s := ⟨fun U => (s.eval U).down, by
    intro U V f
    exact congrArg ULift.down
      ((SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (structureSheafModule B S hS Z)).val.sections_property s f)⟩
  invFun s := ⟨fun U => ULift.up (s.1 U), by
    intro U V f
    exact ULift.ext (s.2 f)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **`dim_k H⁰(Z, 𝒪_Z) = dim_k Γ(Z, 𝒪_Z)`**, for any ring map `k ⟶ Γ(Z, 𝒪_Z)` from a field. -/
theorem finrank_globalModuleCohomology_zero_structureSheafModule (Z : AlgebraicSpaces B S hS)
    {A : Type*} [Field A] (ρ : A →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)) :
    Module.finrank A ((ModuleCat.restrictScalars ρ).obj
        ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O) 0).obj
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
            (structureSheafModule B S hS Z)))) =
      (letI := ρ.toAlgebra; Module.finrank A (Stacks.Cohomology.SiteModules.GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))) := by
  let := ρ.toAlgebra
  let e0 := ((ModuleCat.restrictScalars ρ).mapIso
    ((Stacks.Cohomology.SiteModules.globalModuleCohomologyZeroIso.{u + 1, u, u, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).app
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (structureSheafModule B S hS Z)))).toLinearEquiv
  let e1 := uliftStructureSheafModuleSectionsLinearEquiv (B := B) (S := S) (hS := hS) Z
  let e2 : ((ModuleCat.restrictScalars ρ).obj
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (structureSheafModule B S hS Z))) : Type _) ≃ₗ[A]
      Stacks.Cohomology.SiteModules.GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O) :=
    { e1.toAddEquiv with
      map_smul' := fun a s => e1.map_smul (ρ a) s }
  exact (e0.trans e2).finrank_eq

/-- **The `0`-th derived-fibre Betti number of `Rf_*𝒪_X` is `dim_k Γ(X_k, 𝒪)`**, for `f` proper,
flat and of finite presentation and a field-valued point `p : Spec k ⟶ Y`, with `k` acting on
`Γ(X_k, 𝒪)` by pullback along `X_k ⟶ Spec k`. -/
theorem derivedFibreBettiAt_zero_eq_finrank_globalSectionRing (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (p : FieldValuedPoint B S hS Y.1) :
    derivedFibreBettiAt Y ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))) 0 p =
      (letI := ((globalSectionsRingHom B S hS (AlgebraicSpaces.fiberProduct B S hS f p.toSpace).1
          (AlgebraicSpaces.fiberProduct B S hS f p.toSpace).2
          (pullback.snd f.hom p.toSpace.hom)).comp
            (Scheme.ΓSpecIso (.of p.carrier)).inv.hom).toAlgebra;
        Module.finrank p.carrier (Stacks.Cohomology.SiteModules.GlobalSectionRing
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (AlgebraicSpaces.fiberProduct B S hS f p.toSpace).1
            (AlgebraicSpaces.fiberProduct B S hS f p.toSpace).2).O))) :=
  by
  have h1 := derivedFibreBettiAt_zero_derivedModulePushforward_eq f hf hfl hfp p
  have h2 := finrank_globalSectionsHomologyDerivedModulePushforward_eq B S hS p.carrier
    (Iso.refl ((BigFppfOver.toScheme B S hS).obj p.siteObject))
    (Scheme.ΓSpecIso (.of p.carrier)).inv.hom
    (ObjectProperty.homMk (pullback.snd f.hom p.toSpace.hom) :
      AlgebraicSpaces.fiberProduct B S hS f p.toSpace ⟶ schemeSpace p.siteObject)
    (structureSheafModule B S hS (AlgebraicSpaces.fiberProduct B S hS f p.toSpace)) 0
  have h3 := finrank_globalModuleCohomology_zero_structureSheafModule
    (AlgebraicSpaces.fiberProduct B S hS f p.toSpace)
    ((globalSectionsRingHom B S hS (AlgebraicSpaces.fiberProduct B S hS f p.toSpace).1
      (AlgebraicSpaces.fiberProduct B S hS f p.toSpace).2
      (pullback.snd f.hom p.toSpace.hom)).comp (Scheme.ΓSpecIso (.of p.carrier)).inv.hom)
  exact h1.trans (h2.trans h3)

section H0FibreRank

attribute [local instance] pointTopology

variable {U : BigFppfOver B S hS} (f : X ⟶ schemeSpace U)
  (p : FieldValuedPoint B S hS (yoneda.obj U))

/-- The ring map `k ⟶ H⁰(X_k, 𝒪)` of `AlgebraicGeometry.Space.h0FibreAlgebraMap` is, chart by
chart, pullback along the chart of the fibre. -/
theorem h0FibreAlgebraMap_val (c : p.carrier) :
    (h0FibreAlgebraMap B S hS f p c).val =
      (((globalSectionsRingHom B S hS (h0Fibre B S hS f p).1 (h0Fibre B S hS f p).2
        (pullback.snd f.hom (schemeSpaceMap p.value).hom)).comp
          (Scheme.ΓSpecIso (.of p.carrier)).inv.hom) c).val := by
  funext W
  let a := (Scheme.ΓSpecIso (.of p.carrier)).inv.hom c
  let ψ := chartToScheme B S hS (h0Fibre B S hS f p).obj
    (pullback.snd f.hom (schemeSpaceMap p.value).hom) W.unop
  have hψ : yoneda.map ψ ≫ ((SmallEtale.inclusion B S hS (yoneda.obj p.siteObject)).obj
      (idEtaleChart B S hS p.siteObject)).hom =
      ((SmallEtale.inclusion B S hS (h0Fibre B S hS f p).obj).obj W.unop).hom ≫
        (h0FibreProj B S hS f p).hom := by
    change yoneda.map ψ ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact Functor.FullyFaithful.map_preimage _ _
  have hs : ((globalFunctionsYonedaRingEquiv B S hS p.siteObject).symm a).val
      (op (idEtaleChart B S hS p.siteObject)) = a :=
    (globalFunctionsYonedaRingEquiv B S hS p.siteObject).apply_symm_apply a
  have h := globalFunctionsMap_val_chart B S hS (h0FibreProj B S hS f p)
    (idEtaleChart B S hS p.siteObject) W.unop ψ hψ
    ((globalFunctionsYonedaRingEquiv B S hS p.siteObject).symm a)
  exact h.trans (congrArg (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ψ).op).hom hs)

/-- The ring map `k ⟶ H⁰(X_k, 𝒪)` is pullback of global functions along the proper morphism
`X_k ⟶ Spec k`, read through `k ≅ Γ(Spec k, 𝒪)`. -/
theorem h0FibreAlgebraMap_eq_pullbackToGlobalFunctions :
    h0FibreAlgebraMap B S hS f p =
      (pullbackToGlobalFunctions B S hS (h0Fibre B S hS f p) p.siteObject
        (h0FibreProj B S hS f p)).comp (Scheme.ΓSpecIso (.of p.carrier)).inv.hom :=
  RingHom.ext fun c => Subtype.ext <| (h0FibreAlgebraMap_val f p c).trans <| funext fun W => by
    have hc : chartToScheme B S hS (h0Fibre B S hS f p).obj
        (pullback.snd f.hom (schemeSpaceMap p.value).hom) W.unop =
        yoneda.preimage (W.unop.1.hom ≫ (h0FibreProj B S hS f p).hom) :=
      yoneda.map_injective ((Functor.FullyFaithful.map_preimage _ _).trans
        (Functor.map_preimage _ _).symm)
    refine Eq.trans ?_ (pullbackToGlobalFunctions_apply_chart B S hS _ _ _ W.unop _).symm
    change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToScheme B S hS
      (h0Fibre B S hS f p).obj (pullback.snd f.hom (schemeSpaceMap p.value).hom) W.unop)).op).hom
        _ = _
    rw [hc]
    rfl

/-- **`H⁰(X_k, 𝒪)` is finite dimensional over `k`** for `f` proper (Stacks 0DMY, part (1)). -/
theorem moduleFinite_h0Fibre (hf : IsProper B S hS f.hom) :
    letI := (h0FibreAlgebraMap B S hS f p).toAlgebra
    Module.Finite p.carrier (globalFunctions' B S hS (h0Fibre B S hS f p).obj) := by
  have hq : IsProper B S hS (h0FibreProj B S hS f p).hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f (schemeSpaceMap p.value)) hf
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (IsAffine (Spec (.of p.carrier)))
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj p.siteObject, ⊤) :=
    isNoetherianRing_of_ringEquiv p.carrier
      (Scheme.ΓSpecIso (.of p.carrier)).commRingCatIsoToRingEquiv.symm
  have hN := isNoetherian_globalFunctions_of_isProper B S hS (h0FibreProj B S hS f p) hq
  let iT := globalFunctionsModuleOfHom B S hS (h0Fibre B S hS f p) p.siteObject
    (h0FibreProj B S hS f p)
  have : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj p.siteObject, ⊤)
      (globalFunctions B S hS (h0Fibre B S hS f p).obj) := inferInstance
  let ψ : p.carrier →+* Γ((BigFppfOver.toScheme B S hS).obj p.siteObject, ⊤) :=
    (Scheme.ΓSpecIso (.of p.carrier)).inv.hom
  let iA : Algebra p.carrier Γ((BigFppfOver.toScheme B S hS).obj p.siteObject, ⊤) :=
    ψ.toAlgebra
  have hψ : Function.Surjective ψ :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2
  have : Module.Finite p.carrier Γ((BigFppfOver.toScheme B S hS).obj p.siteObject, ⊤) :=
    RingHom.Finite.of_surjective ψ hψ
  let iK := (h0FibreAlgebraMap B S hS f p).toAlgebra
  have : IsScalarTower p.carrier Γ((BigFppfOver.toScheme B S hS).obj p.siteObject, ⊤)
      (globalFunctions' B S hS (h0Fibre B S hS f p).obj) := by
    refine ⟨fun c r m => ?_⟩
    change pullbackToGlobalFunctions B S hS (h0Fibre B S hS f p) p.siteObject
        (h0FibreProj B S hS f p) (ψ c * r) * m =
      h0FibreAlgebraMap B S hS f p c * (pullbackToGlobalFunctions B S hS (h0Fibre B S hS f p)
        p.siteObject (h0FibreProj B S hS f p) r * m)
    rw [h0FibreAlgebraMap_eq_pullbackToGlobalFunctions, RingHom.comp_apply, map_mul, mul_assoc]
  exact Module.Finite.trans Γ((BigFppfOver.toScheme B S hS).obj p.siteObject, ⊤) _

/-- The ring of global sections of the structure sheaf of an algebraic space is its ring of
global regular functions. -/
def globalSectionRingEquivGlobalFunctions (Z : AlgebraicSpaces B S hS) :
    Stacks.Cohomology.SiteModules.GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O) ≃+*
      globalFunctions' B S hS Z.obj where
  toFun b := ⟨b.1, b.2⟩
  invFun b := ⟨b.1, b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **`dim_k H⁰(X_k, 𝒪)` is the `0`-th derived-fibre Betti number of `Rf_*𝒪_X`** at a
field-valued point `Spec k ⟶ U`, for `f : X ⟶ U` proper, flat and of finite presentation. -/
theorem h0FibreRank_eq_derivedFibreBettiAt (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom) :
    h0FibreRank B S hS f p = (derivedFibreBettiAt (schemeSpace U)
      ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _))) 0 p : ℕ∞) := by
  rw [derivedFibreBettiAt_zero_eq_finrank_globalSectionRing f hf hfl hfp p]
  let := (h0FibreAlgebraMap B S hS f p).toAlgebra
  have := moduleFinite_h0Fibre f p hf
  unfold h0FibreRank
  rw [← Module.finrank_eq_rank, Cardinal.toENat_nat]
  congr 1
  let τ := globalSectionRingEquivGlobalFunctions (B := B) (S := S) (hS := hS) (h0Fibre B S hS f p)
  let ρ := (globalSectionsRingHom B S hS (h0Fibre B S hS f p).1 (h0Fibre B S hS f p).2
    (pullback.snd f.hom (schemeSpaceMap p.value).hom)).comp
      (Scheme.ΓSpecIso (.of p.carrier)).inv.hom
  let := ρ.toAlgebra
  have hτ : ∀ c, τ (ρ c) = h0FibreAlgebraMap B S hS f p c := fun c =>
    Subtype.ext (h0FibreAlgebraMap_val f p c).symm
  let L : Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (h0Fibre B S hS f p).1 (h0Fibre B S hS f p).2).O) ≃ₗ[p.carrier]
      globalFunctions' B S hS (h0Fibre B S hS f p).obj :=
    { τ.toAddEquiv with
      map_smul' := fun c x => by
        change τ (ρ c * x) = h0FibreAlgebraMap B S hS f p c * τ x
        rw [map_mul, hτ] }
  exact L.finrank_eq.symm

/-- **Stacks 0E0R at `i = 0`, for the structure sheaf.** For `f : X ⟶ U` proper, flat and of finite
presentation over a scheme `U` of the site, `dim_k H⁰(X_k, 𝒪_{X_k})` is, at every field-valued
point `Spec k ⟶ U`, the value at its image point of one upper semicontinuous function on `U`:
the `0`-th Betti number of the perfect object `Rf_*𝒪_X` (Stacks 0CTM, 0D1Y). -/
theorem exists_upperSemicontinuous_h0FibreRank (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom) :
    ∃ b : (BigFppfOver.toScheme B S hS).obj U → ℕ∞, UpperSemicontinuous b ∧
      ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
        h0FibreRank B S hS f p = b (schemePoint B S hS U p) := by
  let E := (derivedModulePushforward B S hS f).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj (SheafOfModules.unit _))
  have hE := (isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp _
    (isPerfect_unit X)).1
  have hEpc := RingedSite.isPseudoCoherent_of_isPerfect_general _ hE
  let β := geometricFibreBettiFunction B S hS E 0
  have hβ : UpperSemicontinuous β := upperSemicontinuous_geometricFibreBettiFunction B S hS E hEpc 0
  let e := schemePointsHomeomorph B S hS U
  refine ⟨fun y => (β (e.symm y) : ℕ∞), ?_, fun q => ?_⟩
  · intro y n hn
    have hx := hβ (e.symm y) (β (e.symm y) + 1) (Nat.lt_succ_self _)
    have ht : Filter.Tendsto e.symm (nhds y) (nhds (e.symm y)) := e.symm.continuous.tendsto y
    filter_upwards [ht.eventually hx] with y' hy'
    exact lt_of_le_of_lt (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hy')) hn
  · have hq : e.symm (schemePoint B S hS U q) = q.class B S hS (yoneda.obj U) :=
      e.symm_apply_eq.2 (pointsToScheme_class B S hS U q).symm
    change _ = ((β (e.symm (schemePoint B S hS U q)) : ℕ) : ℕ∞)
    rw [hq, h0FibreRank_eq_derivedFibreBettiAt f q hf hfl hfp]
    congr 1
    change _ = geometricFibreBettiFunction B S hS E 0 (q.class B S hS (schemeSpace U).1)
    rw [geometricFibreBettiFunction_eq_derivedFibreBetti B S hS E hEpc 0]
    exact (derivedFibreBetti_class B S hS (schemeSpace U) E
      (derivedCategoryB_of_isPerfect B S hS _ E hE) 0 q).symm

end H0FibreRank

end AlgebraicGeometry.Space
