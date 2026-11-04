module

public import StacksFrontier.Algebra.C1573Port.Category.ModuleCat.Sheaf.OverTerminalFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSectionsNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartDirectImageTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections

namespace Stacks.SheafOfModules.C1573
end Stacks.SheafOfModules.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The Zariski restriction along the identity chart is fully faithful on quasi-coherent modules

Let `U` be an object of the big fppf site over `S` and `h_U` the algebraic space it represents.
The restriction of quasi-coherent `𝒪_{h_U}`-modules to the Zariski site of the scheme of the
identity chart, `AlgebraicGeometry.Space.C1573.chartZariskiModule` at
`AlgebraicGeometry.Space.idEtaleChart`, is fully faithful.

## Main definitions

* `AlgebraicGeometry.Space.C1573.chartSchemeEtaleModuleFunctorRestrictIso`: for any chart, the
  chart transport followed by the Zariski restriction is the direct image along the composite
  comparison map, naturally in the module.
* `AlgebraicGeometry.Space.C1573.chartZariskiModuleQcohIso`: the chart transport functor and the
  Zariski restriction of a quasi-coherent module are naturally isomorphic.
* `AlgebraicGeometry.Space.C1573.chartSchemeModuleFunctorFullyFaithfulIdEtaleChart` and
  `AlgebraicGeometry.Space.C1573.chartZariskiModuleFullyFaithfulIdEtaleChart`: **full faithfulness
  at the identity chart.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SheafOfModules

open _root_.Stacks.SheafOfModules.C1573
/-- The component at `W` of the morphism `eqToHom h` between equal sheaves of modules is
`eqToHom` of the induced equality of sections. -/
theorem C1573.eqToHom_val_app {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{u} R} (h : M = N) (W : Cᵒᵖ) :
    (eqToHom h).val.app W = eqToHom (by rw [h]) := by
  subst h
  rfl

/-- Two functors into sheaves of modules which agree on objects are isomorphic, by
`CategoryTheory.eqToIso`, as soon as they agree on morphisms after reading on sections, with any
identification of the sections. -/
def C1573.isoOfObjEqOfValApp {𝒞 : Type*} [Category* 𝒞] {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (F G : 𝒞 ⥤ _root_.SheafOfModules.{u} R) (h : ∀ M, F.obj M = G.obj M)
    (e : ∀ M W, (F.obj M).val.obj W = (G.obj M).val.obj W)
    (H : ∀ {P Q : 𝒞} (φ : P ⟶ Q) W,
      (F.map φ).val.app W ≫ eqToHom (e Q W) = eqToHom (e P W) ≫ (G.map φ).val.app W) :
    F ≅ G :=
  NatIso.ofComponents (fun M => eqToIso (h M)) fun {P Q} φ => by
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ?_)
    have h₁ := h P
    have h₂ := h Q
    simp only [eqToIso.hom]
    rw [_root_.SheafOfModules.comp_val, _root_.SheafOfModules.comp_val,
      PresheafOfModules.comp_app, PresheafOfModules.comp_app, eqToHom_val_app, eqToHom_val_app]
    exact H φ W

/-- `Stacks.SheafOfModules.C1573.isoOfObjEqOfValApp`, with both sides read through a common
presentation `T` of the sections. -/
def C1573.isoOfObjEqOfValApp' {𝒞 : Type*} [Category* 𝒞] {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (F G : 𝒞 ⥤ _root_.SheafOfModules.{u} R) (h : ∀ M, F.obj M = G.obj M)
    (T : 𝒞 → ∀ W : Cᵒᵖ, ModuleCat.{u} (R.obj.obj W))
    (e : ∀ M W, (F.obj M).val.obj W = T M W) (hT : ∀ M W, (G.obj M).val.obj W = T M W)
    (g : ∀ {P Q : 𝒞} (_ : P ⟶ Q) W, T P W ⟶ T Q W)
    (hg : ∀ {P Q : 𝒞} (φ : P ⟶ Q) W, HEq ((G.map φ).val.app W) (g φ W))
    (H : ∀ {P Q : 𝒞} (φ : P ⟶ Q) W,
      (F.map φ).val.app W ≫ eqToHom (e Q W) = eqToHom (e P W) ≫ g φ W) :
    F ≅ G :=
  isoOfObjEqOfValApp F G h (fun M W => (e M W).trans (hT M W).symm) fun φ W => by
    rw [(conj_eqToHom_iff_heq _ _ (hT _ W) (hT _ W)).2 (hg φ W),
      ← eqToHom_trans (e _ W) (hT _ W).symm, ← Category.assoc, H]
    simp

/-- The component at `M` of the isomorphism `Stacks.SheafOfModules.C1573.isoOfObjEqOfValApp` is
`eqToHom (h M)`. -/
theorem C1573.isoOfObjEqOfValApp_hom_app {𝒞 : Type*} [Category* 𝒞] {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (F G : 𝒞 ⥤ _root_.SheafOfModules.{u} R) (h : ∀ M, F.obj M = G.obj M)
    (e : ∀ M W, (F.obj M).val.obj W = (G.obj M).val.obj W)
    (H : ∀ {P Q : 𝒞} (φ : P ⟶ Q) W,
      (F.map φ).val.app W ≫ eqToHom (e Q W) = eqToHom (e P W) ≫ (G.map φ).val.app W) (M : 𝒞) :
    (isoOfObjEqOfValApp F G h e H).hom.app M = eqToHom (h M) := rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- On sections over an open `W` of the chart scheme, the Zariski restriction of a morphism `f` is
the restriction of scalars of the component of `f` at the open chart attached to `W`. -/
theorem C1573.chartZariskiModule_map_val_app (A : SmallEtale B S hS X.1)
    {M N : SheafOfModules.{u} (structureRingSheaf B S hS X)} (f : M ⟶ N)
    (W : (chartScheme A).Opens) :
    ((chartZariskiModule B S hS X A).map f).val.app (op W) =
      (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A W)).map
        (f.val.app (op (openChartOfComparison B S hS X A W))) := rfl

/-- **The chart transport followed by the Zariski restriction is the direct image along the
composite comparison map**, naturally in the quasi-coherent module. -/
def C1573.chartSchemeEtaleModuleFunctorRestrictIso (A : SmallEtale B S hS X.1) :
    chartSchemeEtaleModuleFunctor B S hS X A ⋙
        _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property ≅
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf B S hS X)).ι ⋙ chartZariskiModule B S hS X A :=
  Stacks.SheafOfModules.C1573.isoOfObjEqOfValApp' _ _
    (fun M => restrictModule_chartSchemeEtaleModule_eq_pushforward B S hS X M.obj M.property A)
    (fun M W => (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A W.unop)).obj
        (M.obj.val.obj (op (openChartOfComparison B S hS X A W.unop))))
    (fun M W => restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M.obj M.property A
      W.unop)
    (fun _ _ => rfl)
    (fun φ W => (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A W.unop)).map
        (φ.hom.val.app (op (openChartOfComparison B S hS X A W.unop))))
    (fun φ ⟨W⟩ => heq_of_eq (chartZariskiModule_map_val_app B S hS X A φ.hom W))
    (fun φ ⟨W⟩ => chartSectionsLinearEquiv_naturality B S hS X A φ W)

/-- **The chart transport and the Zariski restriction of a quasi-coherent module are naturally
isomorphic.** -/
def C1573.chartZariskiModuleQcohIso (A : SmallEtale B S hS X.1) :
    chartSchemeModuleFunctor B S hS X A ≅
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf B S hS X)).ι ⋙ chartZariskiModule B S hS X A :=
  chartSchemeModuleFunctorIsoRestrictModule B S hS X A ≪≫
    chartSchemeEtaleModuleFunctorRestrictIso B S hS X A

/-- **The chart transport at the identity chart of a represented algebraic space is fully
faithful on quasi-coherent modules.**  Through
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` it is the restriction to the slice at the
identity chart, which is terminal. -/
def C1573.chartSchemeModuleFunctorFullyFaithfulIdEtaleChart (U : BigFppfOver B S hS) :
    (chartSchemeModuleFunctor B S hS (schemeSpace U)
      (idEtaleChart B S hS U)).FullyFaithful :=
  let Y : AlgebraicSpaces B S hS := schemeSpace U
  let A := idEtaleChart B S hS U
  let hO := Stacks.SheafOfModules.C1573.overFunctorFullyFaithfulOfIsTerminal
    (structureRingSheaf B S hS Y) (isTerminalIdEtaleChart B S hS U)
  let hR : (chartSchemeRestrictionFunctor B S hS Y A).FullyFaithful :=
    hO.comp (chartModuleReindexEquivalence B S hS Y A).fullyFaithfulFunctor
  let h1 : ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS Y)).ι ⋙ chartSchemeRestrictionFunctor B S hS Y A).FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp hR
  let h2 : (chartSmallEtaleQcohFunctor B S hS Y A).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
      (h1.ofIso (ObjectProperty.liftCompιIso _ _ _).symm)
  (h2.comp (representedQuasicoherentSchemeEquivalence B S hS
    ((SmallEtale.toOver B S hS Y.1).obj A)).fullyFaithfulInverse).comp
    (ObjectProperty.fullyFaithfulι _)

/-- **The Zariski restriction along the identity chart of a represented algebraic space is fully
faithful on quasi-coherent modules.** -/
def C1573.chartZariskiModuleFullyFaithfulIdEtaleChart (U : BigFppfOver B S hS) :
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf B S hS (schemeSpace U))).ι ⋙
      chartZariskiModule B S hS (schemeSpace U)
        (idEtaleChart B S hS U)).FullyFaithful :=
  Functor.FullyFaithful.ofIso (chartSchemeModuleFunctorFullyFaithfulIdEtaleChart B S hS U)
    (chartZariskiModuleQcohIso B S hS (schemeSpace U)
      (idEtaleChart B S hS U))

end AlgebraicGeometry.Space

end
