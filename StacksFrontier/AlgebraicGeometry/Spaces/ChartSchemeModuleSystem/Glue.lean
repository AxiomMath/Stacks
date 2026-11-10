module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartQuasicoherentGlueingEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartCocycle

/-!
# Glueing quasi-coherent modules given on the schemes of the étale charts

Let `X` be an algebraic space over a scheme `S`.  A *chart-scheme module system* on `X` is a
quasi-coherent module `M_U` on the scheme of every étale chart `U` of `X`, together with an
isomorphism `τ_g : g^*M_U ≅ M_V` for every morphism `g : V ⟶ U` of étale charts, where `g^*` is
pullback of modules along the morphism of chart schemes, subject to the cocycle condition
`τ_h ∘ h^*τ_g = τ_{h ≫ g}` (through `AlgebraicGeometry.Scheme.Modules.pullbackComp`).  This file
glues such a system into an `𝒪_X`-module on the small étale site of `X`, proves it
quasi-coherent, and reads it back on every chart scheme.

The glueing is the equivalence of Stacks 03LY: the scheme module `M_U` is read on the
represented algebraic space of the chart through Stacks 03DX (2)
(`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`), the transitions are
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso` followed by the image of
`τ_g`, and their cocycle condition is the composition law
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_comp` together with its
naturality `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_naturality` and the
cocycle condition of `τ`.  The glued module is the inverse of
`AlgebraicGeometry.Space.chartModuleGlueingEquivalence` at that glueing datum.

## Main definitions

* `AlgebraicGeometry.Space.IsChartSchemeModuleCocycle`: the cocycle condition on the transitions.
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem`: a chart-scheme module system.
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.glueingData`: its chartwise glueing datum of
  Stacks 03LY.
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.glue`: the glued `𝒪_X`-module.
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.restrictToChartSchemeGlueIso`: the
  restriction of the glued module to the scheme of a chart `U` is `M_U`.

## Main results

* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.chartTransition_cocycle`: the transitions
  satisfy the cocycle condition of Stacks 03LY.
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.isQuasicoherentOnSite_glue`: the glued module
  is quasi-coherent.
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.glueChartModuleIso_hom_transition`: the
  identification of the chart restrictions of the glued module with the chart modules carries
  the canonical transitions of the restrictions to the transitions of the system.

## Implementation notes

The chartwise pullback `AlgebraicGeometry.Space.chartModuleInverseImage g` of the cocycle
condition and the inverse image `modulePullback (representedSpaceMap g)` in which the
identification `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso` is stated are
the same functor by `rfl`, but a comparison of `F.map φ` with `F'.map φ` for the two spellings
does not terminate within the heartbeat budget: the elaborator unfolds the functors under the
projection instead of comparing them.  So every input of the cocycle is passed as an equation of
*isomorphisms*, built with `CategoryTheory.Functor.mapIso` and `CategoryTheory.Iso.trans`, which
are compared argument by argument, and the projection to morphisms is taken only inside the
abstract pasting lemma, at variables.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The cocycle condition of a chart-scheme module system.**  For composable morphisms
`h : W ⟶ V` and `g : V ⟶ U` of étale charts of `X`, the transition `τ_h` after the pullback
`h^*τ_g` is the transition `τ_{h ≫ g}`, read through the composition comparison
`AlgebraicGeometry.Scheme.Modules.pullbackComp` of pullbacks of modules on schemes. -/
def IsChartSchemeModuleCocycle (M : ∀ U : SmallEtale B S hS X.1, (chartScheme U).Modules)
    (τ : ∀ {V U : SmallEtale B S hS X.1} (g : V ⟶ U),
      (Scheme.Modules.pullback (chartSchemeMap g)).obj (M U) ≅ M V) : Prop :=
  ∀ {W V U : SmallEtale B S hS X.1} (g : V ⟶ U) (h : W ⟶ V),
    (Scheme.Modules.pullback (chartSchemeMap h)).map (τ g).hom ≫ (τ h).hom =
      (Scheme.Modules.pullbackComp (chartSchemeMap h) (chartSchemeMap g)).hom.app (M U) ≫
        (τ (h ≫ g)).hom

/-- **A chart-scheme module system on an algebraic space `X`**: a quasi-coherent module `M U` on
the scheme of every étale chart `U` of `X`, an isomorphism `τ g : g^*(M U) ≅ M V` for every
morphism `g : V ⟶ U` of étale charts, along the morphism of chart schemes, and the cocycle
condition `AlgebraicGeometry.Space.IsChartSchemeModuleCocycle`. -/
structure ChartSchemeModuleSystem where
  /-- the module on the scheme of each étale chart -/
  M : ∀ U : SmallEtale B S hS X.1, (chartScheme U).Modules
  /-- each chart module is quasi-coherent -/
  isQuasicoherent : ∀ U : SmallEtale B S hS X.1, SheafOfModules.IsQuasicoherent (M U)
  /-- the transition isomorphisms `g^*(M U) ≅ M V` -/
  τ : ∀ {V U : SmallEtale B S hS X.1} (g : V ⟶ U),
    (Scheme.Modules.pullback (chartSchemeMap g)).obj (M U) ≅ M V
  /-- the cocycle condition -/
  cocycle : IsChartSchemeModuleCocycle B S hS X M τ

namespace ChartSchemeModuleSystem

variable {B S hS X} (𝓜 : ChartSchemeModuleSystem B S hS X)

/-- The chart module `M U`, as an object of the category of quasi-coherent modules on the chart
scheme. -/
abbrev qcohObj (U : SmallEtale B S hS X.1) :
    (SheafOfModules.isQuasicoherent (chartScheme U).ringCatSheaf).FullSubcategory :=
  ⟨𝓜.M U, 𝓜.isQuasicoherent U⟩

/-- The chart module `M U` read as an `𝒪`-module on the small étale site of the algebraic space
represented by the chart, through Stacks 03DX (2). -/
def chartModule (U : SmallEtale B S hS X.1) :
    Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2 :=
  ((representedQuasicoherentSchemeEquivalence B S hS (chartFppfObject B S hS X U)).functor.obj
    (𝓜.qcohObj U)).obj

/-- The chart module read on the represented algebraic space is quasi-coherent. -/
theorem isQuasicoherentOnSite_chartModule (U : SmallEtale B S hS X.1) :
    (𝓜.chartModule U).IsQuasicoherentOnSite :=
  ((representedQuasicoherentSchemeEquivalence B S hS (chartFppfObject B S hS X U)).functor.obj
    (𝓜.qcohObj U)).property

/-- The transition `τ g` as an isomorphism of quasi-coherent modules on the chart scheme. -/
abbrev qcohTransition {V U : SmallEtale B S hS X.1} (g : V ⟶ U) :
    quasicoherentPullbackObj B S hS ((SmallEtale.toOver B S hS X.1).map g) (𝓜.qcohObj U) ≅
      𝓜.qcohObj V :=
  ObjectProperty.isoMk _ (𝓜.τ g)

/-- **The transitions of the glueing datum**: for a morphism `f : V ⟶ U` of étale charts, the
inverse image of Stacks 03LU of the module attached to `M U` is the module attached to `f^*(M U)`
(`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`), which is the module
attached to `M V` through `τ f`. -/
def chartTransition {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartModuleInverseImage B S hS X f).obj (𝓜.chartModule U) ≅ 𝓜.chartModule V :=
  modulePullbackRepresentedQuasicoherentIso B S hS ((SmallEtale.toOver B S hS X.1).map f)
      (𝓜.qcohObj U) ≪≫
    (ObjectProperty.ι _).mapIso
      ((representedQuasicoherentSchemeEquivalence B S hS
        (chartFppfObject B S hS X V)).functor.mapIso (𝓜.qcohTransition f))

/-- The pasting of the three squares behind the cocycle condition, at variables. -/
private theorem cocycle_aux {C D D' : Type*} [Category C] [Category D] [Category D']
    (F₁ : D' ⥤ D) (F : D ⥤ C) (H : D' ⥤ C) (α β : F₁ ⋙ F ≅ H) (hαβ : α = β) (M : D')
    {P₀' P₀'' : D} {R R' T K : C}
    (A : F₁.obj M ≅ P₀') (Bi : P₀' ≅ P₀'') (φb : F.obj P₀'' ≅ R) (y : R ≅ R')
    (φbq : F.obj P₀' ≅ T) (z : T ≅ R) (k : T ≅ K) (φba : H.obj M ≅ K) (w : K ≅ R')
    (hnat : F.mapIso Bi ≪≫ φb = φbq ≪≫ z)
    (hcomp : β.app M ≪≫ φba = F.mapIso A ≪≫ φbq ≪≫ k)
    (hτ : k.inv ≫ z.hom ≫ y.hom = w.hom) :
    F.map (A ≪≫ Bi).hom ≫ (φb ≪≫ y).hom = α.hom.app M ≫ (φba ≪≫ w).hom := by
  subst hαβ
  have hnat' : F.map Bi.hom ≫ φb.hom = φbq.hom ≫ z.hom := by
    simpa only [Iso.trans_hom, Functor.mapIso_hom] using congrArg Iso.hom hnat
  have hcomp' : α.hom.app M ≫ φba.hom = F.map A.hom ≫ φbq.hom ≫ k.hom := by
    simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] using congrArg Iso.hom hcomp
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [← hτ, reassoc_of% hcomp', reassoc_of% hnat', Iso.hom_inv_id_assoc]

/-- The cocycle condition of `τ` read in the category of quasi-coherent modules on the smallest
chart scheme. -/
private theorem qcohTransition_cocycle {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    (quasicoherentPullbackCompIso B S hS ((SmallEtale.toOver B S hS X.1).map g)
        ((SmallEtale.toOver B S hS X.1).map f) (𝓜.qcohObj U)).inv ≫
      quasicoherentPullbackMap B S hS ((SmallEtale.toOver B S hS X.1).map g)
        (𝓜.qcohTransition f).hom ≫ (𝓜.qcohTransition g).hom =
      (𝓜.qcohTransition (g ≫ f)).hom := by
  have h := 𝓜.cocycle f g
  ext1
  change (Scheme.Modules.pullbackComp (chartSchemeMap g) (chartSchemeMap f)).inv.app (𝓜.M U) ≫
      (Scheme.Modules.pullback (chartSchemeMap g)).map (𝓜.τ f).hom ≫ (𝓜.τ g).hom =
    (𝓜.τ (g ≫ f)).hom
  rw [h, Iso.inv_hom_id_app_assoc]

/-- The comparison of successive chartwise pullbacks of modules is the contraction of the two
inverse images along the represented morphisms of the underlying objects of the big fppf site, on
the nose. -/
theorem chartModuleInverseImageComp_eq_representedModulePullbackCompIso
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    chartModuleInverseImageComp B S hS X f g =
      representedModulePullbackCompIso B S hS ((SmallEtale.toOver B S hS X.1).map g)
        ((SmallEtale.toOver B S hS X.1).map f) := rfl

/-- The pullback of the transition `τ f` along the morphism of schemes underlying `g`, as an
isomorphism of quasi-coherent modules. -/
abbrev qcohPullbackTransition {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    quasicoherentPullbackObj B S hS ((SmallEtale.toOver B S hS X.1).map g)
        (quasicoherentPullbackObj B S hS ((SmallEtale.toOver B S hS X.1).map f) (𝓜.qcohObj U)) ≅
      quasicoherentPullbackObj B S hS ((SmallEtale.toOver B S hS X.1).map g) (𝓜.qcohObj V) :=
  ObjectProperty.isoMk _ ((Scheme.Modules.pullback
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
      ((SmallEtale.toOver B S hS X.1).map g).left)).mapIso (𝓜.τ f))

/-- The naturality of `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso` at
the transition `τ f`, as an equation of isomorphisms. -/
private theorem chartTransition_naturality {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    (modulePullback B S hS
        (representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map g))).mapIso
        ((ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
          (chartFppfObject B S hS X V)).functor.mapIso (𝓜.qcohTransition f))) ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS ((SmallEtale.toOver B S hS X.1).map g)
          (𝓜.qcohObj V) =
      modulePullbackRepresentedQuasicoherentIso B S hS ((SmallEtale.toOver B S hS X.1).map g)
          (quasicoherentPullbackObj B S hS ((SmallEtale.toOver B S hS X.1).map f)
            (𝓜.qcohObj U)) ≪≫
        (ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
          (chartFppfObject B S hS X W)).functor.mapIso (𝓜.qcohPullbackTransition f g)) := by
  refine Iso.ext ?_
  exact modulePullbackRepresentedQuasicoherentIso_naturality B S hS
    ((SmallEtale.toOver B S hS X.1).map g) (𝓜.qcohTransition f).hom

/-- The cocycle condition of `τ`, read through the module attached on the represented space of
the smallest chart. -/
private theorem chartTransition_schemeCocycle {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    ((ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
          (chartFppfObject B S hS X W)).functor.mapIso
          (quasicoherentPullbackCompIso B S hS ((SmallEtale.toOver B S hS X.1).map g)
            ((SmallEtale.toOver B S hS X.1).map f) (𝓜.qcohObj U)))).inv ≫
        ((ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
          (chartFppfObject B S hS X W)).functor.mapIso (𝓜.qcohPullbackTransition f g))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS
          (chartFppfObject B S hS X W)).functor.map (𝓜.qcohTransition g).hom).hom =
      ((representedQuasicoherentSchemeEquivalence B S hS
          (chartFppfObject B S hS X W)).functor.map (𝓜.qcohTransition (g ≫ f)).hom).hom := by
  have hτ0 := congrArg (fun φ ↦ ((representedQuasicoherentSchemeEquivalence B S hS
      (chartFppfObject B S hS X W)).functor.map φ).hom) (𝓜.qcohTransition_cocycle f g)
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] at hτ0
  exact hτ0

/-- **The cocycle condition of Stacks 03LY for the transitions of a chart-scheme module system**,
written out at two composable morphisms of étale charts. -/
theorem chartTransition_cocycle {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    (chartModuleInverseImage B S hS X g).map (𝓜.chartTransition f).hom ≫
        (𝓜.chartTransition g).hom =
      chartModuleInverseImageCompApp B S hS X f g (𝓜.chartModule U) ≫
        (𝓜.chartTransition (g ≫ f)).hom := by
  rw [chartModuleInverseImageCompApp_eq]
  exact cocycle_aux (chartModuleInverseImage B S hS X f) (chartModuleInverseImage B S hS X g)
    (chartModuleInverseImage B S hS X (g ≫ f)) _ _
    (chartModuleInverseImageComp_eq_representedModulePullbackCompIso f g)
    (𝓜.chartModule U) _ _ _ _ _ _ _ _ _ (𝓜.chartTransition_naturality f g)
    (modulePullbackRepresentedQuasicoherentIso_comp B S hS
      ((SmallEtale.toOver B S hS X.1).map g) ((SmallEtale.toOver B S hS X.1).map f)
      (𝓜.qcohObj U)) (𝓜.chartTransition_schemeCocycle f g)

/-- **The cocycle condition of Stacks 03LY for the transitions of a chart-scheme module
system**, as a term of the predicate. -/
theorem isChartModuleCocycle_chartTransition :
    IsChartModuleCocycle B S hS X 𝓜.chartModule (fun f ↦ 𝓜.chartTransition f) :=
  fun f g ↦ 𝓜.chartTransition_cocycle f g

/-- **The chartwise glueing datum of Stacks 03LY of a chart-scheme module system.** -/
def glueingData : ChartModuleGlueingData B S hS X :=
  ⟨𝓜.chartModule, fun f ↦ 𝓜.chartTransition f, 𝓜.isChartModuleCocycle_chartTransition⟩

/-- **The glued `𝒪_X`-module of a chart-scheme module system**: the inverse of the equivalence of
Stacks 03LY at the glueing datum of the system. -/
def glue : Modules.{u, u} B S hS X.1 X.2 :=
  (chartModuleGlueingEquivalence B S hS X).inverse.obj 𝓜.glueingData

/-- The component at a chart of an isomorphism of chartwise glueing data. -/
def _root_.AlgebraicGeometry.Space.ChartModuleGlueingData.isoApp
    {D E : ChartModuleGlueingData B S hS X} (e : D ≅ E) (U : SmallEtale B S hS X.1) :
    D.sheaf U ≅ E.sheaf U where
  hom := ChartModuleGlueingData.Hom.app e.hom U
  inv := ChartModuleGlueingData.Hom.app e.inv U
  hom_inv_id := by
    rw [← ChartModuleGlueingData.comp_app, e.hom_inv_id, ChartModuleGlueingData.id_app]
  inv_hom_id := by
    rw [← ChartModuleGlueingData.comp_app, e.inv_hom_id, ChartModuleGlueingData.id_app]

/-- The chartwise glueing datum of the glued module is the glueing datum of the system: the
counit of the equivalence of Stacks 03LY. -/
def glueCanonicalIso : (chartModuleGlueingFunctor B S hS X).obj 𝓜.glue ≅ 𝓜.glueingData :=
  (chartModuleGlueingEquivalence B S hS X).counitIso.app 𝓜.glueingData

/-- The restriction of the glued module to the small étale site of the represented space of a
chart is the chart module read there: the counit of the equivalence of Stacks 03LY. -/
def glueChartModuleIso (U : SmallEtale B S hS X.1) :
    (chartModuleRestriction B S hS X U).obj 𝓜.glue ≅ 𝓜.chartModule U :=
  ChartModuleGlueingData.isoApp 𝓜.glueCanonicalIso U

/-- **The identification of the chart restrictions of the glued module with the chart modules is
compatible with the transitions**: it carries the canonical transition of the restrictions of
the glued module along a morphism `f : V ⟶ U` of charts
(`AlgebraicGeometry.Space.chartModuleRestrictionTransitions`) to the transition
`AlgebraicGeometry.Space.ChartSchemeModuleSystem.chartTransition` of the system.  This is the
counit of Stacks 03LY being a morphism of glueing data. -/
theorem glueChartModuleIso_hom_transition {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartModuleInverseImage B S hS X f).map (𝓜.glueChartModuleIso U).hom ≫
        (𝓜.chartTransition f).hom =
      (chartModuleRestrictionTransitions B S hS X 𝓜.glue f).hom ≫
        (𝓜.glueChartModuleIso V).hom :=
  ChartModuleGlueingData.Hom.w 𝓜.glueCanonicalIso.hom f

/-- **The glued module is quasi-coherent**: its restriction to every étale chart is the
quasi-coherent module attached to the chart module. -/
theorem isQuasicoherentOnSite_glue : 𝓜.glue.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_forall_chartModuleRestriction B S hS X _).2 fun U ↦
    SheafOfModules.IsQuasicoherentOnSite.of_iso (𝓜.glueChartModuleIso U).symm
      (𝓜.isQuasicoherentOnSite_chartModule U)

/-- **The glued module restricted to the scheme of a chart is the chart module**:
`restrictToChartScheme (glue M) U ≅ M U`. -/
def restrictToChartSchemeGlueIso (U : SmallEtale B S hS X.1) :
    restrictToChartScheme B S hS X.1 X.2 𝓜.glue U ≅ 𝓜.M U :=
  restrictToChartSchemeIsoRestrictModule B S hS X 𝓜.glue 𝓜.isQuasicoherentOnSite_glue U ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme U) (chartFppfObject B S hS X U).left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS X U)).inverse.mapIso
        ((chartModuleRestrictionIsoChartSmallEtaleRestriction B S hS X 𝓜.glue U).symm ≪≫
          𝓜.glueChartModuleIso U)) ≪≫
    representedZariskiModuleQuasicoherentSchemeIso B S hS (chartFppfObject B S hS X U)
      (𝓜.qcohObj U)

end ChartSchemeModuleSystem

end AlgebraicGeometry.Space

end
