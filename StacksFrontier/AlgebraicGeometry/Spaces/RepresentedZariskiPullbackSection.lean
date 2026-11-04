module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartProjectionSpellingAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnitTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePushforwardSquareSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentablePushforwardChartSections

/-!
# The base-change comparison of the represented Zariski reading, on pulled-back sections

For `g : T' ⟶ T` in the big fppf category over `S` and a quasi-coherent module `P` on the small
étale site of `yoneda.obj T`, `AlgebraicGeometry.Space.representedZariskiModulePullbackIso`
identifies `r^*(P|_{T_Zar})` with `(φ^*P)|_{T'_Zar}`, where `r` is the morphism of schemes and `φ`
the morphism of represented algebraic spaces underlying `g`. Both sides are built from adjunctions,
and nothing computed the identification on sections.  This file computes it on a pulled-back
global section: it is a restriction of the chart section
`AlgebraicGeometry.Space.modulePullbackChartSection` of `φ^*` at the base-changed chart.

## Main results

* `AlgebraicGeometry.SmallEtale.unit_comp_pushforward_map_restrictModulePullbackObjIso_hom`: the
  adjunct of `r^*(𝒢|_{Y_Zar}) ≅ (ε_a^*𝒢)|_{X_Zar}` along `r^* ⊣ r_*` is the Zariski restriction of
  the unit of `ε_a^* ⊣ ε_{a*}`, and
  `AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_hom_app_pullbackSection` its value on
  a pulled-back global section.
* `AlgebraicGeometry.Space.representedUnitTransport_eq`: the scheme-side unit transported through
  `AlgebraicGeometry.Space.representedModulePullbackIso` is the space-side unit.
* `AlgebraicGeometry.Space.representedModulePushforwardSquareIso_inv_spaceUnit`: the inverse of the
  square of direct images on the space-side unit is the chart section at the base-changed chart.
* `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_hom_pullbackSection_eq_restrict`:
  **the comparison on a pulled-back global section is a restriction of the chart section.**

## Implementation notes

The objects of the small étale sites are built from pullbacks and from the comparison equivalence
of the small étale sites of `yoneda.obj T` and of `T`; when a type check has to compare two
spellings of an object, the unifier unfolds those constructions.  Every step is therefore a
declaration of its own with an explicit statement, and the steps that compare sections across the
square of direct images are elaborated with `AlgebraicGeometry.Space.smallBaseChange`,
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` and the structure sheaves locally
irreducible, which none of those comparisons needs to unfold.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.SheafOfModules

universe w u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- The inverse counit of the module equivalence along a site equivalence, followed by the
restriction along the inverse counit of the site equivalence, is the identity. -/
theorem reindexEquivalence_counitInv_restrict (P : _root_.SheafOfModules.{w} (reindexRing J' e R))
    (V : C) (y : P.val.obj (op (e.inverse.obj V))) :
    ((reindexEquivalence e R).inverse.obj P).val.map (e.counitInv.app V).op
      (((reindexEquivalence e R).counitInv.app P).val.app (op (e.inverse.obj V)) y) = y := by
  change P.val.map (e.inverse.map (e.counitInv.app V)).op
    (P.val.map (e.unitInv.app (e.inverse.obj V)).op y) = y
  rw [← PresheafOfModules.map_comp_apply]
  refine (PresheafOfModules.congr_map_apply P.val (show
    (e.unitInv.app (e.inverse.obj V)).op ≫ (e.inverse.map (e.counitInv.app V)).op = 𝟙 _ by
      rw [← op_comp]; simp) y).trans ?_
  rw [P.val.map_id]
  rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **The adjunct of `r^*(𝒢|_{Y_Zar}) ≅ (ε_a^*𝒢)|_{X_Zar}`** along `r^* ⊣ r_*`: it is the
restriction to `Y_Zar` of the unit of `ε_a^* ⊣ ε_{a*}`, followed by the comparison of the two
composite restrictions. -/
theorem unit_comp_pushforward_map_restrictModulePullbackObjIso_hom
    (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)) (hM : M.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).unit.app
          ((restrictModule B Y.obj Y.property).obj M) ≫
        (Scheme.Modules.pushforward (schemeHom B a)).map
          (restrictModulePullbackObjIso B a M hM).hom =
      (restrictModule B Y.obj Y.property).map
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing B a)).unit.app M) ≫
        (baseChangeRestrictIso B a).hom.app
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M) := by
  have hdef : (restrictModulePullbackObjIso B a M hM).hom =
      (associatedModuleAdjunction B X.obj X.property).unit.app
          ((Scheme.Modules.pullback (schemeHom B a)).obj
            ((restrictModule B Y.obj Y.property).obj M)) ≫
        (restrictModule B X.obj X.property).map
          ((associatedModuleObjBaseChangeIso B a ((restrictModule B Y.obj Y.property).obj M)).hom ≫
            (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
              ((associatedModuleAdjunction B Y.obj Y.property).counit.app M)) := rfl
  have hz : (Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).unit.app
          ((restrictModule B Y.obj Y.property).obj M) ≫
        (Scheme.Modules.pushforward (schemeHom B a)).map
          ((associatedModuleAdjunction B X.obj X.property).unit.app
            ((Scheme.Modules.pullback (schemeHom B a)).obj
              ((restrictModule B Y.obj Y.property).obj M))) =
      (zariskiRouteAdjunction B a).unit.app ((restrictModule B Y.obj Y.property).obj M) :=
    (Adjunction.comp_unit_app _ _ _).symm
  have he : (etaleRouteAdjunction B a).unit.app ((restrictModule B Y.obj Y.property).obj M) =
      (associatedModuleAdjunction B Y.obj Y.property).unit.app
          ((restrictModule B Y.obj Y.property).obj M) ≫
        (restrictModule B Y.obj Y.property).map
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing B a)).unit.app
            ((associatedModule B Y.obj Y.property).obj
              ((restrictModule B Y.obj Y.property).obj M))) :=
    Adjunction.comp_unit_app _ _ _
  have hbc := unit_comp_associatedModuleObjBaseChangeIso B a
    ((restrictModule B Y.obj Y.property).obj M)
  have hnat := (baseChangeRestrictIso B a).hom.naturality
    ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
      ((associatedModuleAdjunction B Y.obj Y.property).counit.app M))
  have hunit := (SheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallEtaleStructureMapRing B a)).unit.naturality
      ((associatedModuleAdjunction B Y.obj Y.property).counit.app M)
  have htri := (associatedModuleAdjunction B Y.obj Y.property).right_triangle_components M
  have hbc' : (zariskiRouteAdjunction B a).unit.app ((restrictModule B Y.obj Y.property).obj M) ≫
      (Scheme.Modules.pushforward (schemeHom B a)).map ((restrictModule B X.obj X.property).map
        (associatedModuleObjBaseChangeIso B a ((restrictModule B Y.obj Y.property).obj M)).hom) =
      (etaleRouteAdjunction B a).unit.app ((restrictModule B Y.obj Y.property).obj M) ≫
        (baseChangeRestrictIso B a).hom.app
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj
            ((associatedModule B Y.obj Y.property).obj
              ((restrictModule B Y.obj Y.property).obj M))) := hbc
  have hnat' : (baseChangeRestrictIso B a).hom.app
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj
            ((associatedModule B Y.obj Y.property).obj
              ((restrictModule B Y.obj Y.property).obj M))) ≫
        (Scheme.Modules.pushforward (schemeHom B a)).map ((restrictModule B X.obj X.property).map
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
            ((associatedModuleAdjunction B Y.obj Y.property).counit.app M))) =
      (restrictModule B Y.obj Y.property).map
          ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).map
            ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
              ((associatedModuleAdjunction B Y.obj Y.property).counit.app M))) ≫
        (baseChangeRestrictIso B a).hom.app
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M) := hnat.symm
  have hunit' : (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B a)).unit.app
          ((associatedModule B Y.obj Y.property).obj
            ((restrictModule B Y.obj Y.property).obj M)) ≫
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).map
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
            ((associatedModuleAdjunction B Y.obj Y.property).counit.app M)) =
      (associatedModuleAdjunction B Y.obj Y.property).counit.app M ≫
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B a)).unit.app M := hunit.symm
  rw [hdef, Functor.map_comp, ← Category.assoc, hz, Functor.map_comp, Functor.map_comp,
    ← Category.assoc, hbc', Category.assoc, hnat', he, Category.assoc, ← Category.assoc
      ((restrictModule B Y.obj Y.property).map _), ← Functor.map_comp, hunit', Functor.map_comp,
    ← Category.assoc, ← Category.assoc, htri]
  exact congrArg (· ≫ _) (Category.id_comp _)

/-- The restriction maps of the Zariski restriction of a module on the small étale site are its
restriction maps along the inclusion of opens. -/
theorem restrictModule_obj_val_map {Z : B.Scheme}
    (N : SheafOfModules.{u} (structureSheaf B Z.obj Z.property)) {U V : Z.obj.Opens}
    (h : U ⟶ V) (z : N.val.obj (op ((opensToSmallEtale B Z.obj Z.property).obj V))) :
    ((restrictModule B Z.obj Z.property).obj N).val.map h.op z =
      N.val.map ((opensToSmallEtale B Z.obj Z.property).map h).op z :=
  rfl

/-- Restricting to the top object of `X` after the base-change identification. -/
theorem restrictModule_map_topBaseChange
    (N : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (w : N.val.obj (op ((smallEtaleBaseChange B a).obj (opensObj B Y.obj Y.property ⊤)))) :
    ((restrictModule B X.obj X.property).obj N).val.map
        (homOfLE (le_top : (⊤ : X.obj.Opens) ≤ schemeHom B a ⁻¹ᵁ ⊤)).op
        (N.val.map (baseChangeOpensObjIso B a ⊤).hom.op w) =
      N.val.map ((baseChangeOpensObjIso B a ⊤).hom.op ≫
        ((opensToSmallEtale B X.obj X.property).map
          (homOfLE (le_top : (⊤ : X.obj.Opens) ≤ schemeHom B a ⁻¹ᵁ ⊤))).op) w :=
  (restrictModule_obj_val_map B N (homOfLE (le_top : (⊤ : X.obj.Opens) ≤ schemeHom B a ⁻¹ᵁ ⊤))
    (N.val.map (baseChangeOpensObjIso B a ⊤).hom.op w)).trans
    (PresheafOfModules.map_comp_apply N.val (baseChangeOpensObjIso B a ⊤).hom.op
      ((opensToSmallEtale B X.obj X.property).map
        (homOfLE (le_top : (⊤ : X.obj.Opens) ≤ schemeHom B a ⁻¹ᵁ ⊤))).op w).symm

/-- The comparison at the preimage of the top open, on the unit. -/
theorem restrictModulePullbackObjIso_hom_unit_top
    (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)) (hM : M.IsQuasicoherentOnSite)
    (s : ((restrictModule B Y.obj Y.property).obj M).val.obj (op ⊤)) :
    (restrictModulePullbackObjIso B a M hM).hom.val.app (op (schemeHom B a ⁻¹ᵁ ⊤))
        ((((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).unit.app
          ((restrictModule B Y.obj Y.property).obj M))).val.app (op ⊤) s) =
      ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M).val.map
        (baseChangeOpensObjIso B a ⊤).hom.op
        (((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B a)).unit.app M).val.app
          (op (opensObj B Y.obj Y.property ⊤)) s) :=
  congrArg (fun φ => φ.val.app (op ⊤) s)
    (unit_comp_pushforward_map_restrictModulePullbackObjIso_hom B a M hM)

/-- The comparison on a pulled-back section, by naturality. -/
theorem restrictModulePullbackObjIso_hom_app_pullbackSection_eq
    (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)) (hM : M.IsQuasicoherentOnSite)
    (s : ((restrictModule B Y.obj Y.property).obj M).val.obj (op ⊤)) :
    (restrictModulePullbackObjIso B a M hM).hom.app ⊤
        (pullbackSectionHom (schemeHom B a) ((restrictModule B Y.obj Y.property).obj M) ⊤ ⊤
          le_top s) =
      ((restrictModule B X.obj X.property).obj
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M)).val.map
        (homOfLE (le_top : (⊤ : X.obj.Opens) ≤ schemeHom B a ⁻¹ᵁ ⊤)).op
        ((restrictModulePullbackObjIso B a M hM).hom.val.app (op (schemeHom B a ⁻¹ᵁ ⊤))
          ((((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).unit.app
            ((restrictModule B Y.obj Y.property).obj M))).val.app (op ⊤) s)) :=
  PresheafOfModules.naturality_apply (restrictModulePullbackObjIso B a M hM).hom.val
    (homOfLE (le_top : (⊤ : X.obj.Opens) ≤ schemeHom B a ⁻¹ᵁ ⊤)).op
    ((((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).unit.app
      ((restrictModule B Y.obj Y.property).obj M))).val.app (op ⊤) s)

/-- **`r^*(𝒢|_{Y_Zar}) ≅ (ε_a^*𝒢)|_{X_Zar}` on a pulled-back global section**: it is the unit of
`ε_a^* ⊣ ε_{a*}` at the top object, restricted to the top object of `X`. -/
theorem restrictModulePullbackObjIso_hom_app_pullbackSection
    (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)) (hM : M.IsQuasicoherentOnSite)
    (s : ((restrictModule B Y.obj Y.property).obj M).val.obj (op ⊤)) :
    (restrictModulePullbackObjIso B a M hM).hom.app ⊤
        (pullbackSectionHom (schemeHom B a) ((restrictModule B Y.obj Y.property).obj M) ⊤ ⊤
          le_top s) =
      ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M).val.map
        ((baseChangeOpensObjIso B a ⊤).hom.op ≫
          ((opensToSmallEtale B X.obj X.property).map
          (homOfLE (le_top : (⊤ : X.obj.Opens) ≤ schemeHom B a ⁻¹ᵁ ⊤))).op)
        (((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B a)).unit.app M).val.app
          (op (opensObj B Y.obj Y.property ⊤)) s) :=
  (restrictModulePullbackObjIso_hom_app_pullbackSection_eq B a M hM s).trans
    ((congrArg (fun z => ((restrictModule B X.obj X.property).obj
      ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M)).val.map
        (homOfLE (le_top : (⊤ : X.obj.Opens) ≤ schemeHom B a ⁻¹ᵁ ⊤)).op z)
      (restrictModulePullbackObjIso_hom_unit_top B a M hM s)).trans
      (restrictModule_map_topBaseChange B a
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M) _))

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

/-- Four restriction maps of a presheaf of modules compose. -/
theorem presheafOfModules_map_comp₄_apply {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) {X₀ X₁ X₂ X₃ X₄ : C} (a : X₁ ⟶ X₀) (b : X₂ ⟶ X₁)
    (c : X₃ ⟶ X₂) (d : X₄ ⟶ X₃) (x : M.obj (op X₀)) :
    M.map d.op (M.map c.op (M.map b.op (M.map a.op x))) = M.map (d ≫ c ≫ b ≫ a).op x := by
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply,
    ← PresheafOfModules.map_comp_apply]
  rfl

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section ChartIso

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hrep : yoneda.relativelyRepresentable f.hom)

/-- The chart diagram of the base change of a chart along a representable morphism. -/
def chartDiagramOfSmallBaseChange (V : SmallEtale B S hS Y.1) :
    ChartDiagram B S hS X.1 Y.1 f.hom where
  U := (smallBaseChange B S hS f hrep).obj V
  V := V
  g := hrep.snd V.1.hom
  comm := hrep.w V.1.hom

/-- **The unit of `f^* ⊣ f_*` read across the chart comparison of the direct images is the chart
section at the base-changed chart.** -/
theorem modulePushforwardChartIso_hom_unit_val_app (M : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS Y.1) (x : M.val.obj (op V)) :
    ((modulePushforwardChartIso B S hS f hrep).hom.app ((modulePullback B S hS f).obj M)).val.app
        (op V) (((modulePullbackAdjunction B S hS f).unit.app M).val.app (op V) x) =
      modulePullbackChartSection B S hS f M (chartDiagramOfSmallBaseChange f hrep V) x := by
  refine (modulePushforwardChartIso_hom_app_chartSetProj B S hS f hrep _ V _).trans ?_
  refine (chartSetProj_modulePullbackAdjunction_unit B S hS f hrep M V x).trans ?_
  refine (chartSetProj_eq_moduleChartProjection B S hS f hrep _ V _).trans ?_
  rfl

end ChartIso

section Represented

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (P : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))

/-- The unit of `ε^* ⊣ ε_*` followed by the direct image of the inverse of
`representedModulePullbackIso`. -/
abbrev representedUnitTransport :
    (representedSmallEtaleModuleEquivalence B S hS T).inverse.obj P ⟶
      (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).obj
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj
          ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P)) :=
  (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS g)).unit.app
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj P) ≫
    (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).map
      ((representedModulePullbackIso B S hS g hg).inv.app P)

/-- **The scheme-side unit transported, read on `yoneda.obj T`, is the space-side unit.** -/
theorem representedUnitTransport_eq :
    (representedSmallEtaleModuleEquivalence B S hS T).counitInv.app P ≫
      (representedSmallEtaleModuleEquivalence B S hS T).functor.map
        ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS g)).unit.app
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj P)) ≫
      (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) ⋙
          (representedSmallEtaleModuleEquivalence B S hS T).functor).map
        ((representedModulePullbackIso B S hS g hg).inv.app P) ≫
      (representedModulePushforwardSquareIso B S hS g hg).hom.app
        ((modulePullback B S hS (representedSpaceMap B S hS g) ⋙
          (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj P) =
    (representedSpaceRouteAdjunction B S hS g).unit.app P := by
  have h := NatTrans.congr_app (unit_comp_representedModulePullbackIso_inv B S hS g hg) P
  have hsch : (representedSchemeRouteAdjunction B S hS g hg).unit.app P =
      ((representedSmallEtaleModuleEquivalence B S hS T).counitInv.app P ≫
        (representedSmallEtaleModuleEquivalence B S hS T).functor.map
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS g)).unit.app
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj P))) ≫
        (representedModulePushforwardSquareIso B S hS g hg).hom.app
          ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).obj
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj P)) :=
    rfl
  have hnat := (representedModulePushforwardSquareIso B S hS g hg).hom.naturality
    (show (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).obj
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj P) ⟶
      (modulePullback B S hS (representedSpaceMap B S hS g) ⋙
          (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj P from
      (representedModulePullbackIso B S hS g hg).inv.app P)
  refine Eq.trans ?_ h
  refine Eq.trans ?_ (congrArg (· ≫ (Functor.whiskerRight
    (representedModulePullbackIso B S hS g hg).inv
      ((representedSmallEtaleModuleEquivalence B S hS T').functor ⋙
        modulePushforward B S hS (representedSpaceMap B S hS g))).app P) hsch).symm
  exact (whisker_eq _ (whisker_eq _ hnat)).trans
    ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm)

/-- The étale object of the scheme of `T` cut out by the top open. -/
abbrev topEtaleObj (T : BigFppfOver B S hS) :
    _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property :=
  (_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj ⊤

/-- The chart of `yoneda.obj T` which the top open becomes. -/
abbrev topRepChart (T : BigFppfOver B S hS) : SmallEtale B S hS (yoneda.obj T) :=
  (representedSmallEtaleEquivalence B S hS T).inverse.obj (topEtaleObj T)

/-- **The transported unit on the top étale object.** -/
theorem representedUnitTransport_top (s : P.val.obj (op (topRepChart T))) :
    (representedUnitTransport g hg P).val.app (op (topEtaleObj T)) s =
      ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).obj
          ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P))).val.map
        ((representedSmallEtaleEquivalence B S hS T).counitInv.app (topEtaleObj T)).op
        (((representedModulePushforwardSquareIso B S hS g hg).inv.app
          ((modulePullback B S hS (representedSpaceMap B S hS g) ⋙
            (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj P)).val.app
          (op (topRepChart T))
          (((representedSpaceRouteAdjunction B S hS g).unit.app P).val.app
            (op (topRepChart T)) s)) := by
  refine (congrArg (fun z => (representedUnitTransport g hg P).val.app (op (topEtaleObj T)) z)
    (Stacks.SheafOfModules.reindexEquivalence_counitInv_restrict
      (representedSmallEtaleEquivalence B S hS T) (representedSchemeStructureSheaf B S hS T)
      P (topEtaleObj T) s).symm).trans ?_
  refine (PresheafOfModules.naturality_apply (representedUnitTransport g hg P).val
    ((representedSmallEtaleEquivalence B S hS T).counitInv.app (topEtaleObj T)).op
    (((representedSmallEtaleModuleEquivalence B S hS T).counitInv.app P).val.app
      (op (topRepChart T)) s)).trans ?_
  exact congrArg _ ((sheafOfModules_iso_hom_inv_apply
    ((representedModulePushforwardSquareIso B S hS g hg).app
      ((modulePullback B S hS (representedSpaceMap B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj P))
    (op (topRepChart T)) _).symm.trans
    (congrArg (fun z => ((representedModulePushforwardSquareIso B S hS g hg).inv.app
      ((modulePullback B S hS (representedSpaceMap B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj P)).val.app
      (op (topRepChart T)) z)
      (congrArg (fun m => m.val.app (op (topRepChart T)) s) (representedUnitTransport_eq g hg P))))

/-- **The comparison `r^*(F|_{T_Zar}) ≅ (φ^*F)|_{T'_Zar}` on a pulled-back global section**: the
transported unit at the top étale object, restricted to the top étale object of `T'`. -/
theorem representedZariskiModulePullbackIso_hom_app_pullbackSection
    (hP : P.IsQuasicoherentOnSite) (s : P.val.obj (op (topRepChart T))) :
    (representedZariskiModulePullbackIso B S hS g hg P hP).hom.app ⊤
        (pullbackSectionHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)
          (representedZariskiModule B S hS T P) ⊤ ⊤ le_top s) =
      ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj
          ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P)).val.map
        ((_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensObjIso (associatedBigEtaleSite B)
            g.left ⊤).hom.op ≫
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
            (homOfLE (le_top : (⊤ : ((BigFppfOver.toScheme B S hS).obj T').Opens) ≤
              _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left ⁻¹ᵁ
                ⊤))).op)
        ((representedUnitTransport g hg P).val.app (op (topEtaleObj T)) s) := by
  have hA :=
    _root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_hom_app_pullbackSection
      (associatedBigEtaleSite B) g.left
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj P)
      (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T P hP) s
  have h1 := congrArg (fun z => ((representedModulePullbackIso B S hS g hg).inv.app P).val.app
    (op ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj ⊤)) z) hA
  exact h1.trans (PresheafOfModules.naturality_apply
    ((representedModulePullbackIso B S hS g hg).inv.app P).val _ _)

end Represented

section RepresentedSections

attribute [local irreducible] AlgebraicGeometry.Space.smallBaseChange
  AlgebraicGeometry.Space.representedSmallEtaleEquivalence
  AlgebraicGeometry.Space.structurePresheaf AlgebraicGeometry.Space.structureSheaf
  AlgebraicGeometry.Space.structureSheaf'

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (P : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))

/-- The space-side unit, on sections. -/
theorem representedSpaceRouteAdjunction_unit_val_app (V : SmallEtale B S hS (yoneda.obj T))
    (s : P.val.obj (op V)) :
    ((representedSpaceRouteAdjunction B S hS g).unit.app P).val.app (op V) s =
      ((modulePushforward B S hS (representedSpaceMap B S hS g)).map
          ((representedSmallEtaleModuleEquivalence B S hS T').counitInv.app
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P))).val.app (op V)
        (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).unit.app P).val.app
          (op V) s) :=
  rfl

/-- The chart comparison of the direct images is natural. -/
theorem modulePushforwardChartIso_hom_counitInv (V : SmallEtale B S hS (yoneda.obj T))
    (w : ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P)).val.obj (op V)) :
    ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app
        ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
          ((modulePullback B S hS (representedSpaceMap B S hS g) ⋙
            (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj P))).val.app (op V)
        (((modulePushforward B S hS (representedSpaceMap B S hS g)).map
          ((representedSmallEtaleModuleEquivalence B S hS T').counitInv.app
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P))).val.app (op V) w) =
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P).val.map
          ((representedSmallEtaleEquivalence B S hS T').unitInv.app
            ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj V)).op
        (((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app
          ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P)).val.app (op V) w) :=
  congrArg (fun m => m.val.app (op V) w)
    ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.naturality
      ((representedSmallEtaleModuleEquivalence B S hS T').counitInv.app
        ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P)))

/-- **The inverse square of direct images on the space-side unit is the chart section at the
base-changed chart**, restricted along the two identifications of the base change. -/
theorem representedModulePushforwardSquareIso_inv_spaceUnit (V : SmallEtale B S hS (yoneda.obj T))
    (s : P.val.obj (op V)) :
    ((representedModulePushforwardSquareIso B S hS g hg).inv.app
        ((modulePullback B S hS (representedSpaceMap B S hS g) ⋙
          (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj P)).val.app (op V)
        (((representedSpaceRouteAdjunction B S hS g).unit.app P).val.app (op V) s) =
      ((modulePullback B S hS (representedSpaceMap B S hS g) ⋙
          (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj P).val.map
        ((representedSmallEtaleBaseChangeIso B S hS g hg).inv.app V).op
        (((modulePullback B S hS (representedSpaceMap B S hS g)).obj P).val.map
          ((representedSmallEtaleEquivalence B S hS T').unitInv.app
            ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj V)).op
          (modulePullbackChartSection B S hS (representedSpaceMap B S hS g) P
            (chartDiagramOfSmallBaseChange (representedSpaceMap B S hS g) hg V) s)) := by
  refine (representedModulePushforwardSquareIso_inv_app_val_app g hg _ V _).trans ?_
  refine congrArg (fun z => ((modulePullback B S hS (representedSpaceMap B S hS g) ⋙
    (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj P).val.map
      ((representedSmallEtaleBaseChangeIso B S hS g hg).inv.app V).op z) ?_
  refine (congrArg (fun z => ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g)
    hg).hom.app ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
      ((modulePullback B S hS (representedSpaceMap B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj P))).val.app (op V) z)
    (representedSpaceRouteAdjunction_unit_val_app g P V s)).trans ?_
  refine (modulePushforwardChartIso_hom_counitInv g hg P V _).trans ?_
  exact congrArg (fun z => ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P).val.map
    ((representedSmallEtaleEquivalence B S hS T').unitInv.app
      ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj V)).op z)
    (modulePushforwardChartIso_hom_unit_val_app (representedSpaceMap B S hS g) hg P V s)

/-- The chart morphism from the top chart of `yoneda.obj T'` to the base change of the top chart
of `yoneda.obj T`, along which the comparison restricts. -/
abbrev representedTopBaseChangeChartHom :
    topRepChart T' ⟶ (smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj
      (topRepChart T) :=
  (representedSmallEtaleEquivalence B S hS T').inverse.map
      ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
        (homOfLE (le_top : (⊤ : ((BigFppfOver.toScheme B S hS).obj T').Opens) ≤
          _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left ⁻¹ᵁ ⊤)) ≫
        (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensObjIso (associatedBigEtaleSite B)
          g.left ⊤).hom) ≫
    (representedSmallEtaleEquivalence B S hS T').inverse.map
      ((_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) g.left).map
        ((representedSmallEtaleEquivalence B S hS T).counitInv.app (topEtaleObj T))) ≫
    (representedSmallEtaleEquivalence B S hS T').inverse.map
      ((representedSmallEtaleBaseChangeIso B S hS g hg).inv.app (topRepChart T)) ≫
    (representedSmallEtaleEquivalence B S hS T').unitInv.app
      ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj (topRepChart T))

/-- The four restrictions of the comparison, as one restriction. -/
theorem representedTopBaseChange_restrict
    (x : ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P).val.obj
      (op ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj (topRepChart T)))) :
    ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj
          ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P)).val.map
        ((_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensObjIso (associatedBigEtaleSite B)
            g.left ⊤).hom.op ≫
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
            (homOfLE (le_top : (⊤ : ((BigFppfOver.toScheme B S hS).obj T').Opens) ≤
              _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left ⁻¹ᵁ
                ⊤))).op)
        (((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).obj
          ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P))).val.map
          ((representedSmallEtaleEquivalence B S hS T).counitInv.app (topEtaleObj T)).op
          (((modulePullback B S hS (representedSpaceMap B S hS g) ⋙
              (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj P).val.map
            ((representedSmallEtaleBaseChangeIso B S hS g hg).inv.app (topRepChart T)).op
            (((modulePullback B S hS (representedSpaceMap B S hS g)).obj P).val.map
              ((representedSmallEtaleEquivalence B S hS T').unitInv.app
                ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj
                  (topRepChart T))).op x))) =
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P).val.map
        (representedTopBaseChangeChartHom g hg).op x :=
  presheafOfModules_map_comp₄_apply
    ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P).val _ _ _ _ x

/-- **The comparison `r^*(F|_{T_Zar}) ≅ (φ^*F)|_{T'_Zar}` on a pulled-back global section is a
restriction of the chart section at the base-changed chart.** -/
theorem representedZariskiModulePullbackIso_hom_pullbackSection_eq_restrict
    (hP : P.IsQuasicoherentOnSite) (s : P.val.obj (op (topRepChart T))) :
    (representedZariskiModulePullbackIso B S hS g hg P hP).hom.app ⊤
        (pullbackSectionHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)
          (representedZariskiModule B S hS T P) ⊤ ⊤ le_top s) =
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj P).val.map
        (representedTopBaseChangeChartHom g hg).op
        (modulePullbackChartSection B S hS (representedSpaceMap B S hS g) P
          (chartDiagramOfSmallBaseChange (representedSpaceMap B S hS g) hg (topRepChart T)) s) := by
  rw [representedZariskiModulePullbackIso_hom_app_pullbackSection g hg P hP s,
    representedUnitTransport_top g hg P s,
    representedModulePushforwardSquareIso_inv_spaceUnit g hg P (topRepChart T) s]
  exact representedTopBaseChange_restrict g hg P _

end RepresentedSections

end AlgebraicGeometry.Space

end
