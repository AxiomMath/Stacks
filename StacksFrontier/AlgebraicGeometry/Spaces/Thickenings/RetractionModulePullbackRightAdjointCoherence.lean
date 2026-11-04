module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionModulePullbackNaturalityCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparisonComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseDerivedCoherence

/-!
# The right-adjoint coherence `hR` of the proof of `toLift_pullback` in Stacks 0DLL, and `MC`

`AlgebraicGeometry.Space.extensionOfScalarsCompIso_hom_eq_of_rightAdjoint` reduces the module-level
coherence `MC` to an equation `hR` of comparisons of right adjoints. This file proves `hR`
(`AlgebraicGeometry.Space.squareZeroPullbackRightAdjointIso_comp_coherence`) and so `MC`
(`AlgebraicGeometry.Space.extensionOfScalarsCompIso_hom_eq_squareZeroPullbackIso`).

The right adjoints in `hR` are read through the module equivalences of the two thickenings; an
abstract computation with the units and counits
(`Stacks.CategoryTheory.rightAdjoint_comp_eq_of_equivalence`) reduces `hR` to an equation of
direct images with no inverse equivalence in it
(`AlgebraicGeometry.Space.squareZeroPushforwardIso_comp_coherence_app`). That one is the
composition law of the chart comparisons of direct images
(`AlgebraicGeometry.Space.pushforwardModulesCompAt_trans_chartIso`) together with the compatibility
of `G2a` with the contraction of chart direct images
(`AlgebraicGeometry.Space.squareZeroPushforwardNaturalityIso_hom_app_coherence`), which is checked
on sections at the level of sites
(`AlgebraicGeometry.Space.pushforward_map_comp_pushforwardRestrictScalarsCongrIso_hom_app`) and
instantiated once: both sides restrict a section along the comparison of chart base changes.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {A : Type u₁} [Category.{v₁} A] {CV : Type u₂} [Category.{v₂} CV]
  {CW : Type u₃} [Category.{v₃} CW] {DV : Type u₄} [Category.{v₄} DV]
  {DW : Type u₅} [Category.{v₅} DW]

/-- **A coherence of comparisons of right adjoints read through equivalences.** Let `E_V`, `E_W`
be equivalences, `a_V : P_V ≅ R_V ⋙ E_V`, `a_W : P_W ≅ R_W ⋙ E_W`, `b : P_H ≅ P_H'` and
`G : E_W ⋙ P_H' ≅ R_g ⋙ E_V`. If a comparison `c : P_V ⟶ P_W ⋙ P_H` is carried by `a_V`, `a_W`,
`b` and `G` to `E_V` applied to `r : R_V ⟶ R_W ⋙ R_g`, then the corresponding composite of the
transported comparisons, with the units and counits of the equivalences, is `r`. -/
theorem rightAdjoint_comp_eq_of_equivalence (EV : CV ≌ DV) (EW : CW ≌ DW)
    {PV : A ⥤ DV} {PW : A ⥤ DW} {PH PH' : DW ⥤ DV} {RV : A ⥤ CV} {RW : A ⥤ CW} {Rg : CW ⥤ CV}
    (aV : PV ≅ RV ⋙ EV.functor) (aW : PW ≅ RW ⋙ EW.functor) (b : PH ≅ PH')
    (G : EW.functor ⋙ PH' ≅ Rg ⋙ EV.functor) (c : PV ⟶ PW ⋙ PH) (r : RV ⟶ RW ⋙ Rg)
    (h : ∀ M, c.app M ≫ PH.map (aW.hom.app M) ≫ b.hom.app _ ≫ G.hom.app (RW.obj M) =
      aV.hom.app M ≫ EV.functor.map (r.app M)) :
    (Functor.isoWhiskerRight aV EV.inverse ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft RV EV.unitIso.symm ≪≫ Functor.rightUnitor RV).inv ≫
      Functor.whiskerRight c EV.inverse ≫
      Functor.whiskerLeft PW (Functor.isoWhiskerRight b EV.inverse ≪≫
        Functor.isoWhiskerRight ((Functor.leftUnitor _).symm ≪≫
          Functor.isoWhiskerRight EW.counitIso.symm _ ≪≫ Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ G) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ EV.unitIso.symm ≪≫ Functor.rightUnitor _)).hom ≫
      Functor.whiskerRight (Functor.isoWhiskerRight aW EW.inverse ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft RW EW.unitIso.symm ≪≫ Functor.rightUnitor RW).hom Rg = r := by
  ext M
  simp only [NatTrans.comp_app, Iso.trans_inv, Iso.trans_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_inv_app, Iso.symm_hom, Iso.symm_inv, Category.id_comp, Category.comp_id,
    Category.assoc, Functor.map_comp, Functor.id_obj, Functor.comp_obj]
  set f := EW.inverse.map (aW.hom.app M) ≫ EW.unitIso.inv.app (RW.obj M) with hf
  have h0 : EW.counitIso.inv.app (PW.obj M) ≫ EW.functor.map f = aW.hom.app M := by
    simp [hf]
  have h1 : G.hom.app (EW.inverse.obj (PW.obj M)) ≫ EV.functor.map (Rg.map f) =
      PH'.map (EW.functor.map f) ≫ G.hom.app (RW.obj M) := (G.hom.naturality f).symm
  have h2 : EV.unitIso.inv.app (Rg.obj (EW.inverse.obj (PW.obj M))) ≫ Rg.map f =
      EV.inverse.map (EV.functor.map (Rg.map f)) ≫ EV.unitIso.inv.app (Rg.obj (RW.obj M)) :=
    (EV.unitIso.inv.naturality (Rg.map f)).symm
  have h3 : aV.inv.app M ≫ c.app M ≫ b.hom.app (PW.obj M) ≫
      PH'.map (EW.counitIso.inv.app (PW.obj M)) ≫ G.hom.app (EW.inverse.obj (PW.obj M)) ≫
        EV.functor.map (Rg.map f) = EV.functor.map (r.app M) := by
    rw [h1, ← PH'.map_comp_assoc, h0, ← b.hom.naturality_assoc]
    exact (congrArg (aV.inv.app M ≫ ·) (h M)).trans (Iso.inv_hom_id_app_assoc _ _ _)
  have h4 : EV.unitIso.hom.app (RV.obj M) ≫ EV.inverse.map (EV.functor.map (r.app M)) ≫
      EV.unitIso.inv.app (Rg.obj (RW.obj M)) = r.app M := by
    rw [← Functor.comp_map, ← EV.unitIso.hom.naturality_assoc, Functor.id_map]
    exact (congrArg (r.app M ≫ ·) (Iso.hom_inv_id_app EV.unitIso (Rg.obj (RW.obj M)))).trans
      (Category.comp_id _)
  rw [← Rg.map_comp, h2]
  refine Eq.trans ?_ h4
  simp only [← Functor.map_comp_assoc, h3]

/-- If `e.hom ≫ q₀ ≫ q₁ = Φ.map (p ≫ ch) ≫ b.app Y ≫ c` and `Ψ.map s ≫ G = c ≫ q₂ ≫ q₃`,
then `e.inv ≫ Φ.map (p ≫ ch ≫ s) ≫ b.app Z ≫ G = (q₀ ≫ q₁ ≫ q₂) ≫ q₃`. -/
theorem inv_comp_map_comp_app_comp_eq {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂}
    [Category.{v₂} 𝒟] {Φ Ψ : 𝒞 ⥤ 𝒟} (b : Φ ⟶ Ψ) {A T₁ T₂ T₃ T₄ : 𝒟} {X Y₁ Y Z : 𝒞}
    (e : Φ.obj X ≅ A) (p : X ⟶ Y₁) (ch : Y₁ ⟶ Y) (s : Y ⟶ Z) (c : Ψ.obj Y ⟶ T₂)
    (G : Ψ.obj Z ⟶ T₄) (q₀ : A ⟶ T₁) (q₁ : T₁ ⟶ T₂) (q₂ : T₂ ⟶ T₃) (q₃ : T₃ ⟶ T₄)
    (hK : e.hom ≫ q₀ ≫ q₁ = Φ.map (p ≫ ch) ≫ b.app Y ≫ c)
    (hIII : Ψ.map s ≫ G = c ≫ q₂ ≫ q₃) :
    e.inv ≫ Φ.map (p ≫ ch ≫ s) ≫ b.app Z ≫ G = (q₀ ≫ q₁ ≫ q₂) ≫ q₃ := by
  rw [← Category.assoc p ch s, Φ.map_comp, Category.assoc, b.naturality_assoc, hIII,
    reassoc_of% hK.symm]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- `Stacks.CategoryTheory.inv_comp_map_comp_app_comp_eq` with the first hypothesis an equation of
isomorphisms of functors, in the shape of a compatibility of comparisons with a compositor. -/
theorem compIso_inv_app_comp_map_comp_app_comp_eq {𝒜 : Type u₁} [Category.{v₁} 𝒜]
    {𝒞 : Type u₂} [Category.{v₂} 𝒞] {𝒟 : Type u₃} [Category.{v₃} 𝒟]
    {PW PW' PW'' RW : 𝒜 ⥤ 𝒞} {Φ Φ' Ψ : 𝒞 ⥤ 𝒟} {PV PV' PV'' RV : 𝒜 ⥤ 𝒟}
    (CA : PW ⋙ Φ ≅ PV) (a₁ : PV ≅ PV') (a₂ : PV' ≅ PV'') (aV : PV'' ≅ RV) (w₁ : PW ≅ PW')
    (w₂ : PW' ≅ PW'') (aW : PW'' ≅ RW) (b₁ : Φ ≅ Φ') (b₂ : Φ' ≅ Ψ) (C : PW'' ⋙ Ψ ≅ PV'')
    (hK : CA ≪≫ (a₁ ≪≫ a₂) =
      Functor.isoWhiskerRight (w₁ ≪≫ w₂) Φ ≪≫ Functor.isoWhiskerLeft PW'' (b₁ ≪≫ b₂) ≪≫ C)
    (M : 𝒜) {T : 𝒟} (G : Ψ.obj (RW.obj M) ⟶ T) (q : RV.obj M ⟶ T)
    (hIII : Ψ.map (aW.hom.app M) ≫ G = C.hom.app M ≫ aV.hom.app M ≫ q) :
    CA.inv.app M ≫ Φ.map ((w₁ ≪≫ w₂ ≪≫ aW).hom.app M) ≫ (b₁ ≪≫ b₂).hom.app (RW.obj M) ≫ G =
      (a₁ ≪≫ a₂ ≪≫ aV).hom.app M ≫ q := by
  have h := NatTrans.congr_app (congrArg Iso.hom hK) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  exact (inv_comp_map_comp_app_comp_eq (b₁ ≪≫ b₂).hom (CA.app M) (w₁.hom.app M) (w₂.hom.app M)
    (aW.hom.app M) (C.hom.app M) G (a₁.hom.app M) (a₂.hom.app M) (aV.hom.app M) q
    (by simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc,
      Iso.app_hom] using h)
    hIII).trans (by simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc])

end Stacks.CategoryTheory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

attribute [local instance] isContinuous_smallBaseChange

section Generic

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {F : C ⥤ D} {G : D ⥤ E} {G' : C ⥤ E} [F.IsContinuous J K] [G.IsContinuous K L]
  [(F ⋙ G).IsContinuous J L] [G'.IsContinuous J L]
  {T : Sheaf J RingCat.{u}} {R' : Sheaf K RingCat.{u}} {R R₀ R₁ : Sheaf L RingCat.{u}}

/-- **The two comparisons of pushforwards of `G2a` and of the contraction agree**, at the level of
sites: let `s_W`, `s_V` identify two pushforwards with restrictions of scalars followed by
restriction of sections, both the identity on sections, and `r` be a comparison of restrictions
of scalars which is the identity on sections. Then pushing `s_W` forward along `φ` and applying
`AlgebraicGeometry.Space.pushforwardRestrictScalarsCongrIso` is the contraction of the two
pushforwards followed by `s_V` and `r`, as soon as the two isomorphisms of functors of sites
involved agree. Both sides restrict a section along the component of `e`. -/
theorem pushforward_map_comp_pushforwardRestrictScalarsCongrIso_hom_app (e : G' ≅ F ⋙ G)
    (α : R' ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R₁)
    (φ : T ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R') (β : R₀ ⟶ R₁)
    (γ : T ⟶ (G'.sheafPushforwardContinuous RingCat.{u} J L).obj R₀)
    (h : (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map α) ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J L).app R₁ =
      γ ≫ (G'.sheafPushforwardContinuous RingCat.{u} J L).map β)
    {σW : R' ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R}
    {σV : T ⟶ (G'.sheafPushforwardContinuous RingCat.{u} J L).obj R} {πW : R₁ ⟶ R} {πV : R₀ ⟶ R}
    (sW : SheafOfModules.pushforward.{u} σW ≅ SheafOfModules.restrictScalars.{u} πW ⋙
      (SheafOfModules.pushforward.{u} (F := G)
        (𝟙 ((G.sheafPushforwardContinuous RingCat.{u} K L).obj R₁)) ⋙
        SheafOfModules.restrictScalars.{u} α))
    (hsW : ∀ M U x, (sW.hom.app M).val.app U x = x)
    (sV : SheafOfModules.pushforward.{u} σV ≅ SheafOfModules.restrictScalars.{u} πV ⋙
      (SheafOfModules.pushforward.{u} (F := G')
        (𝟙 ((G'.sheafPushforwardContinuous RingCat.{u} J L).obj R₀)) ⋙
        SheafOfModules.restrictScalars.{u} γ))
    (hsV : ∀ M U x, (sV.hom.app M).val.app U x = x)
    (e' : G' ≅ F ⋙ G)
    (he' : SheafOfModules.comparisonComp φ σW ≫
        (Functor.sheafPushforwardContinuousNatTrans e'.hom RingCat.{u} J L).app R = σV)
    (hee : ∀ U, e'.hom.app U = e.hom.app U)
    (r : SheafOfModules.restrictScalars.{u} πV ⟶
      SheafOfModules.restrictScalars.{u} πW ⋙ SheafOfModules.restrictScalars.{u} β)
    (hr : ∀ M U x, (r.app M).val.app U x = x) (M : SheafOfModules.{u} R) :
    (SheafOfModules.pushforward.{u} φ).map (sW.hom.app M) ≫
        (pushforwardRestrictScalarsCongrIso e α φ β γ h).hom.app
          ((SheafOfModules.restrictScalars.{u} πW).obj M) =
      (SheafOfModules.pushforwardComp.{u} φ σW ≪≫
          SheafOfModules.pushforwardCongr₂.{u} _ e' he').hom.app M ≫ sV.hom.app M ≫
        (SheafOfModules.pushforward.{u} (F := G')
          (𝟙 ((G'.sheafPushforwardContinuous RingCat.{u} J L).obj R₀)) ⋙
            SheafOfModules.restrictScalars.{u} γ).map (r.app M) := by
  refine Stacks.ChartUnitTransport.hom_ext_val_app_apply_unop fun U x => ?_
  have h1 := Stacks.ChartPushforwardContraction.contraction_hom_app_val_app φ σW e' he' M U x
    (hee U)
  exact (congrArg (fun y => M.val.map (e.hom.app U).op y) (hsW M (op (F.obj U)) x)).trans
    (h1.symm.trans ((hsV M _ _).symm.trans (hr M _ _).symm))

end Generic

section Coherence

variable {k : Type u} [CommRing k] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))} {V W : SiteModule k B}
  {X X'V X'W : AlgebraicSpaces B S hS} {p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk)}
  {iW : X ⟶ X'W} (hiW : IsThickeningHom B S hS iW)
  {qW : X'W ⟶ X} (hW : iW ≫ qW = 𝟙 X) {hqW : yoneda.relativelyRepresentable qW.hom}
  {p'W : X'W.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS W)}
  {τW : squareZeroOver k B S hS toS W ⟶ algebraOver k B S hS toS hk}
  (hipW : iW.hom ≫ p'W = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk W))
  (hpbW : IsPullback qW.hom p'W p (yoneda.map τW))
  (hβτW : squareZeroArrow k B S hS toS hk W ≫ τW = 𝟙 _)
  {H : X'W ⟶ X'V} (hiV : IsThickeningHom B S hS (iW ≫ H))
  {qV : X'V ⟶ X} (hV : (iW ≫ H) ≫ qV = 𝟙 X) {hqV : yoneda.relativelyRepresentable qV.hom}
  {p'V : X'V.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τV : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
  (hipV : (iW ≫ H).hom ≫ p'V = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
  (hpbV : IsPullback qV.hom p'V p (yoneda.map τV))
  (hβτV : squareZeroArrow k B S hS toS hk V ≫ τV = 𝟙 _)
  (hH : yoneda.relativelyRepresentable H.hom) {g : (sqZeroExtSheafAnySite
    (structureSheaf B S hS X.1 X.2) ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
    (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)) ⟶ (sqZeroExtSheafAnySite
    (structureSheaf B S hS X.1 X.2) ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
    (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))}

include hiV hiW in
/-- With `i_V = i_W ≫ H`, the comparison `AlgebraicGeometry.Space.squareZeroChartCompIso` of chart
base changes is `AlgebraicGeometry.Space.smallBaseChangeChartCompIso`. -/
theorem smallBaseChangeChartCompIso_hom_app_eq_squareZeroChartCompIso
    (U : SmallEtale B S hS X'V.1) :
    (smallBaseChangeChartCompIso B S hS iW H hiW.isClosedImmersion.rep hH
        hiV.isClosedImmersion.rep).hom.app U =
      (squareZeroChartCompIso hiV hiW hH rfl).hom.app U := by
  simp [squareZeroChartCompIso]

/-- **`G2a` against the contraction of chart pushforwards**: pushing
`AlgebraicGeometry.Space.squareZeroPushforwardIso` for `W` forward along `H` and applying `G2a`
(`AlgebraicGeometry.Space.squareZeroPushforwardNaturalityIso`) is the contraction of the chart
pushforwards along `X ⟶ X_W ⟶ X_V`, followed by `AlgebraicGeometry.Space.squareZeroPushforwardIso`
for `V` and the identification of the restrictions of scalars. -/
theorem squareZeroPushforwardNaturalityIso_hom_app_coherence
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH rfl
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (hgp : g ≫ (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k
      (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)) = (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
      (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (smallBaseChangeModulePushforward.{u, u} B S hS H hH).map
        ((squareZeroPushforwardIso (hq := hqW) hiW hW hipW hpbW hβτW).hom.app M) ≫
      (squareZeroPushforwardNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH rfl
        hg).hom.app
        ((SheafOfModules.restrictScalars
          ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
            (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
              (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
              (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))).obj M) =
      (smallBaseChangeChartPushforwardCompIso B S hS iW H hiW.isClosedImmersion.rep hH
          hiV.isClosedImmersion.rep).hom.app M ≫
        (squareZeroPushforwardIso (hq := hqV) hiV hV hipV hpbV hβτV).hom.app M ≫
        (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor.map
          ((restrictScalarsCompIsoOf g hgp).inv.app M) := by
  have key := pushforward_map_comp_pushforwardRestrictScalarsCongrIso_hom_app
    (squareZeroChartCompIso hiV hiW hH rfl)
    (T := smallEtaleRingSheaf B S hS X'V.1 X'V.2) (R' := smallEtaleRingSheaf B S hS X'W.1 X'W.2)
    (R := smallEtaleRingSheaf B S hS X.1 X.2)
    (R₀ := Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite
      (structureSheaf B S hS X.1 X.2) ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
    (R₁ := Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite
      (structureSheaf B S hS X.1 X.2) ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))
    ((sheafCompose (SmallEtale.topology B S hS X'W.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
      (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (smallBaseChangeSharp B S hS H hH)
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map g)
    ((sheafCompose (SmallEtale.topology B S hS X'V.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
      (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom)
    (squareZeroPushforwardNaturality_ringMap_eq hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH rfl
      hg)
    (σW := smallBaseChangeSharp B S hS iW hiW.isClosedImmersion.rep)
    (σV := smallBaseChangeSharp B S hS (iW ≫ H) hiV.isClosedImmersion.rep)
    (πW := (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
      (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))) (πV := (sheafCompose
      (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
      (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
    (squareZeroPushforwardIso (hq := hqW) hiW hW hipW hpbW hβτW) (fun _ _ _ => rfl)
    (squareZeroPushforwardIso (hq := hqV) hiV hV hipV hpbV hβτV) (fun _ _ _ => rfl)
    (smallBaseChangeChartCompIso B S hS iW H hiW.isClosedImmersion.rep hH hiV.isClosedImmersion.rep)
    (smallBaseChangeSharp_comparisonComp B S hS iW H hiW.isClosedImmersion.rep hH
      hiV.isClosedImmersion.rep)
    (smallBaseChangeChartCompIso_hom_app_eq_squareZeroChartCompIso hiW hiV hH)
    (restrictScalarsCompIsoOf g hgp).inv
    (fun M U x => restrictScalarsCompIsoOf_inv_app_val_app g hgp M U x) M
  refine Eq.trans ?_ (key.trans ?_) <;> rfl

/-- **The right-adjoint coherence `hR`, one module at a time and before transport along the
equivalences**: the compositor of direct images along `X ⟶ X_W ⟶ X_V`, then the identification
of the direct image along `i_W` with restriction of scalars pushed along `H`, then the chart
comparison along `H` and `G2a`, is the identification of the direct image along `i_V = i_W ≫ H`
with restriction of scalars followed by the identification of the restrictions of scalars. -/
theorem squareZeroPushforwardIso_comp_coherence_app
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH rfl
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (hgp : g ≫ (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k
      (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)) = (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
      (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O)) :
    ((pushforwardModulesCompTransport B S hS iW H).inv ≫
        (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS iW)
          (smallEtaleRingedToposHom B S hS H)).hom).app M ≫
      (smallEtaleRingedToposHom B S hS H).pushforwardModules.map
        ((pushforwardModulesIsoModulePushforward B S hS iW ≪≫
          modulePushforwardChartIso B S hS iW hiW.isClosedImmersion.rep ≪≫
          squareZeroPushforwardIso (hq := hqW) hiW hW hipW hpbW hβτW).hom.app M) ≫
      (pushforwardModulesIsoModulePushforward B S hS H ≪≫
        modulePushforwardChartIso B S hS H hH).hom.app
        ((SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map (sqZeroExtSheafAnySiteProj
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))) ⋙
          (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor).obj M) ≫
      (squareZeroPushforwardNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH rfl
        hg).hom.app
        ((SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map (sqZeroExtSheafAnySiteProj
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))).obj M) =
    (pushforwardModulesIsoModulePushforward B S hS (iW ≫ H) ≪≫
        modulePushforwardChartIso B S hS (iW ≫ H) hiV.isClosedImmersion.rep ≪≫
        squareZeroPushforwardIso (hq := hqV) hiV hV hipV hpbV hβτV).hom.app M ≫
      (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor.map
        ((restrictScalarsCompIsoOf g hgp).inv.app M) := by
  have hIII := squareZeroPushforwardNaturalityIso_hom_app_coherence hiW hW hipW hpbW hβτW hiV hV
    hipV hpbV hβτV hH hg hgp M
  have key := Stacks.CategoryTheory.compIso_inv_app_comp_map_comp_app_comp_eq
    (pushforwardModulesCompAt B S hS iW H) _ _
    (squareZeroPushforwardIso (hq := hqV) hiV hV hipV hpbV hβτV)
    _ _ (squareZeroPushforwardIso (hq := hqW) hiW hW hipW hpbW hβτW) _ _ _
    (pushforwardModulesCompAt_trans_chartIso B iW H hiW.isClosedImmersion.rep hH
      hiV.isClosedImmersion.rep) M _ _ hIII
  refine Eq.trans ?_ (key.trans ?_) <;> rfl

/-- **The right-adjoint coherence `hR` of `MC`**: the comparisons of right adjoints behind
`AlgebraicGeometry.Space.squareZeroPullbackIso` for `V` (inverted) and `W`, behind `G2`, and the
compositor of direct images along `X ⟶ X_W ⟶ X_V` compose to the identification of the
restrictions of scalars along `g` and the two projections. This is the hypothesis `hR` of
`AlgebraicGeometry.Space.extensionOfScalarsCompIso_hom_eq_of_rightAdjoint`; it is read off,
through the two equivalences, from
`AlgebraicGeometry.Space.squareZeroPushforwardIso_comp_coherence_app`. -/
theorem squareZeroPullbackRightAdjointIso_comp_coherence
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH rfl
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (hgp : g ≫ (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k
      (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)) = (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
      (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))) :
    (squareZeroPullbackRightAdjointIso (hq := hqV) hiV hV hipV hpbV hβτV).inv ≫
        Functor.whiskerRight ((pushforwardModulesCompTransport B S hS iW H).inv ≫
          (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS iW)
            (smallEtaleRingedToposHom B S hS H)).hom)
          (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).inverse ≫
        Functor.whiskerLeft (smallEtaleRingedToposHom B S hS iW).pushforwardModules
          (squareZeroPushforwardNaturalityRightAdjointIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW
            hβτW hH rfl hg).hom ≫
        Functor.whiskerRight
          (squareZeroPullbackRightAdjointIso (hq := hqW) hiW hW hipW hpbW hβτW).hom
          (SheafOfModules.restrictScalars
            ((sheafCompose (SmallEtale.topology B S hS X.1)
              (forget₂ CommRingCat.{u} RingCat.{u})).map g)) =
      (restrictScalarsCompIsoOf g hgp).inv := by
  refine Stacks.CategoryTheory.rightAdjoint_comp_eq_of_equivalence
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV)
    (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW)
    (pushforwardModulesIsoModulePushforward B S hS (iW ≫ H) ≪≫
      modulePushforwardChartIso B S hS (iW ≫ H) hiV.isClosedImmersion.rep ≪≫
      squareZeroPushforwardIso (hq := hqV) hiV hV hipV hpbV hβτV)
    (pushforwardModulesIsoModulePushforward B S hS iW ≪≫
      modulePushforwardChartIso B S hS iW hiW.isClosedImmersion.rep ≪≫
      squareZeroPushforwardIso (hq := hqW) hiW hW hipW hpbW hβτW)
    (pushforwardModulesIsoModulePushforward B S hS H ≪≫ modulePushforwardChartIso B S hS H hH)
    (squareZeroPushforwardNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH rfl hg)
    ((pushforwardModulesCompTransport B S hS iW H).inv ≫
      (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS iW)
        (smallEtaleRingedToposHom B S hS H)).hom)
    (restrictScalarsCompIsoOf g hgp).inv
    (fun M => ?_)
  have key := squareZeroPushforwardIso_comp_coherence_app hiW hW hipW hpbW hβτW hiV hV hipV hpbV
    hβτV hH hg hgp M
  refine Eq.trans ?_ (key.trans ?_) <;> rfl

/-- **`MC`**: the identification of extension of scalars along `g` and then along
`𝒪_X[𝒪_X ⊗_k W] ⟶ 𝒪_X` with extension of scalars along `𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X` is
`AlgebraicGeometry.Space.squareZeroPullbackIso` for `W` inverted, `G2` inverted and pushed along
`X ⟶ X_W`, the composition comparison of pullbacks along `X ⟶ X_W ⟶ X_V`, and
`AlgebraicGeometry.Space.squareZeroPullbackIso` for `V`:
`AlgebraicGeometry.Space.extensionOfScalarsCompIso_hom_eq_of_rightAdjoint` with its hypothesis
`hR` discharged by `AlgebraicGeometry.Space.squareZeroPullbackRightAdjointIso_comp_coherence`. -/
theorem extensionOfScalarsCompIso_hom_eq_squareZeroPullbackIso
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH rfl
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (hgp : g ≫ (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k
      (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)) = (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
      (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))) :
    (extensionOfScalarsCompIso g hgp).hom =
      Functor.whiskerLeft (extensionOfScalars g)
          (squareZeroPullbackIso (hq := hqW) hiW hW hipW hpbW hβτW).inv ≫
        Functor.whiskerRight (squareZeroPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW
          hβτW hH rfl hg).inv (smallEtaleRingedToposHom B S hS iW).toModulesHom.pullbackModules ≫
        Functor.whiskerLeft (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor
          ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS iW)
          (smallEtaleRingedToposHom B S hS H)).symm ≪≫
          pullbackModulesCompTransport B S hS iW H).hom ≫
        (squareZeroPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV).hom :=
  extensionOfScalarsCompIso_hom_eq_of_rightAdjoint hiW hW hipW hpbW hβτW hiV hV hipV hpbV hβτV hH
    hg hgp
    (squareZeroPullbackRightAdjointIso_comp_coherence hiW hW hipW hpbW hβτW hiV hV hipV hpbV hβτV hH
      hg hgp)

end Coherence

end AlgebraicGeometry.Space
