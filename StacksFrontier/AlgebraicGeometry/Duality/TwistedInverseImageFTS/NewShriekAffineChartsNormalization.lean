module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekComparisonZerothRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.OpenImmersionPrecomposition
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The chart normalizations restrict, at the standard model

Let `f : X ⟶ Y` be a morphism of schemes of finite type over `S`, with `ω_X^•`, `ω_Y^•` normalized
relative to `ω_S^•`, and `W ⊆ V ⊆ f⁻¹U` affine opens. Read at the standard model of `D(𝒪_W)` and
at the compactification of a factorization of `V → Y` restricted to `W`, the normalization
`ω_W^• ≅ (W → Y)^! ω_Y^•` is the restriction of the one on `V`, through
`(W → V)^* (V → Y)^! ≅ (W → Y)^!` and `ω_W^• ≅ (W → V)^* ω_V^•`. Derived pullback along a
composite is compared at the two models of `D(𝒪_X)` by
`Stacks.Duality.UpperShriekDuality.pullModelConj_hom_app_comp_pullCompIso`.

## Main results

* `Stacks.Duality.UpperShriekDuality.pullModelConj_hom_app_comp_pullCompIso`.
* `Stacks.Duality.NormalizedOnOpens.affineNormalizationAt_chart_restrict`.

## References

* [Stacks Project, Tag 0AUB](https://stacks.math.columbia.edu/tag/0AUB)
* [Stacks Project, Tag 0BUL](https://stacks.math.columbia.edu/tag/0BUL)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std comparison plusCoh plusCoh_le_qcoh plusCoh_iff
  pull stdMonoidal stdSymmetric stdMonoidalClosed)

namespace UpperShriekDuality

open TwistedInverseImageDuality

/-- The chase behind `pullModelConj_hom_app_comp_pullCompIso`. -/
theorem pullModelConj_comp_chase {𝒟 : Type*} [Category 𝒟] {o₀ o₁ o₂ o₃ q₂ q₃ : 𝒟}
    (m₁ : o₀ ⟶ o₁) (B : o₁ ⟶ o₂) (C : o₂ ⟶ o₃) (n₁ : o₁ ⟶ o₀) (y : o₀ ⟶ q₂) (n₂ : o₂ ⟶ q₂)
    (y' : q₂ ⟶ o₀) (Z : o₀ ⟶ q₃) (κ : o₃ ≅ q₃) (a2 : B ≫ n₂ = n₁ ≫ y)
    (a4 : C ≫ κ.hom = n₂ ≫ y' ≫ Z) (h1 : m₁ ≫ n₁ = 𝟙 _) (hy : y ≫ y' = 𝟙 _) :
    m₁ ≫ B ≫ C = Z ≫ κ.inv := by
  rw [← cancel_mono κ.hom, Category.assoc, Category.assoc, a4, reassoc_of% a2, Category.assoc,
    reassoc_of% hy, reassoc_of% h1, Iso.inv_hom_id, Category.comp_id]

/-- **`pullModelConj` is compatible with composition**: `Lh^* Lj^* ≅ L(h ≫ j)^*` at the standard
model, read through `pullModelConj`, is the one at the locally small model. -/
theorem pullModelConj_hom_app_comp_pullCompIso {A₀ B₀ C₀ : Scheme.{u}} (h : A₀ ⟶ B₀) (j : B₀ ⟶ C₀)
    (k : A₀ ⟶ C₀) (w : h ≫ j = k) (E : DerivedCategory C₀.Modules) :
    (pullModelConj h).hom.app ((Stacks.Duality.derivedPullback j).obj E) ≫
        (pull h).map ((pullModelConj j).hom.app E) ≫
        (pullCompIso h j k w).hom.app ((comparison C₀).inverse.obj E) =
      (comparison A₀).inverse.map ((Stacks.Duality.derivedPullbackCompIso h j).hom.app E ≫
          eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj E) w)) ≫
        (pullModelConj k).hom.app E := by
  apply (comparison A₀).functor.map_injective
  have a1 := NormalizedOnOpens.comparison_map_pullModelConj_hom_app h
    ((Stacks.Duality.derivedPullback j).obj E)
  have a3 := NormalizedOnOpens.comparison_map_pullModelConj_hom_app j E
  have b2 := NormalizedOnOpens.comparison_map_pullModelConj_hom_app k E
  have a2 := (pullModelIso h).hom.naturality ((pullModelConj j).hom.app E)
  have a4 := pullCompIso_hom_app_comp_pullModelIso_hom j h k w ((comparison C₀).inverse.obj E)
  simp only [Functor.comp_map] at a2
  rw [a3] at a2
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, a1,
    comparison_functor_map_inverse_map, b2]
  exact pullModelConj_comp_chase _ _ _ _ _ _ _ _
    ((pullModelIso k).app ((comparison C₀).inverse.obj E))
    a2 a4 (Iso.inv_hom_id_app _ _) (((Stacks.Duality.derivedPullback h).map_comp _ _).symm.trans
      ((congrArg (Stacks.Duality.derivedPullback h).map (Iso.inv_hom_id_app _ _)).trans
        ((Stacks.Duality.derivedPullback h).map_id _)))

end UpperShriekDuality

namespace NormalizedOnOpens

/-- The chase behind `affineNormalizationAt_chart_restrict`: an identity of isomorphisms at the
standard model, read through `G` (the comparison of the models), from an identity at the locally
small model and the compatibilities `PMC1`, `PMC2` of `M` (derived pullback at the two models)
with composition. -/
theorem chart_restrict_std_chase {𝒮 𝒮' 𝒟 𝒟' : Type*} [Category 𝒮] [Category 𝒮'] [Category 𝒟]
    [Category 𝒟'] (G : 𝒟 ⥤ 𝒮) (P : 𝒮' ⥤ 𝒮) (GV : 𝒟' ⥤ 𝒮') (L : 𝒟' ⥤ 𝒟)
    (M : L ⋙ G ≅ GV ⋙ P) {d₀ d₁ d₂ dQ dK : 𝒟} {v₀ v₁ v₂ v₃ : 𝒟'} {sQ sK : 𝒮'} {t₁ t₂ : 𝒮}
    (α₁ : d₁ ≅ d₀) (α₂ : d₁ ≅ d₂) (ρ : d₀ ≅ dQ) (β₁ : v₃ ≅ v₀) (β₂ : v₃ ≅ v₁) (σV : v₁ ≅ v₂)
    (σW : d₂ ≅ dK) (mj : GV.obj v₀ ≅ sQ) (pci : P.obj sQ ≅ t₁) (mk : G.obj dQ ≅ t₁)
    (mV : GV.obj v₂ ≅ sK) (pci' : P.obj sK ≅ t₂) (mW : G.obj dK ≅ t₂)
    (dc₁ : L.obj v₀ ⟶ dQ) (dc₁' : dQ ⟶ L.obj v₀) (dc₂ : L.obj v₂ ⟶ dK)
    (hdc : dc₁' ≫ dc₁ = 𝟙 _)
    (PMC1 : M.hom.app v₀ ≫ P.map mj.hom ≫ pci.hom = G.map dc₁ ≫ mk.hom)
    (PMC2 : M.hom.app v₂ ≫ P.map mV.hom ≫ pci'.hom = G.map dc₂ ≫ mW.hom)
    (LS : α₁.inv ≫ α₂.hom ≫ σW.hom =
      ρ.hom ≫ dc₁' ≫ L.map (β₁.inv ≫ β₂.hom) ≫ L.map σV.hom ≫ dc₂) :
    (G.mapIso α₁).symm ≪≫ G.mapIso α₂ =
      G.mapIso ρ ≪≫ (P.mapIso mj ≪≫ pci ≪≫ mk.symm).symm ≪≫
        P.mapIso ((GV.mapIso β₁).symm ≪≫ GV.mapIso β₂) ≪≫
        (G.mapIso σW ≪≫ mW ≪≫ pci'.symm ≪≫ P.mapIso (GV.mapIso σV ≪≫ mV).symm).symm := by
  have hδ : M.hom.app v₀ ≫ (P.mapIso mj ≪≫ pci ≪≫ mk.symm).hom = G.map dc₁ := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [reassoc_of% PMC1, Iso.hom_inv_id, Category.comp_id]
  have hδ' : (P.mapIso mj ≪≫ pci ≪≫ mk.symm).inv = G.map dc₁' ≫ M.hom.app v₀ := by
    rw [← cancel_mono (P.mapIso mj ≪≫ pci ≪≫ mk.symm).hom, Iso.inv_hom_id, Category.assoc, hδ,
      ← G.map_comp, hdc, G.map_id]
  have N1 := M.hom.naturality (β₁.inv ≫ β₂.hom)
  have N2 := M.hom.naturality σV.hom
  simp only [Functor.comp_map] at N1 N2
  have hLS : α₁.inv ≫ α₂.hom =
      ρ.hom ≫ dc₁' ≫ L.map (β₁.inv ≫ β₂.hom) ≫ L.map σV.hom ≫ dc₂ ≫ σW.inv := by
    rw [← reassoc_of% LS, Iso.hom_inv_id, Category.comp_id]
  have hδ'' : mk.hom ≫ pci.inv ≫ P.map mj.inv = G.map dc₁' ≫ M.hom.app v₀ := by
    simpa only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc] using hδ'
  ext1
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_inv,
    Iso.symm_inv, Category.assoc]
  rw [← G.map_comp, hLS, reassoc_of% hδ'', ← GV.map_comp, ← reassoc_of% N1, P.map_comp,
    Category.assoc, ← reassoc_of% N2, reassoc_of% PMC2, Iso.hom_inv_id_assoc]
  simp only [G.map_comp]

/-- The chase behind the locally small half of `affineNormalizationAt_chart_restrict`. -/
theorem chart_restrict_ls_chase {𝒟 𝒟' : Type*} [Category 𝒟] [Category 𝒟'] (L : 𝒟' ⥤ 𝒟)
    {o₀ o₁ o₂ o₃ o₄ o₅ o₉ q₁ p₁ : 𝒟} {v₀ v₁ v₂ v₃ v₄ : 𝒟'}
    (A₁ P'W : o₀ ⟶ o₁) (Gd : o₁ ⟶ o₂) (cWinv : o₂ ⟶ o₅) (f2K : o₂ ⟶ o₃) (hlV : o₃ ⟶ o₄)
    (f1inv : o₄ ⟶ o₅) (σWh : o₅ ⟶ o₉) (f1 : o₅ ⟶ o₄) (shlK : o₄ ⟶ L.obj v₃) (σVh : v₃ ⟶ v₄)
    (dc2 : L.obj v₄ ⟶ o₉) (f2ω : o₁ ⟶ q₁) (hlgVd : q₁ ⟶ o₃) (shlω : q₁ ⟶ L.obj v₁)
    (shlb : o₃ ⟶ L.obj v₂) (a : v₁ ⟶ v₂) (b : v₂ ⟶ v₃) (ρ : o₀ ⟶ p₁) (U dc1' : p₁ ⟶ L.obj v₀)
    (β1i PV : v₀ ⟶ v₁)
    (F1 : A₁ = P'W) (F2 : cWinv = (f2K ≫ hlV) ≫ f1inv) (F3 : Gd ≫ f2K = f2ω ≫ hlgVd)
    (F4 : f1inv ≫ f1 = 𝟙 _) (F5 : σWh = f1 ≫ shlK ≫ L.map σVh ≫ dc2)
    (F6a : hlgVd ≫ shlb = shlω ≫ L.map a) (F6b : hlV ≫ shlK = shlb ≫ L.map b)
    (F7 : P'W ≫ f2ω ≫ shlω = ρ ≫ U ≫ L.map PV) (F9 : U = dc1') (F8 : β1i = PV) :
    A₁ ≫ (Gd ≫ cWinv) ≫ σWh = ρ ≫ dc1' ≫ L.map (β1i ≫ a ≫ b) ≫ L.map σVh ≫ dc2 := by
  subst F1 F2 F5 F9 F8
  simp only [Category.assoc, L.map_comp]
  rw [reassoc_of% F4, reassoc_of% F6b, reassoc_of% F3, reassoc_of% F6a, reassoc_of% F7]

/-- `chart_restrict_std_chase` with the isomorphisms of the conclusion given through their
components. -/
theorem chart_restrict_std_chase' {𝒮 𝒮' 𝒟 𝒟' : Type*} [Category 𝒮] [Category 𝒮'] [Category 𝒟]
    [Category 𝒟'] (G : 𝒟 ⥤ 𝒮) (P : 𝒮' ⥤ 𝒮) (GV : 𝒟' ⥤ 𝒮') (L : 𝒟' ⥤ 𝒟)
    (M : L ⋙ G ≅ GV ⋙ P) {d₀ d₁ d₂ dQ dK : 𝒟} {v₀ v₁ v₂ v₃ : 𝒟'} {sQ sK : 𝒮'} {t₁ t₂ : 𝒮}
    (α₁ : d₁ ≅ d₀) (α₂ : d₁ ≅ d₂) (ρ : d₀ ≅ dQ) (β₁ : v₃ ≅ v₀) (β₂ : v₃ ≅ v₁) (σV : v₁ ≅ v₂)
    (σW : d₂ ≅ dK) (mj : GV.obj v₀ ≅ sQ) (pci : P.obj sQ ≅ t₁) (mk : G.obj dQ ≅ t₁)
    (mV : GV.obj v₂ ≅ sK) (pci' : P.obj sK ≅ t₂) (mW : G.obj dK ≅ t₂)
    (dc₁ : L.obj v₀ ⟶ dQ) (dc₁' : dQ ⟶ L.obj v₀) (dc₂ : L.obj v₂ ⟶ dK)
    (hdc : dc₁' ≫ dc₁ = 𝟙 _)
    (PMC1 : M.hom.app v₀ ≫ P.map mj.hom ≫ pci.hom = G.map dc₁ ≫ mk.hom)
    (PMC2 : M.hom.app v₂ ≫ P.map mV.hom ≫ pci'.hom = G.map dc₂ ≫ mW.hom)
    (LS : α₁.inv ≫ α₂.hom ≫ σW.hom =
      ρ.hom ≫ dc₁' ≫ L.map (β₁.inv ≫ β₂.hom) ≫ L.map σV.hom ≫ dc₂)
    (A : G.obj d₁ ≅ G.obj d₀) (B : G.obj d₁ ≅ G.obj d₂) (R : G.obj d₀ ≅ G.obj dQ)
    (δ : P.obj (GV.obj v₀) ≅ G.obj dQ) (N : GV.obj v₀ ≅ GV.obj v₁)
    (Sm : G.obj d₂ ≅ P.obj (GV.obj v₁)) (sW : G.obj d₂ ≅ t₂) (sV : GV.obj v₁ ≅ sK)
    (hA : A = G.mapIso α₁) (hB : B = G.mapIso α₂) (hR : R = G.mapIso ρ)
    (hδ : δ = P.mapIso mj ≪≫ pci ≪≫ mk.symm) (hN : N = (GV.mapIso β₁).symm ≪≫ GV.mapIso β₂)
    (hsW : sW = G.mapIso σW ≪≫ mW) (hsV : sV = GV.mapIso σV ≪≫ mV)
    (hS : Sm = sW ≪≫ pci'.symm ≪≫ P.mapIso sV.symm) :
    A.symm ≪≫ B = R ≪≫ δ.symm ≪≫ P.mapIso N ≪≫ Sm.symm := by
  subst hA hB hR hδ hN hS hsW hsV
  rw [Iso.trans_assoc]
  exact chart_restrict_std_chase G P GV L M α₁ α₂ ρ β₁ β₂ σV σW mj pci mk mV pci' mW dc₁ dc₁' dc₂
    hdc PMC1 PMC2 LS

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
  (hpe : f ≫ q = p) (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
  [LocallyQuasiFinite f]

omit [LocallyQuasiFinite f] in
open UpperShriekDuality TwistedInverseImageDuality in
/-- **The chart normalizations restrict**, read at the standard model: the normalization on
`W ⊆ V` is the restriction of the one on `V`. -/
theorem affineNormalizationAt_chart_restrict (U : Y.affineOpens) {V W : X.affineOpens}
    (hWV : W.1 ≤ V.1) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hWU : W.1 ≤ f ⁻¹ᵁ U.1) :
    haveI := hq.source_noetherian
    ∀ F : OpenFiniteFactorization (affineHom (hp := hp) (hq := hq) hpe V),
    affineNormalizationAt c 𝒦X 𝒦Y hpe hωS W (affineChartNormalization c 𝒦X 𝒦Y hpe U W hWU)
        (F.precompOpen (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
          (affineRestrictHom_comp hpe hWV)) =
      (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison _).inverse).mapIso
        ((upperShriekPlusCongr (affineRestrictHom_comp hpe hWV).symm
          (F.precompOpen (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
            (affineRestrictHom_comp hpe hWV)).compactification
          (F.compactification.precompOpen
            (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left)).app
            ⟨dualizingQCoh (isDualizing_stdComplex c hωS 𝒦Y),
              isBoundedBelow_dualizingQCoh (hp := hp) c 𝒦Y hωS⟩) ≪≫
      (upperShriekDualizingRestrictIso (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
        (affineHom (hp := hp) (hq := hq) hpe V) F.compactification
        (isDualizing_stdComplex c hωS 𝒦Y)).symm ≪≫
      (pull (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left).mapIso
        (affineNormalizationAt c 𝒦X 𝒦Y hpe hωS V
          (affineChartNormalization c 𝒦X 𝒦Y hpe U V hVU) F) ≪≫
      (stdComplexRestrictLEIso c 𝒦X hWV).symm := by
  have := hq.source_noetherian
  intro F
  set D : quasiCoherentDerivedCategoryPlusOfModel (ftsOf (𝟙 Y) (isSeparatedFiniteType_id Y)).left :=
    ⟨dualizingQCoh (isDualizing_stdComplex c hωS 𝒦Y),
      isBoundedBelow_dualizingQCoh (hp := hp) c 𝒦Y hωS⟩
  set φ : D ⟶ 𝒦Y.complex := ObjectProperty.homMk
    (dualizingQCohIso c 𝒦Y (isDualizing_stdComplex c hωS 𝒦Y)).hom
  have hW := hp.isShriekable_ι_comp_of_isAffineOpen hq hpe W.2
  have hV := hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2
  have e₁ : X.homOfLE hWV ≫ V.1.ι = W.1.ι := X.homOfLE_ι hWV
  have e₂ : X.homOfLE hWV ≫ V.1.ι ≫ f = W.1.ι ≫ f := X.homOfLE_ι_assoc hWV f
  have hh : IsShriekable (X.homOfLE hWV) := hp.isShriekable_homOfLE hWV
  have F1 := congrArg (fun i => (i.hom.app D).hom.hom)
    (upperShriekPlusIso_symm (affineHom (hp := hp) (hq := hq) hpe W) (c _ hW)
      (F.precompOpen (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
        (affineRestrictHom_comp hpe hWV)).compactification)
  have F2 := congrArg (fun i => i.inv.hom.hom) (restrictLocalIso_chartIso hpe 𝒦X 𝒦Y hWV
    (hp.isShriekable_of_isAffineOpen V.2) (hp.isShriekable_of_isAffineOpen W.2)
    (hq.isShriekable_of_isAffineOpen U.2) hVU hWU).symm
  have F3 := congrArg (fun φ => φ.hom.hom) ((UpperShriek.factorIsoOf c e₂ hh hV hW).hom.naturality
    φ)
  have F4 := congrArg (fun φ => φ.hom.hom) ((UpperShriek.factorIsoOf c e₁ hh (hp.isShriekable_ι V.1)
    (hp.isShriekable_ι W.1)).inv_hom_id_app 𝒦X.complex)
  have F5 := congrArg (fun φ => φ.hom)
    (UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion_factorIso c e₁ hh (hp.isShriekable_ι V.1)
      (hp.isShriekable_ι W.1) 𝒦X.complex)
  have F6a := congrArg (fun φ => φ.hom)
    ((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c (X.homOfLE hWV) hh).hom.naturality
      ((UpperShriek.shriekOf c (V.1.ι ≫ f) hV).map
        φ))
  have F6b := congrArg (fun φ => φ.hom)
    ((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c (X.homOfLE hWV) hh).hom.naturality
      (affineChartNormalization c 𝒦X 𝒦Y hpe U V hVU).inv)
  have F7 := congrArg (fun φ => φ.hom)
    (UpperShriek.factorIsoOf_hom_app_comp_shriekOfIsoPullbackOfIsOpenImmersion c e₂ hh hV hW
      F.compactification (F.precompOpen (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
        (affineRestrictHom_comp hpe hWV)).compactification
      D)
  have F8 := congrArg (fun i => (i.hom.app D).hom.hom)
    (upperShriekPlusIso_symm (affineHom (hp := hp) (hq := hq) hpe V) (c _ hV) F.compactification)
  have LSfact := chart_restrict_ls_chase (Stacks.Duality.derivedPullback (X.homOfLE hWV))
    (((DominatingCompactification.upperShriekPlusIso (affineHom (hp := hp) (hq := hq) hpe W)
        (c _ hW) (F.precompOpen (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
        (affineRestrictHom_comp hpe hWV)).compactification).inv.app
        D).hom.hom)
    (((DominatingCompactification.upperShriekPlusIso (affineHom (hp := hp) (hq := hq) hpe W)
        (F.precompOpen (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
        (affineRestrictHom_comp hpe hWV)).compactification (c _ hW)).hom.app
        D).hom.hom)
    (((UpperShriek.shriekOf c (W.1.ι ≫ f) hW).map φ).hom.hom)
    ((affineChartNormalization c 𝒦X 𝒦Y hpe U W hWU).inv.hom.hom)
    (((UpperShriek.factorIsoOf c e₂ hh hV hW).hom.app 𝒦Y.complex).hom.hom)
    (((UpperShriek.shriekOf c (X.homOfLE hWV) hh).map
        (affineChartNormalization c 𝒦X 𝒦Y hpe U V hVU).inv).hom.hom)
    (((UpperShriek.factorIsoOf c e₁ hh (hp.isShriekable_ι V.1) (hp.isShriekable_ι W.1)).inv.app
        𝒦X.complex).hom.hom)
    (((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c W.1.ι (hp.isShriekable_ι W.1)).hom.app
        𝒦X.complex).hom)
    (((UpperShriek.factorIsoOf c e₁ hh (hp.isShriekable_ι V.1) (hp.isShriekable_ι W.1)).hom.app
        𝒦X.complex).hom.hom)
    (((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c (X.homOfLE hWV) hh).hom.app
        ((UpperShriek.shriekOf c V.1.ι (hp.isShriekable_ι V.1)).obj 𝒦X.complex)).hom)
    (((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c V.1.ι (hp.isShriekable_ι V.1)).hom.app
        𝒦X.complex).hom)
    (((quasiCoherentDerivedPullbackCompIso (X.homOfLE hWV) V.1.ι).hom.app 𝒦X.complex.obj).hom ≫
        ((quasiCoherentDerivedPullbackCongr e₁).hom.app 𝒦X.complex.obj).hom)
    (((UpperShriek.factorIsoOf c e₂ hh hV hW).hom.app
        D).hom.hom)
    (((UpperShriek.shriekOf c (X.homOfLE hWV) hh).map
        ((UpperShriek.shriekOf c (V.1.ι ≫ f) hV).map φ)).hom.hom)
    (((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c (X.homOfLE hWV) hh).hom.app
        ((UpperShriek.shriekOf c (V.1.ι ≫ f) hV).obj
          D)).hom)
    (((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c (X.homOfLE hWV) hh).hom.app
        ((UpperShriek.shriekOf c (V.1.ι ≫ f) hV).obj 𝒦Y.complex)).hom)
    (((UpperShriek.shriekOf c (V.1.ι ≫ f) hV).map φ).hom.hom)
    ((affineChartNormalization c 𝒦X 𝒦Y hpe U V hVU).inv.hom.hom)
    (((upperShriekPlusCongr (affineRestrictHom_comp hpe hWV).symm
        (F.precompOpen (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
        (affineRestrictHom_comp hpe hWV)).compactification
        (F.compactification.precompOpen
          (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left)).hom.app
        D).hom.hom)
    ((upperShriekPrecompOpenIso (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
        (affineHom (hp := hp) (hq := hq) hpe V) F.compactification).hom.app
        D.obj).hom
    ((Stacks.Duality.derivedPullbackCompIso (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left
        F.compactification.immersion).inv.app ((rightAdjointStd F.compactification.toBase).obj
        (dualizingObject (isDualizing_stdComplex c hωS 𝒦Y))))
    (((DominatingCompactification.upperShriekPlusIso (affineHom (hp := hp) (hq := hq) hpe V)
        (c _ hV) F.compactification).inv.app
        D).hom.hom)
    (((DominatingCompactification.upperShriekPlusIso (affineHom (hp := hp) (hq := hq) hpe V)
        F.compactification (c _ hV)).hom.app
        D).hom.hom)
    F1 F2 F3 F4 F5 F6a F6b F7 (Category.comp_id _) F8
  refine chart_restrict_std_chase' (comparison W.1).inverse
    (pull (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left) (comparison V.1).inverse
    (Stacks.Duality.derivedPullback (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left)
    (pullModelConj (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left)
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _ :
      quasiCoherentDerivedCategoryPlusOfModel (ftsOf (W.1.ι ≫ f) hW.separatedFiniteType).left ⥤
        DerivedCategory (ftsOf (W.1.ι ≫ f) hW.separatedFiniteType).left.Modules).mapIso
      ((DominatingCompactification.upperShriekPlusIso (affineHom (hp := hp) (hq := hq) hpe W)
        (c _ hW) (F.precompOpen (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
          (affineRestrictHom_comp hpe hWV)).compactification).app
        D))
    ((ObjectProperty.ι _).mapIso ((upperShriek (ftsHomSelf hW) (c _ hW)).mapIso
        (dualizingQCohIso c 𝒦Y (isDualizing_stdComplex c hωS 𝒦Y))) ≪≫
      (ObjectProperty.ι _).mapIso ((ObjectProperty.ι _).mapIso
        (affineChartNormalization c 𝒦X 𝒦Y hpe U W hWU).symm))
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _ :
      quasiCoherentDerivedCategoryPlusOfModel (ftsOf (W.1.ι ≫ f) hW.separatedFiniteType).left ⥤
        DerivedCategory (ftsOf (W.1.ι ≫ f) hW.separatedFiniteType).left.Modules).mapIso
        ((upperShriekPlusCongr (affineRestrictHom_comp hpe hWV).symm
          (F.precompOpen (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
            (affineRestrictHom_comp hpe hWV)).compactification
          (F.compactification.precompOpen
            (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left)).app
            D))
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _ :
      quasiCoherentDerivedCategoryPlusOfModel (ftsOf (V.1.ι ≫ f) hV.separatedFiniteType).left ⥤
        DerivedCategory (ftsOf (V.1.ι ≫ f) hV.separatedFiniteType).left.Modules).mapIso
      ((DominatingCompactification.upperShriekPlusIso (affineHom (hp := hp) (hq := hq) hpe V)
        (c _ hV) F.compactification).app
        D))
    ((ObjectProperty.ι _).mapIso ((upperShriek (ftsHomSelf hV) (c _ hV)).mapIso
        (dualizingQCohIso c 𝒦Y (isDualizing_stdComplex c hωS 𝒦Y))) ≪≫
      (ObjectProperty.ι _).mapIso ((ObjectProperty.ι _).mapIso
        (affineChartNormalization c 𝒦X 𝒦Y hpe U V hVU).symm))
    ((ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (V.1 : Scheme.{u}).ringCatSheaf))).mapIso
      ((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c V.1.ι
        (hp.isShriekable_ι V.1)).app 𝒦X.complex))
    ((ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (W.1 : Scheme.{u}).ringCatSheaf))).mapIso
      ((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c W.1.ι
        (hp.isShriekable_ι W.1)).app 𝒦X.complex))
    ((pullModelConj F.compactification.immersion).app
      ((rightAdjointStd F.compactification.toBase).obj
        (dualizingObject (isDualizing_stdComplex c hωS 𝒦Y))))
    ((pullCompIso (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left
      F.compactification.immersion
      ((affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left ≫ F.compactification.immersion)
      rfl).app
      ((rightAdjointStd F.compactification.toBase).obj
        (dualizingObject (isDualizing_stdComplex c hωS 𝒦Y))))
    ((pullModelConj ((affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left ≫
        F.compactification.immersion)).app
      ((rightAdjointStd F.compactification.toBase).obj
        (dualizingObject (isDualizing_stdComplex c hωS 𝒦Y))))
    ((pullModelConj V.1.ι).app _)
    ((pullCompIso (X.homOfLE hWV) V.1.ι W.1.ι (X.homOfLE_ι hWV)).app (stdComplex c 𝒦X))
    ((pullModelConj W.1.ι).app _)
    ((Stacks.Duality.derivedPullbackCompIso (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left
        F.compactification.immersion).hom.app
      ((rightAdjointStd F.compactification.toBase).obj
        (dualizingObject (isDualizing_stdComplex c hωS 𝒦Y))) ≫ eqToHom rfl)
    ((Stacks.Duality.derivedPullbackCompIso (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left
        F.compactification.immersion).inv.app
      ((rightAdjointStd F.compactification.toBase).obj
        (dualizingObject (isDualizing_stdComplex c hωS 𝒦Y))))
    ((Stacks.Duality.derivedPullbackCompIso (X.homOfLE hWV) V.1.ι).hom.app 𝒦X.complex.obj.obj ≫
      eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj 𝒦X.complex.obj.obj)
        (X.homOfLE_ι hWV)))
    ((Iso.inv_hom_id_app_assoc _ _ _).trans (eqToHom_refl _ _))
    (pullModelConj_hom_app_comp_pullCompIso (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left
      F.compactification.immersion _ rfl _)
    (pullModelConj_hom_app_comp_pullCompIso (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left
      V.1.ι W.1.ι (X.homOfLE_ι hWV) _)
    ?_ _ _ _ _ _ _ (stdComplexRestrictIso c 𝒦X W.1)
    (stdComplexRestrictIso c 𝒦X V.1) rfl rfl rfl rfl rfl rfl rfl rfl
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq LSfact) (by heq_congr)))

end NormalizedOnOpens

end Stacks.Duality

end
