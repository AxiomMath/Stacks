module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingHomSquareComparisonIso
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparisonComp
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiChartComparisonBridge

/-!
# Condition (2) of Stacks 0DJ8 under ring transport

Two whole charts of one square of schemes whose coordinate rings are related by isomorphisms
compatible with the chart maps and with the open immersions test the same condition (2) of
[Stacks, Tag 0DJ8]. On derived sheafifications this is the ring-level invariance of Stacks 065Z
(`RingTheory.TorIndependence.isIso_ringHomSquareComparisonLS_comp_iff_of_iso`) read through
`AlgebraicGeometry.BaseChangeChart.isIso_comparison_tilde_iff_of_eq`; the identification of the
two tilde data is the composition law of Stacks 08DW
(`AlgebraicGeometry.affinePullbackComparison_comp_derivedPullbackCompIso`) together with the
coherence of Stacks 0D5S.

## Main results

* `Stacks.Duality.derivedPullbackCompIso_transport_coherence`: coherence of the composition
  isomorphisms for a ring transport square.
* `AlgebraicGeometry.affinePullbackComparison_transport`: the affine comparison of Stacks 08DW
  under a commutative square of rings.
* `AlgebraicGeometry.tildeForm_transport`: the tilde datum of a chart under ring transport.
* `AlgebraicGeometry.BaseChangeChart.isIso_comparison_tilde_iff_of_ringIso`: condition (2) on
  derived sheafifications under ring transport.
* `AlgebraicGeometry.exists_iso_derivedPullback_tilde`: an object with quasi-coherent cohomology
  on a scheme isomorphic to `Spec A` is a derived sheafification.
* `AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_of_ringIso`: condition (2) under ring
  transport, for all data with quasi-coherent cohomology.
* `AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_of_isIso`: on whole charts condition (2)
  does not depend on the chart.
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Duality

variable {X' X P₁ P₁' P P' : Scheme.{u}}

/-- The two composites `X' ⟶ P` of a ring transport square agree. -/
theorem transport_square_eq {g' : X' ⟶ X} {j : X ⟶ P₁} {j' : X' ⟶ P₁'} {γ₁ : P₁' ⟶ P₁}
    {a : P₁ ⟶ P} {a' : P₁' ⟶ P'} {γ : P' ⟶ P} (w₁ : g' ≫ j = j' ≫ γ₁)
    (hr : γ₁ ≫ a = a' ≫ γ) : g' ≫ j ≫ a = (j' ≫ a') ≫ γ := by
  rw [← Category.assoc, w₁, Category.assoc, hr, Category.assoc]

/-- **Coherence of Stacks 0D5S for a ring transport square.** For `g' ≫ j = j' ≫ γ₁` and
`γ₁ ≫ a = a' ≫ γ`, the two identifications of `L(g')^* L(j ≫ a)^* T` with
`L(j')^* L(a')^* L(γ)^* T` built from the composition isomorphisms agree. -/
theorem derivedPullbackCompIso_transport_coherence (g' : X' ⟶ X) (j : X ⟶ P₁) (j' : X' ⟶ P₁')
    (γ₁ : P₁' ⟶ P₁) (a : P₁ ⟶ P) (a' : P₁' ⟶ P') (γ : P' ⟶ P) (w₁ : g' ≫ j = j' ≫ γ₁)
    (hr : γ₁ ≫ a = a' ≫ γ) (T : DerivedCategory P.Modules) :
    (derivedPullback g').map ((derivedPullbackCompIso j a).inv.app T) ≫
        (derivedPullbackCompIso g' j).hom.app ((derivedPullback a).obj T) ≫
        eqToHom (congrArg (fun t => (derivedPullback t).obj ((derivedPullback a).obj T)) w₁) ≫
        (derivedPullbackCompIso j' γ₁).inv.app ((derivedPullback a).obj T) ≫
        (derivedPullback j').map ((derivedPullbackCompIso γ₁ a).hom.app T) ≫
        (derivedPullback j').map (eqToHom (congrArg (fun t => (derivedPullback t).obj T) hr)) ≫
        (derivedPullback j').map ((derivedPullbackCompIso a' γ).inv.app T) =
      (derivedPullbackCompIso g' (j ≫ a)).hom.app T ≫
        eqToHom (congrArg (fun t => (derivedPullback t).obj T)
          (transport_square_eq w₁ hr)) ≫
        (derivedPullbackCompIso (j' ≫ a') γ).inv.app T ≫
        (derivedPullbackCompIso j' a').inv.app ((derivedPullback γ).obj T) := by
  rw [← cancel_mono ((derivedPullback j').map ((derivedPullbackCompIso a' γ).hom.app T) ≫
    (derivedPullbackCompIso j' (a' ≫ γ)).hom.app T)]
  simp only [Category.assoc]
  have hc : ∀ {Y₁ Y₂ Z₁ : Scheme.{u}} (F : Y₁ ⟶ Y₂) {G H : DerivedCategory Z₁.Modules ⥤
      DerivedCategory Y₂.Modules} (α : G ≅ H) (M : DerivedCategory Z₁.Modules)
      {Z : DerivedCategory Y₁.Modules} (h : (derivedPullback F).obj (H.obj M) ⟶ Z),
      (derivedPullback F).map (α.inv.app M) ≫ (derivedPullback F).map (α.hom.app M) ≫ h = h :=
    by
      intro Y₁ Y₂ Z₁ F G H α M Z h
      rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
        Category.id_comp]
  rw [hc, derivedPullback_map_eqToHom_comp_derivedPullbackCompIso_hom_app j' hr T,
    ← derivedPullbackCompIso_hom_app_assoc_assoc, Iso.inv_hom_id_app_assoc,
    eqToHom_comp_derivedPullbackCompIso_hom_app_assoc w₁ a,
    derivedPullbackCompIso_hom_app_assoc'_assoc, hc,
    ← derivedPullbackCompIso_hom_app_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc]
  simp only [eqToHom_trans]

end Stacks.Duality

namespace AlgebraicGeometry

open CochainComplex.DerivedExtensionScalars

/-- The chase behind `affinePullbackComparison_transport`. -/
theorem affinePullbackComparison_transport_chase {𝒟 𝒟' 𝒯 : Type*} [Category* 𝒟] [Category* 𝒟']
    [Category* 𝒯] (t : 𝒯 ⥤ 𝒟) (Pa : 𝒟' ⥤ 𝒟) {B₀ B₁ B₂ B₃ B₄ B₅ : 𝒟} {T₀ T₁ T₂ T₃ T₄ : 𝒯}
    {Y₀ Y₁ Y₂ : 𝒟'}
    (A₁₂ : B₀ ⟶ t.obj T₀) (e₁ : B₀ ⟶ B₁) (e₁' : B₁ ⟶ B₀) (k₁ : B₂ ⟶ B₁) (k₁' : B₁ ⟶ B₂)
    (x₁ : B₂ ⟶ B₃) (x₂ : B₃ ⟶ t.obj T₁) (l₁ : T₁ ⟶ T₀) (E : T₀ ⟶ T₂) (e₂ : B₀ ⟶ B₄)
    (A₂₁ : B₄ ⟶ t.obj T₂) (e₃ : B₄ ⟶ B₅) (k₂' : B₅ ⟶ Pa.obj Y₀) (y₁ : Y₀ ⟶ Y₁)
    (y₂ : Pa.obj Y₁ ⟶ t.obj T₃) (l₂ : T₃ ⟶ T₂) (l₂' : T₂ ⟶ T₃) (tψ : Y₁ ⟶ Y₂)
    (z : Pa.obj Y₂ ⟶ t.obj T₄) (Lψ : T₃ ⟶ T₄) (E' : B₁ ⟶ B₅)
    (h₁ : A₁₂ = e₁ ≫ k₁' ≫ x₁ ≫ x₂ ≫ t.map l₁) (hk : k₁ ≫ k₁' = 𝟙 _) (he₁ : e₁' ≫ e₁ = 𝟙 _)
    (h₃ : A₁₂ ≫ t.map E = e₂ ≫ A₂₁) (h₂ : A₂₁ = e₃ ≫ k₂' ≫ Pa.map y₁ ≫ y₂ ≫ t.map l₂)
    (hl : l₂ ≫ l₂' = 𝟙 _) (h₄ : y₂ ≫ t.map Lψ = Pa.map tψ ≫ z) (hE : e₁' ≫ e₂ ≫ e₃ = E') :
    x₁ ≫ x₂ ≫ t.map (l₁ ≫ E ≫ l₂' ≫ Lψ) = k₁ ≫ E' ≫ k₂' ≫ Pa.map (y₁ ≫ tψ) ≫ z := by
  have e : x₁ ≫ x₂ ≫ t.map l₁ = k₁ ≫ e₁' ≫ A₁₂ := by
    rw [h₁, reassoc_of% he₁, reassoc_of% hk]
  rw [t.map_comp, reassoc_of% e, t.map_comp, reassoc_of% h₃, h₂, t.map_comp]
  simp only [Category.assoc]
  rw [← t.map_comp_assoc, hl, CategoryTheory.Functor.map_id, Category.id_comp, h₄, ← hE]
  simp only [Category.assoc, Pa.map_comp]

/-- Ring transport of the affine comparison of Stacks 08DW along an equality of ring maps. -/
theorem affinePullbackComparison_hom_app_eqToHom {R S : CommRingCat.{u}} {x y : R ⟶ S}
    (h : x = y) (N : DerivedCategory (ModuleCat.{u} R)) :
    (affinePullbackComparison R S x).hom.app N ≫ (tilde.functor S).mapDerivedCategory.map
        (eqToHom (congrArg (fun t => (totalDerivedExtensionScalars.{u, u, u} t).functor.obj N)
          (congrArg CommRingCat.Hom.hom h))) =
      eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback (Spec.map t)).obj
          ((tilde.functor R).mapDerivedCategory.obj N)) h) ≫
        (affinePullbackComparison R S y).hom.app N := by
  subst h
  simp

section Transport

variable {A A' A₁ A₁' : CommRingCat.{u}} {c : A ⟶ A'} {c₁ : A₁ ⟶ A₁'} {eA : A ⟶ A₁}
  {eA' : A' ⟶ A₁'}

/-- A commutative square of rings gives a commutative square of spectra. -/
theorem specMap_transport_eq (wc : c ≫ eA' = eA ≫ c₁) :
    Spec.map c₁ ≫ Spec.map eA = Spec.map eA' ≫ Spec.map c := by
  rw [← Spec.map_comp, ← Spec.map_comp, wc]

/-- **The affine comparison of Stacks 08DW under a ring transport square.** For a commutative
square `c ≫ eA' = eA ≫ c₁` of rings, the comparison along `c₁` at `N ⊗ᴸ_A A₁`, followed by the
morphism induced by `ψ : N ⊗ᴸ_A A' ⟶ N'`, is the comparison along `c` followed by `ψ`, read
through the composition isomorphisms of derived pullback and the comparisons along `eA`, `eA'`. -/
theorem affinePullbackComparison_transport (wc : c ≫ eA' = eA ≫ c₁)
    (N : DerivedCategory (ModuleCat.{u} A)) (N' : DerivedCategory (ModuleCat.{u} A'))
    (ψ : (totalDerivedExtensionScalars.{u, u, u} c.hom).functor.obj N ⟶ N') :
    (Stacks.Duality.derivedPullback (Spec.map c₁)).map
        ((affinePullbackComparison A A₁ eA).hom.app N) ≫
      (affinePullbackComparison A₁ A₁' c₁).hom.app
        ((totalDerivedExtensionScalars.{u, u, u} eA.hom).functor.obj N) ≫
      (tilde.functor A₁').mapDerivedCategory.map
        ((totalDerivedExtensionScalarsComp.{u, u} eA.hom c₁.hom).hom.app N ≫
          eqToHom (congrArg (fun t => (totalDerivedExtensionScalars.{u, u, u} t).functor.obj N)
            (congrArg CommRingCat.Hom.hom wc.symm)) ≫
          (totalDerivedExtensionScalarsComp.{u, u} c.hom eA'.hom).inv.app N ≫
          (totalDerivedExtensionScalars.{u, u, u} eA'.hom).functor.map ψ) =
    (Stacks.Duality.derivedPullbackCompIso (Spec.map c₁) (Spec.map eA)).hom.app
        ((tilde.functor A).mapDerivedCategory.obj N) ≫
      eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj
        ((tilde.functor A).mapDerivedCategory.obj N)) (specMap_transport_eq wc)) ≫
      (Stacks.Duality.derivedPullbackCompIso (Spec.map eA') (Spec.map c)).inv.app
        ((tilde.functor A).mapDerivedCategory.obj N) ≫
      (Stacks.Duality.derivedPullback (Spec.map eA')).map
        ((affinePullbackComparison A A' c).hom.app N ≫
          (tilde.functor A').mapDerivedCategory.map ψ) ≫
      (affinePullbackComparison A' A₁' eA').hom.app N' :=
  affinePullbackComparison_transport_chase (tilde.functor A₁').mapDerivedCategory
    (Stacks.Duality.derivedPullback (Spec.map eA')) _ _
    (eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj
      ((tilde.functor A).mapDerivedCategory.obj N)) (Spec.map_comp eA c₁).symm)) _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _
    (affinePullbackComparison_comp_derivedPullbackCompIso A A₁ A₁' eA c₁ N) (Iso.hom_inv_id_app _ _)
    (by simp only [eqToHom_trans, eqToHom_refl])
    (affinePullbackComparison_hom_app_eqToHom wc.symm N)
    (affinePullbackComparison_comp_derivedPullbackCompIso A A' A₁' c eA' N) (Iso.hom_inv_id_app _ _)
    ((affinePullbackComparison A' A₁' eA').hom.naturality ψ).symm
    (by simp only [eqToHom_trans])

/-- The chase behind `tildeForm_transport`. -/
theorem tildeForm_transport_chase {𝒳 𝒳' 𝒬 : Type*} [Category* 𝒳] [Category* 𝒳'] [Category* 𝒬]
    (Pg : 𝒳 ⥤ 𝒳') (Pj' : 𝒬 ⥤ 𝒳') {U₀ U₁ U₂ : 𝒳} {V₀ V₁ V₂ V₃ V₄ V₅ V₆ V₇ : 𝒳'}
    {Q₀ Q₁ Q₂ Q₃ Q₄ Q₅ Q₆ Q₇ : 𝒬}
    (K₁ : U₀ ⟶ U₁) (jα : U₁ ⟶ U₂) (C₁ : Pg.obj U₂ ⟶ V₀) (Ew : V₀ ⟶ V₁) (C₂ : V₁ ⟶ Pj'.obj Q₀)
    (β : Q₀ ⟶ Q₁) (tψ₁ : Q₁ ⟶ Q₂) (C₁' : Pg.obj U₁ ⟶ V₂) (gjα : V₂ ⟶ V₀) (Ew' : V₂ ⟶ V₃)
    (jγα : V₃ ⟶ V₁) (C₂' : V₃ ⟶ Pj'.obj Q₃) (xα : Q₃ ⟶ Q₀) (k₁ : Q₃ ⟶ Q₄) (E' : Q₄ ⟶ Q₅)
    (k₂' : Q₅ ⟶ Q₆) (yA : Q₆ ⟶ Q₇) (z : Q₇ ⟶ Q₂) (D₁ : Pg.obj U₀ ⟶ V₄) (D₂ : V₄ ⟶ V₅)
    (D₃ : V₅ ⟶ V₆) (D₄ : V₆ ⟶ Pj'.obj Q₆) (yW : V₆ ⟶ V₇) (D₅ : V₇ ⟶ Pj'.obj Q₇)
    (n₁ : Pg.map jα ≫ C₁ = C₁' ≫ gjα) (n₂ : gjα ≫ Ew = Ew' ≫ jγα)
    (n₃ : jγα ≫ C₂ = C₂' ≫ Pj'.map xα) (inner : xα ≫ β ≫ tψ₁ = k₁ ≫ E' ≫ k₂' ≫ yA ≫ z)
    (hS : Pg.map K₁ ≫ C₁' ≫ Ew' ≫ C₂' ≫ Pj'.map k₁ ≫ Pj'.map E' ≫ Pj'.map k₂' =
      D₁ ≫ D₂ ≫ D₃ ≫ D₄) (n₄ : yW ≫ D₅ = D₄ ≫ Pj'.map yA) :
    Pg.map (K₁ ≫ jα) ≫ C₁ ≫ Ew ≫ C₂ ≫ Pj'.map (β ≫ tψ₁) =
      (D₁ ≫ D₂ ≫ D₃ ≫ yW) ≫ D₅ ≫ Pj'.map z := by
  rw [Pg.map_comp, Category.assoc, reassoc_of% n₁, reassoc_of% n₂, reassoc_of% n₃,
    ← Pj'.map_comp, inner]
  simp only [Pj'.map_comp, Category.assoc]
  rw [reassoc_of% hS, reassoc_of% n₄]

variable {X X' : Scheme.{u}}

/-- **The tilde form of a chart datum under ring transport.** For `g' ≫ j = j' ≫ Spec c₁` and a
commutative square `c ≫ eA' = eA ≫ c₁` of rings, the identification
`L(j ≫ Spec eA)^* Ñ ≅ L(j)^* (N ⊗ᴸ_A A₁)~` carries the morphism of Stacks 0DJ8 (2) on derived
sheafifications built from `ψ` along `c` to the one built from the transported `ψ` along `c₁`. -/
theorem tildeForm_transport (wc : c ≫ eA' = eA ≫ c₁) (g' : X' ⟶ X) (j : X ⟶ Spec A₁)
    (j' : X' ⟶ Spec A₁') (w₁ : g' ≫ j = j' ≫ Spec.map c₁)
    (N : DerivedCategory (ModuleCat.{u} A)) (N' : DerivedCategory (ModuleCat.{u} A'))
    (ψ : (totalDerivedExtensionScalars.{u, u, u} c.hom).functor.obj N ⟶ N') :
    (Stacks.Duality.derivedPullback g').map
        ((Stacks.Duality.derivedPullbackCompIso j (Spec.map eA)).inv.app
            ((tilde.functor A).mapDerivedCategory.obj N) ≫
          (Stacks.Duality.derivedPullback j).map ((affinePullbackComparison A A₁ eA).hom.app N)) ≫
      (Stacks.Duality.derivedPullbackCompIso g' j).hom.app
          ((tilde.functor A₁).mapDerivedCategory.obj
            ((totalDerivedExtensionScalars.{u, u, u} eA.hom).functor.obj N)) ≫
      eqToHom (congrArg (fun t : X' ⟶ Spec A₁ => (Stacks.Duality.derivedPullback t).obj
          ((tilde.functor A₁).mapDerivedCategory.obj
            ((totalDerivedExtensionScalars.{u, u, u} eA.hom).functor.obj N))) w₁) ≫
      (Stacks.Duality.derivedPullbackCompIso j' (Spec.map c₁)).inv.app
          ((tilde.functor A₁).mapDerivedCategory.obj
            ((totalDerivedExtensionScalars.{u, u, u} eA.hom).functor.obj N)) ≫
      (Stacks.Duality.derivedPullback j').map
        ((affinePullbackComparison A₁ A₁' c₁).hom.app
            ((totalDerivedExtensionScalars.{u, u, u} eA.hom).functor.obj N) ≫
          (tilde.functor A₁').mapDerivedCategory.map
            ((totalDerivedExtensionScalarsComp.{u, u} eA.hom c₁.hom).hom.app N ≫
              eqToHom (congrArg (fun t => (totalDerivedExtensionScalars.{u, u, u} t).functor.obj N)
                (congrArg CommRingCat.Hom.hom wc.symm)) ≫
              (totalDerivedExtensionScalarsComp.{u, u} c.hom eA'.hom).inv.app N ≫
              (totalDerivedExtensionScalars.{u, u, u} eA'.hom).functor.map ψ)) =
    ((Stacks.Duality.derivedPullbackCompIso g' (j ≫ Spec.map eA)).hom.app
        ((tilde.functor A).mapDerivedCategory.obj N) ≫
      eqToHom (congrArg (fun t : X' ⟶ Spec A => (Stacks.Duality.derivedPullback t).obj
          ((tilde.functor A).mapDerivedCategory.obj N))
        (Stacks.Duality.transport_square_eq w₁ (specMap_transport_eq wc))) ≫
      (Stacks.Duality.derivedPullbackCompIso (j' ≫ Spec.map eA') (Spec.map c)).inv.app
          ((tilde.functor A).mapDerivedCategory.obj N) ≫
      (Stacks.Duality.derivedPullback (j' ≫ Spec.map eA')).map
        ((affinePullbackComparison A A' c).hom.app N ≫
          (tilde.functor A').mapDerivedCategory.map ψ)) ≫
      (Stacks.Duality.derivedPullbackCompIso j' (Spec.map eA')).inv.app
          ((tilde.functor A').mapDerivedCategory.obj N') ≫
      (Stacks.Duality.derivedPullback j').map ((affinePullbackComparison A' A₁' eA').hom.app N') :=
  tildeForm_transport_chase (Stacks.Duality.derivedPullback g') (Stacks.Duality.derivedPullback j')
    _ _ _ _ _ _ _ _ _ _ _ _
    ((Stacks.Duality.derivedPullback (Spec.map c₁)).map
      ((affinePullbackComparison A A₁ eA).hom.app N))
    _ _ _ _ _ _ _ _
    ((Stacks.Duality.derivedPullbackCompIso j' (Spec.map eA')).inv.app
      ((Stacks.Duality.derivedPullback (Spec.map c)).obj
        ((tilde.functor A).mapDerivedCategory.obj N)))
    _ _
    ((Stacks.Duality.derivedPullbackCompIso g' j).hom.naturality
      ((affinePullbackComparison A A₁ eA).hom.app N))
    (Stacks.Duality.derivedPullback_map_comp_eqToHom w₁
      ((affinePullbackComparison A A₁ eA).hom.app N))
    ((Stacks.Duality.derivedPullbackCompIso j' (Spec.map c₁)).inv.naturality
      ((affinePullbackComparison A A₁ eA).hom.app N))
    (affinePullbackComparison_transport wc N N' ψ)
    (Stacks.Duality.derivedPullbackCompIso_transport_coherence g' j j' (Spec.map c₁) (Spec.map eA)
      (Spec.map eA') (Spec.map c) w₁ (specMap_transport_eq wc)
      ((tilde.functor A).mapDerivedCategory.obj N))
    ((Stacks.Duality.derivedPullbackCompIso j' (Spec.map eA')).inv.naturality
      ((affinePullbackComparison A A' c).hom.app N ≫ (tilde.functor A').mapDerivedCategory.map ψ))

end Transport

/-- Every morphism `Pg(K₀) ⟶ K₀'` is, up to isomorphisms `K₀ ≅ K₁` and `K₀' ≅ P(t(T₁))`, of the
form `α ≫ P(a ≫ t(ψ))` for `P`, `t` full and `α` invertible. -/
theorem exists_map_hom_comp_map_eq {𝒳 𝒳' 𝒬 𝒯 : Type*} [Category* 𝒳] [Category* 𝒳']
    [Category* 𝒬] [Category* 𝒯] (Pg : 𝒳 ⥤ 𝒳') (P : 𝒬 ⥤ 𝒳') [P.Full] (t : 𝒯 ⥤ 𝒬) [t.Full]
    {K₀ K₁ : 𝒳} {K₀' Y₁ Y₂ : 𝒳'} {B₀ : 𝒬} {T₀ T₁ : 𝒯} (e : K₀ ≅ K₁)
    (e' : K₀' ≅ P.obj (t.obj T₁)) (φ : Pg.obj K₀ ⟶ K₀') (α₁ : Pg.obj K₁ ⟶ Y₁) (α₂ : Y₁ ⟶ Y₂)
    (α₃ : Y₂ ⟶ P.obj B₀) [IsIso α₁] [IsIso α₂] [IsIso α₃] (a : B₀ ≅ t.obj T₀) :
    ∃ ψ : T₀ ⟶ T₁, Pg.map e.hom ≫ α₁ ≫ α₂ ≫ α₃ ≫ P.map (a.hom ≫ t.map ψ) = φ ≫ e'.hom :=
  ⟨t.preimage (a.inv ≫ P.preimage (inv α₃ ≫ inv α₂ ≫ inv α₁ ≫ Pg.map e.inv ≫ φ ≫ e'.hom)), by
    simp only [Functor.map_preimage, Iso.hom_inv_id_assoc,
      IsIso.hom_inv_id_assoc]
    rw [← Pg.map_comp_assoc, e.hom_inv_id, Pg.map_id, Category.id_comp]⟩

/-- The chase combining a change of data with the ring transport of the tilde datum. -/
theorem map_comp_comp_eq_of_eq {𝒳 𝒳' : Type*} [Category* 𝒳] [Category* 𝒳'] (Pg : 𝒳 ⥤ 𝒳')
    {K₀ K₁ Z K₂ : 𝒳} {K₀' K₁' Z' K₂' : 𝒳'} (e : K₀ ⟶ K₁) (J₁ : K₁ ⟶ Z) (J₂ : Z ⟶ K₂)
    (φ : Pg.obj K₀ ⟶ K₀') (e' : K₀' ⟶ K₁') (J₁' : K₁' ⟶ Z') (J₂' : Z' ⟶ K₂')
    (φW : Pg.obj K₁ ⟶ K₁') (φQ : Pg.obj K₂ ⟶ K₂') (h₁ : Pg.map e ≫ φW = φ ≫ e')
    (hT : Pg.map (J₁ ≫ J₂) ≫ φQ = φW ≫ J₁' ≫ J₂') :
    Pg.map (e ≫ J₁ ≫ J₂) ≫ φQ = φ ≫ e' ≫ J₁' ≫ J₂' := by
  rw [Pg.map_comp, Category.assoc, hT, reassoc_of% h₁]

/-- **An object with quasi-coherent cohomology on a scheme isomorphic to `Spec A` is a derived
sheafification.** For `j : X ⟶ Spec A` with a section `i` (`j ≫ i = 𝟙`), every `K` with
quasi-coherent cohomology is isomorphic to `L(j)^* Ñ` for some `N` in `D(A)`. -/
theorem exists_iso_derivedPullback_tilde {X : Scheme.{u}} {A : CommRingCat.{u}} (i : Spec A ⟶ X)
    (j : X ⟶ Spec A) (hji : j ≫ i = 𝟙 X) (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    ∃ M : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _),
      Nonempty (K ≅ (Stacks.Duality.derivedPullback j).obj ((tilde.functor A).mapDerivedCategory.obj
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M))) := by
  obtain ⟨ι, -, -⟩ := Stacks.Duality.exists_derivedPullbackIdIso_unit_laws X
  obtain ⟨N, ⟨a⟩⟩ := Functor.EssSurj.mem_essImage (F := derivedTilde A)
    ⟨(Stacks.Duality.derivedPullback i).obj K,
      fun n => Stacks.Duality.isQuasicoherent_homology_derivedPullback' i ⟨K, hK⟩ n⟩
  exact ⟨(Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).inverse.obj N,
    ⟨(ι.app K).symm ≪≫
      eqToIso (congrArg (fun t : X ⟶ X => (Stacks.Duality.derivedPullback t).obj K) hji.symm) ≪≫
      ((Stacks.Duality.derivedPullbackCompIso j i).app K).symm ≪≫
      (Stacks.Duality.derivedPullback j).mapIso
        ((tilde.functor A).mapDerivedCategory.mapIso
            ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).counitIso.app N) ≪≫
          ((derivedTildeCompι A).app N).symm ≪≫
          (DerivedCategoryB.derivedCategoryB (A := (Spec A).Modules)
            (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)).ι.mapIso a).symm⟩⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.BaseChangeChart

open CochainComplex.DerivedExtensionScalars

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Condition (2) of Stacks 0DJ8 under ring transport, on derived sheafifications.** Two whole
charts `W`, `Q` of one square whose rings are related by isomorphisms compatible with the
chart maps and the open immersions: the comparison on `W` for the tilde datum of `ψ` is
invertible exactly when the comparison on `Q` for the transported tilde datum is. -/
theorem isIso_comparison_tilde_iff_of_ringIso (W Q : BaseChangeChart f g f' g') [IsIso W.incU]
    [IsIso W.incU'] [IsIso Q.incU] [IsIso Q.incU'] (eR : W.R ≅ Q.R) (eA : W.A ≅ Q.A)
    (eR' : W.R' ≅ Q.R') (eA' : W.A' ≅ Q.A') (wa : W.a ≫ eA.hom = eR.hom ≫ Q.a)
    (wb : W.b ≫ eR'.hom = eR.hom ≫ Q.b) (wc : W.c ≫ eA'.hom = eA.hom ≫ Q.c)
    (wd : W.d ≫ eA'.hom = eR'.hom ≫ Q.d) (hU : inv W.incU = inv Q.incU ≫ Spec.map eA.hom)
    (hU' : inv W.incU' = inv Q.incU' ≫ Spec.map eA'.hom)
    (M : @DerivedCategory (ModuleCat.{u} W.A) _ _ (HasDerivedCategory.standard _))
    (M' : @DerivedCategory (ModuleCat.{u} W.A') _ _ (HasDerivedCategory.standard _))
    (ψ : (totalDerivedExtensionScalars.{u, u, u} W.c.hom).functor.obj
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M) ⟶
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A')).functor.obj M') :
    IsIso (W.comparison
        ((Stacks.Duality.derivedPullback (inv Q.incU ≫ Spec.map eA.hom)).obj
          ((tilde.functor W.A).mapDerivedCategory.obj
            ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M)))
        ((Stacks.Duality.derivedPullback (inv Q.incU' ≫ Spec.map eA'.hom)).obj
          ((tilde.functor W.A').mapDerivedCategory.obj
            ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A')).functor.obj M')))
        ((Stacks.Duality.derivedPullbackCompIso g' (inv Q.incU ≫ Spec.map eA.hom)).hom.app
            ((tilde.functor W.A).mapDerivedCategory.obj
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M)) ≫
          eqToHom (congrArg (fun t : X' ⟶ Spec W.A => (Stacks.Duality.derivedPullback t).obj
            ((tilde.functor W.A).mapDerivedCategory.obj
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M)))
            (Stacks.Duality.transport_square_eq Q.comp_inv_incU (specMap_transport_eq wc))) ≫
          (Stacks.Duality.derivedPullbackCompIso (inv Q.incU' ≫ Spec.map eA'.hom)
            (Spec.map W.c)).inv.app ((tilde.functor W.A).mapDerivedCategory.obj
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M)) ≫
          (Stacks.Duality.derivedPullback (inv Q.incU' ≫ Spec.map eA'.hom)).map
            ((affinePullbackComparison W.A W.A' W.c).hom.app
                ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M) ≫
              (tilde.functor W.A').mapDerivedCategory.map ψ))) ↔
      IsIso (Q.comparison
        ((Stacks.Duality.derivedPullback (inv Q.incU)).obj
          ((tilde.functor Q.A).mapDerivedCategory.obj
            ((totalDerivedExtensionScalars.{u, u, u} eA.hom.hom).functor.obj
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M))))
        ((Stacks.Duality.derivedPullback (inv Q.incU')).obj
          ((tilde.functor Q.A').mapDerivedCategory.obj
            ((totalDerivedExtensionScalars.{u, u, u} eA'.hom.hom).functor.obj
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A')).functor.obj
                M'))))
        ((Stacks.Duality.derivedPullbackCompIso g' (inv Q.incU)).hom.app
            ((tilde.functor Q.A).mapDerivedCategory.obj
              ((totalDerivedExtensionScalars.{u, u, u} eA.hom.hom).functor.obj
                ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj
                  M))) ≫
          eqToHom (congrArg (fun t : X' ⟶ Spec Q.A => (Stacks.Duality.derivedPullback t).obj
            ((tilde.functor Q.A).mapDerivedCategory.obj
              ((totalDerivedExtensionScalars.{u, u, u} eA.hom.hom).functor.obj
                ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj
                  M))))
            Q.comp_inv_incU) ≫
          (Stacks.Duality.derivedPullbackCompIso (inv Q.incU') (Spec.map Q.c)).inv.app
            ((tilde.functor Q.A).mapDerivedCategory.obj
              ((totalDerivedExtensionScalars.{u, u, u} eA.hom.hom).functor.obj
                ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj
                  M))) ≫
          (Stacks.Duality.derivedPullback (inv Q.incU')).map
            ((affinePullbackComparison Q.A Q.A' Q.c).hom.app
                ((totalDerivedExtensionScalars.{u, u, u} eA.hom.hom).functor.obj
                  ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj
                    M)) ≫
              (tilde.functor Q.A').mapDerivedCategory.map
                ((totalDerivedExtensionScalarsComp.{u, u} eA.hom.hom Q.c.hom).hom.app
                    ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj
                      M) ≫
                  eqToHom (congrArg (fun t => (totalDerivedExtensionScalars.{u, u, u} t).functor.obj
                    ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj
                      M))
                    (congrArg CommRingCat.Hom.hom wc.symm)) ≫
                  (totalDerivedExtensionScalarsComp.{u, u} W.c.hom eA'.hom.hom).inv.app
                    ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj
                      M) ≫
                  (totalDerivedExtensionScalars.{u, u, u} eA'.hom.hom).functor.map ψ)))) :=
  (isIso_comparison_tilde_iff_of_eq W hU hU'
    (Stacks.Duality.transport_square_eq Q.comp_inv_incU (specMap_transport_eq wc)) _ _ ψ).trans
    ((RingTheory.TorIndependence.isIso_ringHomSquareComparisonLS_comp_iff_of_iso W.isPushout
      Q.isPushout W.isPushout_hom Q.isPushout_hom eR eA eR' eA' wa wb wc wd M M' ψ).trans
      (isIso_comparison_tilde_iff_of_eq Q rfl rfl Q.comp_inv_incU _ _ _).symm)


/-- **Condition (2) of Stacks 0DJ8 under ring transport.** Two whole charts `W`, `Q` of one
square whose rings are related by isomorphisms compatible with the chart maps and the open
immersions test the same condition (2), for every `K`, `K'` with quasi-coherent cohomology. -/
theorem isIso_comparison_iff_of_ringIso (W Q : BaseChangeChart f g f' g') [IsIso W.incU]
    [IsIso W.incU'] [IsIso Q.incU] [IsIso Q.incU'] (eR : W.R ≅ Q.R) (eA : W.A ≅ Q.A)
    (eR' : W.R' ≅ Q.R') (eA' : W.A' ≅ Q.A') (wa : W.a ≫ eA.hom = eR.hom ≫ Q.a)
    (wb : W.b ≫ eR'.hom = eR.hom ≫ Q.b) (wc : W.c ≫ eA'.hom = eA.hom ≫ Q.c)
    (wd : W.d ≫ eA'.hom = eR'.hom ≫ Q.d) (hU : inv W.incU = inv Q.incU ≫ Spec.map eA.hom)
    (hU' : inv W.incU' = inv Q.incU' ≫ Spec.map eA'.hom) (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (K' : DerivedCategory X'.Modules)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    IsIso (W.comparison K K' φ) ↔ IsIso (Q.comparison K K' φ) := by
  have hj : (inv Q.incU ≫ Spec.map eA.hom) ≫ W.incU = 𝟙 X := by
    rw [← hU, IsIso.inv_hom_id]
  have hj' : (inv Q.incU' ≫ Spec.map eA'.hom) ≫ W.incU' = 𝟙 X' := by
    rw [← hU', IsIso.inv_hom_id]
  have hj'' : W.incU' ≫ (inv Q.incU' ≫ Spec.map eA'.hom) = 𝟙 (Spec W.A') := by
    rw [← hU', IsIso.hom_inv_id]
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_derivedPullback_tilde W.incU _ hj K hK
  obtain ⟨M', ⟨e'⟩⟩ := exists_iso_derivedPullback_tilde W.incU' _ hj' K' hK'
  have : (tilde.functor W.A').mapDerivedCategory.Full := Functor.Full.of_iso (derivedTildeCompι _)
  have : (Stacks.Duality.derivedPullback (inv Q.incU' ≫ Spec.map eA'.hom)).IsEquivalence :=
    by
      obtain ⟨ι₁, -, -⟩ := Stacks.Duality.exists_derivedPullbackIdIso_unit_laws X'
      obtain ⟨ι₂, -, -⟩ := Stacks.Duality.exists_derivedPullbackIdIso_unit_laws (Spec W.A')
      exact Functor.IsEquivalence.mk' (Stacks.Duality.derivedPullback W.incU')
        (Stacks.Duality.derivedPullbackCompIso W.incU' (inv Q.incU' ≫ Spec.map eA'.hom) ≪≫
          eqToIso (congrArg (fun t => Stacks.Duality.derivedPullback t) hj'') ≪≫ ι₂).symm
        (Stacks.Duality.derivedPullbackCompIso (inv Q.incU' ≫ Spec.map eA'.hom) W.incU' ≪≫
          eqToIso (congrArg (fun t => Stacks.Duality.derivedPullback t) hj') ≪≫ ι₁)
  obtain ⟨ψ, h₁⟩ := exists_map_hom_comp_map_eq (Stacks.Duality.derivedPullback g')
    (Stacks.Duality.derivedPullback (inv Q.incU' ≫ Spec.map eA'.hom))
    (tilde.functor W.A').mapDerivedCategory e e' φ
    ((Stacks.Duality.derivedPullbackCompIso g' (inv Q.incU ≫ Spec.map eA.hom)).hom.app
      ((tilde.functor W.A).mapDerivedCategory.obj
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M)))
    (eqToHom (congrArg (fun t : X' ⟶ Spec W.A => (Stacks.Duality.derivedPullback t).obj
      ((tilde.functor W.A).mapDerivedCategory.obj
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M)))
      (Stacks.Duality.transport_square_eq Q.comp_inv_incU (specMap_transport_eq wc))))
    ((Stacks.Duality.derivedPullbackCompIso (inv Q.incU' ≫ Spec.map eA'.hom)
      (Spec.map W.c)).inv.app ((tilde.functor W.A).mapDerivedCategory.obj
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M)))
    ((affinePullbackComparison W.A W.A' W.c).app
      ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M))
  refine (W.isIso_comparison_iff_of_iso e e' φ _ h₁).trans
    ((isIso_comparison_tilde_iff_of_ringIso W Q eR eA eR' eA' wa wb wc wd hU hU' M M' ψ).trans
      (Q.isIso_comparison_iff_of_iso
        (e ≪≫ ((Stacks.Duality.derivedPullbackCompIso (inv Q.incU) (Spec.map eA.hom)).app
            ((tilde.functor W.A).mapDerivedCategory.obj
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj
                M))).symm ≪≫
          (Stacks.Duality.derivedPullback (inv Q.incU)).mapIso
            ((affinePullbackComparison W.A Q.A eA.hom).app
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A)).functor.obj M)))
        (e' ≪≫ ((Stacks.Duality.derivedPullbackCompIso (inv Q.incU') (Spec.map eA'.hom)).app
            ((tilde.functor W.A').mapDerivedCategory.obj
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A')).functor.obj
                M'))).symm ≪≫
          (Stacks.Duality.derivedPullback (inv Q.incU')).mapIso
            ((affinePullbackComparison W.A' Q.A' eA'.hom).app
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} W.A')).functor.obj M')))
        φ _ ?_).symm)
  exact map_comp_comp_eq_of_eq (Stacks.Duality.derivedPullback g') e.hom _ _ φ e'.hom _ _ _ _ h₁
    (tildeForm_transport wc g' (inv Q.incU) (inv Q.incU') Q.comp_inv_incU _ _ ψ)

/-- The isomorphism of coordinate rings of two affine charts `Spec A ≅ T ≅ Spec B` of a
scheme, Spec being fully faithful. -/
def specRingIso {T : Scheme.{u}} {A B : CommRingCat.{u}} (i : Spec A ⟶ T) (j : Spec B ⟶ T)
    [IsIso i] [IsIso j] : A ≅ B where
  hom := Spec.preimage (j ≫ inv i)
  inv := Spec.preimage (i ≫ inv j)
  hom_inv_id := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id, Category.assoc,
      IsIso.inv_hom_id_assoc, IsIso.hom_inv_id])
  inv_hom_id := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id, Category.assoc,
      IsIso.inv_hom_id_assoc, IsIso.hom_inv_id])

/-- `specRingIso i j` induces `j ≫ i⁻¹` on spectra. -/
theorem specMap_specRingIso_hom {T : Scheme.{u}} {A B : CommRingCat.{u}} (i : Spec A ⟶ T)
    (j : Spec B ⟶ T) [IsIso i] [IsIso j] : Spec.map (specRingIso i j).hom = j ≫ inv i :=
  Spec.map_preimage _

/-- The ring isomorphisms of `specRingIso` commute with ring maps inducing one morphism of
schemes. -/
theorem specRingIso_comm {T₁ T₂ : Scheme.{u}} {A₁ A₂ B₁ B₂ : CommRingCat.{u}}
    (i₁ : Spec A₁ ⟶ T₁) (j₁ : Spec B₁ ⟶ T₁) (i₂ : Spec A₂ ⟶ T₂) (j₂ : Spec B₂ ⟶ T₂) [IsIso i₁]
    [IsIso j₁] [IsIso i₂] [IsIso j₂] (m : T₁ ⟶ T₂) (r : A₂ ⟶ A₁) (s : B₂ ⟶ B₁)
    (hr : i₁ ≫ m = Spec.map r ≫ i₂) (hs : j₁ ≫ m = Spec.map s ≫ j₂) :
    r ≫ (specRingIso i₁ j₁).hom = (specRingIso i₂ j₂).hom ≫ s := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_comp, specMap_specRingIso_hom, specMap_specRingIso_hom,
    ← cancel_mono i₂]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hr, IsIso.inv_hom_id_assoc, hs]

/-- **Condition (2) of Stacks 0DJ8 does not depend on the whole chart.** For two charts of one
square all of whose open immersions are isomorphisms, the comparisons for `φ : L(g')^*K ⟶ K'`
are invertible together, for every `K`, `K'` with quasi-coherent cohomology. -/
theorem isIso_comparison_iff_of_isIso (W Q : BaseChangeChart f g f' g') [IsIso W.incV]
    [IsIso W.incU] [IsIso W.incV'] [IsIso W.incU'] [IsIso Q.incV] [IsIso Q.incU]
    [IsIso Q.incV'] [IsIso Q.incU'] (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (K' : DerivedCategory X'.Modules)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    IsIso (W.comparison K K' φ) ↔ IsIso (Q.comparison K K' φ) :=
  isIso_comparison_iff_of_ringIso W Q (specRingIso W.incV Q.incV) (specRingIso W.incU Q.incU)
    (specRingIso W.incV' Q.incV') (specRingIso W.incU' Q.incU')
    (specRingIso_comm W.incU Q.incU W.incV Q.incV f W.a Q.a W.wU Q.wU)
    (specRingIso_comm W.incV' Q.incV' W.incV Q.incV g W.b Q.b W.wV' Q.wV')
    (specRingIso_comm W.incU' Q.incU' W.incU Q.incU g' W.c Q.c W.wU'U Q.wU'U)
    (specRingIso_comm W.incU' Q.incU' W.incV' Q.incV' f' W.d Q.d W.wU'V' Q.wU'V')
    (by rw [specMap_specRingIso_hom, IsIso.inv_hom_id_assoc])
    (by rw [specMap_specRingIso_hom, IsIso.inv_hom_id_assoc]) K hK K' hK' φ

end AlgebraicGeometry.BaseChangeChart
