module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartComparisonTilde

/-!
# Restriction of the chart comparison of Stacks 0DJ8 along open immersions

A chart `ch` of a cartesian square of schemes `X₂' → S₂'`, `X₂' → X₂`, `X₂ → S₂`, `S₂' → S₂` is
pushed forward along a map to a second square whose components on `X₂`, `S₂`, `S₂'` are open
immersions (`AlgebraicGeometry.BaseChangeChart.mapSquare`): it is the chart with the same rings and
the composite open immersions. Its comparison map of Stacks 0DJ8 (2) is the comparison of `ch` for
the restricted data, up to isomorphisms on both sides.

## Main definitions

* `AlgebraicGeometry.BaseChangeChart.mapSquare`: the pushed-forward chart.

## Main results

* `Stacks.Duality.derivedPullbackCompIso_restriction_square`: the coherence of Stacks 0D5S
  behind the comparison.
* `AlgebraicGeometry.BaseChangeChart.isIso_mapSquare_comparison_iff`: condition (2) on the
  pushed-forward chart is condition (2) on `ch` for the restrictions.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Duality

variable {A' A X₂' X₂ X₁' X₁ : Scheme.{u}}

/-- **Coherence of Stacks 0D5S for a restriction square.** For `u' ≫ g₂ = p ≫ u` and
`g₂ ≫ h = h' ≫ g₁`, the two identifications of `L(p)^* L(u ≫ h)^* K` with
`L(u')^* L(h')^* L(g₁)^* K` built from the composition isomorphisms agree. -/
theorem derivedPullbackCompIso_restriction_square (p : A' ⟶ A) (u : A ⟶ X₂) (h : X₂ ⟶ X₁)
    (u' : A' ⟶ X₂') (h' : X₂' ⟶ X₁') (g₂ : X₂' ⟶ X₂) (g₁ : X₁' ⟶ X₁) (w₂ : u' ≫ g₂ = p ≫ u)
    (w : g₂ ≫ h = h' ≫ g₁) (w₁ : (u' ≫ h') ≫ g₁ = p ≫ u ≫ h) (K : DerivedCategory X₁.Modules) :
    (derivedPullbackCompIso p (u ≫ h)).hom.app K ≫
        eqToHom (congrArg (fun t : A' ⟶ X₁ => (derivedPullback t).obj K) w₁.symm) ≫
        (derivedPullbackCompIso (u' ≫ h') g₁).inv.app K ≫
        (derivedPullbackCompIso u' h').inv.app ((derivedPullback g₁).obj K) =
      (derivedPullback p).map ((derivedPullbackCompIso u h).inv.app K) ≫
        (derivedPullbackCompIso p u).hom.app ((derivedPullback h).obj K) ≫
        eqToHom (congrArg (fun t : A' ⟶ X₂ => (derivedPullback t).obj ((derivedPullback h).obj K))
          w₂.symm) ≫
        (derivedPullbackCompIso u' g₂).inv.app ((derivedPullback h).obj K) ≫
        (derivedPullback u').map ((derivedPullbackCompIso g₂ h).hom.app K ≫
          eqToHom (congrArg (fun t : X₂' ⟶ X₁ => (derivedPullback t).obj K) w) ≫
          (derivedPullbackCompIso h' g₁).inv.app K) := by
  rw [← cancel_mono ((derivedPullback u').map ((derivedPullbackCompIso h' g₁).hom.app K) ≫
    (derivedPullbackCompIso u' (h' ≫ g₁)).hom.app K)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (derivedPullback u') ((derivedPullbackCompIso h' g₁).inv.app K),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    derivedPullback_map_eqToHom_comp_derivedPullbackCompIso_hom_app u' w K,
    ← derivedPullbackCompIso_hom_app_assoc_assoc u' g₂ h K, Iso.inv_hom_id_app_assoc,
    eqToHom_comp_derivedPullbackCompIso_hom_app_assoc w₂.symm h K,
    derivedPullbackCompIso_hom_app_assoc'_assoc p u h K,
    ← Functor.map_comp_assoc (derivedPullback p) ((derivedPullbackCompIso u h).inv.app K),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← derivedPullbackCompIso_hom_app_assoc u' h' g₁ K, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app_assoc]
  simp only [eqToHom_trans]

end Stacks.Duality

namespace AlgebraicGeometry.BaseChangeChart

/-- The comparison of two charts with the same rings, one the restriction of the other, for
abstract functors: the affine part of the identification of Stacks 0DJ8 (2) is natural in the
object it is applied to, and the remaining factors compare by the hypothesis `h`. -/
theorem comparison_restrict_aux {𝒜 𝒜₀ 𝒜₀' 𝒜' ℛ ℛ' : Type*} [Category* 𝒜] [Category* 𝒜₀]
    [Category* 𝒜₀'] [Category* 𝒜'] [Category* ℛ] [Category* ℛ']
    {Γ : 𝒜 ⥤ 𝒜₀} {E : 𝒜₀ ⥤ 𝒜₀'} {F' Z' : 𝒜₀' ⥤ 𝒜'} {G' : 𝒜' ⥤ 𝒜₀'} {Z F : 𝒜₀ ⥤ 𝒜}
    {Lc : 𝒜 ⥤ 𝒜'} {Ra : 𝒜₀ ⥤ ℛ} {Lb : ℛ ⥤ ℛ'} {Rd : 𝒜₀' ⥤ ℛ'} (τ : Ra ⋙ Lb ⟶ E ⋙ Rd)
    (adj : F' ⊣ G') (ι' : F' ⟶ Z') (b : E ⋙ Z' ⟶ Z ⋙ Lc) (ι : Z ⟶ F) (ε : Γ ⋙ F ⟶ 𝟭 𝒜)
    {M₁ M₂ : 𝒜} (β : M₁ ⟶ M₂) {P₁ P₁' N₁ Y₁ P₂ P₂' N₂ Y₂ : 𝒜'}
    (c₁ : Lc.obj M₁ ⟶ P₁) (e₁ : P₁ ⟶ P₁') (c₁' : P₁' ⟶ N₁) (f₁ : N₁ ⟶ Y₁)
    (c₂ : Lc.obj M₂ ⟶ P₂) (e₂ : P₂ ⟶ P₂') (c₂' : P₂' ⟶ N₂) (f₂ : N₂ ⟶ Y₂) (β' : Y₁ ⟶ Y₂)
    (h : Lc.map β ≫ c₂ ≫ e₂ ≫ c₂' ≫ f₂ = c₁ ≫ e₁ ≫ c₁' ≫ f₁ ≫ β') :
    ((τ.app (Γ.obj M₁) ≫ Rd.map (adj.unit.app (E.obj (Γ.obj M₁)) ≫
        G'.map (ι'.app (E.obj (Γ.obj M₁))) ≫ G'.map (b.app (Γ.obj M₁)) ≫
        G'.map (Lc.map (ι.app (Γ.obj M₁))) ≫ G'.map (Lc.map (ε.app M₁)) ≫
        G'.map c₁ ≫ G'.map e₁ ≫ G'.map c₁')) ≫ Rd.map (G'.map f₁)) ≫ Rd.map (G'.map β') =
      Lb.map (Ra.map (Γ.map β)) ≫ ((τ.app (Γ.obj M₂) ≫ Rd.map (adj.unit.app (E.obj (Γ.obj M₂)) ≫
        G'.map (ι'.app (E.obj (Γ.obj M₂))) ≫ G'.map (b.app (Γ.obj M₂)) ≫
        G'.map (Lc.map (ι.app (Γ.obj M₂))) ≫ G'.map (Lc.map (ε.app M₂)) ≫
        G'.map c₂ ≫ G'.map e₂ ≫ G'.map c₂')) ≫ Rd.map (G'.map f₂)) := by
  have hτ := τ.naturality (Γ.map β)
  simp only [Functor.comp_map] at hτ
  simp only [Category.assoc]
  rw [reassoc_of% hτ]
  simp only [← Rd.map_comp]
  congr 2
  symm
  simp only [Category.assoc]
  rw [← adj.unit_naturality_assoc]
  simp only [← Functor.map_comp]
  congr 1
  have h₁ := ι'.naturality (E.map (Γ.map β))
  have h₂ := b.naturality (Γ.map β)
  have h₃ := ι.naturality (Γ.map β)
  have h₄ := ε.naturality β
  simp only [Functor.comp_map, Functor.id_map] at h₂ h₄
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Lc.map_comp_assoc, h₃, Lc.map_comp_assoc,
    ← Lc.map_comp_assoc (F.map _), h₄, Lc.map_comp_assoc, h]

end AlgebraicGeometry.BaseChangeChart

namespace AlgebraicGeometry.BaseChangeChart

variable {X₁ X₁' S₁ S₁' X₂ X₂' S₂ S₂' : Scheme.{u}} {f₁ : X₁ ⟶ S₁} {g₁ : S₁' ⟶ S₁}
  {f₁' : X₁' ⟶ S₁'} {g₁' : X₁' ⟶ X₁} {f₂ : X₂ ⟶ S₂} {g₂ : S₂' ⟶ S₂} {f₂' : X₂' ⟶ S₂'}
  {g₂' : X₂' ⟶ X₂}

/-- A chart of a square of schemes, pushed forward along a map of squares whose three components
`X₂ ⟶ X₁`, `S₂ ⟶ S₁`, `S₂' ⟶ S₁'` are open immersions: the same rings, with the open immersions
composed. -/
def mapSquare (ch : BaseChangeChart f₂ g₂ f₂' g₂') (hX : X₂ ⟶ X₁) (hS : S₂ ⟶ S₁)
    (hS' : S₂' ⟶ S₁') (hX' : X₂' ⟶ X₁') [IsOpenImmersion hX] [IsOpenImmersion hS]
    [IsOpenImmersion hS'] (wf : f₂ ≫ hS = hX ≫ f₁) (wg : g₂ ≫ hS = hS' ≫ g₁)
    (wg' : g₂' ≫ hX = hX' ≫ g₁') (wf' : f₂' ≫ hS' = hX' ≫ f₁') :
    BaseChangeChart f₁ g₁ f₁' g₁' where
  R := ch.R
  A := ch.A
  R' := ch.R'
  A' := ch.A'
  incV := ch.incV ≫ hS
  incU := ch.incU ≫ hX
  incV' := ch.incV' ≫ hS'
  incU' := ch.incU' ≫ hX'
  isOpenImmersion_incV := by have := ch.isOpenImmersion_incV; infer_instance
  isOpenImmersion_incU := by have := ch.isOpenImmersion_incU; infer_instance
  isOpenImmersion_incV' := by have := ch.isOpenImmersion_incV'; infer_instance
  a := ch.a
  b := ch.b
  c := ch.c
  d := ch.d
  wU := by rw [Category.assoc, ← wf, ← Category.assoc, ch.wU, Category.assoc]
  wV' := by rw [Category.assoc, ← wg, ← Category.assoc, ch.wV', Category.assoc]
  wU'U := by rw [Category.assoc, ← wg', ← Category.assoc, ch.wU'U, Category.assoc]
  wU'V' := by rw [Category.assoc, ← wf', ← Category.assoc, ch.wU'V', Category.assoc]
  isPushout := ch.isPushout

/-- **Condition (2) of Stacks 0DJ8 on a pushed-forward chart.** For a chart `ch` of a square and
a map of squares with open immersions as components, the comparison on `ch.mapSquare` for
`φ : L(g₁')^*K ⟶ K'` is invertible if and only if the comparison on `ch` is, for the restrictions
of `K`, `K'` and of `φ`. -/
theorem isIso_mapSquare_comparison_iff (ch : BaseChangeChart f₂ g₂ f₂' g₂') (hX : X₂ ⟶ X₁)
    (hS : S₂ ⟶ S₁) (hS' : S₂' ⟶ S₁') (hX' : X₂' ⟶ X₁') [IsOpenImmersion hX]
    [IsOpenImmersion hS] [IsOpenImmersion hS'] (wf : f₂ ≫ hS = hX ≫ f₁)
    (wg : g₂ ≫ hS = hS' ≫ g₁) (wg' : g₂' ≫ hX = hX' ≫ g₁') (wf' : f₂' ≫ hS' = hX' ≫ f₁')
    (K : DerivedCategory X₁.Modules) (K' : DerivedCategory X₁'.Modules)
    (φ : (Stacks.Duality.derivedPullback g₁').obj K ⟶ K') :
    IsIso ((ch.mapSquare hX hS hS' hX' wf wg wg' wf').comparison K K' φ) ↔
      IsIso (ch.comparison ((Stacks.Duality.derivedPullback hX).obj K)
        ((Stacks.Duality.derivedPullback hX').obj K')
        ((Stacks.Duality.derivedPullbackCompIso g₂' hX).hom.app K ≫
          eqToHom (congrArg (fun t : X₂' ⟶ X₁ => (Stacks.Duality.derivedPullback t).obj K) wg') ≫
          (Stacks.Duality.derivedPullbackCompIso hX' g₁').inv.app K ≫
          (Stacks.Duality.derivedPullback hX').map φ)) := by
  have hE := Stacks.Duality.derivedPullbackCompIso_restriction_square (Spec.map ch.c) ch.incU hX
    ch.incU' hX' g₂' g₁' ch.wU'U wg' (ch.mapSquare hX hS hS' hX' wf wg wg' wf').wU'U K
  have hn := (Stacks.Duality.derivedPullbackCompIso ch.incU' hX').inv.naturality φ
  simp only [Functor.comp_map] at hn
  have key : ∀ {P Q P' Q' : DerivedCategory (ModuleCat.{u} ch.R')} (x : P ⟶ Q) (y : P' ⟶ Q')
      (i : Q ≅ Q') (j : P ≅ P'), x ≫ i.hom = j.hom ≫ y → (IsIso x ↔ IsIso y) :=
    fun x y i j h => by rw [← isIso_comp_right_iff x i.hom, h, isIso_comp_left_iff]
  refine key _ _
    ((ModuleCat.restrictScalars ch.d.hom).mapDerivedCategory.mapIso
      ((derivedGlobalSectionsOver (𝟙 (Spec ch.A'))).mapIso
        ((Stacks.Duality.derivedPullbackCompIso ch.incU' hX').app K').symm))
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.b.hom).functor.mapIso ((ModuleCat.restrictScalars ch.a.hom).mapDerivedCategory.mapIso
          ((derivedGlobalSectionsOver (𝟙 (Spec ch.A))).mapIso
            ((Stacks.Duality.derivedPullbackCompIso ch.incU hX).app K).symm)))
    (comparison_restrict_aux
      (@RingTheory.TorIndependence.derivedBaseChangeComparison _ _ _ _ _ _ _ _ _ _ _ _
        ch.a.hom ch.b.hom ch.c.hom ch.d.hom ch.isPushout_hom
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          ch.b.hom).functor
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          ch.c.hom).functor
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          ch.b.hom).comparison
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          ch.c.hom).comparison
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          ch.b.hom).isLeftDerived
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          ch.c.hom).isLeftDerived).2.1
      (derivedTildeGlobalSectionsAdjunction ch.A').val (derivedTildeCompι ch.A').hom
      (affinePullbackComparison ch.A ch.A' ch.c).inv (derivedTildeCompι ch.A).inv
      (derivedTildeGlobalSectionsAdjunction ch.A).val.counit
      ((Stacks.Duality.derivedPullbackCompIso ch.incU hX).inv.app K) _ _ _ _ _ _ _ _ _ ?_)
  dsimp only [mapSquare, Iso.symm_hom, Iso.app_inv]
  rw [hn]
  simp only [Functor.map_comp] at hE ⊢
  rw [reassoc_of% hE.symm]
  rfl

end AlgebraicGeometry.BaseChangeChart
