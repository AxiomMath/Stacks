module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.RelationStages
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.TerminalSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedThickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.GluedEtaleRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

/-!
# Absolute Noetherian approximation: points related in every glued relation are identified in `X`

Let `V ⟶ X` be a morphism from a scheme to an algebraic space and `R = lim R_j` a limit of glued
étale relations `R_j = V_j ⨿_{W_j} P_j` on `V = lim V_j`. Then `R ⊆ V ×_X V`: two `T`-points
`x, y` of `V` such that `(x, y)` lifts to every `R_j` have the same image in `X`.

## Main results

* `AlgebraicGeometry.Space.BigFppfOver.yoneda_hom_ext_of_opens`: two morphisms from a
  representable presheaf to a sheaf agreeing on two opens covering the source are equal.
* `AlgebraicGeometry.Space.comp_eq_comp_of_forall_lift_gluedRelation`: the inclusion above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section OpenCover

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Morphisms into a sheaf are determined on two covering opens.** Two morphisms from the
presheaf represented by an object `T` of the big fppf site over `S` to a sheaf which agree on
the open subobjects attached to two opens covering `T` are equal. -/
theorem BigFppfOver.yoneda_hom_ext_of_opens {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) {T : BigFppfOver B S hS}
    (U₁ U₂ : ((BigFppfOver.toScheme B S hS).obj T).Opens) (hU : ∀ t, t ∈ U₁ ∨ t ∈ U₂)
    {φ ψ : yoneda.obj T ⟶ F}
    (h₁ : yoneda.map (openSiteObjectHom B S hS T U₁) ≫ φ =
      yoneda.map (openSiteObjectHom B S hS T U₁) ≫ ψ)
    (h₂ : yoneda.map (openSiteObjectHom B S hS T U₂) ≫ φ =
      yoneda.map (openSiteObjectHom B S hS T U₂) ≫ ψ) : φ = ψ := by
  refine hom_ext_of_openCover_of_isSheaf B S hS (K := Bool)
    (W := fun b ↦ openSiteObject B S hS T (cond b U₁ U₂)) hF
    (fun b ↦ openSiteObjectHom B S hS T (cond b U₁ U₂))
    (fun b ↦ inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (cond b U₁ U₂).ι))
    (fun t ↦ ?_) (fun b ↦ ?_)
  · rcases hU t with ht | ht
    · exact ⟨true, show t ∈ Set.range U₁.ι by rwa [Scheme.Opens.range_ι]⟩
    · exact ⟨false, show t ∈ Set.range U₂.ι by rwa [Scheme.Opens.range_ι]⟩
  · cases b <;> assumption

end OpenCover

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

/-- Over the terminal scheme, a morphism of the big fppf site whose image lands in the image
of an open immersion factors through it, on any open of the source. -/
private lemma exists_comp_eq_of_le {T Y Z : BigFppfOver B (⊤_ Scheme.{u}) hZ} (f : Y ⟶ Z)
    (g : T ⟶ Z)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map f)]
    (O : ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T).Opens)
    (hO : O ≤ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map g ⁻¹ᵁ
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map f).opensRange) :
    ∃ c : openSiteObject B (⊤_ Scheme.{u}) hZ T O ⟶ Y,
      c ≫ f = openSiteObjectHom B (⊤_ Scheme.{u}) hZ T O ≫ g := by
  have H : Set.range ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
      (openSiteObjectHom B (⊤_ Scheme.{u}) hZ T O ≫ g)) ⊆
      Set.range ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map f) := by
    rintro _ ⟨z, rfl⟩
    have hz : O.ι z ∈ O := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨z, rfl⟩
    exact hO hz
  refine ⟨(BigFppfOver.toSchemeFullyFaithfulOfTerminal B hZ).preimage
    (IsOpenImmersion.lift _ _ H), ?_⟩
  apply (BigFppfOver.toSchemeFullyFaithfulOfTerminal B hZ).map_injective
  rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, IsOpenImmersion.lift_fac]

/-- **Two points of `V` related in every glued relation `R_j` have the same image in
`X`.** -/
theorem comp_eq_comp_of_forall_lift_gluedRelation
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X) (U : Subfunctor X)
    (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (f : yoneda.obj V ⟶ X)
    (W : BigFppfOver B (⊤_ Scheme.{u}) hZ) (ιW : W ⟶ V) (gW : yoneda.obj W ⟶ U.toFunctor)
    (hW : IsPullback (yoneda.map ιW) gW f U.ι)
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (D : Jᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hD : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.obj j))
    (uπ : (Functor.const Jᵒᵖ).obj U.toFunctor ⟶ D) (huπ : IsLimit (Cone.mk _ uπ))
    (Vs Ws P R : Jᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ) (ι : Ws ⟶ Vs)
    (hι : ∀ j, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (ι.app j)))
    (g : Ws ⋙ yoneda ⟶ D) (p₁ p₂ : P ⟶ Ws)
    (hP : ∀ j, IsPullback (yoneda.map (p₁.app j)) (yoneda.map (p₂.app j)) (g.app j) (g.app j))
    (δ : Ws ⟶ P)
    (hδ : ∀ j, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (δ.app j)))
    (a : Vs ⟶ R) (b : P ⟶ R) (s t : R ⟶ Vs)
    (hR : ∀ j, IsPushout ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (ι.app j))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (δ.app j))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (a.app j))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (b.app j)))
    (has : ∀ j, a.app j ≫ s.app j = 𝟙 _) (hat : ∀ j, a.app j ≫ t.app j = 𝟙 _)
    (hbs : ∀ j, b.app j ≫ s.app j = p₁.app j ≫ ι.app j)
    (hbt : ∀ j, b.app j ≫ t.app j = p₂.app j ≫ ι.app j)
    (hcartR : ∀ {j j' : Jᵒᵖ} (e : j ⟶ j'), IsPullback (R.map e) (s.app j) (s.app j') (Vs.map e))
    (hjm : ∀ j, JointlyMono₂ ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (t.app j))
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (s.app j)))
    (vπ : (Functor.const Jᵒᵖ).obj V ⟶ Vs)
    (hvπ : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone (Cone.mk V vπ)))
    (wπ : (Functor.const Jᵒᵖ).obj W ⟶ Ws)
    (hwcart : ∀ j, IsPullback (wπ.app j) ιW (ι.app j) (vπ.app j))
    (hwg : ∀ j, yoneda.map (wπ.app j) ≫ g.app j = gW ≫ uπ.app j)
    (T : BigFppfOver B (⊤_ Scheme.{u}) hZ) (x y : T ⟶ V)
    (hr : ∀ j, ∃ r : T ⟶ R.obj j, r ≫ s.app j = x ≫ vπ.app j ∧ r ≫ t.app j = y ≫ vπ.app j) :
    yoneda.map x ≫ f = yoneda.map y ≫ f := by
  have hv : ∀ {j j' : Jᵒᵖ} (e : j ⟶ j'), vπ.app j ≫ Vs.map e = vπ.app j' := fun e ↦ by
    simpa using (vπ.naturality e).symm
  have hιm : ∀ j, Mono (ι.app j) := fun j ↦ by
    have := hι j
    exact (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mono_of_mono_map inferInstance
  have hoa : ∀ j, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (a.app j)) := fun j ↦ by
    have := hι j
    have := hδ j
    exact isOpenImmersion_inl_of_isPushout (hR j)
  have hob : ∀ j, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (b.app j)) := fun j ↦ by
    have := hι j
    have := hδ j
    exact isOpenImmersion_inr_of_isPushout (hR j)
  have hcover : ∀ j (Y : BigFppfOver B (⊤_ Scheme.{u}) hZ) (ρ : Y ⟶ R.obj j)
      (z : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Y),
      z ∈ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ρ ⁻¹ᵁ
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (a.app j)).opensRange ∨
        z ∈ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ρ ⁻¹ᵁ
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (b.app j)).opensRange := by
    intro j Y ρ z
    have := hι j
    have := hδ j
    exact exists_eq_of_isPushout_of_isOpenImmersion (hR j) _
  obtain ⟨j₀⟩ := (inferInstance : Nonempty J)
  obtain ⟨r₀, hr₀s, hr₀t⟩ := hr (op j₀)
  refine BigFppfOver.yoneda_hom_ext_of_opens hX.isSheaf _ _ (hcover (op j₀) T r₀) ?_ ?_
  · set N := (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map r₀ ⁻¹ᵁ
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (a.app (op j₀))).opensRange
    set iN := openSiteObjectHom B (⊤_ Scheme.{u}) hZ T N
    obtain ⟨c, hc⟩ := exists_comp_eq_of_le (a.app (op j₀)) r₀ N le_rfl
    have hstage : ∀ (j : Jᵒᵖ) (e : j ⟶ op j₀), iN ≫ x ≫ vπ.app j = iN ≫ y ≫ vπ.app j := by
      intro j e
      obtain ⟨r, hrs, hrt⟩ := hr j
      have hk : (iN ≫ r) ≫ R.map e = iN ≫ r₀ := by
        refine (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
          ((hjm (op j₀)).right_cancellation _ _ ?_ ?_)
        · simp only [← Functor.map_comp, Category.assoc, t.naturality e, reassoc_of% hrt, hv,
            hr₀t]
        · simp only [← Functor.map_comp, Category.assoc, s.naturality e, reassoc_of% hrs, hv,
            hr₀s]
      simpa only [Category.assoc, hrs, hrt] using
        (comp_t_eq_comp_s_of_eq_comp_a e (hcartR e) has hat hk hc.symm).symm
    have hNeq : iN ≫ x = iN ≫ y := by
      refine (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective (hvπ.hom_ext fun j ↦ ?_)
      obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) (unop j) j₀
      have h := hstage (op k) (homOfLE hk₂).op
      simp only [Functor.mapCone_π_app, ← Functor.map_comp, Category.assoc]
      rw [← hv (homOfLE hk₁).op, reassoc_of% h]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hNeq]
  · set M := (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map r₀ ⁻¹ᵁ
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (b.app (op j₀))).opensRange
    set iM := openSiteObjectHom B (⊤_ Scheme.{u}) hZ T M
    obtain ⟨q, hq⟩ := exists_comp_eq_of_le (b.app (op j₀)) r₀ M le_rfl
    have hlift : ∀ (st : R ⟶ Vs) (p : P ⟶ Ws), (∀ j, b.app j ≫ st.app j = p.app j ≫ ι.app j) →
        ∀ z, r₀ ≫ st.app (op j₀) = z ≫ vπ.app (op j₀) →
        ∃ z' : _ ⟶ W, z' ≫ ιW = iM ≫ z := fun st p hb z hz ↦
      ⟨_, (hwcart (op j₀)).lift_snd (q ≫ p.app (op j₀)) (iM ≫ z) (by
        rw [Category.assoc, ← hb, reassoc_of% hq, hz, Category.assoc])⟩
    obtain ⟨x', hx'⟩ := hlift s p₁ hbs x hr₀s
    obtain ⟨y', hy'⟩ := hlift t p₂ hbt y hr₀t
    have hgW : yoneda.map x' ≫ gW = yoneda.map y' ≫ gW := by
      refine huπ.hom_ext fun j ↦ ?_
      change (yoneda.map x' ≫ gW) ≫ uπ.app j = (yoneda.map y' ≫ gW) ≫ uπ.app j
      rw [Category.assoc, Category.assoc, ← hwg, ← Functor.map_comp_assoc,
        ← Functor.map_comp_assoc]
      obtain ⟨r, hrs, hrt⟩ := hr j
      refine BigFppfOver.yoneda_hom_ext_of_opens (hD j).isSheaf _ _
        (hcover j _ (iM ≫ r)) ?_ ?_
      · set i := openSiteObjectHom B (⊤_ Scheme.{u}) hZ _
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (iM ≫ r) ⁻¹ᵁ
            ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (a.app j)).opensRange)
        obtain ⟨c, hc⟩ := exists_comp_eq_of_le (a.app j) (iM ≫ r) _ le_rfl
        have h : i ≫ x' ≫ wπ.app j = i ≫ y' ≫ wπ.app j := by
          refine (cancel_mono (ι.app j)).1 ?_
          simp only [Category.assoc, (hwcart j).w, reassoc_of% hx', reassoc_of% hy']
          have hc' : i ≫ iM ≫ r = c ≫ a.app j := hc.symm
          rw [← hrs, ← hrt, reassoc_of% hc', reassoc_of% hc', has, hat]
        rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, h]
      · set i := openSiteObjectHom B (⊤_ Scheme.{u}) hZ _
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (iM ≫ r) ⁻¹ᵁ
            ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (b.app j)).opensRange)
        obtain ⟨q', hq'⟩ := exists_comp_eq_of_le (b.app j) (iM ≫ r) _ le_rfl
        have hq'' : i ≫ iM ≫ r = q' ≫ b.app j := hq'.symm
        have hh : ∀ (st : R ⟶ Vs) (p : P ⟶ Ws), (∀ j, b.app j ≫ st.app j = p.app j ≫ ι.app j) →
            ∀ z z', z' ≫ ιW = iM ≫ z → r ≫ st.app j = z ≫ vπ.app j →
            i ≫ z' ≫ wπ.app j = q' ≫ p.app j := fun st p hb z z' hz' hrz ↦ by
          refine (cancel_mono (ι.app j)).1 ?_
          simp only [Category.assoc, (hwcart j).w, reassoc_of% hz']
          rw [← hrz, reassoc_of% hq'', hb]
        rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hh s p₁ hbs x x' hx' hrs,
          hh t p₂ hbt y y' hy' hrt, Functor.map_comp_assoc,
          Functor.map_comp_assoc, (hP j).w]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← hx', ← hy', Functor.map_comp_assoc,
      Functor.map_comp_assoc, hW.w, reassoc_of% hgW]

end AlgebraicGeometry.Space

end
