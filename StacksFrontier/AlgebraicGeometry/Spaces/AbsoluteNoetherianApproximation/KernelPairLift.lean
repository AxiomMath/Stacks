module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.TerminalSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.GluedEtaleRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

/-!
# Absolute Noetherian approximation: the kernel pair of the chart maps to the glued relations

If `f : V ⟶ X` is étale, an isomorphism over the closed subspace `Z`, and `|X| = |U| ∪ |Z|` for
an open subspace `U`, then `V ×_X V` is the union of the opens `Δ(V)` and `W ×_U W`, where
`W = f⁻¹U`. Hence the kernel pair of `f` maps into every glued relation `R_j = V_j ⊔_{W_j} P_j`
compatible with `V ⊇ W ⟶ U`.

## Main results

* `AlgebraicGeometry.Space.exists_lift_gluedRelation_of_kernelPair`: the kernel pair of
  `f : V ⟶ X` maps into every glued relation `R_j`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

/-- **The kernel pair of `V ⟶ X` maps into every glued relation `R_j`.** -/
theorem exists_lift_gluedRelation_of_kernelPair
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (U : Subfunctor X) (hU : IsOpenSubspace B (⊤_ Scheme.{u}) hZ U)
    (Z : Subfunctor X) (_hZc : IsClosedSubspace B (⊤_ Scheme.{u}) hZ Z)
    (hcover : ∀ x : points B (⊤_ Scheme.{u}) hZ X,
      x ∈ Set.range (pointsMap B (⊤_ Scheme.{u}) hZ U.toFunctor U.ι) ∨
        x ∈ Set.range (pointsMap B (⊤_ Scheme.{u}) hZ Z.toFunctor Z.ι))
    (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (f : yoneda.obj V ⟶ X)
    (hfe : IsEtale B (⊤_ Scheme.{u}) hZ f) (hfZ : IsIso (pullback.fst Z.ι f))
    (W : BigFppfOver B (⊤_ Scheme.{u}) hZ) (ιW : W ⟶ V) (gW : yoneda.obj W ⟶ U.toFunctor)
    (hW : IsPullback (yoneda.map ιW) gW f U.ι)
    -- one stage of the system: the glued relation `R_j = V_j ⊔_{W_j} P_j`
    {Dj : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    {Vj Wj Pj Rj : BigFppfOver B (⊤_ Scheme.{u}) hZ} (ιj : Wj ⟶ Vj) (gj : yoneda.obj Wj ⟶ Dj)
    (p₁ p₂ : Pj ⟶ Wj) (hP : IsPullback (yoneda.map p₁) (yoneda.map p₂) gj gj)
    (a : Vj ⟶ Rj) (b : Pj ⟶ Rj) (s t : Rj ⟶ Vj)
    [JointlyMono₂ ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map t)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map s)]
    (has : a ≫ s = 𝟙 Vj) (hat : a ≫ t = 𝟙 Vj) (hbs : b ≫ s = p₁ ≫ ιj) (hbt : b ≫ t = p₂ ≫ ιj)
    -- the comparison of `V ⊇ W ⟶ U` with the stage
    (vj : V ⟶ Vj) (wj : W ⟶ Wj) (uj : U.toFunctor ⟶ Dj) (hwv : wj ≫ ιj = ιW ≫ vj)
    (hwg : yoneda.map wj ≫ gj = gW ≫ uj)
    -- the kernel pair of `f`
    (E : BigFppfOver B (⊤_ Scheme.{u}) hZ) (sE tE : E ⟶ V)
    (hE : IsPullback (yoneda.map sE) (yoneda.map tE) f f) :
    ∃ r : E ⟶ Rj, r ≫ t = tE ≫ vj ∧ r ≫ s = sE ≫ vj := by
  let F := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ
  let hF := BigFppfOver.toSchemeFullyFaithfulOfTerminal B hZ
  obtain ⟨Δ', hΔs, hΔt⟩ : ∃ Δ' : V ⟶ E, Δ' ≫ sE = 𝟙 V ∧ Δ' ≫ tE = 𝟙 V := by
    refine ⟨Yoneda.fullyFaithful.preimage (hE.lift (𝟙 _) (𝟙 _) rfl), ?_, ?_⟩ <;>
      apply Yoneda.fullyFaithful.map_injective <;> simp
  have hsEt : Etale (F.map sE) := (presheaf_etale_of_isEtale B _ hZ hfe).property _ _ _ hE.flip
  have hΔ : AlgebraicGeometry.IsOpenImmersion (F.map Δ') :=
    isOpenImmersion_of_section_of_etale (F.map sE) (F.map Δ')
      (by rw [← F.map_comp, hΔs, F.map_id])
  have hιW : AlgebraicGeometry.IsOpenImmersion (F.map ιW) := hU.2.property _ _ _ hW.flip
  let D : (F.obj E).Opens := (F.map Δ').opensRange
  let O : (F.obj E).Opens := (F.map sE) ⁻¹ᵁ (F.map ιW).opensRange
  have hlift : ∀ (G : Subfunctor X) (T : BigFppfOver B (⊤_ Scheme.{u}) hZ) (g : T ⟶ V),
      f.app (op T) g ∈ G.obj (op T) →
        ∃ z : yoneda.obj T ⟶ G.toFunctor, z ≫ G.ι = yoneda.map g ≫ f := by
    intro G T g hg
    refine ⟨Subfunctor.lift (yoneda.map g ≫ f) ?_, Subfunctor.lift_ι _ _⟩
    rwa [Subfunctor.range_eq_ofSection, Subfunctor.ofSection_le_iff, yonedaEquiv_comp,
      yonedaEquiv_yoneda_map]
  have hZdiag : ∀ (T : BigFppfOver B (⊤_ Scheme.{u}) hZ) (g : T ⟶ E),
      f.app (op T) (g ≫ sE) ∈ Z.obj (op T) → g = (g ≫ sE) ≫ Δ' := by
    intro T g hg
    obtain ⟨z, hzs⟩ := hlift Z T _ hg
    have hzt : z ≫ Z.ι = yoneda.map (g ≫ tE) ≫ f := by
      rw [hzs, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hE.w]
    have hst : g ≫ sE = g ≫ tE := by
      apply Yoneda.fullyFaithful.map_injective
      have : Mono (pullback.fst Z.ι f) := IsIso.mono_of_iso _
      have := congrArg (· ≫ pullback.snd Z.ι f) ((cancel_mono (pullback.fst Z.ι f)).1
        ((pullback.lift_fst z (yoneda.map (g ≫ sE)) hzs).trans
          (pullback.lift_fst z (yoneda.map (g ≫ tE)) hzt).symm))
      rwa [pullback.lift_snd, pullback.lift_snd] at this
    apply Yoneda.fullyFaithful.map_injective
    refine hE.hom_ext ?_ ?_
    · simp [← Functor.map_comp, hΔs]
    · simp [← Functor.map_comp, hΔt, hst]
  have hUfac : ∀ (T : BigFppfOver B (⊤_ Scheme.{u}) hZ) (g : T ⟶ V),
      f.app (op T) g ∈ U.obj (op T) → ∃ w : T ⟶ W, w ≫ ιW = g := by
    intro T g hg
    obtain ⟨z, hz⟩ := hlift U T _ hg
    refine ⟨Yoneda.fullyFaithful.preimage (hW.lift _ _ hz.symm), ?_⟩
    apply Yoneda.fullyFaithful.map_injective
    simp
  have hpts : ∀ e : F.obj E, e ∈ D ∨ e ∈ O := by
    intro e
    obtain ⟨K, instK, hK, ρ, hρ⟩ := exists_fieldSpec_at_point B E.left.2 e
    let T : BigFppfOver B (⊤_ Scheme.{u}) hZ := Over.mk (⟨ρ ≫ E.hom.hom⟩ : B.obj hK ⟶ B.obj hZ)
    let ê : T ⟶ E := Over.homMk (⟨ρ⟩ : B.obj hK ⟶ E.left) (by ext; rfl)
    let p : FieldValuedPoint B (⊤_ Scheme.{u}) hZ X :=
      { carrier := K, contained := hK, toBase := ρ ≫ E.hom.hom, value := f.app (op T) (ê ≫ sE) }
    have key : ∀ G : Subfunctor X,
        p.class B _ hZ X ∈ Set.range (pointsMap B (⊤_ Scheme.{u}) hZ G.toFunctor G.ι) →
        ∃ (T' : BigFppfOver B (⊤_ Scheme.{u}) hZ) (σ : T' ⟶ E) (c : F.obj T'),
          F.map σ c = e ∧ f.app (op T') (σ ≫ sE) ∈ G.obj (op T') := by
      rintro G ⟨q, hq⟩
      obtain ⟨q, rfl⟩ := Quot.exists_rep q
      obtain ⟨r, ⟨τ, hτ⟩, ⟨σ, hσ⟩⟩ := (FieldValuedPoint.class_eq_class_iff B _ hZ X _ _).1 hq
      refine ⟨r.siteObject, σ ≫ ê, (show F.obj r.siteObject from IsLocalRing.closedPoint r.carrier),
        ?_, ?_⟩
      · rw [F.map_comp, Scheme.Hom.comp_apply]
        exact hρ _
      · have h1 : f.app (op r.siteObject) ((σ ≫ ê) ≫ sE) = r.value := by
          rw [← hσ]
          refine Eq.trans ?_ (NatTrans.naturality_apply (D := Type u) f σ.op
            (ê ≫ sE : (yoneda.obj V).obj (op T)))
          rw [Category.assoc]
          rfl
        rw [h1, ← hτ]
        exact G.map τ.op q.value.2
    rcases hcover (p.class B _ hZ X) with hu | hz
    · obtain ⟨T', σ, c, hc, hmem⟩ := key U hu
      obtain ⟨w, hw⟩ := hUfac T' (σ ≫ sE) hmem
      right
      change F.map sE e ∈ Set.range (F.map ιW)
      refine ⟨F.map w c, ?_⟩
      rw [← hc, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← F.map_comp, ← F.map_comp,
        hw]
    · obtain ⟨T', σ, c, hc, hmem⟩ := key Z hz
      left
      change e ∈ Set.range (F.map Δ')
      refine ⟨F.map (σ ≫ sE) c, ?_⟩
      rw [← hc, ← Scheme.Hom.comp_apply, ← F.map_comp, ← hZdiag T' σ hmem]
  obtain ⟨φ, hφt, hφs⟩ := AlgebraicGeometry.exists_lift_of_jointlyMono₂_of_forall
    (F.map t) (F.map s) (F.map (tE ≫ vj)) (F.map (sE ≫ vj)) <| by
    intro x
    rcases hpts x with hx | hx
    · refine ⟨D, hx, (F.map Δ').isoOpensRange.inv ≫ F.map (vj ≫ a), ?_, ?_⟩
      · rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc,
          ← F.map_comp, ← F.map_comp]
        simp [hat, reassoc_of% hΔt]
      · rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc,
          ← F.map_comp, ← F.map_comp]
        simp [has, reassoc_of% hΔs]
    · let Os := openSiteObject B (⊤_ Scheme.{u}) hZ E O
      let o : Os ⟶ E := openSiteObjectHom B (⊤_ Scheme.{u}) hZ E O
      have hrange : Set.range (O.ι ≫ F.map sE) ⊆ Set.range (F.map ιW) := by
        rintro _ ⟨y, rfl⟩
        exact y.2
      let w₁ : Os ⟶ W := hF.preimage (IsOpenImmersion.lift (F.map ιW) _ hrange)
      have hw₁ : w₁ ≫ ιW = o ≫ sE := by
        apply hF.map_injective
        rw [F.map_comp, hF.map_preimage, F.map_comp]
        exact IsOpenImmersion.lift_fac _ _ _
      have hw₂e : yoneda.map (o ≫ tE) ≫ f = (yoneda.map w₁ ≫ gW) ≫ U.ι := by
        rw [Category.assoc, ← hW.w, ← Category.assoc, ← Functor.map_comp, hw₁,
          Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hE.w]
      let w₂ : Os ⟶ W := Yoneda.fullyFaithful.preimage (hW.lift _ _ hw₂e)
      have hw₂ : w₂ ≫ ιW = o ≫ tE := by
        apply Yoneda.fullyFaithful.map_injective
        simp [w₂]
      have hw₂g : yoneda.map w₂ ≫ gW = yoneda.map w₁ ≫ gW := by
        simp [w₂]
      have hπe : yoneda.map (w₁ ≫ wj) ≫ gj = yoneda.map (w₂ ≫ wj) ≫ gj := by
        rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hwg,
          reassoc_of% hw₂g]
      let π : Os ⟶ Pj := Yoneda.fullyFaithful.preimage (hP.lift _ _ hπe)
      have hπ₁ : π ≫ p₁ = w₁ ≫ wj := by
        apply Yoneda.fullyFaithful.map_injective
        simp [π]
      have hπ₂ : π ≫ p₂ = w₂ ≫ wj := by
        apply Yoneda.fullyFaithful.map_injective
        simp [π]
      refine ⟨O, hx, F.map (π ≫ b), ?_, ?_⟩ <;>
        change F.map (π ≫ b) ≫ F.map _ = F.map o ≫ F.map _ <;>
        rw [← F.map_comp, ← F.map_comp, Category.assoc]
      · rw [hbt, reassoc_of% hπ₂, hwv, reassoc_of% hw₂]
      · rw [hbs, reassoc_of% hπ₁, hwv, reassoc_of% hw₁]
  refine ⟨hF.preimage φ, hF.map_injective ?_, hF.map_injective ?_⟩ <;>
    rw [F.map_comp, hF.map_preimage]
  exacts [hφt, hφs]

end AlgebraicGeometry.Space

end
