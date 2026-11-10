module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceProper
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedAffineBase

/-!
# An isomorphism over the limit is an isomorphism over a stage

Let `V = lim V_i` be a cofiltered limit of affine objects of the big fppf site, `N ⟶ V_i` an
affine object over a stage and `p : Y ⟶ V_i` a proper morphism of finite presentation from an
algebraic space. If the base change of `p` to `V ×_{V_i} N` is an isomorphism, then so is its base
change to `V_k ×_{V_i} N` for some `k ⟶ i`.

The inverse over the limit is a section, which comes from a stage by relative limit
preservation (Stacks 04AK); that the section composed with the projection is the identity is
checked on an affine étale atlas, where it holds at a later stage, and descends along the atlas
(Stacks 0262). This is the step "we may assume `V'_λ ⟶ V_λ` is an isomorphism over
`V_λ ∖ Z_λ`" of the proof of Stacks 0GI5 (there quoted from Stacks 081E), on a basic open.

## Main results

* `AlgebraicGeometry.Space.exists_stage_isIso_of_isLimit_baseChange`

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site times out at the default
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ContractionLimitSpaceIso :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ContractionLimitSpaceIso
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

local instance (priority := high) hasPullback_bigFppfOver_ContractionLimitSpaceIso
    {X Y Z : BigFppfOver B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  have := hasPullbacks_bigFppfOver B S hS
  HasLimitsOfShape.has_limit _

/-- The last step of `exists_stage_isIso_of_isLimit_baseChange`: a section at a stage which,
composed with the projection, agrees with the identity on an étale atlas at a later stage, makes
the projection an isomorphism there. -/
theorem isIso_of_stage_section {I : Type u} [Category.{u} I] (E : I ⥤ BigFppfOver B S hS)
    (i : I) {N : BigFppfOver B S hS} (n₀ : N ⟶ E.obj i) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (p : Y ⟶ yoneda.obj (E.obj i)) (k₁ : Over i)
    (b' : yoneda.obj (pullback (E.map k₁.hom) n₀) ⟶ Y)
    (hb' : b' ≫ p = yoneda.map (pullback.snd (E.map k₁.hom) n₀ ≫ n₀))
    {M : BigFppfOver B S hS}
    (m : yoneda.obj M ⟶ pullback (yoneda.map (pullback.snd (E.map k₁.hom) n₀ ≫ n₀)) p)
    (hmsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf m)
    (hmet' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf m)
    (n₁ : M ⟶ pullback (E.map k₁.hom) n₀) (hn₁ : yoneda.map n₁ = m ≫ pullback.fst _ _)
    (k₂ : Over k₁.left)
    (hg' : yoneda.map (pullback.snd (E.map k₂.hom) (n₁ ≫ pullback.fst (E.map k₁.hom) n₀)) ≫ m =
      yoneda.map (pullback.snd (E.map k₂.hom) (n₁ ≫ pullback.fst (E.map k₁.hom) n₀)) ≫
        yoneda.map n₁ ≫ pullback.lift (𝟙 _) b' (by rw [Category.id_comp, hb'])) :
    IsIso (pullback.fst (yoneda.map (pullback.snd (E.map (k₂.hom ≫ k₁.hom)) n₀ ≫ n₀)) p) := by
  let T := BigFppfOver.toScheme B S hS
  have hVi := isAlgebraicSpace_yoneda B S hS (E.obj i)
  let s₁ : yoneda.obj (pullback (E.map k₁.hom) n₀) ⟶
      (pullback (yoneda.map (pullback.snd (E.map k₁.hom) n₀ ≫ n₀)) p) :=
    pullback.lift (𝟙 _) b' (by rw [Category.id_comp, hb'])
  have hs₁' : s₁ ≫ pullback.snd _ _ = b' := pullback.lift_snd _ _ _
  let n₂ : M ⟶ E.obj k₁.left := n₁ ≫ pullback.fst (E.map k₁.hom) n₀
  -- the stage `k₃ = k₂ ≫ k₁`
  let k₃ : Over i := Over.mk (k₂.hom ≫ k₁.hom)
  change IsIso (pullback.fst (yoneda.map (pullback.snd (E.map k₃.hom) n₀ ≫ n₀)) p)
  have hτ : pullback.fst (E.map k₃.hom) n₀ ≫ E.map k₂.hom ≫ E.map k₁.hom =
      pullback.snd (E.map k₃.hom) n₀ ≫ n₀ := by
    rw [← Functor.map_comp]
    exact pullback.condition
  let τ : (pullback (E.map k₃.hom) n₀) ⟶ (pullback (E.map k₁.hom) n₀) :=
    pullback.lift (pullback.fst _ _ ≫ E.map k₂.hom) (pullback.snd _ _)
    (by rw [Category.assoc, hτ])
  have hτψ : τ ≫ (pullback.snd (E.map k₁.hom) n₀ ≫ n₀) = (pullback.snd (E.map k₃.hom) n₀ ≫ n₀) := by
    simp only [τ, pullback.lift_snd_assoc]
  have hτf : τ ≫ pullback.fst (E.map k₁.hom) n₀ =
      pullback.fst (E.map k₃.hom) n₀ ≫ E.map k₂.hom := pullback.lift_fst _ _ _
  let s₃ : yoneda.obj (pullback (E.map k₃.hom) n₀) ⟶
      pullback (yoneda.map (pullback.snd (E.map k₃.hom) n₀ ≫ n₀)) p :=
    pullback.lift (𝟙 _) (yoneda.map τ ≫ b') (by
      rw [Category.id_comp, Category.assoc, hb', ← Functor.map_comp, hτψ])
  have hs₃ : s₃ ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  let ρ : pullback (yoneda.map (pullback.snd (E.map k₃.hom) n₀ ≫ n₀)) p ⟶
      (pullback (yoneda.map (pullback.snd (E.map k₁.hom) n₀ ≫ n₀)) p) :=
    pullback.lift (pullback.fst _ _ ≫ yoneda.map τ) (pullback.snd _ _) (by
      rw [Category.assoc, ← Functor.map_comp, hτψ, pullback.condition])
  have hρs : ρ ≫ pullback.snd _ _ =
      pullback.snd (yoneda.map (pullback.snd (E.map k₃.hom) n₀ ≫ n₀)) p :=
    pullback.lift_snd _ _ _
  have hρf : ρ ≫ pullback.fst _ _ =
      pullback.fst (yoneda.map (pullback.snd (E.map k₃.hom) n₀ ≫ n₀)) p ≫ yoneda.map τ :=
    pullback.lift_fst _ _ _
  have hP₃ :
      IsAlgebraicSpace B S hS (pullback (yoneda.map (pullback.snd (E.map k₃.hom) n₀ ≫ n₀)) p) :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS _) hY hVi
  have hid : pullback.fst (yoneda.map (pullback.snd (E.map k₃.hom) n₀ ≫ n₀)) p ≫ s₃ = 𝟙 _ := by
    refine hom_ext_yoneda fun W z => ?_
    rw [Category.comp_id]
    let z₁ := z ≫ ρ
    obtain ⟨W', c₁, μ, hμ, hc₁s, hc₁e⟩ : ∃ (W' : BigFppfOver B S hS) (c₁ : W' ⟶ W)
        (μ : yoneda.obj W' ⟶ yoneda.obj M), μ ≫ m = yoneda.map c₁ ≫ z₁ ∧
          Surjective (T.map c₁) ∧ Etale (T.map c₁) :=
      ⟨_, hmet'.rep.snd z₁, hmet'.rep.fst z₁, hmet'.rep.w z₁, hmsurj.property_snd z₁,
        hmet'.property_snd z₁⟩
    let μ' := yoneda.preimage μ
    have hμ' : yoneda.map μ' = μ := yoneda.map_preimage _
    let t' := yoneda.preimage (yoneda.map c₁ ≫ z ≫ pullback.fst _ _)
    have ht' : yoneda.map t' = yoneda.map c₁ ≫ z ≫ pullback.fst _ _ := yoneda.map_preimage _
    have hμn : μ' ≫ n₁ = t' ≫ τ := yoneda.map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hμ', hn₁, ← Category.assoc, hμ, ht']
      simp only [z₁, Category.assoc, hρf])
    let lam : _ ⟶ pullback (E.map k₂.hom) n₂ :=
      pullback.lift (t' ≫ pullback.fst (E.map k₃.hom) n₀) μ' (by
        rw [Category.assoc, ← hτf, ← Category.assoc, ← hμn, Category.assoc])
    have hlam : lam ≫ pullback.snd (E.map k₂.hom) n₂ = μ' := pullback.lift_snd _ _ _
    have hm' : μ ≫ m = μ ≫ yoneda.map n₁ ≫ s₁ := by
      have := yoneda.map lam ≫= hg'
      rwa [← Category.assoc, ← Functor.map_comp, hlam, hμ', ← Category.assoc (yoneda.map lam),
        ← Functor.map_comp, hlam, hμ'] at this
    have hsnd : yoneda.map c₁ ≫ z ≫ pullback.snd _ _ = μ ≫ yoneda.map n₁ ≫ b' := by
      have h1 : μ ≫ m ≫ pullback.snd _ _ = yoneda.map c₁ ≫ z ≫ pullback.snd _ _ := by
        rw [← Category.assoc, hμ]
        simp only [z₁, Category.assoc, hρs]
      have h2 := hm' =≫ pullback.snd _ _
      simp only [Category.assoc, hs₁'] at h2
      exact h1.symm.trans h2
    have hR : μ ≫ yoneda.map n₁ ≫ b' =
        yoneda.map c₁ ≫ z ≫ pullback.fst _ _ ≫ yoneda.map τ ≫ b' := by
      rw [← hμ', ← Category.assoc, ← Functor.map_comp, hμn, Functor.map_comp, ht']
      simp only [Category.assoc]
    refine hom_ext_of_etale_atlas B S hS (isSheaf_yoneda_obj B S hS W) hP₃.isSheaf
      (yoneda.map c₁) ((presheaf_yoneda_map_iff B S hS inferInstance c₁).2 hc₁s)
      ((presheaf_yoneda_map_iff B S hS inferInstance c₁).2 hc₁e) ?_
    apply pullback.hom_ext
    · simp only [Category.assoc, hs₃, Category.comp_id]
    · have hs₃' : s₃ ≫ pullback.snd _ _ = yoneda.map τ ≫ b' := pullback.lift_snd _ _ _
      simp only [Category.assoc]
      rw [hs₃', hsnd, hR]
  exact ⟨s₃, hid, hs₃⟩

/-- **An isomorphism over the limit is an isomorphism over a stage.** -/
theorem exists_stage_isIso_of_isLimit_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ BigFppfOver B S hS} {c : Cone E}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)) (i : I)
    {N : BigFppfOver B S hS} (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N))
    (n₀ : N ⟶ E.obj i) (hn₀ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map n₀))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (p : Y ⟶ yoneda.obj (E.obj i)) (hp : IsProper B S hS p)
    (hpf : IsLocallyOfFinitePresentation B S hS p)
    (hiso : IsIso (pullback.fst (yoneda.map (pullback.snd (c.π.app i) n₀ ≫ n₀)) p)) :
    ∃ k : Over i, IsIso (pullback.fst (yoneda.map (pullback.snd (E.map k.hom) n₀ ≫ n₀)) p) := by
  let T := BigFppfOver.toScheme B S hS
  have hVi := isAlgebraicSpace_yoneda B S hS (E.obj i)
  have hrel := relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hY hVi hpf
  have : ∀ j, IsAffine (T.obj (E.obj j)) := hE
  have : IsAffine (T.obj N) := hN
  have hO : ∀ {j : I} (g : j ⟶ i), IsAffine (T.obj (pullback (E.map g) n₀)) := fun g =>
    IsAffine.of_isIso (PreservesPullback.iso T (E.map g) n₀).hom
  -- the section over the limit, and its lift to a stage
  let ψL := pullback.snd (c.π.app i) n₀ ≫ n₀
  let b : yoneda.obj (pullback (c.π.app i) n₀) ⟶ Y :=
    inv (pullback.fst (yoneda.map ψL) p) ≫ pullback.snd (yoneda.map ψL) p
  have hb : b ≫ p = yoneda.map (pullback.snd (c.π.app i) n₀ ≫ n₀) := by
    simp only [b, Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc, ψL]
  obtain ⟨k₁, b', hb', hbb'⟩ :=
    exists_stage_lift_of_isLimit_baseChange hc hE hpt i p hrel hN n₀ b hb
  -- uniqueness of lifts over the limit
  have huniq : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (ν : W ⟶ yoneda.obj (pullback (c.π.app i) n₀)) (z z' : W ⟶ Y),
      z ≫ p = ν ≫ yoneda.map ψL → z' ≫ p = ν ≫ yoneda.map ψL → z = z' := by
    intro W ν z z' hz hz'
    have e : pullback.lift ν z hz.symm = pullback.lift ν z' hz'.symm :=
      (@cancel_mono _ _ _ _ _ (pullback.fst (yoneda.map ψL) p) (IsIso.mono_of_iso _) _ _).1
        (by rw [pullback.lift_fst, pullback.lift_fst])
    simpa only [pullback.lift_snd] using congrArg (· ≫ pullback.snd (yoneda.map ψL) p) e
  -- the section at the stage `k₁`
  let j₁ := k₁.left
  let O₁ := pullback (E.map k₁.hom) n₀
  let ψ₁ := pullback.snd (E.map k₁.hom) n₀ ≫ n₀
  let P₁ := pullback (yoneda.map ψ₁) p
  let s₁ : yoneda.obj O₁ ⟶ P₁ := pullback.lift (𝟙 _) b' (by rw [Category.id_comp, hb'])
  have hs₁ : s₁ ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have hs₁' : s₁ ≫ pullback.snd _ _ = b' := pullback.lift_snd _ _ _
  have hP₁ : IsAlgebraicSpace B S hS P₁ :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS _) hY hVi
  have hP₁p : IsProper B S hS (pullback.fst (yoneda.map ψ₁) p) :=
    isProper_pullback_fst B S hS hY hVi (isAlgebraicSpace_yoneda B S hS _) p _ hp
  have hP₁qc : IsQuasiCompactSpace B S hS P₁ :=
    isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS O₁ (hO k₁.hom) hP₁
      (isAlgebraicSpace_yoneda B S hS _) _ hP₁p.2.2
  obtain ⟨M, m, hM, hmsurj, hmet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS P₁ hP₁).1 hP₁qc
  have hmet' := (isEtale_iff_presheaf_of_yoneda B S hS m).1 hmet
  let n₁ : M ⟶ O₁ := yoneda.preimage (m ≫ pullback.fst _ _)
  have hn₁ : yoneda.map n₁ = m ≫ pullback.fst _ _ := yoneda.map_preimage _
  let n₂ : M ⟶ E.obj j₁ := n₁ ≫ pullback.fst (E.map k₁.hom) n₀
  -- the composite `P₁ ⟶ V_{j₁}` is relatively limit preserving
  let p₁ : P₁ ⟶ yoneda.obj (E.obj j₁) :=
    pullback.fst (yoneda.map ψ₁) p ≫ yoneda.map (pullback.fst (E.map k₁.hom) n₀)
  have hp₁ : IsLocallyOfFinitePresentation B S hS p₁ := by
    have h₁ : IsLocallyOfFinitePresentation B S hS (pullback.fst (yoneda.map ψ₁) p) :=
      (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
        (AlgebraicSpaces.isPullback_fiberProduct B S hS
          (ObjectProperty.homMk (yoneda.map ψ₁) :
            (⟨_, isAlgebraicSpace_yoneda B S hS O₁⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hVi⟩)
          (ObjectProperty.homMk p : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hVi⟩)).flip hpf
    have h₂ : IsLocallyOfFinitePresentation B S hS
        (yoneda.map (pullback.fst (E.map k₁.hom) n₀)) := by
      refine (isLocallyOfFinitePresentation_iff_presheaf B S hS (isAlgebraicSpace_yoneda B S hS _)
        (isAlgebraicSpace_yoneda B S hS _) (Functor.relativelyRepresentable.map yoneda _)).2
        ((presheaf_yoneda_map_iff B S hS inferInstance _).2 ?_)
      rw [← PreservesPullback.iso_hom_fst T (E.map k₁.hom) n₀]
      infer_instance
    exact isLocallyOfFinitePresentation_comp B S hS hP₁ (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS _) _ _ h₁ h₂
  have hrel₁ := relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hP₁
    (isAlgebraicSpace_yoneda B S hS _) hp₁
  let k₀ : Over j₁ := Over.mk (𝟙 j₁)
  let β₁ : yoneda.obj (pullback (E.map k₀.hom) n₂) ⟶ P₁ :=
    yoneda.map (pullback.snd (E.map k₀.hom) n₂) ≫ m
  let β₂ : yoneda.obj (pullback (E.map k₀.hom) n₂) ⟶ P₁ :=
    yoneda.map (pullback.snd (E.map k₀.hom) n₂) ≫ yoneda.map n₁ ≫ s₁
  have hβ₁ : β₁ ≫ p₁ = yoneda.map (pullback.snd (E.map k₀.hom) n₂ ≫ n₂) := by
    simp only [β₁, p₁, n₂, Category.assoc, ← reassoc_of% hn₁, Functor.map_comp]
  have hβ₂ : β₂ ≫ p₁ = yoneda.map (pullback.snd (E.map k₀.hom) n₂ ≫ n₂) := by
    simp only [β₂, p₁, n₂, Category.assoc, reassoc_of% hs₁, Functor.map_comp]
  have hlim : yoneda.map ((overBaseChangeCone E c j₁ n₂).π.app k₀) ≫ β₁ =
      yoneda.map ((overBaseChangeCone E c j₁ n₂).π.app k₀) ≫ β₂ := by
    have hF : yoneda.map ((overBaseChangeCone E c j₁ n₂).π.app k₀) ≫
        yoneda.map (pullback.snd (E.map k₀.hom) n₂) =
          yoneda.map (pullback.snd (c.π.app j₁) n₂) := by
      rw [← Functor.map_comp, pullback.lift_snd]
    simp only [β₁, β₂, ← Category.assoc, hF]
    simp only [Category.assoc]
    let F₀ := yoneda.map (pullback.snd (c.π.app j₁) n₂)
    have hcond : pullback.fst (c.π.app j₁) n₂ ≫ c.π.app i =
        (pullback.snd (c.π.app j₁) n₂ ≫ n₁ ≫ pullback.snd (E.map k₁.hom) n₀) ≫ n₀ := by
      rw [← c.w k₁.hom, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
        Category.assoc, pullback.condition]
      rfl
    let ν : pullback (c.π.app j₁) n₂ ⟶ pullback (c.π.app i) n₀ :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ n₁ ≫ pullback.snd (E.map k₁.hom) n₀)
        hcond
    have hν : yoneda.map ν ≫ yoneda.map ψL = F₀ ≫ yoneda.map n₁ ≫ yoneda.map ψ₁ := by
      simp only [ν, ψL, ψ₁, F₀, ← Functor.map_comp, Category.assoc, pullback.lift_snd_assoc]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, hs₁, ← hn₁, Category.comp_id]
    · refine huniq (yoneda.map ν) _ _ ?_ ?_
      · rw [hν, Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc m,
          ← hn₁]
      · rw [hν, Category.assoc, Category.assoc, Category.assoc, reassoc_of% hs₁', hb']
  obtain ⟨k₂, g, hg⟩ :=
    exists_stage_eq_of_isLimit_baseChange hc hE hpt j₁ p₁ hrel₁ hM n₂ k₀ β₁ β₂ hβ₁ hβ₂ hlim
  have hg' : yoneda.map (pullback.snd (E.map k₂.hom) n₂) ≫ m =
      yoneda.map (pullback.snd (E.map k₂.hom) n₂) ≫ yoneda.map n₁ ≫ s₁ := by
    have e : (overBaseChangeDiagram E j₁ n₂).map g ≫ pullback.snd (E.map k₀.hom) n₂ =
        pullback.snd (E.map k₂.hom) n₂ := pullback.lift_snd _ _ _
    simp only [β₁, β₂, ← Category.assoc, ← Functor.map_comp, e] at hg
    simpa only [Functor.map_comp, Category.assoc] using hg
  exact ⟨Over.mk (k₂.hom ≫ k₁.hom),
    isIso_of_stage_section E i n₀ hY p k₁ b' hb' m hmsurj hmet' n₁ hn₁ k₂ hg'⟩

end AlgebraicGeometry.Space

end
