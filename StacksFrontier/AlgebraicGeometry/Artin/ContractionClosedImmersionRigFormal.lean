module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionRig

/-!
# The rig-étale, rig-surjective closed immersions `W'' → W` and `W'' → Y_{/Z}`

Continuation of `StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionRig`. With `Y`
the scheme-theoretic image of `X' → S` and `W'' = W ×_{S_{/Z}} Y_{/Z}`, the factorizations
`g : X'_{/T'} → W'' → W` and `X'_{/T'} → W'' → Y_{/Z}` of the two formal modifications out of
`X'_{/T'}` make both projections of `W''` rig-étale and rig-surjective closed immersions, so by
**Stacks 0GD6** some ideal of definition annihilates their kernels on every chart.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
attribute [local instance 10000] presheafHasPullback

variable (c : ContractionSituation B S hS)
  (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))

/-- The closed subset `T_Y = Y ∩ Z` of `|Y|`. -/
abbrev imageYT : Set (Space.points B S hS c.imageY.toFunctor) :=
  Space.pointsMap B S hS _ c.imageY.ι ⁻¹' Z

/-- The closed immersion `Y_{/Z} → S_{/Z}`. -/
noncomputable abbrev imageYCompletion :
    Space.completionSheaf B S hS c.imageY.toFunctor (c.imageYT Z) ⟶
      Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z :=
  Space.completionSheafMap B S hS c.imageY.ι Z

/-- The morphism `Y_{/Z} → S_{/Z}` is a closed immersion of formal algebraic spaces. -/
theorem isClosedImmersion_imageYCompletion :
    FormalSpace.IsClosedImmersion B S hS (c.imageYCompletion Z) :=
  FormalSpace.isClosedImmersion_completionSheafMap B S hS c.isClosedSubspace_imageY.1
    (Space.isAlgebraicSpace_terminal B S hS) c.imageY.ι Z c.isClosedSubspace_imageY.2

/-- If `X'` is proper over `S`, then the morphism `X' → Y` to the scheme-theoretic image is
proper. -/
theorem isProper_toImageY (hproper : Space.IsProper B S hS (terminal.from c.X')) :
    Space.IsProper B S hS c.toImageY :=
  Space.isProper_of_comp_of_isSeparated B S hS c.isAlgebraicSpace_X'
    c.isClosedSubspace_imageY.1 (Space.isAlgebraicSpace_terminal B S hS) c.toImageY
    c.imageY.ι (by rwa [toImageY_ι])
    (Space.isSeparated_of_isClosedImmersion B S hS _ c.isClosedSubspace_imageY.2)

/-- If the preimage of `Z` in `|X'|` is `T'`, then the preimage of `T_Y = Y ∩ Z` under `X' → Y`
is `T'`. -/
theorem preimage_imageYT
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T') :
    Space.pointsMap B S hS c.X' c.toImageY ⁻¹' c.imageYT Z = c.T' := by
  rw [← Set.preimage_comp, ← Space.pointsMap_comp, toImageY_ι, hT']

/-- The scheme-theoretic image `Y` is locally Noetherian. -/
theorem isLocallyNoetherian_imageY : Space.IsLocallyNoetherian B S hS c.imageY.toFunctor := by
  have h : terminal.from c.imageY.toFunctor = c.imageY.ι := terminal.hom_ext _ _
  apply c.isLocallyNoetherian_of_isLocallyOfFiniteType_base
  rw [h]
  exact Space.isLocallyOfFiniteType_of_isClosedImmersion B S hS _ c.isClosedSubspace_imageY.2

/-- The restriction of `X' → Y` over the complement of `T_Y = Y ∩ Z` is an isomorphism. -/
theorem isIso_openComplementRestriction_toImageY
    (hproper : Space.IsProper B S hS (terminal.from c.X')) (hZ : IsClosed Z)
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T')
    (u : c.U'.toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor)
    (hu : Space.IsClosedImmersion B S hS u) :
    IsIso (Space.openComplementRestriction B S hS c.toImageY (c.imageYT Z)) := by
  have hpre := c.preimage_imageYT Z hT'
  have hmono : Mono u := Space.mono_of_isClosedImmersion B S hS u hu
  have hYU := c.imageY_inf_compl hproper Z hZ hT' u hu
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  rw [isIso_iff_bijective]
  induction V using Opposite.rec with
  | op V =>
  have hU' : ∀ a : (Space.openSubspaceOfPoints B S hS c.X'
      (Space.pointsMap B S hS c.X' c.toImageY ⁻¹' (c.imageYT Z)ᶜ)).toFunctor.obj
        (Opposite.op V), a.1 ∈ c.U'.obj (Opposite.op V) := by
    intro a
    have ha := a.2
    change Set.range _ ⊆ _ at ha
    show Set.range _ ⊆ c.T'ᶜ
    refine ha.trans ?_
    rw [Set.preimage_compl, hpre]
  have htgt : Subsingleton ((Space.openSubspaceOfPoints B S hS c.imageY.toFunctor
      (c.imageYT Z)ᶜ).toFunctor.obj (Opposite.op V)) := by
    have := subsingleton_subfunctor_terminal_obj c.imageY (Opposite.op V)
    exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  refine ⟨fun a b _ => ?_, fun y => ?_⟩
  · have hsub := subsingleton_subfunctor_terminal_obj
      (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ)
      (Opposite.op V)
    have hinj : Function.Injective (u.app (Opposite.op V)) :=
      (mono_iff_injective _).1 inferInstance
    have := hinj (a₁ := ⟨a.1, hU' a⟩) (a₂ := ⟨b.1, hU' b⟩) (Subsingleton.elim _ _)
    exact Subtype.ext (Subtype.mk.inj this)
  · let t : (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).obj (Opposite.op V) := y.1.1
    have htZ : t ∈ (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
        Zᶜ).obj (Opposite.op V) := by
      have hy := y.2
      show Set.range (Space.pointsMap B S hS (yoneda.obj V) (yonedaEquiv.symm t)) ⊆ Zᶜ
      have hs : yonedaEquiv.symm t = yonedaEquiv.symm y.1 ≫ c.imageY.ι := by
        show yonedaEquiv.symm (c.imageY.ι.app _ y.1) = _
        rw [yonedaEquiv_symm_naturality_right]
      rw [hs, Space.pointsMap_comp, Set.range_comp]
      rintro _ ⟨p, hp, rfl⟩
      exact hy hp
    have htR : t ∈ (Subfunctor.range
        (u ≫ (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).ι)).obj
          (Opposite.op V) := by
      rw [← hYU]
      exact ⟨y.1.2, htZ⟩
    obtain ⟨z, -⟩ := htR
    refine ⟨⟨z.1, ?_⟩, Subsingleton.elim _ _⟩
    have hz := z.2
    change Set.range _ ⊆ c.T'ᶜ at hz
    show Set.range _ ⊆ _
    rwa [Set.preimage_compl, hpre]

/-- **`X' → Y` is an isomorphism over `Y ∖ Z`.** -/
theorem isIso_pullback_snd_toImageY
    (hproper : Space.IsProper B S hS (terminal.from c.X')) (hZ : IsClosed Z)
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T')
    (u : c.U'.toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor)
    (hu : Space.IsClosedImmersion B S hS u) :
    IsIso (pullback.snd c.toImageY
      (Space.openSubspaceOfPoints B S hS c.imageY.toFunctor (c.imageYT Z)ᶜ).ι) := by
  have hsq := Space.isPullback_openComplementRestriction B S hS c.toImageY (c.imageYT Z)
  have := c.isIso_openComplementRestriction_toImageY Z hproper hZ hT' u hu
  have : pullback.snd c.toImageY
      (Space.openSubspaceOfPoints B S hS c.imageY.toFunctor (c.imageYT Z)ᶜ).ι =
      hsq.isoPullback.inv ≫ Space.openComplementRestriction B S hS c.toImageY (c.imageYT Z) := by
    rw [Iso.eq_inv_comp, hsq.isoPullback_hom_snd]
  rw [this]
  infer_instance

/-- **`X'_{/T'} → Y_{/Z}` is a formal modification** (Stacks 0GDM). -/
theorem isFormalModification_completion_toImageY
    (hproper : Space.IsProper B S hS (terminal.from c.X')) (hZ : IsClosed Z)
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T')
    (u : c.U'.toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor)
    (hu : Space.IsClosedImmersion B S hS u) :
    FormalSpace.IsFormalModification B S hS
      (Space.completionSheafRestrict B S hS c.toImageY c.T' (c.imageYT Z)
        (c.preimage_imageYT Z hT').symm.subset) := by
  have hFM := FormalSpace.isFormalModification_completionSheafMap c.isAlgebraicSpace_X'
    c.isClosedSubspace_imageY.1 c.isLocallyNoetherian_imageY c.toImageY (c.imageYT Z)
    (hZ.preimage (Space.continuous_pointsMap B S hS _)) (c.isProper_toImageY hproper)
    (c.isIso_pullback_snd_toImageY Z hproper hZ hT' u hu)
  have key : ∀ (T'' : Set (Space.points B S hS c.X'))
      (h : T'' = Space.pointsMap B S hS c.X' c.toImageY ⁻¹' c.imageYT Z),
      FormalSpace.IsFormalModification B S hS
        (Space.completionSheafRestrict B S hS c.toImageY T'' (c.imageYT Z) h.subset) := by
    rintro _ rfl
    rw [Space.completionSheafRestrict_self]
    exact hFM
  exact key _ (c.preimage_imageYT Z hT').symm

/-- The completion `X'_{/T'} → Y_{/Z}` of `X' → Y`. -/
noncomputable abbrev completionToImageY
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T') :
    Space.completionSheaf B S hS c.X' c.T' ⟶
      Space.completionSheaf B S hS c.imageY.toFunctor (c.imageYT Z) :=
  Space.completionSheafRestrict B S hS c.toImageY c.T' (c.imageYT Z)
    (c.preimage_imageYT Z hT').symm.subset

/-- A closed immersion `ι` of locally Noetherian formal algebraic spaces such that `ℓ ≫ ι` is
rig-étale and rig-surjective for some rig-étale, rig-surjective `ℓ` has kernel annihilated on
charts by ideals of definition. -/
theorem hasAnnihilatedKerOnPullbackCharts_of_comp {X P T : FormalSpace.FppfSheaf B S hS}
    (ℓ : X ⟶ P) (ι : P ⟶ T) (hX : FormalSpace.IsLocallyNoetherian B S hS X)
    (hP : FormalSpace.IsLocallyNoetherian B S hS P)
    (hT : FormalSpace.IsLocallyNoetherian B S hS T) (hι : FormalSpace.IsClosedImmersion B S hS ι)
    (hℓet : FormalSpace.IsRigEtale B S hS ℓ) (hℓsurj : FormalSpace.IsRigSurjective B S hS ℓ)
    (het : FormalSpace.IsRigEtale B S hS (ℓ ≫ ι))
    (hsurj : FormalSpace.IsRigSurjective B S hS (ℓ ≫ ι)) :
    FormalSpace.HasAnnihilatedKerOnPullbackCharts B S hS ι :=
  (FormalSpace.isRigSmooth_and_isRigSurjective_tfae_of_isClosedImmersion' B S hS ι hP hT hι
    (FormalSpace.IsRigEtale B S hS ι ∧ FormalSpace.IsRigSurjective B S hS ι)
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (FormalSpace.HasAnnihilatedKerOnPullbackCharts B S hS ι)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).1
    ⟨FormalSpace.isRigEtale_of_comp_of_isRigSurjective_of_isLocallyNoetherian B S hS ℓ ι hX
      (FormalSpace.IsLocallyOfFiniteType.of_isClosedImmersion B S hS ι hι) hℓet hℓsurj het,
     FormalSpace.IsRigSurjective.of_comp B S hS ℓ ι hsurj⟩

/-- **Both projections of `W'' = W ×_{S_{/Z}} Y_{/Z}` are closed immersions whose kernels
are annihilated on charts by ideals of definition.** They are closed immersions as base
changes of the closed immersions `Y_{/Z} → S_{/Z}` and `W → S_{/Z}`. The two formal
modifications `g : X'_{/T'} → W` and `X'_{/T'} → Y_{/Z}` factor through `W''` (all morphisms
into `S_{/Z}` agree), so by Stacks 0GH5 and 0GH4 the factorization is rig-surjective and
rig-étale, and then by Stacks 0GH6 and 0AQT both projections are rig-étale and
rig-surjective; Stacks 0GD6 converts this into condition (3). -/
theorem projections_W''
    (hproper : Space.IsProper B S hS (terminal.from c.X')) (hZ : IsClosed Z)
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T')
    (u : c.U'.toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor)
    (hu : Space.IsClosedImmersion B S hS u)
    (w : c.W ⟶ Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z)
    (hw : FormalSpace.IsClosedImmersion B S hS w) :
    FormalSpace.IsClosedImmersion B S hS (pullback.fst w (c.imageYCompletion Z)) ∧
      FormalSpace.IsClosedImmersion B S hS (pullback.snd w (c.imageYCompletion Z)) ∧
      FormalSpace.HasAnnihilatedKerOnPullbackCharts B S hS
        (pullback.fst w (c.imageYCompletion Z)) ∧
      FormalSpace.HasAnnihilatedKerOnPullbackCharts B S hS
        (pullback.snd w (c.imageYCompletion Z)) := by
  let ιW := pullback.fst w (c.imageYCompletion Z)
  let ιY := pullback.snd w (c.imageYCompletion Z)
  have hsq := IsPullback.of_hasPullback w (c.imageYCompletion Z)
  have hιW : FormalSpace.IsClosedImmersion B S hS ιW :=
    FormalSpace.isClosedImmersion_of_isPullback B S hS hsq.flip
      (c.isClosedImmersion_imageYCompletion Z)
  have hιY : FormalSpace.IsClosedImmersion B S hS ιY :=
    FormalSpace.isClosedImmersion_of_isPullback B S hS hsq hw
  have hg := c.isFormalModification_g
  have hh := c.isFormalModification_completion_toImageY Z hproper hZ hT' u hu
  let ℓ : Space.completionSheaf B S hS c.X' c.T' ⟶ pullback w (c.imageYCompletion Z) :=
    pullback.lift c.g (c.completionToImageY Z hT') (hom_ext_completionSheaf_terminal Z _ _)
  have hℓW : ℓ ≫ ιW = c.g := pullback.lift_fst _ _ _
  have hℓY : ℓ ≫ ιY = c.completionToImageY Z hT' := pullback.lift_snd _ _ _
  have hXN := hg.isLocallyNoetherian_source
  have hWN := hg.isLocallyNoetherian_target
  have hYN := hh.isLocallyNoetherian_target
  have hιWft := FormalSpace.IsLocallyOfFiniteType.of_isClosedImmersion B S hS ιW hιW
  have hW''f : FormalSpace.IsFormalAlgebraicSpace B S hS (pullback w (c.imageYCompletion Z)) :=
    FormalSpace.isFormalAlgebraicSpace_of_isRepresentableByAlgebraicSpacesULift B S hS ιW
      hWN.1 hιW.1
  have hW''N : FormalSpace.IsLocallyNoetherian B S hS (pullback w (c.imageYCompletion Z)) :=
    FormalSpace.isLocallyNoetherian_source_of_isLocallyOfFiniteType' B S hS ιW hW''f hWN hιWft
  have hℓft : FormalSpace.IsLocallyOfFiniteType B S hS ℓ :=
    FormalSpace.IsLocallyOfFiniteType.of_comp B S hS ℓ ιW hW''f
      (by rw [hℓW]; exact FormalSpace.IsProper.isLocallyOfFiniteType B S hS hg.isProper)
  have hmW : Mono ιW := FormalSpace.mono_of_isClosedImmersion B S hS ιW hιW
  have hℓsurj : FormalSpace.IsRigSurjective B S hS ℓ :=
    FormalSpace.IsRigSurjective.of_comp_of_mono B S hS ℓ ιW hℓft hιWft
      (by rw [hℓW]; exact hg.isRigSurjective) hmW
  have hℓet : FormalSpace.IsRigEtale B S hS ℓ :=
    FormalSpace.isRigEtale_of_comp_of_isAdicMorphism_of_mono_of_isLocallyNoetherian B S hS ℓ ιW
      hXN hW''N hWN (by rw [hℓW]; exact hg.isRigEtale) hιW.1 hmW
  exact ⟨hιW, hιY, hasAnnihilatedKerOnPullbackCharts_of_comp ℓ ιW hXN hW''N hWN hιW hℓet hℓsurj
    (by rw [hℓW]; exact hg.isRigEtale) (by rw [hℓW]; exact hg.isRigSurjective),
    hasAnnihilatedKerOnPullbackCharts_of_comp ℓ ιY hXN hW''N hYN hιY hℓet hℓsurj
    (by rw [hℓY]; exact hh.isRigEtale) (by rw [hℓY]; exact hh.isRigSurjective)⟩

end AlgebraicGeometry.Artin.ContractionSituation
