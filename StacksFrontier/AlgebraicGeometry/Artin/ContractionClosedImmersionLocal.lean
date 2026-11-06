module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionChartAdic
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionRigFormal

/-!
# The closed subscheme of Stacks 0GHE over an affine open of the base

In the situation of Stacks 0GH8 with `X' → S` proper, `Z ⊆ S` closed with inverse image `T'`,
and `U' → S ∖ Z`, `W → S_{/Z}` closed immersions, let `Spec A ⊆ S` be an affine open and
`I ⊆ A` an ideal with `V(I) = Z ∩ Spec A`. This file constructs the ideal `J ⊆ A` of the proof of
**Stacks 0GHE** and proves that `V(J)` has the right open part and the right completion: a point
of `Spec A` avoiding `Z` factors through `U'` exactly when it kills `J`, and a point killing a
power of `I` lies in `W` exactly when it kills `J`.

The construction follows the source with one change. The source compares the ideal `J'` of `W`
in `A^∧` with `J'' A^∧`, `J''` the ideal of the scheme-theoretic image `Y` of `X'`, by the
theorem on formal functions; here the comparison `I^r J'' A^∧ ⊆ J'` and `I^r J' ⊆ J'' A^∧` is
read off the two projections of `W ×_{S_{/Z}} Y_{/Z}` (Stacks 0GD6). The ideal `J` is then the
ideal of `A` with `J A^∧ = J'` and `I^{2r} J ⊆ I^r J'' ⊆ J`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

/-- Pullbacks of fppf sheaves on `BigFppfOver B S hS`: instance search for them times out under
Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_sheaf_ContractionClosedImmersionLocal
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks (FormalSpace.FppfSheaf B S hS) := by
  set_option synthInstance.maxHeartbeats 400000 in infer_instance

local instance (priority := high) hasLimit_cospan_sheaf_ContractionClosedImmersionLocal
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : FormalSpace.FppfSheaf B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Chart

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {hA : B.Contains (Spec (.of A))}
  {f : Spec (.of A) ⟶ S}

omit [IsNoetherianRing A] in
/-- A point of `Spec A` killing a power of `I` has image in `V(I)`. -/
theorem hasImageIn_zeroLocusPoints_of_pow (I : Ideal A) {V : BigFppfOver B S hS}
    (v : V ⟶ FormalSpace.affineOver B S hS hA f) (n : ℕ)
    (hv : ∀ a ∈ I ^ (n + 1), FormalSpace.chartRing v a = 0) :
    Space.HasImageIn B S hS (yoneda.obj (FormalSpace.affineOver B S hS hA f))
      (FormalSpace.zeroLocusPoints B S hS hA f I) V v := by
  rw [FormalSpace.hasImageIn_zeroLocusPoints_iff B S hS hA f I V v]
  intro x
  rw [← FormalSpace.toSpecΓ_comp_spec_chartRing v]
  intro a ha
  show FormalSpace.chartRing v a ∈ (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ x).asIdeal
  apply Ideal.IsPrime.mem_of_pow_mem inferInstance (n + 1)
  rw [← map_pow, hv _ (Ideal.pow_mem_pow ha _)]
  exact Ideal.zero_mem _

omit [IsNoetherianRing A] in
/-- **A point of a closed subspace of `S` lying over `V(I)` is a section of its completion.** -/
theorem nonempty_completionSheaf_of_pow (Z : Set (Space.points B S hS
      (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))) (I : Ideal A)
    (hIZ : FormalSpace.zeroLocusPoints B S hS hA f I = Space.pointsMap B S hS _
      (terminal.from (yoneda.obj (FormalSpace.affineOver B S hS hA f))) ⁻¹' Z)
    (G : Subfunctor (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) {V : BigFppfOver B S hS}
    (v : V ⟶ FormalSpace.affineOver B S hS hA f) (n : ℕ)
    (hv : ∀ a ∈ I ^ (n + 1), FormalSpace.chartRing v a = 0)
    (g : G.toFunctor.obj (Opposite.op V)) :
    Nonempty ((Space.completionSheaf B S hS G.toFunctor
      (Space.pointsMap B S hS _ G.ι ⁻¹' Z)).obj.obj (Opposite.op V)) := by
  have hvI := (Space.hasImageIn_iff_range_subset B S hS
    (X := yoneda.obj (FormalSpace.affineOver B S hS hA f))
    (FormalSpace.zeroLocusPoints B S hS hA f I) V (v : (yoneda.obj _).obj (Opposite.op V))).1
    (hasImageIn_zeroLocusPoints_of_pow I v n hv)
  have hg : Space.HasImageIn B S hS G.toFunctor (Space.pointsMap B S hS _ G.ι ⁻¹' Z) V g := by
    rw [Space.hasImageIn_iff_range_subset]
    rintro _ ⟨p, rfl⟩
    show Space.pointsMap B S hS _ G.ι (Space.pointsMap B S hS _ (yonedaEquiv.symm g) p) ∈ Z
    rw [← Function.comp_apply (f := Space.pointsMap B S hS _ G.ι), ← Space.pointsMap_comp]
    have h1 : yonedaEquiv.symm g ≫ G.ι = yonedaEquiv.symm v ≫
        terminal.from (yoneda.obj (FormalSpace.affineOver B S hS hA f)) := terminal.hom_ext _ _
    rw [h1, Space.pointsMap_comp, Function.comp_apply]
    have := hvI ⟨p, rfl⟩
    rwa [hIZ] at this
  exact ⟨((BigFppfOver.topology B S hS).toSheafify
    (Space.completionSubfunctor B S hS G.toFunctor
      (Space.pointsMap B S hS _ G.ι ⁻¹' Z)).toFunctor).app (Opposite.op V) ⟨⟨g⟩, hg⟩⟩

omit [IsNoetherianRing A] in
/-- The ring map of the inclusion of `Spec (A ⧸ K)` has kernel `K`. -/
theorem ker_chartRing_quotientToAffineOver (K : Ideal A) :
    RingHom.ker (FormalSpace.chartRing (Space.quotientToAffineOver B S hS f hA K)) = K := by
  ext a
  show (Scheme.ΓSpecIso (CommRingCat.of A)).inv a ∈ RingHom.ker
      ((BigFppfOver.toScheme B S hS).map (Space.quotientToAffineOver B S hS f hA K)).appTop.hom ↔ _
  rw [Space.ker_appTop_quotientToAffineOver B S hS f hA K]
  show (Scheme.ΓSpecIso (CommRingCat.of A)).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)
    ∈ K ↔ _
  rw [Iso.inv_hom_id_apply]

end Chart

section Local

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {hA : B.Contains (Spec (.of A))}
  {f : Spec (.of A) ⟶ S}

/-- **The ideal of Stacks 0GHE over an affine open of the base.** Let `Spec A ⊆ S` be an affine
open and `I ⊆ A` an ideal with `V(I) = Z ∩ Spec A`. There is an ideal `J ⊆ A` such that, for
points `v` of `Spec A`:

1. if `V` is affine, `v` kills `J` and avoids `Z`, then `V` lies in `U'`;
2. if `V` is affine and lies in `U'`, then `v` kills `J`;
3. if `v` kills `J` and a power of `I`, then `V` lies in `W`;
4. if `v` kills a power of `I` and `V` lies in `W`, then `v` kills `J`. -/
theorem exists_chartIdeal (c : ContractionSituation B S hS)
    (hproper : Space.IsProper B S hS (terminal.from c.X'))
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (hZ : IsClosed Z)
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T')
    (u : c.U'.toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor)
    (hu : Space.IsClosedImmersion B S hS u)
    (w : c.W ⟶ Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z)
    (hw : FormalSpace.IsClosedImmersion B S hS w)
    [IsOpenImmersion f] (I : Ideal A)
    (hIZ : FormalSpace.zeroLocusPoints B S hS hA f I = Space.pointsMap B S hS _
      (terminal.from (yoneda.obj (FormalSpace.affineOver B S hS hA f))) ⁻¹' Z) :
    ∃ J : Ideal A,
      (∀ (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
        (v : V ⟶ FormalSpace.affineOver B S hS hA f),
          J ≤ RingHom.ker (FormalSpace.chartRing v) → I.map (FormalSpace.chartRing v) = ⊤ →
            Nonempty (c.U'.toFunctor.obj (Opposite.op V))) ∧
      (∀ (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
        (v : V ⟶ FormalSpace.affineOver B S hS hA f),
          Nonempty (c.U'.toFunctor.obj (Opposite.op V)) →
            J ≤ RingHom.ker (FormalSpace.chartRing v)) ∧
      (∀ (V : BigFppfOver B S hS) (v : V ⟶ FormalSpace.affineOver B S hS hA f) (n : ℕ),
          J ≤ RingHom.ker (FormalSpace.chartRing v) →
            I ^ (n + 1) ≤ RingHom.ker (FormalSpace.chartRing v) →
              Nonempty (c.W.obj.obj (Opposite.op V))) ∧
      (∀ (V : BigFppfOver B S hS) (v : V ⟶ FormalSpace.affineOver B S hS hA f) (n : ℕ),
          I ^ (n + 1) ≤ RingHom.ker (FormalSpace.chartRing v) →
            Nonempty (c.W.obj.obj (Opposite.op V)) →
              J ≤ RingHom.ker (FormalSpace.chartRing v)) := by
  classical
  have hI : I.FG := I.fg_of_isNoetherianRing
  let : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
  obtain ⟨hTR, hLT, hJadic, hAadic, hAw⟩ := FormalSpace.adicCompletion_isAdic_of_fg I hI
  have : IsNoetherianRing (AdicCompletion I A) := Stacks.AdicCompletion.NoetherianRing.solution I
  let V0 := FormalSpace.affineOver B S hS hA f
  let D := FormalSpace.adicQuotientSystem B S hS hA f I hI
  let hD := FormalSpace.quotientSystemCompatible_adicQuotientSystem B S hS hA f I hI
  have := FormalSpace.isIso_completionComparison_adicQuotientSystem B S hS hA f I hI
  let comp := FormalSpace.completionComparison B S hS hA f I D hD
  have hone := Space.isAlgebraicSpace_terminal B S hS
  let q0 := terminal.from (yoneda.obj V0)
  -- the chart `Spf A^∧ → S_{/Z}` is representable étale
  have hEt : Etale ((BigFppfOver.toScheme B S hS).map (terminal.from V0)) := by
    have h := Space.toScheme_map_terminal_from B S hS V0
    have : Etale ((BigFppfOver.toScheme B S hS).map (terminal.from V0) ≫
        (Space.toSchemeTerminalIso B S hS).hom) := by
      rw [h]; show Etale f; infer_instance
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @Etale) _ _).1 this
  have h1 : Space.IsEtale B S hS (yoneda.map (terminal.from V0)) :=
    (Space.isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((Space.presheaf_yoneda_map_iff B S hS
        AlgebraicGeometry.Etale.etale_isStableUnderBaseChange _).2 hEt)
  have hq0 : Space.IsEtale B S hS q0 := by
    rw [show q0 = yoneda.map (terminal.from V0) ≫ (Space.yonedaTerminalIso B S hS).hom from
      terminal.hom_ext _ _]
    exact Space.isEtale_comp B S hS h1 (Space.isEtale_of_isIso B S hS _)
  have hb0 : FormalSpace.IsRepresentableEtale B S hS (Space.completionSheafMap B S hS q0 Z) :=
    FormalSpace.isEtale_completionSheafMap B S hS (isAlgebraicSpace_yoneda B S hS V0) hone
      q0 Z hq0
  let b : FormalSpace.formalSpectrum D ⟶
      Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z :=
    comp ≫ eqToHom (congrArg (Space.completionSheaf B S hS (yoneda.obj V0)) hIZ) ≫
      Space.completionSheafMap B S hS q0 Z
  have hb : FormalSpace.IsRepresentableEtale B S hS b :=
    (FormalSpace.isRepresentableEtale_of_isIso B S hS comp).comp B S hS
      ((FormalSpace.isRepresentableEtale_of_isIso B S hS _).comp B S hS hb0)
  -- presentations of the charts of `W` and of `Y_{/Z}`
  have hyc := c.isClosedImmersion_imageYCompletion Z
  obtain ⟨CW, _, _, _, _, _, hCWa, EW, eW, φW, hφW⟩ :=
    FormalSpace.exists_adic_presentation_of_isPullback B S hS hw (IsPullback.of_hasPullback w b)
      hAadic hAw D (Iso.refl _)
  obtain ⟨CY, _, _, _, _, _, hCYa, EY, eY, φY, hφY⟩ :=
    FormalSpace.exists_adic_presentation_of_isPullback B S hS hyc
      (IsPullback.of_hasPullback (c.imageYCompletion Z) b) hAadic hAw D (Iso.refl _)
  -- the comparison of Stacks 0GD6
  obtain ⟨hfst, hsnd, hkW, hkY⟩ := c.projections_W'' Z hproper hZ hT' u hu w hw
  obtain ⟨L, hLo, hLY, hLW⟩ := FormalSpace.exists_isOpen_mul_ker_le_of_hasAnnihilatedKer w
    (c.imageYCompletion Z) hfst hsnd hkW hkY b hb hAw (Iso.refl _) hCWa eW φW hφW hCYa eY φY hφY
  obtain ⟨r, hr⟩ := (isAdic_iff.mp hJadic).2 _ (hLo.mem_nhds L.zero_mem)
  have hrL : (I.map (algebraMap A (AdicCompletion I A))) ^ r ≤ L := hr
  -- the ideal `J''` of `Y` over the chart
  let G := c.imageY.preimage q0
  have hG : Space.IsClosedSubspace B S hS G :=
    Space.isClosedSubspace_preimage B S hS q0 c.imageY hone (isAlgebraicSpace_yoneda B S hS V0)
      c.isClosedSubspace_imageY
  let J'' := Space.closedChartRingIdeal B S hS f hA G hG
  have hsubY := subsingleton_subfunctor_terminal_obj c.imageY
  have hmemG' : ∀ {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      (v : V ⟶ V0), q0.app _ v ∈ c.imageY.obj (Opposite.op V) ↔
        J'' ≤ RingHom.ker (FormalSpace.chartRing v) := fun v =>
    FormalSpace.mem_iff_closedChartRingIdeal_le G hG v
  have hmemG : ∀ {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      (v : V ⟶ V0), Nonempty (c.imageY.toFunctor.obj (Opposite.op V)) ↔
        J'' ≤ RingHom.ker (FormalSpace.chartRing v) := by
    intro V _ v
    rw [← hmemG' v]
    constructor
    · rintro ⟨y⟩
      have := subsingleton_terminal_obj (B := B) (S := S) (hS := hS) (Opposite.op V)
      rw [Subsingleton.elim (q0.app _ v) y.1]
      exact y.2
    · intro hv
      exact ⟨⟨_, hv⟩⟩
  -- a point of the chart is invertible on `I` exactly when it avoids `Z`
  have hZt : ∀ {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      (v : V ⟶ V0), I.map (FormalSpace.chartRing v) = ⊤ ↔
        q0.app _ v ∈ (Space.openSubspaceOfPoints B S hS _ Zᶜ).obj (Opposite.op V) := by
    intro V _ v
    rw [← FormalSpace.range_subset_compl_zeroLocusPoints_iff I v]
    show _ ↔ Set.range (Space.pointsMap B S hS (yoneda.obj V) (yonedaEquiv.symm (q0.app _ v))) ⊆ Zᶜ
    have h1 : yonedaEquiv.symm (q0.app _ v) = yoneda.map v ≫ q0 := terminal.hom_ext _ _
    rw [h1, Space.pointsMap_comp, Set.range_comp, hIZ, Set.image_subset_iff, Set.preimage_compl]
  -- every ideal `K` is the kernel of an affine point, which kills any ideal contained in `K`
  have hpt : ∀ K J : Ideal A, J ≤ K → ∃ (T : BigFppfOver B S hS)
      (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (t : T ⟶ V0),
        RingHom.ker (FormalSpace.chartRing t) = K ∧ ∀ a ∈ J, FormalSpace.chartRing t a = 0 :=
    fun K J hJ => ⟨_, (FormalSpace.quotientOver B S hS f hA K).property,
      Space.quotientToAffineOver B S hS f hA K, ker_chartRing_quotientToAffineOver K,
      fun a ha => RingHom.mem_ker.1
        (by rw [ker_chartRing_quotientToAffineOver K]; exact hJ ha)⟩
  -- every point of the chart killing a power of `I` factors through a quotient stage
  let st := fun n => FormalSpace.adicCompletionPowStageIdeal I hI n
  let Q := fun n => FormalSpace.quotientStageToAffine B S hS hA f I D hD (st n)
  let Yq := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  -- the kernel of the chart of `Y_{/Z}` is `J'' A^∧`
  have hKYn : ∀ n : ℕ, (RingHom.ker φY.toRingHom ⊔ (st n).1).comap
      (algebraMap A (AdicCompletion I A)) = J'' ⊔ I ^ (n + 1) := by
    intro n
    apply le_antisymm
    · -- a point of `Y` over the stage kills the chart kernel of `Y_{/Z}`
      obtain ⟨T, _, t, hker, htI⟩ :=
        hpt (J'' ⊔ I ^ (n + 1)) _ le_sup_right
      obtain ⟨y⟩ := (hmemG t).2 (by rw [hker]; exact le_sup_left)
      obtain ⟨sec⟩ := nonempty_completionSheaf_of_pow Z I hIZ c.imageY t n htI y
      obtain ⟨t', ht', hring⟩ := FormalSpace.exists_stage_factor hA f I hI n t htI
      have hlift := (FormalSpace.exists_lift_iff_ker_le_of_stage hyc b hAadic hAw
        (Iso.refl _) hCYa (IsPullback.of_hasPullback _ _) eY φY hφY (st n) t').1
        ⟨(Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm sec,
          hom_ext_completionSheaf_terminal Z _ _⟩
      intro a ha
      obtain ⟨k, hk, j, hj, hkj⟩ := Submodule.mem_sup.1 (Ideal.mem_comap.1 ha)
      have hmk : Ideal.Quotient.mk (st n).1 (algebraMap A (AdicCompletion I A) a) =
          Ideal.Quotient.mk (st n).1 k := by
        rw [← hkj, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, add_zero]
      have := hlift k hk
      rwa [← hmk, hring, ← RingHom.mem_ker, hker] at this
    · -- a point over the stage killing the chart kernel of `Y_{/Z}` lies in `Y`
      refine sup_le ?_ ?_
      · let K := (RingHom.ker φY.toRingHom ⊔ (st n).1).comap (algebraMap A (AdicCompletion I A))
        obtain ⟨T, _, t, hker, htI⟩ := hpt K (I ^ (n + 1)) fun a ha =>
          Ideal.mem_comap.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha))
        obtain ⟨t', ht', hring⟩ := FormalSpace.exists_stage_factor hA f I hI n t htI
        obtain ⟨m, -⟩ := (FormalSpace.exists_lift_iff_ker_le_of_stage hyc b hAadic hAw
          (Iso.refl _) hCYa (IsPullback.of_hasPullback _ _) eY φY hφY (st n) t').2 (by
            intro x hx
            obtain ⟨a, ha⟩ := Ideal.exists_sub_algebraMap_mem_map_pow I x (n + 1)
            have hmk : Ideal.Quotient.mk (st n).1 x =
                Ideal.Quotient.mk (st n).1 (algebraMap A (AdicCompletion I A) a) :=
              Ideal.Quotient.eq.2 ha
            have haK : a ∈ K := by
              refine Ideal.mem_comap.2 ?_
              have := Ideal.sub_mem _ (Ideal.mem_sup_left hx) (Ideal.mem_sup_right ha)
              rwa [sub_sub_cancel] at this
            rw [hmk, hring]
            exact RingHom.mem_ker.1 (by rw [hker]; exact haK))
        obtain ⟨y⟩ := FormalSpace.nonempty_of_completionSheaf c.imageY
          c.isClosedSubspace_imageY.1 _ (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) m)
        have := (hmemG t).1 ⟨y⟩
        rwa [hker] at this
      · exact fun a ha => Ideal.mem_comap.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha))
  have hKY : RingHom.ker φY.toRingHom = J''.map (algebraMap A (AdicCompletion I A)) := by
    have hsup : ∀ n : ℕ, RingHom.ker φY.toRingHom ⊔ (st n).1 =
        J''.map (algebraMap A (AdicCompletion I A)) ⊔ (st n).1 := by
      intro n
      apply le_antisymm
      · intro x hx
        obtain ⟨a, ha⟩ := Ideal.exists_sub_algebraMap_mem_map_pow I x (n + 1)
        have haK : a ∈ J'' ⊔ I ^ (n + 1) := by
          rw [← hKYn n]
          refine Ideal.mem_comap.2 ?_
          have := Ideal.sub_mem _ hx (Ideal.mem_sup_right ha)
          rwa [sub_sub_cancel] at this
        have hmap := Ideal.mem_map_of_mem (algebraMap A (AdicCompletion I A)) haK
        rw [Ideal.map_sup] at hmap
        rw [← add_sub_cancel (algebraMap A (AdicCompletion I A) a) x]
        exact Ideal.add_mem _ hmap (Ideal.mem_sup_right ha)
      · refine sup_le ?_ le_sup_right
        rw [Ideal.map_le_iff_le_comap, hKYn n]
        exact le_sup_left
    rw [← Ideal.iInf_sup_map_pow_eq I (RingHom.ker φY.toRingHom),
      ← Ideal.iInf_sup_map_pow_eq I (J''.map (algebraMap A (AdicCompletion I A)))]
    exact iInf_congr hsup
  -- the ideal `J`
  let N : Ideal A := I ^ r * J''
  have hNmap : N.map (algebraMap A (AdicCompletion I A)) =
      (I.map (algebraMap A (AdicCompletion I A))) ^ r * RingHom.ker φY.toRingHom := by
    rw [Ideal.map_mul, Ideal.map_pow, hKY]
  have hN : N.map (algebraMap A (AdicCompletion I A)) ≤ RingHom.ker φW.toRingHom := by
    rw [hNmap]
    exact (Ideal.mul_mono_left hrL).trans hLY
  have hK : (I ^ (r + r)).map (algebraMap A (AdicCompletion I A)) * RingHom.ker φW.toRingHom ≤
      N.map (algebraMap A (AdicCompletion I A)) := by
    rw [hNmap, Ideal.map_pow, pow_add, Ideal.mul_assoc]
    exact Ideal.mul_mono_right ((Ideal.mul_mono_left hrL).trans hLW)
  obtain ⟨J, hNJ, hIJ, hJK⟩ := Ideal.exists_map_adicCompletion_eq I N (RingHom.ker φW.toRingHom)
    (r + r) hN hK
  -- the `θ` of a point over a stage
  have hθ : ∀ {V : BigFppfOver B S hS} (v : V ⟶ V0) (n : ℕ)
      (v' : V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage (st n)))
      (hring : ∀ a : A, ((BigFppfOver.toScheme B S hS).map v').appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (AdicCompletion I A ⧸ (st n).1))).inv
            (Ideal.Quotient.mk (st n).1 (algebraMap A (AdicCompletion I A) a))) =
          FormalSpace.chartRing v a),
      J ≤ RingHom.ker (FormalSpace.chartRing v) →
        ∀ x ∈ RingHom.ker φW.toRingHom, ((BigFppfOver.toScheme B S hS).map v').appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (AdicCompletion I A ⧸ (st n).1))).inv
            (Ideal.Quotient.mk (st n).1 x)) = 0 := by
    intro V v n v' hring hJ x hx
    let θ : AdicCompletion I A →+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
      (((Scheme.ΓSpecIso (CommRingCat.of (AdicCompletion I A ⧸ (st n).1))).inv ≫
        ((BigFppfOver.toScheme B S hS).map v').appTop).hom).comp (Ideal.Quotient.mk (st n).1)
    have hJθ : J.map (algebraMap A (AdicCompletion I A)) ≤ RingHom.ker θ := by
      rw [Ideal.map_le_iff_le_comap]
      intro j hj
      rw [Ideal.mem_comap, RingHom.mem_ker]
      show ((BigFppfOver.toScheme B S hS).map v').appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (AdicCompletion I A ⧸ (st n).1))).inv
          (Ideal.Quotient.mk (st n).1 (algebraMap A (AdicCompletion I A) j))) = 0
      rw [hring]
      exact RingHom.mem_ker.1 (hJ hj)
    rw [← hJK] at hx
    exact RingHom.mem_ker.1 (hJθ hx)
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · -- (1) a point avoiding `Z` and killing `J` lies in `U'`
    intro V _ v hJ hIv
    have hJ'' : J'' ≤ RingHom.ker (FormalSpace.chartRing v) := by
      rw [← Ideal.map_eq_bot_iff_le_ker]
      have h0 : N.map (FormalSpace.chartRing v) = ⊥ :=
        (Ideal.map_eq_bot_iff_le_ker _).2 (hNJ.trans hJ)
      rwa [Ideal.map_mul, Ideal.map_pow, hIv, Ideal.top_pow, Ideal.top_mul] at h0
    have htR : q0.app _ v ∈ (Subfunctor.range (u ≫ (Space.openSubspaceOfPoints B S hS _ Zᶜ).ι)).obj
        (Opposite.op V) := by
      rw [← c.imageY_inf_compl hproper Z hZ hT' u hu]
      exact ⟨(hmemG' v).2 hJ'', (hZt v).1 hIv⟩
    obtain ⟨x, -⟩ := htR
    exact ⟨x⟩
  · -- (2) a point of `U'` kills `J`
    intro V _ v ⟨x⟩
    have := subsingleton_terminal_obj (B := B) (S := S) (hS := hS) (Opposite.op V)
    have htq : (u ≫ (Space.openSubspaceOfPoints B S hS _ Zᶜ).ι).app _ x = q0.app _ v :=
      Subsingleton.elim _ _
    have htY : q0.app _ v ∈ c.imageY.obj (Opposite.op V) := by
      have : q0.app _ v ∈ (Subfunctor.range (u ≫ (Space.openSubspaceOfPoints B S hS _ Zᶜ).ι)).obj
          (Opposite.op V) := ⟨x, htq⟩
      rw [← c.imageY_inf_compl hproper Z hZ hT' u hu] at this
      exact this.1
    have hJ'' := (hmemG' v).1 htY
    have hIv : I.map (FormalSpace.chartRing v) = ⊤ := (hZt v).2 (htq ▸ (u.app _ x).2)
    rw [← Ideal.map_eq_bot_iff_le_ker]
    have h0 : (I ^ (r + r) * J).map (FormalSpace.chartRing v) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      exact hIJ.trans ((Ideal.mul_le_right).trans hJ'')
    rwa [Ideal.map_mul, Ideal.map_pow, hIv, Ideal.top_pow, Ideal.top_mul] at h0
  · -- (3) a point killing `J` and a power of `I` lies in `W`
    intro V v n hJ hIn
    obtain ⟨v', -, hring⟩ := FormalSpace.exists_stage_factor hA f I hI n v
      (fun a ha => RingHom.mem_ker.1 (hIn ha))
    obtain ⟨m, -⟩ := (FormalSpace.exists_lift_iff_ker_le_of_stage hw b hAadic hAw
      (Iso.refl _) hCWa (IsPullback.of_hasPullback _ _) eW φW hφW (st n) v').2
      (hθ v n v' hring hJ)
    exact ⟨Sheaf.sectionEquiv (BigFppfOver.topology B S hS) m⟩
  · -- (4) a point of `W` killing a power of `I` kills `J`
    intro V v n hIn ⟨sw⟩
    obtain ⟨v', -, hring⟩ := FormalSpace.exists_stage_factor hA f I hI n v
      (fun a ha => RingHom.mem_ker.1 (hIn ha))
    have := FormalSpace.mono_of_isClosedImmersion B S hS w hw
    have hlift := (FormalSpace.exists_lift_iff_ker_le_of_stage hw b hAadic hAw
      (Iso.refl _) hCWa (IsPullback.of_hasPullback _ _) eW φW hφW (st n) v').1
      ⟨(Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm sw,
        hom_ext_completionSheaf_terminal Z _ _⟩
    intro j hj
    have hx : algebraMap A (AdicCompletion I A) j ∈ RingHom.ker φW.toRingHom := by
      rw [← hJK]; exact Ideal.mem_map_of_mem _ hj
    have := hlift _ hx
    rwa [hring] at this

end Local

end AlgebraicGeometry.Artin.ContractionSituation
