module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionUnique
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProjGluing

/-!
# Gluing the ideals of Stacks 0GHE over the affine opens of the base

For every affine open `U` of the base `S`, the proof of **Stacks 0GHE** produces an ideal
`J_U ⊆ Γ(S, U)` (`AlgebraicGeometry.Artin.ContractionSituation.exists_chartIdeal`). This file
glues them into an ideal sheaf on `S`: the ideal attached to `U` is the intrinsic ideal of
functions vanishing at all good affine points over `U`, which contains `J_U` and, by the Krull
argument `mem_of_forall_isGoodPoint` applied over basic opens, is compatible with restriction to
basic opens — "to find `X` is clearly a local question on `S`".
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An affine open of `S` lies in the site. -/
theorem contains_spec_affineOpen (hS : B.Contains S) (U : S.affineOpens) :
    B.Contains (Spec Γ(S, U)) :=
  B.contains_of_isOpenImmersion (Stacks.RelativeProj.isAffineOpen U).fromSpec hS

/-- The affine open `U` of `S` as a chart `Spec Γ(S, U)` of the site over `S`. -/
noncomputable abbrev chartOf (U : S.affineOpens) : BigFppfOver B S hS :=
  FormalSpace.affineOver B S hS (contains_spec_affineOpen hS U)
    (Stacks.RelativeProj.isAffineOpen U).fromSpec

/-- The intrinsic ideal attached to an affine open `U`: the functions on `U` vanishing at every
good affine point over `U`. -/
noncomputable def intrinsicIdeal (c : ContractionSituation B S hS)
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (U : S.affineOpens) : Ideal Γ(S, U) :=
  ⨅ (V : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (v : V ⟶ chartOf (hS := hS) U) (_ : c.IsGoodPoint Z V), RingHom.ker (FormalSpace.chartRing v)

/-- A function on `U` lies in the intrinsic ideal if and only if it vanishes at every good
affine point over `U`. -/
theorem mem_intrinsicIdeal_iff (c : ContractionSituation B S hS)
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (U : S.affineOpens) (a : Γ(S, U)) :
    a ∈ c.intrinsicIdeal Z U ↔ ∀ (V : BigFppfOver B S hS)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (v : V ⟶ chartOf (hS := hS) U),
        c.IsGoodPoint Z V → FormalSpace.chartRing v a = 0 := by
  simp only [intrinsicIdeal, Submodule.mem_iInf, RingHom.mem_ker]

/-- The morphism of charts attached to a basic open `D(f) ⊆ U`: the spectrum of the restriction
map `Γ(S, U) → Γ(S, D(f))`. -/
noncomputable def chartRestrict (U : S.affineOpens) (f : Γ(S, U)) :
    chartOf (hS := hS) (S.affineBasicOpen f) ⟶ chartOf (hS := hS) U :=
  Over.homMk (ObjectProperty.homMk (Spec.map (S.presheaf.map (homOfLE (S.basicOpen_le f)).op)))
    (by
      apply ObjectProperty.hom_ext
      exact (Stacks.RelativeProj.isAffineOpen U).map_fromSpec
        (Stacks.RelativeProj.isAffineOpen (S.affineBasicOpen f)) (homOfLE (S.basicOpen_le f)).op)

/-- The ring map of a point composed with `chartRestrict U f` is the ring map of the point
precomposed with the restriction `Γ(S, U) → Γ(S, D(f))`. -/
theorem chartRing_comp_chartRestrict (U : S.affineOpens) (f : Γ(S, U)) {V : BigFppfOver B S hS}
    (v : V ⟶ chartOf (hS := hS) (S.affineBasicOpen f)) (a : Γ(S, U)) :
    FormalSpace.chartRing (v ≫ chartRestrict U f) a =
      FormalSpace.chartRing v ((S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom a) := by
  have key := (congrArg (fun g => g.hom a)
    (Scheme.ΓSpecIso_inv_naturality (S.presheaf.map (homOfLE (S.basicOpen_le f)).op))).symm
  change ((BigFppfOver.toScheme B S hS).map v).appTop
    ((Spec.map (S.presheaf.map (homOfLE (S.basicOpen_le f)).op)).appTop
      ((Scheme.ΓSpecIso Γ(S, U)).inv a)) = _
  rw [show (Spec.map (S.presheaf.map (homOfLE (S.basicOpen_le f)).op)).appTop
      ((Scheme.ΓSpecIso Γ(S, U)).inv a) = _ from key]
  rfl

/-- An affine point of a chart all of whose scheme points lie in `V(I)` kills a power of `I`. -/
theorem exists_pow_le_ker_of_mem_zeroLocus {A : Type u} [CommRing A] [IsNoetherianRing A]
    {hA : B.Contains (Spec (.of A))} {f : Spec (.of A) ⟶ S} (I : Ideal A)
    {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (v : V ⟶ FormalSpace.affineOver B S hS hA f)
    (hpts : ∀ y, (BigFppfOver.toScheme B S hS).map v y ∈ PrimeSpectrum.zeroLocus (I : Set A)) :
    ∃ n : ℕ, I ^ (n + 1) ≤ RingHom.ker (FormalSpace.chartRing v) := by
  have e : ∀ y, (BigFppfOver.toScheme B S hS).map v y =
      PrimeSpectrum.comap (FormalSpace.chartRing v)
        (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ y) := by
    intro y
    rw [← FormalSpace.toSpecΓ_comp_spec_chartRing v]
    rfl
  have hnil : I.map (FormalSpace.chartRing v) ≤ (⊥ : Ideal _).radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hn : IsNilpotent (FormalSpace.chartRing v a) := by
      rw [nilpotent_iff_mem_prime]
      intro P hP
      obtain ⟨y, hy⟩ := ((BigFppfOver.toScheme B S hS).obj V).toSpecΓ.homeomorph.surjective ⟨P, hP⟩
      have := hpts y
      rw [e, show ((BigFppfOver.toScheme B S hS).obj V).toSpecΓ y = ⟨P, hP⟩ from hy] at this
      exact this ha
    exact hn.imp fun _ => (Submodule.mem_bot _).2
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hnil (I.fg_of_isNoetherianRing.map _)
  refine ⟨N, (Ideal.pow_le_pow_right (Nat.le_succ N)).trans ((Ideal.map_eq_bot_iff_le_ker _).1 ?_)⟩
  rw [Ideal.map_pow]
  exact le_bot_iff.1 hN

/-- The hypotheses of Stacks 0GHE on a situation `c`: `X' → S` proper, a closed `Z ⊆ |S|` with
inverse image `T'`, and closed immersions `U' → S ∖ Z` and `W → S_{/Z}`. -/
structure ClosedImmersionData (c : ContractionSituation B S hS) where
  /-- The morphism `X' → S` is proper. -/
  hproper : Space.IsProper B S hS (terminal.from c.X')
  /-- The closed subset `Z ⊆ |S|`. -/
  Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))
  /-- The subset `Z` is closed. -/
  hZ : IsClosed Z
  /-- The inverse image of `Z` in `|X'|` is `T'`. -/
  hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T'
  /-- The morphism `U' → S ∖ Z`. -/
  u : c.U'.toFunctor ⟶
    (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor
  /-- The morphism `u` is a closed immersion. -/
  hu : Space.IsClosedImmersion B S hS u
  /-- The morphism `W → S_{/Z}` to the completion of `S` along `Z`. -/
  w : c.W ⟶ Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z
  /-- The morphism `w` is a closed immersion. -/
  hw : FormalSpace.IsClosedImmersion B S hS w

namespace ClosedImmersionData

variable {c : ContractionSituation B S hS} (h : ClosedImmersionData c)

variable (c) in
include c in
/-- The ring of sections of `S` over an affine open is Noetherian. -/
theorem isNoetherianRing_section (U : S.affineOpens) : IsNoetherianRing Γ(S, U) :=
  have := c.isLocallyNoetherian_base
  IsLocallyNoetherian.component_noetherian U

/-- The canonical morphism `Spec Γ(S, U) → S` of an affine open is an open immersion. -/
instance (U : S.affineOpens) : IsOpenImmersion (Stacks.RelativeProj.isAffineOpen U).fromSpec :=
  IsAffineOpen.isOpenImmersion_fromSpec _

/-- There is an ideal of `Γ(S, U)` whose zero locus in the chart of `U` is the inverse image
of `Z`. -/
theorem exists_ideal (U : S.affineOpens) :
    ∃ I : Ideal Γ(S, U), FormalSpace.zeroLocusPoints B S hS (contains_spec_affineOpen hS U)
      (Stacks.RelativeProj.isAffineOpen U).fromSpec I = Space.pointsMap B S hS _
        (terminal.from (yoneda.obj (chartOf (hS := hS) U))) ⁻¹' h.Z :=
  (FormalSpace.exists_zeroLocusPoints_eq_of_isClosed B S hS _ _ _
    (h.hZ.preimage (Space.continuous_pointsMap B S hS _))).imp fun _ hI => hI.symm

/-- An ideal of `Γ(S, U)` whose zero locus in the chart of `U` is the inverse image of `Z`. -/
noncomputable def zIdeal (U : S.affineOpens) : Ideal Γ(S, U) := (h.exists_ideal U).choose

/-- The zero locus of `zIdeal U` in the chart of `U` is the inverse image of `Z`. -/
theorem zIdeal_spec (U : S.affineOpens) :
    FormalSpace.zeroLocusPoints B S hS (contains_spec_affineOpen hS U)
        (Stacks.RelativeProj.isAffineOpen U).fromSpec (h.zIdeal U) =
      Space.pointsMap B S hS _ (terminal.from (yoneda.obj (chartOf (hS := hS) U))) ⁻¹' h.Z :=
  (h.exists_ideal U).choose_spec

/-- The four properties of the ideal of Stacks 0GHE over the chart of `U`. -/
def ChartProps (U : S.affineOpens) (J : Ideal Γ(S, U)) : Prop :=
  (∀ (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (v : V ⟶ chartOf (hS := hS) U),
      J ≤ RingHom.ker (FormalSpace.chartRing v) →
        (h.zIdeal U).map (FormalSpace.chartRing v) = ⊤ →
          Nonempty (c.U'.toFunctor.obj (Opposite.op V))) ∧
  (∀ (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (v : V ⟶ chartOf (hS := hS) U),
      Nonempty (c.U'.toFunctor.obj (Opposite.op V)) →
        J ≤ RingHom.ker (FormalSpace.chartRing v)) ∧
  (∀ (V : BigFppfOver B S hS) (v : V ⟶ chartOf (hS := hS) U) (n : ℕ),
      J ≤ RingHom.ker (FormalSpace.chartRing v) →
        h.zIdeal U ^ (n + 1) ≤ RingHom.ker (FormalSpace.chartRing v) →
          Nonempty (c.W.obj.obj (Opposite.op V))) ∧
  (∀ (V : BigFppfOver B S hS) (v : V ⟶ chartOf (hS := hS) U) (n : ℕ),
      h.zIdeal U ^ (n + 1) ≤ RingHom.ker (FormalSpace.chartRing v) →
        Nonempty (c.W.obj.obj (Opposite.op V)) →
          J ≤ RingHom.ker (FormalSpace.chartRing v))

/-- Some ideal of `Γ(S, U)` satisfies `ChartProps U`. -/
theorem exists_chartProps (U : S.affineOpens) : ∃ J, h.ChartProps U J :=
  have := isNoetherianRing_section c U
  exists_chartIdeal c h.hproper h.Z h.hZ h.hT' h.u h.hu h.w h.hw (h.zIdeal U) (h.zIdeal_spec U)

/-- The ideal `J_U` of the proof of Stacks 0GHE over the affine open `U`. -/
noncomputable def chartIdeal (U : S.affineOpens) : Ideal Γ(S, U) :=
  (h.exists_chartProps U).choose

/-- The ideal `chartIdeal U` satisfies `ChartProps U`. -/
theorem chartIdeal_props (U : S.affineOpens) : h.ChartProps U (h.chartIdeal U) :=
  (h.exists_chartProps U).choose_spec

/-- The structure map of a point of `V` factors through any morphism `v : V ⟶ W` of the site. -/
private theorem pointsMap_terminal_from_yoneda_map {V W : BigFppfOver B S hS} (v : V ⟶ W)
    (p : Space.points B S hS (yoneda.obj V)) :
    Space.pointsMap B S hS _ (terminal.from (yoneda.obj V)) p =
      Space.pointsMap B S hS _ (terminal.from (yoneda.obj W))
        (Space.pointsMap B S hS _ (yoneda.map v) p) := by
  rw [← Function.comp_apply (f := Space.pointsMap B S hS _ _), ← Space.pointsMap_comp,
    terminal.hom_ext (yoneda.map v ≫ _) (terminal.from _)]

/-- A point of the chart of `U` killing a power of `I_U` lies over `Z`. -/
theorem range_subset_of_pow_le (U : S.affineOpens) {V : BigFppfOver B S hS}
    (v : V ⟶ chartOf (hS := hS) U) (n : ℕ)
    (hv : h.zIdeal U ^ (n + 1) ≤ RingHom.ker (FormalSpace.chartRing v)) :
    Set.range (Space.pointsMap B S hS (yoneda.obj V) (terminal.from (yoneda.obj V))) ⊆ h.Z := by
  have := isNoetherianRing_section c U
  have hvI := (Space.hasImageIn_iff_range_subset B S hS
    (X := yoneda.obj (chartOf (hS := hS) U)) _ V (v : (yoneda.obj _).obj (Opposite.op V))).1
    (hasImageIn_zeroLocusPoints_of_pow (h.zIdeal U) v n fun a ha => RingHom.mem_ker.1 (hv ha))
  rintro _ ⟨p, rfl⟩
  rw [pointsMap_terminal_from_yoneda_map v]
  have := hvI ⟨p, rfl⟩
  rwa [h.zIdeal_spec U] at this

/-- An affine point of the chart of `U` lying over `Z` kills a power of `I_U`. -/
theorem exists_pow_le_of_range_subset (U : S.affineOpens) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (v : V ⟶ chartOf (hS := hS) U)
    (hV : Set.range (Space.pointsMap B S hS (yoneda.obj V) (terminal.from (yoneda.obj V))) ⊆
      h.Z) :
    ∃ n : ℕ, h.zIdeal U ^ (n + 1) ≤ RingHom.ker (FormalSpace.chartRing v) := by
  have := isNoetherianRing_section c U
  refine exists_pow_le_ker_of_mem_zeroLocus (h.zIdeal U) v fun y => ?_
  obtain ⟨p, rfl⟩ := Space.surjective_pointsToScheme B S hS V y
  rw [← Space.pointsToScheme_pointsMap_yoneda, ← FormalSpace.mem_zeroLocusPoints_iff,
    h.zIdeal_spec U]
  change Space.pointsMap B S hS _ _ (Space.pointsMap B S hS _ (yoneda.map v) p) ∈ h.Z
  rw [← pointsMap_terminal_from_yoneda_map v]
  exact hV ⟨p, rfl⟩

/-- `J_U` vanishes at every good affine point over `U`. -/
theorem chartIdeal_le_intrinsicIdeal (U : S.affineOpens) :
    h.chartIdeal U ≤ c.intrinsicIdeal h.Z U := by
  intro a ha
  rw [mem_intrinsicIdeal_iff]
  intro V _ v hgood
  obtain ⟨-, h2, -, h4⟩ := h.chartIdeal_props U
  rcases hgood with hU' | ⟨hW, hZ⟩
  · exact RingHom.mem_ker.1 (h2 V v hU' ha)
  · obtain ⟨n, hn⟩ := h.exists_pow_le_of_range_subset U v hZ
    exact RingHom.mem_ker.1 (h4 V v n hn hW ha)

/-- **Compatibility with basic opens.** The intrinsic ideal of `D(f) ⊆ U` is the extension of
that of `U`: one inclusion restricts good points, the other is the Krull argument over the
chart of `D(f)` for the ideals `J_U Γ(D(f))` and `I_U Γ(D(f))`. -/
theorem map_intrinsicIdeal (U : S.affineOpens) (f : Γ(S, U)) :
    (c.intrinsicIdeal h.Z U).map (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom =
      c.intrinsicIdeal h.Z (S.affineBasicOpen f) := by
  have := isNoetherianRing_section c U
  have : IsNoetherianRing Γ(S, S.basicOpen f) := isNoetherianRing_section c (S.affineBasicOpen f)
  let res := (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom
  have hcomp : ∀ {V : BigFppfOver B S hS} (v : V ⟶ chartOf (hS := hS) (S.affineBasicOpen f)),
      (FormalSpace.chartRing (v ≫ chartRestrict U f)) =
        (FormalSpace.chartRing v).comp res := fun v =>
    RingHom.ext fun a => chartRing_comp_chartRestrict U f v a
  have hmapc : ∀ {V : BigFppfOver B S hS}
      (v : V ⟶ chartOf (hS := hS) (S.affineBasicOpen f)) (K : Ideal Γ(S, U)),
      K.map (FormalSpace.chartRing (v ≫ chartRestrict U f)) =
        (K.map res).map (FormalSpace.chartRing v) := fun v K =>
    (congrArg (fun φ => K.map φ) (hcomp v)).trans (Ideal.map_map _ _).symm
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    change res a ∈ c.intrinsicIdeal h.Z (S.affineBasicOpen f)
    refine (mem_intrinsicIdeal_iff c h.Z _ _).2 ?_
    intro V _ v hgood
    rw [← chartRing_comp_chartRestrict]
    exact (mem_intrinsicIdeal_iff c h.Z U a).1 ha V (v ≫ chartRestrict U f) hgood
  · intro x hx
    obtain ⟨h1, -, h3, -⟩ := h.chartIdeal_props U
    have hker : ∀ {V : BigFppfOver B S hS}
        (v : V ⟶ chartOf (hS := hS) (S.affineBasicOpen f)) (K : Ideal Γ(S, U)),
        K.map res ≤ RingHom.ker (FormalSpace.chartRing v) →
          K ≤ RingHom.ker (FormalSpace.chartRing (v ≫ chartRestrict U f)) := by
      intro V v K hK a ha
      rw [hcomp]
      exact hK (Ideal.mem_map_of_mem _ ha)
    have hmem := mem_of_forall_isGoodPoint c h.Z ((h.zIdeal U).map res) ((h.chartIdeal U).map res)
      (fun V v n hv => h.range_subset_of_pow_le U (v ≫ chartRestrict U f) n
        (hker v _ (by rwa [Ideal.map_pow])))
      (fun V _ v hJ hI => h1 V (v ≫ chartRestrict U f) (hker v _ hJ)
        ((hmapc v _).trans hI))
      (fun V v n hJ hI => h3 V (v ≫ chartRestrict U f) n (hker v _ hJ)
        (hker v _ (by rwa [Ideal.map_pow])))
      x ((mem_intrinsicIdeal_iff c h.Z (S.affineBasicOpen f) x).1 hx)
    exact Ideal.map_mono (h.chartIdeal_le_intrinsicIdeal U) hmem

/-- **The ideal sheaf of Stacks 0GHE.** -/
noncomputable def idealSheaf : S.IdealSheafData where
  ideal U := c.intrinsicIdeal h.Z U
  map_ideal_basicOpen U f := h.map_intrinsicIdeal U f

end ClosedImmersionData

end AlgebraicGeometry.Artin.ContractionSituation
