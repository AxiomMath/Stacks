module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartFibreCover
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyPolarizedCharts
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange

/-!
# Two-chart data on étale charts of a family of curves: piece (C)

This file proves `AlgebraicGeometry.C1590Private.hasTwoChartEtaleCovers`: every point `s` of the
affine Noetherian base of a family of curves is in the image of an étale chart from an affine
scheme over which the family is a scheme carrying a good two-chart datum.

## The argument

Step C of the 0D53 route (`AlgebraicGeometry.C1590Private.hasPolarizedChartAt`) gives an étale
chart `T' ⟶ S` through `s`, over which the family is a scheme `Z` with an invertible module `L`
ample relative to `Z ⟶ T'`. Restricting the chart to an affine open `W₀ ∋ u` of `T'` makes `L`
ample (`Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`), and the fibre at `u` has
dimension at most one, the family being one of curves. Then
`AlgebraicGeometry.C1590Private.exists_sections_cover_near_fibre` gives two sections `σ`, `τ` of a
power of `L` with affine nonvanishing loci covering `q⁻¹ D(f)` for a basic open `D(f) ∋ u`.
Restricting the chart once more, to `D(f)`, and pulling `L`, `σ`, `τ` back, the nonvanishing loci
are affine and cover the new total space, and
`AlgebraicGeometry.C1590Private.exists_isGood_twoChartDatum` gives the good datum.

## Main results

* `AlgebraicGeometry.C1590Private.exists_powSections_pullback`: a section of a power of an
  invertible module pulls back, with nonvanishing locus the preimage.
* `AlgebraicGeometry.C1590Private.exists_restrict_chart`: a scheme chart of a family restricts to
  an open of its base.
* `AlgebraicGeometry.C1590Private.hasTwoChartEtaleCovers`: (C).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.TensorPowerTrivialize Stacks.GradedSections

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Pulling back sections of powers -/

/-- **A section of a power of an invertible module pulls back**, along any morphism of schemes,
to a section of the same power of the pulled back module, with nonvanishing locus the preimage
(Stacks 0H78). -/
theorem exists_powSections_pullback {Y Z : Scheme.{u}} (i : Y ⟶ Z) (L : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z L] {n : ℕ} (σ : powSections L n) :
    ∃ σ' : powSections (Stacks.AmpleLocallyClosed.pullbackModule i L) n,
      Stacks.AmpleFiniteAvoidance.nvOpen _ σ' = i ⁻¹ᵁ Stacks.AmpleFiniteAvoidance.nvOpen L σ := by
  set L' := Stacks.AmpleLocallyClosed.pullbackModule i L
  have hF : Stacks.TensorPowers.natTensorPow L n = Stacks.Ample.tensorPowModule Z L (n : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow _ L n
  have hF' : Stacks.TensorPowers.natTensorPow L' n = Stacks.Ample.tensorPowModule Y L' (n : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow _ L' n
  let e : Stacks.AmpleLocallyClosed.pullbackModule i (Stacks.Ample.tensorPowModule Z L (n : ℤ)) ≅
      Stacks.Ample.tensorPowModule Y L' (n : ℤ) :=
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso i L n
  let s := (eqToIso hF).hom.app ⊤ (Stacks.SectionProduct.globalSection Z _ σ)
  let s' : Γ(Stacks.AmpleLocallyClosed.pullbackModule i (Stacks.Ample.tensorPowModule Z L (n : ℤ)),
      ⊤) := pullbackGlobalSections i _ s
  let s'' := e.hom.app ⊤ s'
  let s''' := (eqToIso hF').inv.app ⊤ s''
  have h1 : Stacks.Ample.nonvanishingLocus _ s''' = Stacks.Ample.nonvanishingLocus _ s'' :=
    Stacks.Ample.nonvanishingLocus_congr (eqToIso hF').symm s''
  have h2 : Stacks.Ample.nonvanishingLocus _ s'' = Stacks.Ample.nonvanishingLocus _ s' :=
    Stacks.Ample.nonvanishingLocus_congr e s'
  have h3 : Stacks.Ample.nonvanishingLocus _ s' =
      i.base ⁻¹' Stacks.Ample.nonvanishingLocus _ s :=
    (Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections i _ s).symm
  have h4 : Stacks.Ample.nonvanishingLocus _ s =
      Stacks.Ample.nonvanishingLocus _ (Stacks.SectionProduct.globalSection Z _ σ) :=
    Stacks.Ample.nonvanishingLocus_congr (eqToIso hF) _
  refine ⟨(Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm s''', ?_⟩
  refine Opens.ext ?_
  change Stacks.Ample.nonvanishingLocus _
      (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm s''')) =
    i.base ⁻¹' Stacks.Ample.nonvanishingLocus _ (Stacks.SectionProduct.globalSection Z _ σ)
  rw [AddEquiv.apply_symm_apply, h1, h2, h3, h4]

/-! ### Restricting a scheme chart to an open of its base -/

section Charts

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **A scheme chart of a family of curves restricts to an open of its base.** For a chart
`φ : T' ⟶ S` over which the family is the scheme `q : Z ⟶ T'`, and an open `W` of `T'`, the open
subscheme `W` is an object of the site with an open immersion `π` onto `W`, over which the
family is the scheme `Z ×_{T'} W`. -/
theorem exists_restrict_chart (X : CurveFamily B hZ) {T' Z : BigFppfOver B integerBase hZ}
    (φ : T' ⟶ X.base) (q : Z ⟶ T') (p : schemeSpace Z ⟶ X.total)
    (hpb : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap φ))
    (W : ((BigFppfOver.toScheme B integerBase hZ).obj T').Opens) :
    ∃ (T'' Z'' : BigFppfOver B integerBase hZ) (π : T'' ⟶ T') (q'' : Z'' ⟶ T'') (g : Z'' ⟶ Z)
      (p'' : schemeSpace Z'' ⟶ X.total),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
      Set.range ((BigFppfOver.toScheme B integerBase hZ).map π) = W ∧
      (IsAffineOpen W → IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj T'')) ∧
      IsPullback p'' (schemeSpaceMap q'') X.toBase (schemeSpaceMap (π ≫ φ)) ∧
      IsPullback ((BigFppfOver.toScheme B integerBase hZ).map g)
        ((BigFppfOver.toScheme B integerBase hZ).map q'')
        ((BigFppfOver.toScheme B integerBase hZ).map q)
        ((BigFppfOver.toScheme B integerBase hZ).map π) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  let T'' : BigFppfOver B integerBase hZ :=
    Over.mk (⟨W.ι ≫ T'.hom.hom⟩ :
      B.obj (Scheme.size_lt_of_isOpenImmersion W.ι T'.left.property) ⟶ B.obj hZ)
  let π : T'' ⟶ T' := Over.homMk ⟨W.ι⟩ rfl
  have hsite := IsPullback.of_hasPullback q π
  have hsq : IsPullback (schemeSpaceMap (pullback.fst q π) ≫ p)
      (schemeSpaceMap (pullback.snd q π)) X.toBase (schemeSpaceMap (π ≫ φ)) := by
    rw [schemeSpaceMap_comp]
    exact (isPullback_schemeSpaceMap hsite).paste_horiz hpb
  refine ⟨T'', pullback q π, π, pullback.snd q π, pullback.fst q π, _,
    inferInstanceAs (IsOpenImmersion W.ι), Scheme.Opens.range_ι W, fun hW => hW, hsq,
    hsite.map T⟩

end Charts

/-! ### (C) -/

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **(C): two-chart data on étale charts.** -/
theorem hasTwoChartEtaleCovers : HasTwoChartEtaleCovers B hZ := by
  intro X hSa hSn s
  let T := BigFppfOver.toScheme B integerBase hZ
  obtain ⟨T', φ, het, ⟨u, rfl⟩, Z, p, q, hpb, L, hL, hamp⟩ := hasPolarizedChartAt B hZ X s
  have : IsLocallyNoetherian (T.obj T') := LocallyOfFiniteType.isLocallyNoetherian (T.map φ)
  -- restrict to an affine open around `u`
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, huW₀, -⟩ :=
    (T.obj T').isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ u) isOpen_univ
  obtain ⟨T₁, Z₁, π₁, q₁, g₁, p₁, hπ₁, hrange₁, haff₁, hpb₁, hsq₁⟩ :=
    exists_restrict_chart X φ q p hpb W₀
  have : IsAffine (T.obj T₁) := haff₁ hW₀
  have : Etale (T.map (π₁ ≫ φ)) := by rw [Functor.map_comp]; infer_instance
  have : IsLocallyNoetherian (T.obj T₁) :=
    LocallyOfFiniteType.isLocallyNoetherian (T.map (π₁ ≫ φ))
  have : IsProper (T.map q₁) := X.isProper_toScheme_map_of_isPullback_schemeSpaceMap hpb₁
  have : Flat (T.map q₁) := X.flat_toScheme_map_of_isPullback hpb₁
  obtain ⟨u₁, hu₁⟩ : u ∈ Set.range (T.map π₁) := by rw [hrange₁]; exact huW₀
  let L₁ := Stacks.AmpleLocallyClosed.pullbackModule (T.map g₁) L
  have hamp₁ : Stacks.RelativeAmple.IsRelativelyAmple (T.map q₁) L₁ :=
    Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hsq₁ L hamp
  have hL₁ : Stacks.Ample.IsAmple (T.obj Z₁) L₁ :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (T.map q₁) L₁).1 hamp₁
  have hdim := X.topologicalKrullDim_fiber_toScheme_map_le_of_isPullback hpb₁ inferInstance u₁
  -- two sections covering a neighbourhood of the fibre
  obtain ⟨n, hn, σ, τ, hσ, hτ, f, huf, hcov⟩ :=
    exists_sections_cover_near_fibre L₁ (T.map q₁) hL₁ u₁ hdim
  -- restrict to the basic open `D(f)`
  obtain ⟨T₂, Z₂, π₂, q₂, g₂, p₂, hπ₂, hrange₂, haff₂, hpb₂, hsq₂⟩ :=
    exists_restrict_chart X (π₁ ≫ φ) q₁ p₁ hpb₁ ((T.obj T₁).basicOpen f)
  have : IsAffine (T.obj T₂) := haff₂ ((isAffineOpen_top _).basicOpen f)
  have : Etale (T.map (π₂ ≫ π₁ ≫ φ)) := by rw [Functor.map_comp]; infer_instance
  have : IsLocallyNoetherian (T.obj T₂) :=
    LocallyOfFiniteType.isLocallyNoetherian (T.map (π₂ ≫ π₁ ≫ φ))
  have : IsProper (T.map q₂) := X.isProper_toScheme_map_of_isPullback_schemeSpaceMap hpb₂
  have : Flat (T.map q₂) := X.flat_toScheme_map_of_isPullback hpb₂
  obtain ⟨u₂, hu₂⟩ : u₁ ∈ Set.range (T.map π₂) := by rw [hrange₂]; exact huf
  -- the pulled back module and sections
  have : IsOpenImmersion (T.map g₂) := MorphismProperty.of_isPullback hsq₂.flip hπ₂
  let M := Stacks.AmpleLocallyClosed.pullbackModule (T.map g₂) L₁
  have hM : Stacks.Ample.IsAmple (T.obj Z₂) M :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (T.map q₂) M).1
      (Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hsq₂ L₁ hamp₁)
  obtain ⟨σ', hσ'⟩ := exists_powSections_pullback (T.map g₂) L₁ σ
  obtain ⟨τ', hτ'⟩ := exists_powSections_pullback (T.map g₂) L₁ τ
  have hrangeg : (T.map g₂).opensRange = (T.map q₁) ⁻¹ᵁ (T.obj T₁).basicOpen f := by
    refine Opens.ext (Set.ext fun z => ⟨?_, fun hz => ?_⟩)
    · rintro ⟨y, rfl⟩
      change (T.map g₂ ≫ T.map q₁) y ∈ ((T.obj T₁).basicOpen f : Set (T.obj T₁))
      rw [hsq₂.w, Scheme.Hom.comp_apply, ← hrange₂]
      exact ⟨_, rfl⟩
    · obtain ⟨w, rfl⟩ : z ∈ Set.range (pullback.fst (T.map q₁) (T.map π₂)) := by
        rw [Scheme.Pullback.range_fst, hrange₂]
        exact hz
      refine ⟨hsq₂.isoPullback.inv w, ?_⟩
      rw [← hsq₂.isoPullback_inv_fst, Scheme.Hom.comp_apply]
  have haffine : ∀ {V : (T.obj Z₁).Opens}, IsAffineOpen V → IsAffineOpen ((T.map g₂) ⁻¹ᵁ V) := by
    intro V hV
    rw [← (T.map g₂).isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, hrangeg, Scheme.preimage_basicOpen_top,
      inf_comm, ← Scheme.basicOpen_res _ _ (homOfLE le_top).op]
    exact hV.basicOpen _
  refine ⟨T₂, Z₂, π₂ ≫ π₁ ≫ φ, q₂, p₂, inferInstance, ⟨u₂, ?_⟩, inferInstance, hpb₂, ?_⟩
  · rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hu₂,
      hu₁]
  refine exists_isGood_twoChartDatum (T.map q₂) M hM hn σ' τ' (hσ' ▸ haffine hσ)
    (hτ' ▸ haffine hτ) ?_
  rw [hσ', hτ', ← Scheme.Hom.preimage_sup, eq_top_iff]
  exact fun z _ => hcov (hrangeg.le ⟨z, rfl⟩)

end AlgebraicGeometry.C1590Private
