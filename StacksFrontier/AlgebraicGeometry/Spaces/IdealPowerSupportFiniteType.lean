module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSectionsConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosedImageGenericLength

/-!
# A power of a finite type ideal annihilating a finite type module supported on its zero locus

Let `X` be a quasi-compact algebraic space over a scheme `S`, let `ℐ ⊆ 𝒪_X` be a finite type
quasi-coherent sheaf of ideals and let `ℱ` be a finite type quasi-coherent `𝒪_X`-module which has
no sections over the étale charts on which `ℐ` is the whole structure sheaf.  Then `ℐⁿ ℱ = 0` for
some `n`.

This is the substantial half of Stacks 07UK with the Noetherian hypothesis replaced by finiteness
of `ℐ` and of `ℱ`: over a surjective affine chart `U` the sections `ℱ(U)` form a finite module and
the ideal `ℐ(U)` is finitely generated, and these are the only two inputs of the Noetherian
argument of `AlgebraicGeometry.Space.exists_pow_sectionIdeal_smul_top_eq_bot` that used
Noetherianity.  The globalisation from one surjective affine chart to every chart is
`AlgebraicGeometry.Space.sectionIdeal_pow_smul_top_eq_bot_of_surjective_affine_chart`, which
needs only quasi-coherence.

## Main results

* `AlgebraicGeometry.Space.exists_pow_smul_eq_zero_of_subsingleton_sections_basicOpen_of_finite`:
  over an affine chart with finite module of sections, a function killing the sections over its
  nonvanishing locus has a power killing the sections over the chart.
* `AlgebraicGeometry.Space.exists_pow_sectionIdeal_smul_top_eq_bot_of_isFiniteTypeOnSite`: the
  local step.
* `AlgebraicGeometry.Space.exists_idealPowSmul_eq_bot_of_isFiniteTypeOnSite`: the global
  statement.

## References

* [Stacks Project, Tag 07UK](https://stacks.math.columbia.edu/tag/07UK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **A regular function on an affine étale chart over which the sections of a quasi-coherent
module form a finite module, and which kills the sections over its own nonvanishing locus, has a
power annihilating the sections over the chart.**  This is
`AlgebraicGeometry.Space.exists_pow_smul_eq_zero_of_subsingleton_sections_basicOpen` with the
finiteness of the sections as the hypothesis, in place of coherence on a Noetherian chart. -/
theorem exists_pow_smul_eq_zero_of_subsingleton_sections_basicOpen_of_finite
    (M : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    {U : SmallEtale B S hS F} (hUaff : IsAffine (chartScheme U))
    (hfin : Module.Finite (chartRing B S hS F hF U) (M.val.obj (op U)))
    (f : chartRing B S hS F hF U)
    (hsub : Subsingleton
      (M.val.obj (op (openChart B S hS F U ((chartScheme U).basicOpen f))))) :
    ∃ k : ℕ, ∀ x : M.val.obj (op U), f ^ k • x = 0 := by
  have hVaff : IsAffine
      (chartScheme (openChart B S hS F U ((chartScheme U).basicOpen f))) :=
    (isAffineOpen_top (chartScheme U)).basicOpen f
  let _ := chartAlgebra (hF := hF)
    (openChartInclusion B S hS F U ((chartScheme U).basicOpen f))
  have hbij := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M
    hM U (openChart B S hS F U ((chartScheme U).basicOpen f))
    hUaff hVaff (openChartInclusion B S hS F U ((chartScheme U).basicOpen f))
  have hA' := isLocalization_away_chartRing_basicOpen (hF := hF) hUaff f
  have hsubT : Subsingleton (chartRing B S hS F hF
      (openChart B S hS F U ((chartScheme U).basicOpen f)) ⊗[chartRing B S hS F hF U]
        M.val.obj (op U)) := ⟨fun a b => hbij.1 (hsub.allEq _ _)⟩
  -- a finite module whose localization away from `f` vanishes is killed by a power of `f`
  have hmono : ∀ (y : M.val.obj (op U)) (j m : ℕ), f ^ j • y = 0 → j ≤ m → f ^ m • y = 0 := by
    intro y j m hj hjm
    rw [← Nat.sub_add_cancel hjm, pow_add, mul_smul, hj, smul_zero]
  have hzero : ∀ y : M.val.obj (op U), ∃ k : ℕ, f ^ k • y = 0 := by
    intro y
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
      (TensorProduct.mk (chartRing B S hS F hF U)
        (chartRing B S hS F hF (openChart B S hS F U ((chartScheme U).basicOpen f)))
        (M.val.obj (op U)) 1)).1 (hsubT.allEq _ _)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
    exact ⟨k, by rw [hk]; exact hs⟩
  classical
  obtain ⟨r, x, hx⟩ := Module.Finite.exists_fin (R := chartRing B S hS F hF U)
    (M := M.val.obj (op U))
  choose k hk using fun i : Fin r => hzero (x i)
  refine ⟨Finset.univ.sup k, fun y => ?_⟩
  have hy : y ∈ Submodule.span (chartRing B S hS F hF U) (Set.range x) := by
    rw [hx]; exact Submodule.mem_top
  refine Submodule.span_induction (fun z hz => ?_) (smul_zero _) (fun a b _ _ ha hb => ?_)
    (fun c a _ ha => ?_) hy
  · obtain ⟨i, rfl⟩ := hz
    exact hmono (x i) (k i) _ (hk i) (Finset.le_sup (Finset.mem_univ i))
  · rw [smul_add, ha, hb, add_zero]
  · rw [smul_comm, ha, smul_zero]

variable (B S hS F hF)

/-- A quasi-coherent module of finite type has finite sections over an affine étale chart. -/
private theorem module_finite_sections_of_isFiniteTypeOnSite_of_isQuasicoherentOnSite
    (M : Modules.{u, u} B S hS F hF) (hMq : M.IsQuasicoherentOnSite)
    (hMft : SheafOfModules.IsFiniteTypeOnSite M) (U : SmallEtale B S hS F)
    (hUaff : IsAffine (chartScheme U)) :
    Module.Finite (chartRing B S hS F hF U) (M.val.obj (op U)) :=
  module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite M
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M hMq) hMft U hUaff

/-- **Stacks 07UK, the local step, for finite type data.**  Let `M` be a quasi-coherent
`𝒪_F`-module of finite type and let `I ⊆ 𝒪_F` be a quasi-coherent sheaf of ideals of finite type
which is the unit ideal only over charts carrying no sections of `M`.  Over an affine étale chart
`U` some power of the ideal `I(U)` annihilates the sections `M(U)`.

Both `M(U)` and `I(U)` are finite over the ring of the chart, by
`module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite`. -/
theorem exists_pow_sectionIdeal_smul_top_eq_bot_of_isFiniteTypeOnSite
    (M : Modules.{u, u} B S hS F hF) (hMq : M.IsQuasicoherentOnSite)
    (hMft : SheafOfModules.IsFiniteTypeOnSite M)
    (I : (_root_.SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hIft : SheafOfModules.IsFiniteTypeOnSite I.toSheafOfModules)
    (U : SmallEtale B S hS F) (hUaff : IsAffine (chartScheme U))
    (h : ∀ V : SmallEtale B S hS F, I.obj (op V) = ⊤ → Subsingleton (M.val.obj (op V))) :
    ∃ n : ℕ, chartSectionIdeal B S hS F hF I U ^ n •
      (⊤ : Submodule (chartRing B S hS F hF U) (M.val.obj (op U))) = ⊥ := by
  have hfin := module_finite_sections_of_isFiniteTypeOnSite_of_isQuasicoherentOnSite
    B S hS F hF M hMq hMft U hUaff
  have hIfin := module_finite_sections_of_isFiniteTypeOnSite_of_isQuasicoherentOnSite
    B S hS F hF _ hIq hIft U hUaff
  have hIfg : (chartSectionIdeal B S hS F hF I U).FG :=
    (Module.Finite.iff_fg (N := chartSectionIdeal B S hS F hF I U)).1 hIfin
  have hrad : chartSectionIdeal B S hS F hF I U ≤
      (Module.annihilator (chartRing B S hS F hF U) (M.val.obj (op U))).radical := by
    intro f hf
    let _ := chartAlgebra (hF := hF)
      (openChartInclusion B S hS F U ((chartScheme U).basicOpen f))
    have := isLocalization_away_chartRing_basicOpen (hF := hF) hUaff f
    have hunit : IsUnit (chartRestrict (hF := hF)
        (openChartInclusion B S hS F U ((chartScheme U).basicOpen f)) f) :=
      IsLocalization.map_units (M := Submonoid.powers f)
        (chartRing B S hS F hF (openChart B S hS F U ((chartScheme U).basicOpen f)))
        ⟨f, Submonoid.mem_powers f⟩
    have hmem : chartRestrict (hF := hF)
        (openChartInclusion B S hS F U ((chartScheme U).basicOpen f)) f ∈
        chartSectionIdeal B S hS F hF I
          (openChart B S hS F U ((chartScheme U).basicOpen f)) :=
      Stacks.Sites.map_mem_sectionIdeal I
        (openChartInclusion B S hS F U ((chartScheme U).basicOpen f)).op hf
    have htop : I.obj (op (openChart B S hS F U ((chartScheme U).basicOpen f))) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ hmem hunit
    obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_subsingleton_sections_basicOpen_of_finite M hMq
      hUaff hfin f (h _ htop)
    exact Ideal.mem_radical_iff.2 ⟨k, Module.mem_annihilator.2 hk⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hIfg
  refine ⟨n, ?_⟩
  rwa [← Submodule.annihilator_top, Submodule.le_annihilator_iff] at hn

/-- **A quasi-compact algebraic space has a surjective affine étale chart**, surjective both as a
relatively representable morphism and on points. -/
theorem exists_surjective_affineChart_of_isQuasiCompactSpace
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1) :
    ∃ U : SmallEtale B S hS X.1,
      IsAffine (chartScheme U) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf U.1.hom ∧
          Function.Surjective (pointsMap B S hS
            (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom) := by
  obtain ⟨U₀, f, hAff, hSurj, hEt⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hqc
  have hEt' : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
    presheaf_etale_of_isEtale B S hS hEt
  exact ⟨⟨CostructuredArrow.mk f, hEt'⟩, hAff, hSurj,
    (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U₀ f).1 hSurj⟩

/-- **The substantial half of Stacks 07UK for a finite type module and a finite type ideal on a
quasi-compact algebraic space.**  If a quasi-coherent module `M` of finite type has no sections
over the charts on which the quasi-coherent sheaf of ideals `ℐ` of finite type is the unit ideal,
then `ℐⁿ M = 0` for some `n`.  No Noetherian hypothesis is needed. -/
theorem exists_idealPowSmul_eq_bot_of_isFiniteTypeOnSite (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (M : Modules.{u, u} B S hS X.1 X.2) (hMq : M.IsQuasicoherentOnSite)
    (hMft : SheafOfModules.IsFiniteTypeOnSite M)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : IsFiniteTypeQuasicoherentIdeal B S hS X I)
    (h : ∀ V : SmallEtale B S hS X.1, I.obj (op V) = ⊤ → Subsingleton (M.val.obj (op V))) :
    ∃ n : ℕ, Stacks.Sites.idealSmul (M := M)
        (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O) I n) ⊤ = ⊥ := by
  obtain ⟨U, hU, -, hUsurj⟩ := exists_surjective_affineChart_of_isQuasiCompactSpace B S hS X hqc
  obtain ⟨n, hn⟩ := exists_pow_sectionIdeal_smul_top_eq_bot_of_isFiniteTypeOnSite B S hS X.1 X.2
    M hMq hMft I hI.1 hI.2 U hU h
  exact ⟨n, (idealSmul_idealPow_top_eq_bot_iff B S hS X.1 X.2 I M n).2
    (sectionIdeal_pow_smul_top_eq_bot_of_surjective_affine_chart B S hS X.1 X.2 M
      hMq I hI.1 U hU hUsurj n hn)⟩

/-- **A finite type quasi-coherent module on an algebraic space with a terminal affine étale chart
is jointly hit by finitely many maps out of the structure sheaf.**  This is
`exists_unit_homs_of_isTerminal_of_isCoherent` with finite type in place of coherence: the
sections over the affine chart are finite by
`module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite`. -/
theorem exists_unit_homs_of_isTerminal_of_isFiniteTypeOnSite (U : AlgebraicSpaces B S hS)
    {T : SmallEtale B S hS U.1} (hT : IsTerminal T) (hTa : IsAffine (chartScheme T))
    (M : Modules.{u, u} B S hS U.1 U.2) (hMq : M.IsQuasicoherentOnSite)
    (hMft : SheafOfModules.IsFiniteTypeOnSite M) :
    ∃ (n : ℕ) (θ : Fin n → (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O) ⟶ M)),
      ∀ ⦃Z : Modules.{u, u} B S hS U.1 U.2⦄ (d : M ⟶ Z), (∀ i, θ i ≫ d = 0) → d = 0 := by
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS U.1 U.2 M hMq
  obtain ⟨n, s, hs⟩ := generates_of_module_finite_sections M hcart hTa
    (module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite M hcart hMft T hTa)
  obtain ⟨θ, hθ⟩ := Stacks.SheafOfModules.exists_unit_homs_of_generates hT s hs
  exact ⟨n, θ, hθ⟩

attribute [local instance] pointTopology in
/-- **A finite type quasi-coherent module vanishing on `X ∖ V(ℐ)` is killed by a power of `ℐ`**,
section by section, on a quasi-compact algebraic space and for a finite type quasi-coherent sheaf
of ideals `ℐ`.  This is the non-Noetherian form of the consequence of Stacks 07UK used in the
proof of Stacks 0GUZ: the support of the module misses the open complement, where its restriction
vanishes, so it has no sections over a chart on which `ℐ` is the unit ideal
(`AlgebraicGeometry.Space.subsingleton_sections_of_supportOfSheaf_subset_idealZeroLocus`), and
`AlgebraicGeometry.Space.exists_idealPowSmul_eq_bot_of_isFiniteTypeOnSite` applies. -/
theorem exists_smul_eq_zero_of_isZero_restrictToIdealComplement (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : IsFiniteTypeQuasicoherentIdeal B S hS X I)
    (M : Modules.{u, u} B S hS X.1 X.2) (hMq : M.IsQuasicoherentOnSite)
    (hMft : SheafOfModules.IsFiniteTypeOnSite M)
    (hz : IsZero ((restrictToIdealComplement B S hS X I).obj M)) :
    ∃ n : ℕ, ∀ (W : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ)
      (a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj W),
      a ∈ (SheafOfModules.idealSheafPow I n).obj W → ∀ q : M.val.obj W, a • q = 0 := by
  have hι := isEtale_idealComplementι B S hS X I
  have hz' : IsZero ((etaleModulePullback B S hS (idealComplementι B S hS X I) hι).obj M) := hz
  have hsupp : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ⊆
      idealZeroLocus B S hS X I := by
    intro y hy hyU
    rw [← range_pointsMap_idealComplementι B S hS X I] at hyU
    obtain ⟨u, rfl⟩ := hyU
    have hpre := supportOfSheaf_modulePullback_eq_preimage_of_isFlat B S hS
      (idealComplementι B S hS X I) (isFlat_of_isEtale B S hS hι) M
    have hu := (Set.ext_iff.1 hpre u).2 hy
    rw [supportOfSheaf_eq_of_iso B S hS _
      ((modulePullbackIsoEtaleModulePullback B S hS (idealComplementι B S hS X I) hι).app _),
      supportOfSheaf_eq_empty_of_isZero B S hS _ hz'] at hu
    exact hu
  obtain ⟨n, hn⟩ := exists_idealPowSmul_eq_bot_of_isFiniteTypeOnSite B S hS X hqc M hMq hMft I hI
    fun V hV => subsingleton_sections_of_supportOfSheaf_subset_idealZeroLocus B S hS X M I hsupp V
      hV
  exact ⟨n, smul_eq_zero_of_idealSmul_idealPow_top_eq_bot B S hS X I n M hn⟩

end AlgebraicGeometry.Space

end
