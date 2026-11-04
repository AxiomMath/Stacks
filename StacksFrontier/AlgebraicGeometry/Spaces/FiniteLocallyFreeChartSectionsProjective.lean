module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSectionsConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerAffineChartSections
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresProd
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback

/-!
# Sections of a finite locally free module over affine étale charts

Let `F` be an algebraic space over a scheme `S` and `G` an `𝒪_F`-module on the small étale site.
This file reads finite local freeness of `G` (Stacks 03DL(2),
`SheafOfModules.IsFiniteLocallyFreeOnSite`) on the sections over affine étale charts, in both
directions and with no rank fixed.

## Main results

* `AlgebraicGeometry.Space.module_finite_projective_sections_of_isFiniteLocallyFreeOnSite`: the
  sections of a finite locally free module over an affine étale chart form a finite projective
  module over the chart ring.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_of_finite_projective_sections`: conversely,
  a module cartesian on affine charts (for instance quasi-coherent) whose sections over every
  affine étale chart are finite projective is finite locally free.
* `Module.Projective.pi_ring`: a finite product of projective modules is projective over the
  product of the coefficient rings.
* `Module.Basis.ofIsLocalizedModuleAway`: transport of a basis of a localization away from an
  element to any module realizing that localization.

## Implementation notes

The first direction is faithfully flat descent of projectivity (Stacks 058S,
`Module.Projective.of_finite_of_isBaseChange_of_faithfullyFlat`) along a finite family of affine
charts refining a trivialising covering: the base change of the sections to the product of their
rings is the product of the sections over the members, by the base change comparison of
Stacks 03DX(2), and that product is projective over the product ring.  The second direction is the
rankless form of `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_freeRankPresieve`: a finite
projective module is free on the basic opens of a family of functions generating the unit ideal
(Stacks 00NX, `Stacks.LocallyFree.FiniteProjective.solution`), the sections over such a basic open
chart are the localization, and over an affine chart with free sections the module is a finite
coproduct of copies of the structure sheaf
(`AlgebraicGeometry.Space.exists_isColimitCofan_of_basis`).

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [Stacks Project, Tag 058S](https://stacks.math.columbia.edu/tag/058S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

/-- A finite product of projective modules over a finite product of rings is projective over
the product ring. -/
theorem Module.Projective.pi_ring {ι : Type*} [Finite ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module (R i) (M i)]
    [∀ i, Module.Projective (R i) (M i)] :
    Module.Projective (∀ i, R i) (∀ i, M i) := by
  classical
  have := Fintype.ofFinite ι
  let : ∀ j, Algebra (∀ i, R i) (R j) := fun j => (Pi.evalRingHom R j).toAlgebra
  let : ∀ j, Module (∀ i, R i) (M j) := fun j => Module.compHom (M j) (Pi.evalRingHom R j)
  have : ∀ j, IsScalarTower (∀ i, R i) (R j) (M j) :=
    fun j => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : ∀ j, Module.Projective (∀ i, R i) (R j) := fun j =>
    Module.Projective.of_split
      ({ toFun := fun x => Pi.single j x
         map_add' := fun x y => by simp [Pi.single_add]
         map_smul' := fun r x => by
           ext k
           by_cases h : k = j
           · subst h; simp; rfl
           · simp [Pi.single_eq_of_ne h] } : R j →ₗ[∀ i, R i] ∀ i, R i)
      ({ toFun := fun r => r j
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } : (∀ i, R i) →ₗ[∀ i, R i] R j)
      (by ext x; exact Pi.single_eq_same j x)
  have : ∀ j, Module.Projective (∀ i, R i) (M j) := fun j => Module.Projective.trans _ (R j) _
  have hsum : Module.Projective (∀ i, R i) (DirectSum ι M) :=
    Module.Projective.directSum_iff.mpr inferInstance
  exact Module.Projective.of_equiv (DirectSum.linearEquivFunOnFintype (∀ i, R i) ι M)

/-- A basis of the localization of `M` away from `r` is a basis of any module realizing that
localization, over any ring realizing the localization of the coefficients. -/
noncomputable def Module.Basis.ofIsLocalizedModuleAway {R : Type*} [CommRing R] {A : Type*}
    [CommRing A] [Algebra R A] {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (r : R) [IsLocalization.Away r A] (f : M →ₗ[R] N) [IsLocalizedModule.Away r f]
    {I : Type*} (b : Module.Basis I (Localization.Away r)
      (LocalizedModule (Submonoid.powers r) M)) :
    Module.Basis I A N :=
  let e := IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) A
  letI : Module (Localization.Away r) N := Module.compHom N e.toRingHom
  haveI : IsScalarTower R (Localization.Away r) N :=
    IsScalarTower.of_algebraMap_smul fun a n => by
      change e (algebraMap R (Localization.Away r) a) • n = a • n
      rw [e.commutes, IsScalarTower.algebraMap_smul]
  let eM := (IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M) f).extendScalarsOfIsLocalization
      (Submonoid.powers r) (Localization.Away r)
  (b.map eM).mapCoeffs e.toRingEquiv fun _ _ => rfl

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

variable (hF) in
/-- **The sections of a finite locally free module over an affine étale chart are a finite
projective module over the chart ring.** -/
theorem module_finite_projective_sections_of_isFiniteLocallyFreeOnSite
    (G : Modules.{u, u} B S hS F hF) (hG : SheafOfModules.IsFiniteLocallyFreeOnSite G)
    (U : SmallEtale B S hS F) (hU : IsAffine (chartScheme U)) :
    Module.Finite (chartRing B S hS F hF U) (G.val.obj (op U)) ∧
      Module.Projective (chartRing B S hS F hF U) (G.val.obj (op U)) := by
  classical
  have := SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hG
  have hc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G inferInstance
  have hfin : Module.Finite (chartRing B S hS F hF U) (G.val.obj (op U)) :=
    module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite G hc
      inferInstance U hU
  refine ⟨hfin, ?_⟩
  obtain ⟨I, V, f, hcov, hfree⟩ := hG U
  obtain ⟨ι, hι, Z, g, hZaff, hR, hff⟩ :=
    SmallEtale.exists_finite_affine_faithfullyFlat_refinement B S hS F hF U hU hcov
  have _ : Fintype ι := Fintype.ofFinite ι
  have hproj : ∀ i, Module.Projective (chartRing B S hS F hF (Z i)) (G.val.obj (op (Z i))) := by
    intro i
    obtain ⟨j, c, -⟩ := (Sieve.mem_ofArrows_iff V f (g i)).1 (hR i)
    obtain ⟨n, κ, ⟨hκ⟩⟩ := (SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).1 (hfree j)
    obtain ⟨b⟩ := RingedSite.nonempty_basis_sections_of_isColimitCofanUnit
      (smallEtaleRingedSite B S hS F hF) G n (V j) κ hκ c
    exact Module.Projective.of_basis b
  let Bi := fun i => chartRing B S hS F hF (Z i)
  let : ∀ i, Algebra (chartRing B S hS F hF U) (Bi i) := fun i => chartAlgebra (hF := hF) (g i)
  let : ∀ i, Module (chartRing B S hS F hF U) (G.val.obj (op (Z i))) := fun i =>
    chartSectionsModule G (g i)
  have : ∀ i, IsScalarTower (chartRing B S hS F hF U) (Bi i) (G.val.obj (op (Z i))) :=
    fun i => chartSections_isScalarTower G (g i)
  have : Module.FaithfullyFlat (chartRing B S hS F hF U) (∀ i, Bi i) :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hff
  let e : ∀ i, Bi i ⊗[chartRing B S hS F hF U] G.val.obj (op U) ≃ₗ[Bi i]
      G.val.obj (op (Z i)) := fun i =>
    LinearEquiv.ofBijective (sectionsBaseChange G (g i)) (hc U (Z i) hU (hZaff i) (g i))
  have hE : ∀ (b' : ∀ i, Bi i) (x : G.val.obj (op U)) (i : ι),
      TensorProduct.piLeft (R := chartRing B S hS F hF U) (M := Bi) (N := G.val.obj (op U))
        (b' ⊗ₜ x) i = b' i ⊗ₜ x := fun b' x i => by
    simp [TensorProduct.piLeft]
  let E : (∀ i, Bi i) ⊗[chartRing B S hS F hF U] G.val.obj (op U) →ₗ[∀ i, Bi i]
      ∀ i, G.val.obj (op (Z i)) :=
    { toFun := fun z i => e i (TensorProduct.piLeft (R := chartRing B S hS F hF U) (M := Bi)
        (N := G.val.obj (op U)) z i)
      map_add' := fun z z' => by funext i; simp
      map_smul' := fun b z => by
        funext i
        show e i (TensorProduct.piLeft (R := chartRing B S hS F hF U) (M := Bi)
            (N := G.val.obj (op U)) (b • z) i) =
          b i • e i (TensorProduct.piLeft (R := chartRing B S hS F hF U) (M := Bi)
            (N := G.val.obj (op U)) z i)
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul b' x =>
          rw [TensorProduct.smul_tmul', hE, hE, show (b • b') i = b i • b' i from rfl,
            ← TensorProduct.smul_tmul', LinearEquiv.map_smul]
        | add z z' hz hz' =>
          rw [smul_add, map_add, Pi.add_apply, map_add, hz, hz', map_add, Pi.add_apply,
            map_add, smul_add] }
  have hEbij : Function.Bijective E := by
    have hfun : (E : _ → _) = (fun y i => e i (y i)) ∘
        TensorProduct.piLeft (R := chartRing B S hS F hF U) (M := Bi) (N := G.val.obj (op U)) :=
      rfl
    rw [hfun]
    refine Function.Bijective.comp ⟨fun y y' hy => funext fun i => (e i).injective
      (congrFun hy i), fun y => ⟨fun i => (e i).symm (y i), funext fun i => by simp⟩⟩
      (LinearEquiv.bijective _)
  have : Module.Projective (∀ i, Bi i) (∀ i, G.val.obj (op (Z i))) := Module.Projective.pi_ring
  have : Module.Projective (∀ i, Bi i)
      ((∀ i, Bi i) ⊗[chartRing B S hS F hF U] G.val.obj (op U)) :=
    Module.Projective.of_equiv (LinearEquiv.ofBijective E hEbij).symm
  exact Module.Projective.of_finite_of_isBaseChange_of_faithfullyFlat
    (TensorProduct.mk (chartRing B S hS F hF U) (∀ i, Bi i) (G.val.obj (op U)) 1)
    (TensorProduct.isBaseChange _ _ _)

variable (hF) in
/-- **A module cartesian on affine charts whose sections over every affine étale chart are finite
projective is finite locally free.**  Over an affine chart the sections become free on the basic
opens of a family of functions generating the unit ideal (Stacks 00NX), the sections over such a
basic-open chart are the corresponding localization, and over an affine chart with free sections
of finite rank the module is a finite coproduct of copies of the structure sheaf
(`AlgebraicGeometry.Space.exists_isColimitCofan_of_basis`). -/
theorem isFiniteLocallyFreeOnSite_of_finite_projective_sections
    (G : Modules.{u, u} B S hS F hF) (hG : IsCartesianOnAffineCharts G)
    (h : ∀ U : SmallEtale B S hS F, IsAffine (chartScheme U) →
      Module.Finite (chartRing B S hS F hF U) (G.val.obj (op U)) ∧
        Module.Projective (chartRing B S hS F hF U) (G.val.obj (op U))) :
    SheafOfModules.IsFiniteLocallyFreeOnSite G := by
  classical
  let P : ∀ U : SmallEtale B S hS F, Presieve U := fun _ V _ =>
    IsAffine (chartScheme V) ∧ ∃ r : ℕ,
      Nonempty (Module.Basis (Fin r) (chartRing B S hS F hF V) (G.val.obj (op V)))
  have hcov : ∀ U, Sieve.generate (P U) ∈ SmallEtale.topology B S hS F U := by
    intro U
    refine smallEtale_sieve_of_pointwise_covering B S hS F U _ fun z => ?_
    obtain ⟨T₀, j, hT₀, w₀, hw₀⟩ := exists_affine_chart_at B S hS F U z
    have hT₀' : IsAffine (chartScheme T₀) := hT₀
    obtain ⟨hfin, hproj⟩ := h T₀ hT₀'
    have hmid : Module.Finite (chartRing B S hS F hF T₀) (G.val.obj (op T₀)) ∧
        Module.Projective (chartRing B S hS F hF T₀) (G.val.obj (op T₀)) := ⟨hfin, hproj⟩
    obtain ⟨s, hs, hfree⟩ :=
      ((Stacks.LocallyFree.FiniteProjective.solution (chartRing B S hS F hF T₀)
        (G.val.obj (op T₀))).out 2 7).mp hmid
    have hz : w₀ ∈ (⨆ i ∈ s, (chartScheme T₀).basicOpen i) := by
      have he : (⨆ i ∈ s, (chartScheme T₀).basicOpen i) = (⊤ : (chartScheme T₀).Opens) :=
        iSup_basicOpen_of_span_eq_top (X := chartScheme T₀) ⊤ s hs
      exact he.ge (show w₀ ∈ (⊤ : (chartScheme T₀).Opens) from trivial)
    simp only [TopologicalSpace.Opens.mem_iSup] at hz
    obtain ⟨g, hg, hwg⟩ := hz
    let := chartAlgebra (hF := hF)
      (openChartInclusion B S hS F T₀ ((chartScheme T₀).basicOpen g))
    let := chartSectionsModule G
      (openChartInclusion B S hS F T₀ ((chartScheme T₀).basicOpen g))
    have := chartSections_isScalarTower G
      (openChartInclusion B S hS F T₀ ((chartScheme T₀).basicOpen g))
    have := isLocalization_away_chartRing_openChart_basicOpen B S hS hF T₀ hT₀' g
    have := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS hF G hG T₀ hT₀' g
    have := (hfree g hg).1
    have := (hfree g hg).2
    let b := Module.Free.chooseBasis (Localization.Away g)
      (LocalizedModule (Submonoid.powers g) (G.val.obj (op T₀)))
    have : Finite (Module.Free.ChooseBasisIndex (Localization.Away g)
      (LocalizedModule (Submonoid.powers g) (G.val.obj (op T₀)))) := inferInstance
    let b' := b.reindex (Fintype.equivFin _)
    refine ⟨openChart B S hS F T₀ ((chartScheme T₀).basicOpen g),
      openChartInclusion B S hS F T₀ ((chartScheme T₀).basicOpen g) ≫ j,
      ⟨_, 𝟙 _, _, ⟨isAffine_chartScheme_openChart_basicOpen B S hS F T₀ hT₀' g, _,
        ⟨Module.Basis.ofIsLocalizedModuleAway g (chartRestrictLinear G
          (openChartInclusion B S hS F T₀ ((chartScheme T₀).basicOpen g))) b'⟩⟩,
        Category.id_comp _⟩, ⟨w₀, hwg⟩, ?_⟩
    rw [Functor.map_comp, Functor.map_comp]
    show ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map j))
      (((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map
        (openChartInclusion B S hS F T₀ ((chartScheme T₀).basicOpen g)))) ⟨w₀, hwg⟩) = z
    rw [toScheme_map_toOver_map_openChartInclusion]
    exact hw₀
  rw [SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit]
  intro U
  refine ⟨Σ V : SmallEtale B S hS F, {f : V ⟶ U // P U f},
    fun i => i.1, fun i => i.2.1, ?_, fun i => ?_⟩
  · refine GrothendieckTopology.superset_covering _ ?_ (hcov U)
    rintro T k ⟨V, m, v, hV, rfl⟩
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk
      (fun i : Σ V : SmallEtale B S hS F, {f : V ⟶ U // P U f} => i.1)
      (fun i => i.2.1) ⟨V, ⟨v, hV⟩⟩) m
  · obtain ⟨r, ⟨b⟩⟩ := i.2.2.2
    exact ⟨r, exists_isColimitCofan_of_basis B S hS F hF G hG i.1 i.2.2.1 b⟩

end AlgebraicGeometry.Space

end
