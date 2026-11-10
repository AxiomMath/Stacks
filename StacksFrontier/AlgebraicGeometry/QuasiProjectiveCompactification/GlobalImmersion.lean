module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseThreeMorphism
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.OverBase

/-!
# `r_{L, ψ}` is an immersion as soon as its charts at degree-one sections are

Let `(S, 𝒜, f : X ⟶ S, L, ψ)` be the data of [Stacks, Tag 01O8] and
`r_{L, ψ} : U(ψ) ⟶ Proj_S(𝒜)` the morphism of [Stacks, Tag 01O9]. Over an affine open `V` of the
base and on the nonvanishing open `X_{ψ(g)}` of a section `g ∈ 𝒜(V)₁`, `r_{L, ψ}` is the chart
`X_{ψ(g)} ⟶ Spec 𝒜(V)_{(g)}` of [Stacks, Tag 01NK] followed by the open immersions
`Spec 𝒜(V)_{(g)} = D₊(g) ⊆ Proj 𝒜(V) ⊆ Proj_S(𝒜)`, and the preimage of that open is exactly
`X_{ψ(g)}`. So if the nonvanishing opens of sections whose charts are immersions cover `X`, then
`U(ψ) = X` and `r_{L, ψ}` is an immersion, being one locally on its target.

This is the last step of the proof of [Stacks, Tag 07RM]: "it follows that `r_{L, ψ_i}|_{V_j}` is
an immersion. Since `S = ⋃ V_j` we conclude that `r_{L, ψ_i}` is an immersion."

## Main results

* `Stacks.QuasiProjectiveCompactification.isImmersion_of_forall_exists_isOpenImmersion`: a
  morphism is an immersion when every point of the source has an open neighbourhood of its image
  whose preimage is the range of an open immersion along which the morphism is an immersion.
* `Stacks.QuasiProjectiveCompactification.coveringOpen_eq_top_of_chartsAreImmersions` and
  `Stacks.QuasiProjectiveCompactification.isImmersion_globalMorphism_of_chartsAreImmersions`: the
  statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjFromSections
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.ProjChartFullGraded
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.QuasiProjectiveCompactification

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- **Being an immersion, checked through open immersions onto preimages.** If every point `x` of
`X` admits an open `U ∋ f x` of `Y` and an open immersion `m : W ⟶ X` onto `f⁻¹(U)` such that
`m ≫ f` is an immersion, then `f` is an immersion. This is Zariski locality on the target, with
the preimage presented by an arbitrary open immersion rather than as an open subscheme. -/
theorem isImmersion_of_forall_exists_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ x : X, ∃ (U : Y.Opens) (W : Scheme.{u}) (m : W ⟶ X), IsOpenImmersion m ∧
      Set.range m.base = (f ⁻¹ᵁ U : Set X) ∧ f x ∈ U ∧ IsImmersion (m ≫ f)) :
    IsImmersion f := by
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg => by have := hi; have := hg; infer_instance⟩
  have : MorphismProperty.HasOfPostcompProperty @IsImmersion @IsOpenImmersion :=
    ⟨fun g i _ h => by have := h; exact IsImmersion.of_comp g i⟩
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage f fun x => ?_
  obtain ⟨U, W, m, hm, hrange, hx, himm⟩ := h x
  refine ⟨U, hx, ?_⟩
  have e : Set.range m.base = Set.range (f ⁻¹ᵁ U).ι.base := by
    rw [hrange, Scheme.Opens.range_ι]
  have hfac : (f ⁻¹ᵁ U).ι ≫ f = (IsOpenImmersion.isoOfRangeEq m (f ⁻¹ᵁ U).ι e).inv ≫ m ≫ f := by
    rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac]
  rw [hfac]
  infer_instance

/-! ### The charts of `r_{L, ψ}` at degree-one sections -/

section Chart

variable {S X : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : X ⟶ S}
  (P : GradedPowerMap A f) (rp : RelativeProjData A) {V : S.Opens} (hV : IsAffineOpen V)
  {g : A.sectionRing V} (hg : g ∈ A.grading V 1)

/-- The nonvanishing open `X_{ψ(g)}` of `f⁻¹(V)`, for `g ∈ 𝒜(V)₁`. -/
abbrev chartOpen : (f ⁻¹ᵁ V).toScheme.Opens :=
  nonvanishingOpen (f ⁻¹ᵁ V).toScheme
    (natTensorPow ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) 1)
    ((P.affineDatum V).toFun 1 ⟨g, hg⟩)

/-- The inclusion of `X_{ψ(g)}` into `U(ψ)`. -/
def chartIncl : (chartOpen P hg).toScheme ⟶ P.coveringOpen.toScheme :=
  (f ⁻¹ᵁ V).toScheme.homOfLE
      ((P.affineDatum V).nonvanishingOpenAt_le_coveringOpen_of_pos hg one_pos) ≫
    P.affineDatumInclusion ⟨V, hV⟩

/-- The inclusion of `X_{ψ(g)}` into `U(ψ)` is an open immersion. -/
instance : IsOpenImmersion (chartIncl P hV hg) := by
  rw [chartIncl, GradedPowerMap.affineDatumInclusion]
  infer_instance

/-- The inclusion of `X_{ψ(g)}` into `U(ψ)`, followed by `U(ψ) ⟶ X`, is the inclusion
`X_{ψ(g)} ⟶ f⁻¹(V) ⟶ X`. -/
theorem chartIncl_ι :
    chartIncl P hV hg ≫ P.coveringOpen.ι = (chartOpen P hg).ι ≫ (f ⁻¹ᵁ V).ι := by
  rw [chartIncl, Category.assoc, P.affineDatumInclusion_ι ⟨V, hV⟩, ← Category.assoc,
    Scheme.homOfLE_ι]

/-- `chartIncl_ι` on points. -/
theorem chartIncl_apply (z : (chartOpen P hg).toScheme) :
    P.coveringOpen.ι (chartIncl P hV hg z) = (f ⁻¹ᵁ V).ι ((chartOpen P hg).ι z) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun φ => φ z) (chartIncl_ι P hV hg)

/-- `GradedPowerMap.affineDatumInclusion_ι` on points. -/
theorem affineDatumInclusion_apply (z : ((P.affineDatum V).coveringOpen).toScheme) :
    P.coveringOpen.ι (P.affineDatumInclusion ⟨V, hV⟩ z) =
      (f ⁻¹ᵁ V).ι ((P.affineDatum V).coveringOpen.ι z) := by
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun φ => φ z) (P.affineDatumInclusion_ι ⟨V, hV⟩)

/-- **On `X_{ψ(g)}`, `r_{L, ψ}` is the chart of [Stacks, Tag 01NK] followed by the chart of the
relative `Proj`.** -/
theorem chartIncl_globalMorphism :
    chartIncl P hV hg ≫ P.globalMorphism rp =
      (P.affineDatum V).chartToProj hg le_rfl one_pos ≫ rp.chart V hV := by
  rw [chartIncl, Category.assoc, P.affineDatumInclusion_globalMorphism rp ⟨V, hV⟩,
    ← Category.assoc]
  exact homOfLE_relativeChart_of_pos rp V hV (P.affineDatum V) hg one_pos

/-- **The preimage under `r_{L, ψ}` of the chart image of `D₊(g)` is `X_{ψ(g)}`.** -/
theorem range_chartIncl :
    Set.range (chartIncl P hV hg).base =
      (P.globalMorphism rp ⁻¹ᵁ (rp.chart V hV ''ᵁ
        AlgebraicGeometry.Proj.basicOpen (A.grading V) g) : Set P.coveringOpen.toScheme) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    change (P.globalMorphism rp) ((chartIncl P hV hg) z) ∈ rp.chart V hV '' _
    rw [← Scheme.Hom.comp_apply, chartIncl_globalMorphism, Scheme.Hom.comp_apply]
    exact ⟨_, GradedSections.chartToProj_base_mem _ hg le_rfl one_pos z, rfl⟩
  · rintro ⟨w, hw, hwy⟩
    replace hwy : rp.chart V hV w = P.globalMorphism rp y := hwy
    have hyV : P.toBase y ∈ V := by
      have h1 := congrArg (fun φ => φ y) (P.globalMorphism_comp_toBase rp)
      have h2 := congrArg (fun φ => φ w) (rp.chart_isPullback V hV).w
      simp only [Scheme.Hom.comp_apply] at h1 h2
      rw [← h1, ← hwy, h2]
      exact (projInclusionToOpen A V hV w).2
    let y₀ : (P.toBase ⁻¹ᵁ V).toScheme := ⟨y, hyV⟩
    let y' := (P.pieceIso V hV).hom y₀
    have hy' : P.affineDatumInclusion ⟨V, hV⟩ y' = y :=
      congrArg (P.toBase ⁻¹ᵁ V).ι (Scheme.hom_inv_apply _ y₀)
    have hry' : relativeChart rp V hV (P.affineDatum V) y' = P.globalMorphism rp y := by
      have e := congrArg (fun φ => φ y') (P.affineDatumInclusion_globalMorphism rp ⟨V, hV⟩)
      simp only [Scheme.Hom.comp_apply, hy'] at e
      exact e.symm
    have hmem : y' ∈ relativeChart rp V hV (P.affineDatum V) ⁻¹ᵁ
        (rp.chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g) := by
      change relativeChart rp V hV (P.affineDatum V) y' ∈ rp.chart V hV '' _
      rw [hry']
      exact ⟨w, hw, hwy⟩
    rw [preimage_image_basicOpen_relativeChart rp V hV (P.affineDatum V) hg one_pos] at hmem
    let z : (chartOpen P hg).toScheme := ⟨(P.affineDatum V).coveringOpen.ι y', hmem⟩
    refine ⟨z, P.coveringOpen.ι.isOpenEmbedding.injective ?_⟩
    rw [chartIncl_apply, ← hy', affineDatumInclusion_apply]
    rfl

end Chart

/-! ### `r_{L, ψ}` is an immersion -/

section Global

variable {S X : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : X ⟶ S}
  (P : GradedPowerMap A f) (rp : RelativeProjData A)

/-- The hypothesis of the two results below: every point of `X` lies in the nonvanishing open
`X_{ψ(g)}` of a degree-one section `g` over an affine open of the base, at which the chart of
[Stacks, Tag 01NK] is an immersion. -/
def ChartsAreImmersions : Prop :=
  ∀ x : X, ∃ (V : S.Opens) (_ : IsAffineOpen V) (g : A.sectionRing V) (hg : g ∈ A.grading V 1)
    (x' : (chartOpen P hg).toScheme), (f ⁻¹ᵁ V).ι ((chartOpen P hg).ι x') = x ∧
      IsImmersion (((P.affineDatum V).homogeneousRatios hg le_rfl).toSpecAway one_pos)

/-- **`U(ψ) = X`** when the charts at degree-one sections cover `X`. -/
theorem coveringOpen_eq_top_of_chartsAreImmersions (h : ChartsAreImmersions P) :
    P.coveringOpen = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨V, hV, g, hg, x', hx', -⟩ := h x
  have h1 : (chartOpen P hg).ι x' ∈ (P.affineDatum V).coveringOpen :=
    (P.affineDatum V).nonvanishingOpenAt_le_coveringOpen_of_pos hg one_pos x'.2
  have h2 : x ∈ (f ⁻¹ᵁ V).ι ''ᵁ (P.affineDatum V).coveringOpen := ⟨_, h1, hx'⟩
  rw [P.image_coveringOpen_affineDatum V, ← P.coveringOpen_inf_preimage_eq hV] at h2
  exact h2.1

/-- **`r_{L, ψ}` is an immersion** when the charts at degree-one sections cover `X` and are
immersions. -/
theorem isImmersion_globalMorphism_of_chartsAreImmersions (h : ChartsAreImmersions P) :
    IsImmersion (P.globalMorphism rp) := by
  refine isImmersion_of_forall_exists_isOpenImmersion _ fun y => ?_
  obtain ⟨V, hV, g, hg, x', hx', himm⟩ := h (P.coveringOpen.ι y)
  refine ⟨rp.chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g, _,
    chartIncl P hV hg, inferInstance, range_chartIncl P rp hV hg, ?_, ?_⟩
  · have hy : y ∈ Set.range (chartIncl P hV hg).base := by
      refine ⟨x', P.coveringOpen.ι.isOpenEmbedding.injective ?_⟩
      rw [chartIncl_apply, hx']
    rw [range_chartIncl P rp hV hg] at hy
    exact hy
  · rw [chartIncl_globalMorphism]
    have := himm
    change IsImmersion ((((P.affineDatum V).homogeneousRatios hg le_rfl).toSpecAway one_pos ≫
      AlgebraicGeometry.Proj.awayι (A.grading V) g hg one_pos) ≫ rp.chart V hV)
    infer_instance

end Global

end Stacks.QuasiProjectiveCompactification

end
