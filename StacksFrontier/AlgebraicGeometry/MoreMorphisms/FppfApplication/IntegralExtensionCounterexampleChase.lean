module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FppfApplication.IntegralExtensionCounterexample
public import StacksFrontier.AlgebraicGeometry.TwoChartGluing
public import StacksFrontier.AlgebraicGeometry.OpenBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.SqZeroScaleIso
public import StacksFrontier.AlgebraicGeometry.RestrictIso
public import StacksFrontier.AlgebraicGeometry.ChartLocalProperty

/-!
# The glued cover of the counterexample has no integral extension

This file carries the second half of the refutation of [Stacks, Tag 0CNX] for a general open
subscheme: the comparison of the two charts of the glued scheme with the charts of a hypothetical
integral extension.
-/

@[expose] public section

namespace Stacks.IntegralExtensionCounterexample

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open Stacks.SqZero Stacks.ModuleQuadraticExtension Stacks.TwoChartGluing

universe u

noncomputable section

lemma range_ι_comp_psi_subset (Ω : Sch.{u}.Opens) :
    Set.range ((toSch.{u} ⁻¹ᵁ Ω).ι ≫ psi.{u}) ⊆ Set.range ((toSch.{u} ⁻¹ᵁ Ω).ι) := by
  rintro x ⟨y, rfl⟩
  refine ⟨⟨psi.{u} ((toSch.{u} ⁻¹ᵁ Ω).ι y), ?_⟩, rfl⟩
  have : toSch.{u} (psi.{u} ((toSch.{u} ⁻¹ᵁ Ω).ι y)) = toSch.{u} ((toSch.{u} ⁻¹ᵁ Ω).ι y) := by
    rw [← Scheme.Hom.comp_apply, psi_comp_toSch]
  change toSch.{u} (psi.{u} ((toSch.{u} ⁻¹ᵁ Ω).ι y)) ∈ Ω
  rw [this]
  exact y.2

/-- The scaling endomorphism `psi`, restricted to the part of `Aff` over an open of the base. -/
def psiRes (Ω : Sch.{u}.Opens) :
    (toSch.{u} ⁻¹ᵁ Ω).toScheme ⟶ (toSch.{u} ⁻¹ᵁ Ω).toScheme :=
  IsOpenImmersion.lift ((toSch.{u} ⁻¹ᵁ Ω).ι) ((toSch.{u} ⁻¹ᵁ Ω).ι ≫ psi.{u})
    (range_ι_comp_psi_subset Ω)

@[reassoc (attr := simp)]
lemma psiRes_ι (Ω : Sch.{u}.Opens) :
    psiRes.{u} Ω ≫ (toSch.{u} ⁻¹ᵁ Ω).ι = (toSch.{u} ⁻¹ᵁ Ω).ι ≫ psi.{u} :=
  IsOpenImmersion.lift_fac _ _ _

lemma psiRes_homOfLE {Ω Ω' : Sch.{u}.Opens} (h : Ω' ≤ Ω) :
    Aff.{u}.homOfLE (preimage_mono toSch.{u} h) ≫ psiRes.{u} Ω
      = psiRes.{u} Ω' ≫ Aff.{u}.homOfLE (preimage_mono toSch.{u} h) := by
  rw [← cancel_mono ((toSch.{u} ⁻¹ᵁ Ω).ι), Category.assoc, Category.assoc, psiRes_ι,
    Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι, psiRes_ι]

lemma psiRes_morphismRestrict (Ω : Sch.{u}.Opens) :
    psiRes.{u} Ω ≫ toSch.{u} ∣_ Ω = toSch.{u} ∣_ Ω := by
  rw [← cancel_mono Ω.ι, Category.assoc, morphismRestrict_ι, psiRes_ι_assoc,
    psi_comp_toSch]

/-- The data the two-chart gluing produces for the counterexample: a scheme over the
non-retrocompact open `Uo`, with its three charts cut out of `Aff`, and the twist on the
`Wo` leg given by scaling the square-zero ideal by `(1, 2, 4, …)`. -/
structure GluedCover where
  /-- The glued scheme. -/
  carrier : Scheme.{u}
  /-- Its structure morphism to the open subscheme. -/
  str : carrier ⟶ Uo.{u}.toScheme
  /-- The chart over `Df`. -/
  chartDf : (toSch.{u} ⁻¹ᵁ Df.{u}).toScheme ⟶ carrier
  /-- The chart over `Wo`. -/
  chartWo : (toSch.{u} ⁻¹ᵁ Wo.{u}).toScheme ⟶ carrier
  /-- The chart over the overlap. -/
  chartIn : (toSch.{u} ⁻¹ᵁ (Df.{u} ⊓ Wo.{u})).toScheme ⟶ carrier
  /-- The `Df` chart is the part of the glued scheme over `Df`. -/
  isPullback_Df : IsPullback (toSch.{u} ∣_ Df.{u}) chartDf Df.{u}.ι (str ≫ Uo.{u}.ι)
  /-- The `Wo` chart is the part of the glued scheme over `Wo`. -/
  isPullback_Wo : IsPullback (toSch.{u} ∣_ Wo.{u}) chartWo Wo.{u}.ι (str ≫ Uo.{u}.ι)
  /-- The overlap chart is the part of the glued scheme over the overlap. -/
  isPullback_In : IsPullback (toSch.{u} ∣_ (Df.{u} ⊓ Wo.{u})) chartIn
    (Df.{u} ⊓ Wo.{u}).ι (str ≫ Uo.{u}.ι)
  /-- The overlap chart agrees with the `Df` chart. -/
  chart_left : Aff.{u}.homOfLE (preimage_mono toSch.{u}
    (inf_le_left : Df.{u} ⊓ Wo.{u} ≤ Df.{u})) ≫ chartDf = chartIn
  /-- The overlap chart agrees with the `Wo` chart after the twist. -/
  chart_right : psiRes.{u} (Df.{u} ⊓ Wo.{u}) ≫ Aff.{u}.homOfLE (preimage_mono toSch.{u}
    (inf_le_right : Df.{u} ⊓ Wo.{u} ≤ Wo.{u})) ≫ chartWo = chartIn

namespace GluedCover

variable (G : GluedCover.{u})

/-- The chart over an open contained in `Df`. -/
def chartD {Ω : Sch.{u}.Opens} (h : Ω ≤ Df.{u}) : (toSch.{u} ⁻¹ᵁ Ω).toScheme ⟶ G.carrier :=
  Aff.{u}.homOfLE (preimage_mono toSch.{u} h) ≫ G.chartDf

/-- The chart over an open contained in `Wo`. -/
def chartW {Ω : Sch.{u}.Opens} (h : Ω ≤ Wo.{u}) : (toSch.{u} ⁻¹ᵁ Ω).toScheme ⟶ G.carrier :=
  Aff.{u}.homOfLE (preimage_mono toSch.{u} h) ≫ G.chartWo

/-- The chart over an open contained in the overlap. -/
def chartI {Ω : Sch.{u}.Opens} (h : Ω ≤ Df.{u} ⊓ Wo.{u}) :
    (toSch.{u} ⁻¹ᵁ Ω).toScheme ⟶ G.carrier :=
  Aff.{u}.homOfLE (preimage_mono toSch.{u} h) ≫ G.chartIn

lemma isPullback_chartD {Ω : Sch.{u}.Opens} (h : Ω ≤ Df.{u}) :
    IsPullback (toSch.{u} ∣_ Ω) (G.chartD h) Ω.ι (G.str ≫ Uo.{u}.ι) :=
  isPullback_restrict_chart toSch.{u} (G.str ≫ Uo.{u}.ι) h G.isPullback_Df

lemma isPullback_chartW {Ω : Sch.{u}.Opens} (h : Ω ≤ Wo.{u}) :
    IsPullback (toSch.{u} ∣_ Ω) (G.chartW h) Ω.ι (G.str ≫ Uo.{u}.ι) :=
  isPullback_restrict_chart toSch.{u} (G.str ≫ Uo.{u}.ι) h G.isPullback_Wo

lemma isPullback_chartI {Ω : Sch.{u}.Opens} (h : Ω ≤ Df.{u} ⊓ Wo.{u}) :
    IsPullback (toSch.{u} ∣_ Ω) (G.chartI h) Ω.ι (G.str ≫ Uo.{u}.ι) :=
  isPullback_restrict_chart toSch.{u} (G.str ≫ Uo.{u}.ι) h G.isPullback_In

lemma ovl_le_Df (n : ℕ) : D.{u} (ovl n) ≤ Df.{u} := (Df_inf_De n) ▸ inf_le_left

lemma ovl_le_De (n : ℕ) : D.{u} (ovl n) ≤ De.{u} n := (Df_inf_De n) ▸ inf_le_right

lemma ovl_le_inf (n : ℕ) : D.{u} (ovl n) ≤ Df.{u} ⊓ Wo.{u} :=
  le_inf (ovl_le_Df n) ((ovl_le_De n).trans (De_le_Wo n))

/-- Over the `n`-th overlap, the `Df` chart agrees with the overlap chart. -/
lemma chartD_ovl (n : ℕ) : G.chartD (ovl_le_Df.{u} n) = G.chartI (ovl_le_inf.{u} n) := by
  rw [chartD, chartI, ← G.chart_left, ← Category.assoc, Scheme.homOfLE_homOfLE]

/-- Over the `n`-th overlap, the `Wo` chart agrees with the overlap chart after the twist. -/
lemma chartW_ovl (n : ℕ) :
    psiRes.{u} (D.{u} (ovl n)) ≫ G.chartW ((ovl_le_De.{u} n).trans (De_le_Wo n))
      = G.chartI (ovl_le_inf.{u} n) := by
  rw [chartW, chartI, ← G.chart_right]
  conv_rhs => rw [← Category.assoc, psiRes_homOfLE (ovl_le_inf.{u} n)]
  simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]

end GluedCover

section Extension

open Stacks.OpenBaseChangeCharts

variable (G : GluedCover.{u}) {A' : Scheme.{u}} {α : A' ⟶ Sch.{u}} {ρ : G.carrier ⟶ A'}
  (hρ : IsPullback ρ G.str α Uo.{u}.ι)

lemma Df_le_Uo : Df.{u} ≤ Uo.{u} := le_sup_left

lemma Wo_le_Uo : Wo.{u} ≤ Uo.{u} := le_sup_right

lemma ovl_le_Uo (n : ℕ) : D.{u} (ovl n) ≤ Uo.{u} := (GluedCover.ovl_le_Df.{u} n).trans Df_le_Uo

include hρ in
/-- The chart of a hypothetical extension, as a cartesian square over the base scheme. -/
lemma isPullback_extChart {Ω : Sch.{u}.Opens} (hΩ : Ω ≤ Uo.{u}) :
    IsPullback (α ∣_ Ω) (chart hρ hΩ) Ω.ι (G.str ≫ Uo.{u}.ι) :=
  isPullback_comp_mono (isPullback_chart hρ hΩ) Uo.{u}.ι (Scheme.homOfLE_ι Sch.{u} hΩ)

include hρ in
lemma mono_extChart {Ω : Sch.{u}.Opens} (hΩ : Ω ≤ Uo.{u}) : Mono (chart hρ hΩ) :=
  mono_of_mono_fac (chart_comp hρ hΩ)

/-- The comparison between a chart of the glued cover and the corresponding chart of a
hypothetical extension. -/
def cmp {Ω : Sch.{u}.Opens} (hΩ : Ω ≤ Uo.{u}) (κ : (toSch.{u} ⁻¹ᵁ Ω).toScheme ⟶ G.carrier)
    (hκ : IsPullback (toSch.{u} ∣_ Ω) κ Ω.ι (G.str ≫ Uo.{u}.ι)) :
    (toSch.{u} ⁻¹ᵁ Ω).toScheme ≅ (α ⁻¹ᵁ Ω).toScheme :=
  hκ.isoIsPullback _ _ (isPullback_extChart G hρ hΩ)

@[reassoc (attr := simp)]
lemma cmp_hom_chart {Ω : Sch.{u}.Opens} (hΩ : Ω ≤ Uo.{u})
    (κ : (toSch.{u} ⁻¹ᵁ Ω).toScheme ⟶ G.carrier)
    (hκ : IsPullback (toSch.{u} ∣_ Ω) κ Ω.ι (G.str ≫ Uo.{u}.ι)) :
    (cmp G hρ hΩ κ hκ).hom ≫ chart hρ hΩ = κ :=
  hκ.isoIsPullback_hom_snd _ _ (isPullback_extChart G hρ hΩ)

@[reassoc (attr := simp)]
lemma cmp_hom_morphismRestrict {Ω : Sch.{u}.Opens} (hΩ : Ω ≤ Uo.{u})
    (κ : (toSch.{u} ⁻¹ᵁ Ω).toScheme ⟶ G.carrier)
    (hκ : IsPullback (toSch.{u} ∣_ Ω) κ Ω.ι (G.str ≫ Uo.{u}.ι)) :
    (cmp G hρ hΩ κ hκ).hom ≫ (α ∣_ Ω) = toSch.{u} ∣_ Ω :=
  hκ.isoIsPullback_hom_fst _ _ (isPullback_extChart G hρ hΩ)

/-- **The comparison respects the structure morphisms.** Reading sections, this says that the
image of a global section of the base ring is the same whether it is taken through the
hypothetical extension or through `Aff`. -/
lemma cmp_hom_ι {Ω : Sch.{u}.Opens} (hΩ : Ω ≤ Uo.{u})
    (κ : (toSch.{u} ⁻¹ᵁ Ω).toScheme ⟶ G.carrier)
    (hκ : IsPullback (toSch.{u} ∣_ Ω) κ Ω.ι (G.str ≫ Uo.{u}.ι)) :
    (cmp G hρ hΩ κ hκ).hom ≫ (α ⁻¹ᵁ Ω).ι ≫ α = (toSch.{u} ⁻¹ᵁ Ω).ι ≫ toSch.{u} := by
  rw [← morphismRestrict_ι α Ω, ← Category.assoc, cmp_hom_morphismRestrict,
    morphismRestrict_ι]

/-- A map between source charts that is compatible with the chart maps is compatible with the
comparisons, up to the inclusion of the extension charts. -/
private theorem comp_cmp_hom_eq {Ω Ω' : Sch.{u}.Opens} (hΩ : Ω ≤ Uo.{u}) (hΩ' : Ω' ≤ Uo.{u})
    (h : Ω' ≤ Ω) (κ : (toSch.{u} ⁻¹ᵁ Ω).toScheme ⟶ G.carrier)
    (hκ : IsPullback (toSch.{u} ∣_ Ω) κ Ω.ι (G.str ≫ Uo.{u}.ι))
    (κ' : (toSch.{u} ⁻¹ᵁ Ω').toScheme ⟶ G.carrier)
    (hκ' : IsPullback (toSch.{u} ∣_ Ω') κ' Ω'.ι (G.str ≫ Uo.{u}.ι))
    (f : (toSch.{u} ⁻¹ᵁ Ω').toScheme ⟶ (toSch.{u} ⁻¹ᵁ Ω).toScheme) (hf : f ≫ κ = κ') :
    f ≫ (cmp G hρ hΩ κ hκ).hom
      = (cmp G hρ hΩ' κ' hκ').hom ≫ A'.homOfLE (preimage_mono α h) := by
  have := mono_extChart G hρ hΩ
  rw [← cancel_mono (chart hρ hΩ), Category.assoc, Category.assoc, cmp_hom_chart,
    chart_comp_homOfLE hρ h (chart_comp hρ hΩ) (chart_comp hρ hΩ'), cmp_hom_chart, hf]

/-- Over the `n`-th overlap, the comparison from the `Df` chart and the comparison from the
overlap chart differ only by the inclusions. -/
lemma cmp_left (n : ℕ) :
    Aff.{u}.homOfLE (preimage_mono toSch.{u} (GluedCover.ovl_le_Df.{u} n))
        ≫ (cmp G hρ Df_le_Uo.{u} G.chartDf G.isPullback_Df).hom
      = (cmp G hρ (ovl_le_Uo.{u} n) (G.chartI (GluedCover.ovl_le_inf.{u} n))
          (G.isPullback_chartI (GluedCover.ovl_le_inf.{u} n))).hom
        ≫ A'.homOfLE (preimage_mono α (GluedCover.ovl_le_Df.{u} n)) :=
  comp_cmp_hom_eq G hρ _ _ (GluedCover.ovl_le_Df.{u} n) _ _ _ _ _ (G.chartD_ovl n)

/-- Over the `n`-th overlap, the comparison from the `Wo` chart and the comparison from the
overlap chart differ by the twist. -/
lemma cmp_right (n : ℕ) :
    psiRes.{u} (D.{u} (ovl n)) ≫ Aff.{u}.homOfLE (preimage_mono toSch.{u}
          ((GluedCover.ovl_le_De.{u} n).trans (De_le_Wo n)))
        ≫ (cmp G hρ Wo_le_Uo.{u} G.chartWo G.isPullback_Wo).hom
      = (cmp G hρ (ovl_le_Uo.{u} n) (G.chartI (GluedCover.ovl_le_inf.{u} n))
          (G.isPullback_chartI (GluedCover.ovl_le_inf.{u} n))).hom
        ≫ A'.homOfLE (preimage_mono α ((GluedCover.ovl_le_De.{u} n).trans (De_le_Wo n))) := by
  rw [← Category.assoc]
  exact comp_cmp_hom_eq G hρ _ _ ((GluedCover.ovl_le_De.{u} n).trans (De_le_Wo n)) _ _ _ _ _
    (G.chartW_ovl n)

end Extension

section Construction

open Stacks.SqZeroScaleIso

/-- Scaling preserves every open pulled back from the base scheme. -/
lemma psi_preimage (Ω : Sch.{u}.Opens) :
    psi.{u} ⁻¹ᵁ (toSch.{u} ⁻¹ᵁ Ω) = toSch.{u} ⁻¹ᵁ Ω := by
  rw [← Scheme.Hom.comp_preimage, psi_comp_toSch]

/-- The restricted scaling endomorphism is the `morphismRestrict` of `psi`, transported along
the equality of preimages. -/
lemma psiRes_eq (Ω : Sch.{u}.Opens) :
    psiRes.{u} Ω = (Aff.{u}.isoOfEq (psi_preimage.{u} Ω)).inv
      ≫ psi.{u} ∣_ (toSch.{u} ⁻¹ᵁ Ω) := by
  rw [← cancel_mono ((toSch.{u} ⁻¹ᵁ Ω).ι), psiRes_ι, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, Scheme.isoOfEq_inv_ι]

/-- `(1, 2, 4, …)` divides a power of `2 · eₙ`, so the twist is an isomorphism over the `n`-th
piece of the overlap. -/
instance isIso_psi_restrict_ovl (n : ℕ) : IsIso (psi.{u} ∣_ (toSch.{u} ⁻¹ᵁ D.{u} (ovl n))) :=
  isIso_morphismRestrict_specMap_scale_of_eq pows.{u} (ovl n) (ovl n) (n + 1)
    (pows_mul_ovl n) (D.{u} (ovl n)) rfl

/-- **The twist of the counterexample is an isomorphism over the overlap.** -/
instance isIso_psiRes_inf : IsIso (psiRes.{u} (Df.{u} ⊓ Wo.{u})) := by
  have h : IsIso (psi.{u} ∣_ (toSch.{u} ⁻¹ᵁ (Df.{u} ⊓ Wo.{u}))) := by
    refine Stacks.RestrictIso.isIso_morphismRestrict_of_iSup psi.{u}
      (toSch.{u} ⁻¹ᵁ (Df.{u} ⊓ Wo.{u})) (fun n ↦ toSch.{u} ⁻¹ᵁ D.{u} (ovl n)) ?_
      (fun n ↦ isIso_psi_restrict_ovl n)
    rw [← Scheme.Hom.preimage_iSup, ← Df_inf_Wo]
  rw [psiRes_eq]
  infer_instance

/-- **The glued cover of the counterexample exists.** -/
theorem nonempty_gluedCover : Nonempty GluedCover.{u} := by
  obtain ⟨V, f, κ, hκ, hleft, hright⟩ := Stacks.TwoChartGluing.exists_glued Df.{u} Wo.{u}
    toSch.{u} (psiRes.{u} (Df.{u} ⊓ Wo.{u})) (psiRes_morphismRestrict _)
  exact ⟨{ carrier := V
           str := f
           chartDf := κ (some WalkingPair.left)
           chartWo := κ (some WalkingPair.right)
           chartIn := κ none
           isPullback_Df := hκ (some WalkingPair.left)
           isPullback_Wo := hκ (some WalkingPair.right)
           isPullback_In := hκ none
           chart_left := hleft
           chart_right := hright }⟩

namespace GluedCover

variable (G : GluedCover.{u})

/-- The two opens of the cover, as a family indexed by `Bool`. -/
def covOpen : Bool → Sch.{u}.Opens
  | false => Df.{u}
  | true => Wo.{u}

/-- The two charts, as a family indexed by `Bool`. -/
def covChart : (b : Bool) → (toSch.{u} ⁻¹ᵁ covOpen.{u} b).toScheme ⟶ G.carrier
  | false => G.chartDf
  | true => G.chartWo

lemma iSup_covOpen : ⨆ b, covOpen.{u} b = Uo.{u} := by
  rw [iSup_bool_eq]
  exact sup_comm _ _

lemma isPullback_covChart (b : Bool) :
    IsPullback (toSch.{u} ∣_ covOpen.{u} b) (G.covChart b) (covOpen.{u} b).ι
      (G.str ≫ Uo.{u}.ι) := by
  cases b with
  | false => exact G.isPullback_Df
  | true => exact G.isPullback_Wo

/-- The structure morphism of the glued cover is integral. -/
instance isIntegralHom_str : IsIntegralHom G.str :=
  Stacks.ChartLocalProperty.isIntegralHom_of_charts G.str toSch.{u} covOpen.{u}
    iSup_covOpen.{u} G.covChart G.isPullback_covChart

/-- The structure morphism of the glued cover is surjective. -/
instance surjective_str : Surjective G.str :=
  Stacks.ChartLocalProperty.surjective_of_charts G.str toSch.{u} covOpen.{u}
    iSup_covOpen.{u} G.covChart G.isPullback_covChart

end GluedCover

end Construction

end

end Stacks.IntegralExtensionCounterexample
