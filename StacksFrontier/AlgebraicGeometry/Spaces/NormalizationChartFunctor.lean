module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationChartObject

/-!
# The charts of a representable morphism, and their normalizations, as a functor

Let `f : X ⟶ Y` be a relatively representable morphism of presheaves on the big fppf site of a
scheme `S`. Every morphism `w : h_W ⟶ Y` from a representable presheaf then has a *chart*: the
fibre product `X ×_Y W`, represented by an object of the site, with its projection to `W`. A
morphism `k : W₂ ⟶ W₁` of the site compatible with the two structure morphisms to `Y` induces a
morphism of charts, cartesian over `k`, and this assignment is functorial.

`AlgebraicGeometry.Space.chartNorm` attaches to a chart its relative normalization, read in the
site, and `AlgebraicGeometry.Space.chartNormMap` to a morphism of charts the canonical morphism
of Tag 035J.
Composing the two gives the assignment `w ↦ chartNorm`, functorial in `k`, which is the descent
datum that the normalization of `Y` in `X` must be glued from. This file is the bookkeeping that
makes that assignment a functor: it fixes the morphism of charts induced by `k` and proves that
it is unique, cartesian, and functorial, and transports all three to the chart normalizations.

## Main definitions

* `AlgebraicGeometry.Space.NormalizationGluing.chartMap` is the morphism of charts induced by a
  morphism `k` of the bases, over `Y`.
* `AlgebraicGeometry.Space.NormalizationGluing.normChartMap` is the induced morphism of chart
  normalizations.

## Main results

* `AlgebraicGeometry.Space.NormalizationGluing.chartMap_unique`,
  `AlgebraicGeometry.Space.NormalizationGluing.chartMap_id` and
  `AlgebraicGeometry.Space.NormalizationGluing.chartMap_comp`: the morphism of charts is the
  unique one over `k` compatible with the projections to `X`, and the assignment is functorial.
* `AlgebraicGeometry.Space.NormalizationGluing.isPullback_chartMap`: the induced square of charts
  is cartesian.
* `AlgebraicGeometry.Space.NormalizationGluing.normChartMap_id`,
  `AlgebraicGeometry.Space.NormalizationGluing.normChartMap_comp`: the induced morphisms of chart
  normalizations are functorial; the second is the cocycle condition.
* `AlgebraicGeometry.Space.NormalizationGluing.isPullback_normChartMap`: for an étale `k`, the
  induced square of chart normalizations is cartesian.

## Implementation notes

The quasi-compactness and quasi-separatedness of the chart projections are carried as instance
hypotheses, as for `AlgebraicGeometry.Space.chartNorm`; for a quasi-finite separated `f` they
are supplied by `AlgebraicGeometry.Space.NormalizationGluing.quasiCompact_hrep_snd` and
`AlgebraicGeometry.Space.NormalizationGluing.isSeparated_hrep_snd`.

## References

* [Stacks Project, Tag 035J](https://stacks.math.columbia.edu/tag/035J)
* [Stacks Project, Tag 03GV](https://stacks.math.columbia.edu/tag/03GV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.NormalizationGluing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
  (hrep : yoneda.relativelyRepresentable f)
  {W₁ W₂ W₃ : BigFppfOver B S hS}

/-! ### The morphism of charts induced by a morphism of the bases -/

/-- The morphism of charts over a morphism `k : W₂ ⟶ W₁` of the bases which commutes with the
two structure morphisms to `Y`: the morphism `X ×_Y W₂ ⟶ X ×_Y W₁` given by the universal
property of the second chart. -/
def chartMap {w₁ : yoneda.obj W₁ ⟶ Y} {w₂ : yoneda.obj W₂ ⟶ Y} (k : W₂ ⟶ W₁)
    (hk : yoneda.map k ≫ w₁ = w₂) : hrep.pullback w₂ ⟶ hrep.pullback w₁ :=
  hrep.lift (hrep.fst w₂) (hrep.snd w₂ ≫ k) (by
    rw [Functor.map_comp, Category.assoc, hk]
    exact (hrep.isPullback w₂).w)

/-- The morphism of charts commutes with the projections to `X`. -/
@[reassoc]
lemma yoneda_map_chartMap_comp_fst {w₁ : yoneda.obj W₁ ⟶ Y} {w₂ : yoneda.obj W₂ ⟶ Y}
    (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂) :
    yoneda.map (chartMap B S hS hrep k hk) ≫ hrep.fst w₁ = hrep.fst w₂ :=
  hrep.lift_fst _ _ _

/-- The morphism of charts lies over `k`. -/
@[reassoc]
lemma chartMap_comp_snd {w₁ : yoneda.obj W₁ ⟶ Y} {w₂ : yoneda.obj W₂ ⟶ Y}
    (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂) :
    chartMap B S hS hrep k hk ≫ hrep.snd w₁ = hrep.snd w₂ ≫ k :=
  hrep.lift_snd _ _ _

/-- **The morphism of charts is unique.** Any morphism of the chart sources which commutes with
the projections to `X` and lies over `k` is the induced one. -/
lemma chartMap_unique {w₁ : yoneda.obj W₁ ⟶ Y} {w₂ : yoneda.obj W₂ ⟶ Y}
    (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂)
    (m : hrep.pullback w₂ ⟶ hrep.pullback w₁)
    (hm₁ : yoneda.map m ≫ hrep.fst w₁ = hrep.fst w₂)
    (hm₂ : m ≫ hrep.snd w₁ = hrep.snd w₂ ≫ k) :
    m = chartMap B S hS hrep k hk :=
  hrep.hom_ext
    (hm₁.trans (yoneda_map_chartMap_comp_fst B S hS hrep k hk).symm)
    (hm₂.trans (chartMap_comp_snd B S hS hrep k hk).symm)

/-- **The morphism of charts over the identity is the identity.** -/
lemma chartMap_id (w₁ : yoneda.obj W₁ ⟶ Y) :
    chartMap B S hS hrep (𝟙 W₁) (by simp) = 𝟙 (hrep.pullback w₁) :=
  (chartMap_unique B S hS hrep (𝟙 W₁) (by simp) (𝟙 _) (by simp) (by simp)).symm

/-- **The morphisms of charts compose.** -/
lemma chartMap_comp {w₁ : yoneda.obj W₁ ⟶ Y} {w₂ : yoneda.obj W₂ ⟶ Y}
    {w₃ : yoneda.obj W₃ ⟶ Y} (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂)
    (k' : W₃ ⟶ W₂) (hk' : yoneda.map k' ≫ w₂ = w₃) :
    chartMap B S hS hrep k' hk' ≫ chartMap B S hS hrep k hk =
      chartMap B S hS hrep (k' ≫ k) (by rw [Functor.map_comp, Category.assoc, hk, hk']) :=
  chartMap_unique B S hS hrep _ _ _
    (by rw [Functor.map_comp, Category.assoc, yoneda_map_chartMap_comp_fst,
      yoneda_map_chartMap_comp_fst])
    (by rw [Category.assoc, chartMap_comp_snd, chartMap_comp_snd_assoc])

/-- **The square of charts over `k` is cartesian**, as a square of the site. -/
lemma isPullback_chartMap {w₁ : yoneda.obj W₁ ⟶ Y} {w₂ : yoneda.obj W₂ ⟶ Y}
    (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂) :
    IsPullback (chartMap B S hS hrep k hk) (hrep.snd w₂) (hrep.snd w₁) k := by
  refine IsPullback.of_map_of_faithful yoneda ?_
  refine IsPullback.of_right (h₁₂ := hrep.fst w₁) (v₁₃ := f) (h₂₂ := w₁) ?_ ?_ (hrep.isPullback w₁)
  · rw [yoneda_map_chartMap_comp_fst, hk]
    exact hrep.isPullback w₂
  · rw [← Functor.map_comp, ← Functor.map_comp, chartMap_comp_snd]

/-! ### The induced morphism of chart normalizations -/

/-- The canonical morphism of chart normalizations of Tag 035J depends on the morphism of
charts and not on the proof that the square commutes, the latter being a proposition. -/
lemma chartNormMap_congr_hom {V₁ V₂ XV₁ XV₂ : BigFppfOver B S hS} (q₁ : XV₁ ⟶ V₁)
    (q₂ : XV₂ ⟶ V₂)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map q₁)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map q₁)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map q₂)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map q₂)]
    (k : V₂ ⟶ V₁) (κ κ' : XV₂ ⟶ XV₁) (sq : κ ≫ q₁ = q₂ ≫ k) (sq' : κ' ≫ q₁ = q₂ ≫ k)
    (h : κ = κ') :
    chartNormMap B S hS q₁ q₂ k κ sq = chartNormMap B S hS q₁ q₂ k κ' sq' := by
  subst h; rfl

/-- The morphism of chart normalizations induced by a morphism `k : W₂ ⟶ W₁` of the bases over
`Y`: the canonical morphism of Tag 035J attached to the cartesian square of charts. -/
def normChartMap {w₁ : yoneda.obj W₁ ⟶ Y} {w₂ : yoneda.obj W₂ ⟶ Y}
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w₁))]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w₁))]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w₂))]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w₂))]
    (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂) :
    chartNorm B S hS (hrep.snd w₂) ⟶ chartNorm B S hS (hrep.snd w₁) :=
  chartNormMap B S hS (hrep.snd w₁) (hrep.snd w₂) k (chartMap B S hS hrep k hk)
    (chartMap_comp_snd B S hS hrep k hk)

section

variable {w₁ : yoneda.obj W₁ ⟶ Y} {w₂ : yoneda.obj W₂ ⟶ Y} {w₃ : yoneda.obj W₃ ⟶ Y}
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w₁))]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w₁))]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w₂))]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w₂))]

/-- The induced morphism of chart normalizations commutes with the canonical morphisms from the
chart sources. -/
@[reassoc]
lemma chartNormUnit_comp_normChartMap (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂) :
    chartNormUnit B S hS (hrep.snd w₂) ≫ normChartMap B S hS hrep k hk =
      chartMap B S hS hrep k hk ≫ chartNormUnit B S hS (hrep.snd w₁) :=
  chartNormUnit_comp_chartNormMap B S hS _ _ _ _ _

/-- The induced morphism of chart normalizations commutes with the normalization morphisms of
the charts. -/
@[reassoc]
lemma normChartMap_comp_chartNormProj (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂) :
    normChartMap B S hS hrep k hk ≫ chartNormProj B S hS (hrep.snd w₁) =
      chartNormProj B S hS (hrep.snd w₂) ≫ k :=
  chartNormMap_comp_chartNormProj B S hS _ _ _ _ _

/-- **The induced morphisms of chart normalizations carry identities to identities.** -/
lemma normChartMap_id :
    normChartMap B S hS hrep (𝟙 W₁) (by simp : yoneda.map (𝟙 W₁) ≫ w₁ = w₁) =
      𝟙 (chartNorm B S hS (hrep.snd w₁)) := by
  refine chartNorm_hom_ext B S hS (hrep.snd w₁) (hrep.snd w₁) (𝟙 W₁) (𝟙 _) (by simp) _ _ ?_ ?_
    (by simp) (by simp)
  · rw [chartNormUnit_comp_normChartMap, chartMap_id]
  · rw [normChartMap_comp_chartNormProj]

/-- **The induced morphisms of chart normalizations compose.** This is the cocycle condition of
the descent datum the chart normalizations form. -/
lemma normChartMap_comp
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w₃))]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w₃))]
    (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂)
    (k' : W₃ ⟶ W₂) (hk' : yoneda.map k' ≫ w₂ = w₃) :
    normChartMap B S hS hrep k' hk' ≫ normChartMap B S hS hrep k hk =
      normChartMap B S hS hrep (k' ≫ k)
        (by rw [Functor.map_comp, Category.assoc, hk, hk']) := by
  rw [normChartMap, normChartMap, normChartMap, chartNormMap_comp]
  exact chartNormMap_congr_hom B S hS (hrep.snd w₁) (hrep.snd w₃) (k' ≫ k) _ _ _ _
    (chartMap_comp B S hS hrep k hk k' hk')

/-- **The induced morphisms of chart normalizations depend only on the morphism of the bases.**
Two morphisms over the same `k` agree, the compatibility being a proposition. -/
lemma normChartMap_congr (k k' : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂)
    (hk' : yoneda.map k' ≫ w₁ = w₂) (h : k = k') :
    normChartMap B S hS hrep k hk = normChartMap B S hS hrep k' hk' := by
  subst h; rfl

/-- **The square of chart normalizations over an étale `k` is cartesian**, read on underlying
schemes. This is Tag 03GV. -/
lemma isPullback_toScheme_map_normChartMap (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂)
    [Etale ((BigFppfOver.toScheme B S hS).map k)] :
    IsPullback ((BigFppfOver.toScheme B S hS).map (normChartMap B S hS hrep k hk))
      ((BigFppfOver.toScheme B S hS).map (chartNormProj B S hS (hrep.snd w₂)))
      ((BigFppfOver.toScheme B S hS).map (chartNormProj B S hS (hrep.snd w₁)))
      ((BigFppfOver.toScheme B S hS).map k) := by
  have _ : Smooth ((BigFppfOver.toScheme B S hS).map k) := inferInstance
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  exact isPullback_toScheme_map_chartNormMap_of_smooth B S hS (hrep.snd w₁) (hrep.snd w₂) k
    (chartMap B S hS hrep k hk) (chartMap_comp_snd B S hS hrep k hk)
    ((isPullback_chartMap B S hS hrep k hk).map (BigFppfOver.toScheme B S hS))

/-- **The square of chart normalizations over an étale `k` is cartesian**, as a square of the
site. The forgetful functor to schemes preserves fibre products and reflects isomorphisms, so
it reflects them too. -/
lemma isPullback_normChartMap (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂)
    [Etale ((BigFppfOver.toScheme B S hS).map k)] :
    IsPullback (normChartMap B S hS hrep k hk) (chartNormProj B S hS (hrep.snd w₂))
      (chartNormProj B S hS (hrep.snd w₁)) k := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : ReflectsLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (isPullback_toScheme_map_normChartMap B S hS hrep k hk)

/-- **The square of chart normalizations over an étale `k` is cartesian**, as a square of
presheaves. -/
lemma isPullback_yoneda_map_normChartMap (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂)
    [Etale ((BigFppfOver.toScheme B S hS).map k)] :
    IsPullback (yoneda.map (normChartMap B S hS hrep k hk))
      (yoneda.map (chartNormProj B S hS (hrep.snd w₂)))
      (yoneda.map (chartNormProj B S hS (hrep.snd w₁))) (yoneda.map k) :=
  (isPullback_normChartMap B S hS hrep k hk).map yoneda

/-- The induced morphism of chart normalizations over an étale `k` is étale. -/
lemma etale_toScheme_map_normChartMap (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂)
    [Etale ((BigFppfOver.toScheme B S hS).map k)] :
    Etale ((BigFppfOver.toScheme B S hS).map (normChartMap B S hS hrep k hk)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Etale.{u})
    (isPullback_toScheme_map_normChartMap B S hS hrep k hk).flip inferInstance

end

end AlgebraicGeometry.Space.NormalizationGluing

end
