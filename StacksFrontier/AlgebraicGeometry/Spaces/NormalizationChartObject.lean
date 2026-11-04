module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FunctorialComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInConstruction

/-!
# The normalizations of the charts of a morphism, as a descent datum in the site

The chart condition of `AlgebraicGeometry.Space.NormalizationInData` asks, of an étale scheme
chart `w : W ⟶ Y` of the target and a representation of the fibre product `W ×_Y X` by a scheme
`XW` of the big fppf site of `S`, that the fibre product `W ×_Y Y'` be represented by an object
of the site whose underlying scheme is the relative normalization of `XW ⟶ W`. Two of the four
clauses of that condition are about the chart alone and no global `Y'` enters them. This file
constructs the object and proves those two clauses, for *every* chart, and assembles the
transition morphisms between the chart normalizations into a descent datum.

Let `p : XW ⟶ W` be a morphism of the site whose underlying morphism of schemes is
quasi-compact and quasi-separated. `AlgebraicGeometry.Space.chartNorm` is its relative
normalization, read in the site: the size bound
`AlgebraicGeometry.Scheme.Hom.size_normalization_le` of the missing clause of Tag 000R makes
the containment free, through `AlgebraicGeometry.Space.contains_normalization`. A morphism of
charts — a commutative square from `p₂` to `p₁` — induces
`AlgebraicGeometry.Space.chartNormMap`, the canonical morphism of Tag 035J read in the site.
These transition morphisms compose, carry identities to identities, are rigid, and are
cartesian whenever the morphism of bases is smooth; that is a descent datum on the chart
normalizations along any étale covering of `Y`, with the cocycle condition supplied by
functoriality.

## Main definitions

* `AlgebraicGeometry.Space.siteHom` is the constructive form of
  `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`: a morphism of the underlying schemes
  of two objects of the site which commutes with the structure morphisms to `S`, read as a
  morphism of the site.  It is `AlgebraicGeometry.BigFppfOver.homMk` with the target an
  arbitrary object instead of one presented by
  `AlgebraicGeometry.BigFppfOver.mk`.
* `AlgebraicGeometry.Space.chartNorm` is the relative normalization of a quasi-compact
  quasi-separated morphism of the site, as an object of the site, with
  `AlgebraicGeometry.Space.chartNormProj` the normalization morphism and
  `AlgebraicGeometry.Space.chartNormUnit` the canonical morphism from the source.
* `AlgebraicGeometry.Space.chartNormMap` is the transition morphism of a morphism of charts.

## Main results

* `AlgebraicGeometry.Space.chartNormUnit_comp_chartNormProj`: the two morphisms factor the
  chart.
* `AlgebraicGeometry.Space.chartNormUnit_comp_chartNormMap` and
  `AlgebraicGeometry.Space.chartNormMap_comp_chartNormProj`: the transition morphism commutes
  with the morphisms from the sources and with the normalization morphisms.
* `AlgebraicGeometry.Space.chartNormMap_id` and
  `AlgebraicGeometry.Space.chartNormMap_comp`: the transition morphisms are functorial. The
  second is the cocycle condition of the descent datum.
* `AlgebraicGeometry.Space.chartNorm_hom_ext`: rigidity. A morphism of chart normalizations
  over a given morphism of charts, commuting with the two structural morphisms, is unique.
* `AlgebraicGeometry.Space.chartNormMap_comp_eq_id`: a morphism of charts with a section has a
  transition morphism with a section. On the relation `R = W ×_Y W` of an étale covering of the
  target this is the reflexivity and the symmetry of the descent datum.
* `AlgebraicGeometry.Space.isPullback_toScheme_map_chartNormMap_of_smooth` and
  `AlgebraicGeometry.Space.etale_toScheme_map_chartNormMap`: the transition morphism of a
  cartesian morphism of charts with smooth base morphism is cartesian, and étale when the base
  morphism is.
* `AlgebraicGeometry.Space.exists_chart_of_isPullback`: the conclusion of the chart condition
  of `AlgebraicGeometry.Space.NormalizationInData` at an arbitrary chart, granted a morphism
  from the chart normalization to the normalization which is cartesian over the chart and
  compatible with the canonical morphism. The two clauses naming the relative normalization of
  the chart are discharged outright, with the identity as the comparison isomorphism; what the
  hypotheses still carry is exactly the two clauses that mention the global object.

## Implementation notes

**Why `change` and not `rw`.** `AlgebraicGeometry.Space.toScheme_obj_chartNorm` holds by `rfl`,
but the two spellings of that scheme are not syntactically equal, so a rewrite which replaces
`AlgebraicGeometry.Space.chartNormProj` by `AlgebraicGeometry.Scheme.Hom.fromNormalization`
inside a composite leaves a term whose middle object has the other spelling, and that term is
not type-correct at the transparency the rewriting tactics check at. The identities which have
to be computed on underlying schemes therefore move there with
`CategoryTheory.Functor.map_injective` and a `change`, which elaborates up to definitional
unfolding, and only then compute. The identities derived from those — the retraction law and
the two étaleness and cartesianness statements — are proved in the site and need no such
transport.

Tag 035J is `AlgebraicGeometry.Scheme.Hom.normalizationMap` with its lemmas, and Tag 03GV is
`AlgebraicGeometry.isPullback_normalizationMap_of_smooth`; this file reads them in the site,
which is a change of shape and not a new assertion. Tag 0ABP, part (1), is the assertion that
the fibre product of the normalization morphism with an étale morphism *is* the normalization of
the base change; it is about the normalization of Tag 0822 and mentions the global object, which
does not occur in this file.

## References

* [Stacks Project, Tag 035J](https://stacks.math.columbia.edu/tag/035J)
* [Stacks Project, Tag 035E](https://stacks.math.columbia.edu/tag/035E)
* [Stacks Project, Tag 03GV](https://stacks.math.columbia.edu/tag/03GV)
* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms of the site from morphisms of the underlying schemes -/

/-- A morphism between the underlying schemes of two objects of the big fppf category over `S`
which commutes with their structure morphisms, read as a morphism of the category. The functor
to schemes is faithful but not full, and the compatibility is exactly what makes a morphism of
schemes a morphism of the slice.

This is the constructive form of `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`, and it
is `AlgebraicGeometry.BigFppfOver.homMk` with the target an arbitrary object rather than one
presented by `AlgebraicGeometry.BigFppfOver.mk`.  It is built from
`CategoryTheory.ObjectProperty.homMk` and not from the fullness of the site's inclusion into
schemes, which is what makes `AlgebraicGeometry.Space.toScheme_map_siteHom` hold by `rfl`; that
in turn is what lets every proof below pass between the site and the schemes by
definitional unfolding alone. -/
def siteHom {A C : BigFppfOver B S hS}
    (φ : (BigFppfOver.toScheme B S hS).obj A ⟶ (BigFppfOver.toScheme B S hS).obj C)
    (hφ : φ ≫ B.inclusion.map C.hom = B.inclusion.map A.hom) : A ⟶ C :=
  Over.homMk (ObjectProperty.homMk φ) (by apply ObjectProperty.hom_ext; exact hφ)

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.siteHom` is the given one. -/
lemma toScheme_map_siteHom {A C : BigFppfOver B S hS}
    (φ : (BigFppfOver.toScheme B S hS).obj A ⟶ (BigFppfOver.toScheme B S hS).obj C)
    (hφ : φ ≫ B.inclusion.map C.hom = B.inclusion.map A.hom) :
    (BigFppfOver.toScheme B S hS).map (siteHom B S hS φ hφ) = φ :=
  rfl

/-! ### The normalization object of a chart -/

variable {W₁ W₂ W₃ XW₁ XW₂ XW₃ : BigFppfOver B S hS}

/-- **The relative normalization of a morphism of the big fppf site, as an object of the
site.** Containment is free: the size of a relative normalization is bounded by the maximum of
the sizes of the source and the target, so
`AlgebraicGeometry.Space.contains_normalization` discharges it with no hypothesis. -/
def chartNorm (p₁ : XW₁ ⟶ W₁)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map p₁)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map p₁)] :
    BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_normalization B S hS XW₁ W₁ p₁)
    (((BigFppfOver.toScheme B S hS).map p₁).fromNormalization ≫ B.inclusion.map W₁.hom)

/-- The underlying scheme of the chart normalization is the relative normalization. -/
lemma toScheme_obj_chartNorm (p₁ : XW₁ ⟶ W₁)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map p₁)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map p₁)] :
    (BigFppfOver.toScheme B S hS).obj (chartNorm B S hS p₁) =
      ((BigFppfOver.toScheme B S hS).map p₁).normalization :=
  rfl

/-- The structure morphism of the chart normalization is the normalization morphism followed
by the structure morphism of the base. -/
lemma inclusion_hom_chartNorm (p₁ : XW₁ ⟶ W₁)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map p₁)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map p₁)] :
    B.inclusion.map (chartNorm B S hS p₁).hom =
      ((BigFppfOver.toScheme B S hS).map p₁).fromNormalization ≫ B.inclusion.map W₁.hom :=
  rfl

variable (p₁ : XW₁ ⟶ W₁) (p₂ : XW₂ ⟶ W₂) (p₃ : XW₃ ⟶ W₃)
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map p₁)]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map p₁)]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map p₂)]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map p₂)]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map p₃)]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map p₃)]

/-- The normalization morphism of a chart, as a morphism of the site. -/
def chartNormProj : chartNorm B S hS p₁ ⟶ W₁ :=
  siteHom B S hS (((BigFppfOver.toScheme B S hS).map p₁).fromNormalization) rfl

/-- The normalization morphism of a chart, read on underlying schemes. -/
lemma toScheme_map_chartNormProj :
    (BigFppfOver.toScheme B S hS).map (chartNormProj B S hS p₁) =
      ((BigFppfOver.toScheme B S hS).map p₁).fromNormalization :=
  toScheme_map_siteHom B S hS _ _

/-- The morphism from the source of a chart into its relative normalization commutes with the
structure morphisms to `S`. -/
lemma toNormalization_comp_structure :
    ((BigFppfOver.toScheme B S hS).map p₁).toNormalization ≫
        (((BigFppfOver.toScheme B S hS).map p₁).fromNormalization ≫
          B.inclusion.map W₁.hom) =
      B.inclusion.map XW₁.hom := by
  rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization,
    toScheme_map_comp_inclusion_hom]

/-- The canonical morphism from the source of a chart into its normalization, as a morphism of
the site. -/
def chartNormUnit : XW₁ ⟶ chartNorm B S hS p₁ :=
  siteHom B S hS (((BigFppfOver.toScheme B S hS).map p₁).toNormalization)
    (toNormalization_comp_structure B S hS p₁)

/-- The canonical morphism into the chart normalization, read on underlying schemes. -/
lemma toScheme_map_chartNormUnit :
    (BigFppfOver.toScheme B S hS).map (chartNormUnit B S hS p₁) =
      ((BigFppfOver.toScheme B S hS).map p₁).toNormalization :=
  toScheme_map_siteHom B S hS _ _

/-- The two structural morphisms of the chart normalization factor the chart. -/
lemma chartNormUnit_comp_chartNormProj :
    chartNormUnit B S hS p₁ ≫ chartNormProj B S hS p₁ = p₁ := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, toScheme_map_chartNormUnit, toScheme_map_chartNormProj]
  exact Scheme.Hom.toNormalization_fromNormalization _

/-! ### The transition morphism of a morphism of charts -/

omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map p₁)]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map p₁)]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map p₂)]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map p₂)] in
/-- A morphism of charts, read on underlying schemes. -/
lemma toScheme_map_sq (k : W₂ ⟶ W₁) (κ : XW₂ ⟶ XW₁) (sq : κ ≫ p₁ = p₂ ≫ k) :
    (BigFppfOver.toScheme B S hS).map κ ≫ (BigFppfOver.toScheme B S hS).map p₁ =
      (BigFppfOver.toScheme B S hS).map p₂ ≫ (BigFppfOver.toScheme B S hS).map k := by
  rw [← Functor.map_comp, ← Functor.map_comp, sq]

/-- The canonical morphism of relative normalizations attached to a morphism of charts commutes
with the structure morphisms to `S`. -/
lemma normalizationMap_comp_structure (k : W₂ ⟶ W₁) (κ : XW₂ ⟶ XW₁)
    (sq : κ ≫ p₁ = p₂ ≫ k) :
    Scheme.Hom.normalizationMap ((BigFppfOver.toScheme B S hS).map p₁)
          ((BigFppfOver.toScheme B S hS).map p₂) ((BigFppfOver.toScheme B S hS).map κ)
          ((BigFppfOver.toScheme B S hS).map k)
          (toScheme_map_sq B S hS p₁ p₂ k κ sq) ≫
        (((BigFppfOver.toScheme B S hS).map p₁).fromNormalization ≫
          B.inclusion.map W₁.hom) =
      ((BigFppfOver.toScheme B S hS).map p₂).fromNormalization ≫ B.inclusion.map W₂.hom := by
  rw [← Category.assoc, Scheme.Hom.normalizationMap_fromNormalization, Category.assoc,
    toScheme_map_comp_inclusion_hom]

/-- **The canonical morphism of chart normalizations attached to a morphism of charts**, as a
morphism of the site. This is the canonical morphism of Tag 035J of the commutative square
which the morphism of charts is. -/
def chartNormMap (k : W₂ ⟶ W₁) (κ : XW₂ ⟶ XW₁) (sq : κ ≫ p₁ = p₂ ≫ k) :
    chartNorm B S hS p₂ ⟶ chartNorm B S hS p₁ :=
  siteHom B S hS
    (Scheme.Hom.normalizationMap ((BigFppfOver.toScheme B S hS).map p₁)
      ((BigFppfOver.toScheme B S hS).map p₂) ((BigFppfOver.toScheme B S hS).map κ)
      ((BigFppfOver.toScheme B S hS).map k)
      (toScheme_map_sq B S hS p₁ p₂ k κ sq))
    (normalizationMap_comp_structure B S hS p₁ p₂ k κ sq)

/-- The transition morphism of a morphism of charts, read on underlying schemes. -/
lemma toScheme_map_chartNormMap (k : W₂ ⟶ W₁) (κ : XW₂ ⟶ XW₁) (sq : κ ≫ p₁ = p₂ ≫ k) :
    (BigFppfOver.toScheme B S hS).map (chartNormMap B S hS p₁ p₂ k κ sq) =
      Scheme.Hom.normalizationMap ((BigFppfOver.toScheme B S hS).map p₁)
        ((BigFppfOver.toScheme B S hS).map p₂) ((BigFppfOver.toScheme B S hS).map κ)
        ((BigFppfOver.toScheme B S hS).map k)
        (toScheme_map_sq B S hS p₁ p₂ k κ sq) :=
  toScheme_map_siteHom B S hS _ _

/-- The transition morphism commutes with the morphisms from the sources of the charts. -/
lemma chartNormUnit_comp_chartNormMap (k : W₂ ⟶ W₁) (κ : XW₂ ⟶ XW₁) (sq : κ ≫ p₁ = p₂ ≫ k) :
    chartNormUnit B S hS p₂ ≫ chartNormMap B S hS p₁ p₂ k κ sq =
      κ ≫ chartNormUnit B S hS p₁ := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_chartNormUnit, toScheme_map_chartNormMap,
    toScheme_map_chartNormUnit]
  exact Scheme.Hom.toNormalization_normalizationMap _ _ _ _ _

/-- The transition morphism commutes with the normalization morphisms of the charts. -/
lemma chartNormMap_comp_chartNormProj (k : W₂ ⟶ W₁) (κ : XW₂ ⟶ XW₁) (sq : κ ≫ p₁ = p₂ ≫ k) :
    chartNormMap B S hS p₁ p₂ k κ sq ≫ chartNormProj B S hS p₁ =
      chartNormProj B S hS p₂ ≫ k := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_chartNormMap, toScheme_map_chartNormProj,
    toScheme_map_chartNormProj]
  exact Scheme.Hom.normalizationMap_fromNormalization _ _ _ _ _

/-- The transition morphism of the identity morphism of charts is the identity. -/
lemma chartNormMap_id : chartNormMap B S hS p₁ p₁ (𝟙 W₁) (𝟙 XW₁) (by simp) =
    𝟙 (chartNorm B S hS p₁) := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  exact (toScheme_map_chartNormMap B S hS p₁ p₁ _ _ _).trans
    (Scheme.Hom.normalizationMap_id _)

/-- **The transition morphisms compose.** This is the cocycle condition of the descent datum
the chart normalizations form. -/
lemma chartNormMap_comp (k : W₂ ⟶ W₁) (κ : XW₂ ⟶ XW₁) (sq : κ ≫ p₁ = p₂ ≫ k)
    (k' : W₃ ⟶ W₂) (κ' : XW₃ ⟶ XW₂) (sq' : κ' ≫ p₂ = p₃ ≫ k') :
    chartNormMap B S hS p₂ p₃ k' κ' sq' ≫ chartNormMap B S hS p₁ p₂ k κ sq =
      chartNormMap B S hS p₁ p₃ (k' ≫ k) (κ' ≫ κ)
        (by rw [Category.assoc, sq, ← Category.assoc, sq', Category.assoc]) := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, toScheme_map_chartNormMap, toScheme_map_chartNormMap,
    toScheme_map_chartNormMap]
  exact Scheme.Hom.normalizationMap_comp _ _ _ _ _ _ _ _ _

/-- **Rigidity of the transition morphisms.** Two morphisms of chart normalizations in the site
which commute with the morphisms from the sources of the charts and with the normalization
morphisms of the charts, over the same morphism of charts, are equal. This is Tag 035J's
uniqueness clause read in the site. -/
lemma chartNorm_hom_ext (k : W₂ ⟶ W₁) (κ : XW₂ ⟶ XW₁) (sq : κ ≫ p₁ = p₂ ≫ k)
    (h h' : chartNorm B S hS p₂ ⟶ chartNorm B S hS p₁)
    (hs : chartNormUnit B S hS p₂ ≫ h = κ ≫ chartNormUnit B S hS p₁)
    (ht : h ≫ chartNormProj B S hS p₁ = chartNormProj B S hS p₂ ≫ k)
    (hs' : chartNormUnit B S hS p₂ ≫ h' = κ ≫ chartNormUnit B S hS p₁)
    (ht' : h' ≫ chartNormProj B S hS p₁ = chartNormProj B S hS p₂ ≫ k) :
    h = h' := by
  have key : ∀ g : chartNorm B S hS p₂ ⟶ chartNorm B S hS p₁,
      chartNormUnit B S hS p₂ ≫ g = κ ≫ chartNormUnit B S hS p₁ →
      g ≫ chartNormProj B S hS p₁ = chartNormProj B S hS p₂ ≫ k →
      (BigFppfOver.toScheme B S hS).map g = (BigFppfOver.toScheme B S hS).map
        (chartNormMap B S hS p₁ p₂ k κ sq) := fun g hs ht =>
    Scheme.Hom.normalizationMap_unique _ _ _ _ (toScheme_map_sq B S hS p₁ p₂ k κ sq) _
      (congrArg (BigFppfOver.toScheme B S hS).map hs)
      (congrArg (BigFppfOver.toScheme B S hS).map ht)
  exact (BigFppfOver.toScheme B S hS).map_injective ((key h hs ht).trans (key h' hs' ht').symm)

/-- **A retraction of charts gives a retraction of chart normalizations.** If a morphism of
charts has a section, then so does its transition morphism, with the transition morphism of the
section as the section.

Read on the relation `R = W ×_Y W` of an étale covering of the target, this is both the
reflexivity and the symmetry of the descent datum the chart normalizations form: the diagonal
of `R` is a section of each projection, and the swap of `R` interchanges them. -/
lemma chartNormMap_comp_eq_id (k : W₂ ⟶ W₁) (κ : XW₂ ⟶ XW₁) (sq : κ ≫ p₁ = p₂ ≫ k)
    (k' : W₁ ⟶ W₂) (κ' : XW₁ ⟶ XW₂) (sq' : κ' ≫ p₂ = p₁ ≫ k')
    (hk : k' ≫ k = 𝟙 W₁) (hκ : κ' ≫ κ = 𝟙 XW₁) :
    chartNormMap B S hS p₂ p₁ k' κ' sq' ≫ chartNormMap B S hS p₁ p₂ k κ sq =
      𝟙 (chartNorm B S hS p₁) := by
  refine chartNorm_hom_ext B S hS p₁ p₁ (𝟙 W₁) (𝟙 XW₁) (by simp) _ _ ?_ ?_ (by simp) (by simp)
  · rw [← Category.assoc, chartNormUnit_comp_chartNormMap, Category.assoc,
      chartNormUnit_comp_chartNormMap, ← Category.assoc, hκ]
  · rw [Category.assoc, chartNormMap_comp_chartNormProj, ← Category.assoc,
      chartNormMap_comp_chartNormProj, Category.assoc, hk]

/-! ### Cartesianness along a smooth morphism of charts -/

/-- **The transition morphism of a smooth morphism of charts is cartesian.** For a cartesian
square of charts whose morphism of bases is smooth, the square formed by the transition
morphism and the two normalization morphisms is cartesian: the normalization of the smaller
chart is the fibre product of the normalization of the larger one with the smaller base.

This is `AlgebraicGeometry.isPullback_normalizationMap_of_smooth`, that is Tag 03GV, read in
the site. -/
lemma isPullback_toScheme_map_chartNormMap_of_smooth (k : W₂ ⟶ W₁) (κ : XW₂ ⟶ XW₁)
    (sq : κ ≫ p₁ = p₂ ≫ k) [Smooth ((BigFppfOver.toScheme B S hS).map k)]
    (hsq : IsPullback ((BigFppfOver.toScheme B S hS).map κ)
      ((BigFppfOver.toScheme B S hS).map p₂) ((BigFppfOver.toScheme B S hS).map p₁)
      ((BigFppfOver.toScheme B S hS).map k)) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (chartNormMap B S hS p₁ p₂ k κ sq))
      ((BigFppfOver.toScheme B S hS).map (chartNormProj B S hS p₂))
      ((BigFppfOver.toScheme B S hS).map (chartNormProj B S hS p₁))
      ((BigFppfOver.toScheme B S hS).map k) := by
  rw [toScheme_map_chartNormMap, toScheme_map_chartNormProj, toScheme_map_chartNormProj]
  exact isPullback_normalizationMap_of_smooth ((BigFppfOver.toScheme B S hS).map p₁)
    ((BigFppfOver.toScheme B S hS).map k) hsq

/-- The transition morphism of a cartesian étale morphism of charts is étale, being a base
change of the morphism of bases. -/
lemma etale_toScheme_map_chartNormMap (k : W₂ ⟶ W₁) (κ : XW₂ ⟶ XW₁) (sq : κ ≫ p₁ = p₂ ≫ k)
    [Etale ((BigFppfOver.toScheme B S hS).map k)]
    (hsq : IsPullback ((BigFppfOver.toScheme B S hS).map κ)
      ((BigFppfOver.toScheme B S hS).map p₂) ((BigFppfOver.toScheme B S hS).map p₁)
      ((BigFppfOver.toScheme B S hS).map k)) :
    Etale ((BigFppfOver.toScheme B S hS).map (chartNormMap B S hS p₁ p₂ k κ sq)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Etale.{u})
    (isPullback_toScheme_map_chartNormMap_of_smooth B S hS p₁ p₂ k κ sq hsq).flip inferInstance

/-! ### The chart condition at an arbitrary chart -/

/-- **The conclusion of the chart condition of
`AlgebraicGeometry.Space.NormalizationInData` at an arbitrary chart**, granted a morphism from
the chart normalization to the normalization which is cartesian over the chart and compatible
with the canonical morphism.

Two of the four clauses — that the object's underlying scheme is the relative normalization of
the chart, compatibly with both legs — are discharged outright, with the identity as the
comparison isomorphism, for *every* étale chart and with no surjectivity and no size
hypothesis. The two clauses that remain as hypotheses are exactly the two that mention the
global object: the cartesian square over the chart, and the compatibility of the canonical
morphism. -/
theorem exists_chart_of_isPullback {X Y N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (toNorm : X ⟶ N) (fromNorm : N ⟶ Y)
    {W XW : BigFppfOver B S hS} (w : yoneda.obj W ⟶ Y) (p : XW ⟶ W) (a : yoneda.obj XW ⟶ X)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map p)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map p)]
    (b : yoneda.obj (chartNorm B S hS p) ⟶ N)
    (hb : IsPullback b (yoneda.map (chartNormProj B S hS p)) fromNorm w)
    (hr : yoneda.map (chartNormUnit B S hS p) ≫ b = a ≫ toNorm) :
    ∃ (W' : BigFppfOver B S hS) (q : W' ⟶ W) (b' : yoneda.obj W' ⟶ N) (r : XW ⟶ W')
      (e : (BigFppfOver.toScheme B S hS).obj W' ≅
        ((BigFppfOver.toScheme B S hS).map p).normalization),
      IsPullback b' (yoneda.map q) fromNorm w ∧
      yoneda.map r ≫ b' = a ≫ toNorm ∧
      (BigFppfOver.toScheme B S hS).map r ≫ e.hom =
        ((BigFppfOver.toScheme B S hS).map p).toNormalization ∧
      e.hom ≫ ((BigFppfOver.toScheme B S hS).map p).fromNormalization =
        (BigFppfOver.toScheme B S hS).map q :=
  ⟨chartNorm B S hS p, chartNormProj B S hS p, b, chartNormUnit B S hS p, Iso.refl _, hb, hr,
    (Category.comp_id _).trans (toScheme_map_chartNormUnit B S hS p),
    (Category.id_comp _).trans (toScheme_map_chartNormProj B S hS p).symm⟩

end AlgebraicGeometry.Space

end
