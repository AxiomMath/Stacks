module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationChartFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient

/-!
# The chart normalizations along an étale presentation form an étale equivalence relation

Let `f : X ⟶ Y` be a relatively representable morphism of presheaves on the big fppf site of a
scheme `S`, let `w : h_U ⟶ Y` be a chart of `Y` and let `pr₁, pr₂ : R ⟶ U` exhibit `R` as the
self-fibre-product `U ×_Y U`. Over each of `U`, `R` and the triple fibre product `R ×_U R` the
morphism `f` has a chart, and the chart normalizations `AlgebraicGeometry.Space.chartNorm` are
related by the morphisms induced by the projections.

This file proves that the two morphisms `N(R) ⇉ N(U)` so obtained are an *equivalence relation*
of presheaves: jointly monic, with the reflexivity, symmetry and transitivity morphisms induced
by the diagonal, the swap and the composition of `R ×_U R`. For an étale `w` the two morphisms
are étale, so the relation is an étale equivalence relation of schemes over `S` in the sense of
Tag 02WS, and Tag 02WW applies to its quotient sheaf.

## Main definitions

* `AlgebraicGeometry.Space.NormalizationGluing.relDiag`,
  `AlgebraicGeometry.Space.NormalizationGluing.relSwap` and
  `AlgebraicGeometry.Space.NormalizationGluing.rel₂Outer` are the diagonal, the swap and the
  composition of the relation `R = U ×_Y U`.
* `AlgebraicGeometry.Space.NormalizationGluing.normRelFst` and
  `AlgebraicGeometry.Space.NormalizationGluing.normRelSnd` are the two morphisms `N(R) ⇉ N(U)` of
  chart normalizations which the relation induces.

## Main results

* `AlgebraicGeometry.Space.NormalizationGluing.jointlyMono₂_normRel`: the two induced morphisms
  are jointly monic.
* `AlgebraicGeometry.Space.NormalizationGluing.isPullback_normRel₂`: the chart normalization of
  `R ×_U R` is the fibre product of two copies of that of `R` over that of `U`, which is the
  limiting cone transitivity needs.
* `AlgebraicGeometry.Space.NormalizationGluing.equivalenceRelation_normRel`: the two induced
  morphisms form an internal equivalence relation of presheaves.
* `AlgebraicGeometry.Space.NormalizationGluing.isEtaleEquivalenceRelation_normRel`: for an étale
  chart of `Y` the relation is an étale equivalence relation over `S`, in the sense of Tag 02WS.

## Implementation notes

The diagonal, the swap and the composition of the relation are built from the universal
property of the cartesian square `R = U ×_Y U`, not from a choice of fibre product in the site;
the triple fibre product is the site's own `R ×_U R`, which exists because the big fppf category
over `S` has fibre products.

All three transitivity identities, and both reflexivity and both symmetry identities, are
instances of the functoriality `AlgebraicGeometry.Space.NormalizationGluing.normChartMap_comp`
of Tag 035J together with an identity between the corresponding morphisms of the bases: no new
computation with normalizations is involved.

## References

* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
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
  {U R : BigFppfOver B S hS} (w : yoneda.obj U ⟶ Y) (pr₁ pr₂ : R ⟶ U)

/-! ### The structural morphisms of the relation `R = U ×_Y U` -/

/-- The structure morphism of `R = U ×_Y U` to `Y`, read through the first projection. -/
def relBase : yoneda.obj R ⟶ Y := yoneda.map pr₁ ≫ w

/-- The structure morphism of the triple fibre product `R ×_U R` to `Y`. -/
def rel₂Base : yoneda.obj (Limits.pullback pr₂ pr₁) ⟶ Y :=
  yoneda.map (Limits.pullback.fst pr₂ pr₁) ≫ relBase B S hS w pr₁

variable (hsq : IsPullback (yoneda.map pr₁) (yoneda.map pr₂) w w)

/-- The first projection of `R` followed by the chart is the structure morphism of `R`. -/
lemma yoneda_map_pr₁_comp : yoneda.map pr₁ ≫ w = relBase B S hS w pr₁ := rfl

include hsq in
/-- The second projection of `R` followed by the chart is the structure morphism of `R`. -/
lemma yoneda_map_pr₂_comp : yoneda.map pr₂ ≫ w = relBase B S hS w pr₁ := hsq.w.symm

/-- The diagonal `U ⟶ R` of the relation. -/
def relDiag : U ⟶ R :=
  yoneda.preimage (hsq.lift (𝟙 (yoneda.obj U)) (𝟙 (yoneda.obj U)) rfl)

/-- The diagonal followed by the first projection is the identity. -/
@[reassoc]
lemma relDiag_comp_pr₁ : relDiag B S hS w pr₁ pr₂ hsq ≫ pr₁ = 𝟙 U :=
  yoneda.map_injective (by simp [relDiag])

/-- The diagonal followed by the second projection is the identity. -/
@[reassoc]
lemma relDiag_comp_pr₂ : relDiag B S hS w pr₁ pr₂ hsq ≫ pr₂ = 𝟙 U :=
  yoneda.map_injective (by simp [relDiag])

/-- The swap `R ⟶ R` of the relation, interchanging the two projections. -/
def relSwap : R ⟶ R :=
  yoneda.preimage (hsq.lift (yoneda.map pr₂) (yoneda.map pr₁) hsq.w.symm)

/-- The swap followed by the first projection is the second projection. -/
@[reassoc]
lemma relSwap_comp_pr₁ : relSwap B S hS w pr₁ pr₂ hsq ≫ pr₁ = pr₂ :=
  yoneda.map_injective (by simp [relSwap])

/-- The swap followed by the second projection is the first projection. -/
@[reassoc]
lemma relSwap_comp_pr₂ : relSwap B S hS w pr₁ pr₂ hsq ≫ pr₂ = pr₁ :=
  yoneda.map_injective (by simp [relSwap])

include hsq in
/-- The two projections of the triple fibre product agree on the middle factor, read over
`Y`. -/
lemma rel₂_middle_comp :
    yoneda.map (Limits.pullback.fst pr₂ pr₁ ≫ pr₁) ≫ w =
      yoneda.map (Limits.pullback.snd pr₂ pr₁ ≫ pr₂) ≫ w := by
  calc yoneda.map (Limits.pullback.fst pr₂ pr₁ ≫ pr₁) ≫ w
      = yoneda.map (Limits.pullback.fst pr₂ pr₁) ≫ yoneda.map pr₁ ≫ w := by
        rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = yoneda.map (Limits.pullback.fst pr₂ pr₁) ≫ yoneda.map pr₂ ≫ w := by rw [hsq.w]
    _ = yoneda.map (Limits.pullback.fst pr₂ pr₁ ≫ pr₂) ≫ w := by
        rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = yoneda.map (Limits.pullback.snd pr₂ pr₁ ≫ pr₁) ≫ w := by rw [Limits.pullback.condition]
    _ = yoneda.map (Limits.pullback.snd pr₂ pr₁) ≫ yoneda.map pr₁ ≫ w := by
        rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = yoneda.map (Limits.pullback.snd pr₂ pr₁) ≫ yoneda.map pr₂ ≫ w := by rw [hsq.w]
    _ = yoneda.map (Limits.pullback.snd pr₂ pr₁ ≫ pr₂) ≫ w := by
        rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- The composition `R ×_U R ⟶ R` of the relation: the outer pair of the three points. -/
def rel₂Outer : Limits.pullback pr₂ pr₁ ⟶ R :=
  yoneda.preimage (hsq.lift (yoneda.map (Limits.pullback.fst pr₂ pr₁ ≫ pr₁))
    (yoneda.map (Limits.pullback.snd pr₂ pr₁ ≫ pr₂)) (rel₂_middle_comp B S hS w pr₁ pr₂ hsq))

/-- The composition followed by the first projection is the first projection of the first
factor. -/
@[reassoc]
lemma rel₂Outer_comp_pr₁ :
    rel₂Outer B S hS w pr₁ pr₂ hsq ≫ pr₁ = Limits.pullback.fst pr₂ pr₁ ≫ pr₁ :=
  yoneda.map_injective (by simp [rel₂Outer])

/-- The composition followed by the second projection is the second projection of the second
factor. -/
@[reassoc]
lemma rel₂Outer_comp_pr₂ :
    rel₂Outer B S hS w pr₁ pr₂ hsq ≫ pr₂ = Limits.pullback.snd pr₂ pr₁ ≫ pr₂ :=
  yoneda.map_injective (by simp [rel₂Outer])

/-! ### The base morphisms of the three charts -/

/-- The diagonal is a morphism over `Y` from the chart to the relation. -/
lemma yoneda_map_relDiag_comp :
    yoneda.map (relDiag B S hS w pr₁ pr₂ hsq) ≫ relBase B S hS w pr₁ = w := by
  rw [relBase, ← Category.assoc, ← CategoryTheory.Functor.map_comp, relDiag_comp_pr₁,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The swap is a morphism over `Y`. -/
lemma yoneda_map_relSwap_comp :
    yoneda.map (relSwap B S hS w pr₁ pr₂ hsq) ≫ relBase B S hS w pr₁ =
      relBase B S hS w pr₁ := by
  rw [relBase, ← Category.assoc, ← CategoryTheory.Functor.map_comp, relSwap_comp_pr₁]
  exact yoneda_map_pr₂_comp B S hS w pr₁ pr₂ hsq

/-- The first projection of `R ×_U R` is a morphism over `Y`. -/
lemma yoneda_map_rel₂Fst_comp :
    yoneda.map (Limits.pullback.fst pr₂ pr₁) ≫ relBase B S hS w pr₁ =
      rel₂Base B S hS w pr₁ pr₂ := rfl

include hsq in
/-- The second projection of `R ×_U R` is a morphism over `Y`. -/
lemma yoneda_map_rel₂Snd_comp :
    yoneda.map (Limits.pullback.snd pr₂ pr₁) ≫ relBase B S hS w pr₁ =
      rel₂Base B S hS w pr₁ pr₂ := by
  calc yoneda.map (Limits.pullback.snd pr₂ pr₁) ≫ relBase B S hS w pr₁
      = yoneda.map (Limits.pullback.snd pr₂ pr₁ ≫ pr₁) ≫ w := by
        rw [relBase, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
    _ = yoneda.map (Limits.pullback.fst pr₂ pr₁ ≫ pr₂) ≫ w := by rw [Limits.pullback.condition]
    _ = yoneda.map (Limits.pullback.fst pr₂ pr₁) ≫ yoneda.map pr₂ ≫ w := by
        rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = rel₂Base B S hS w pr₁ pr₂ := by
        rw [yoneda_map_pr₂_comp B S hS w pr₁ pr₂ hsq, rel₂Base]

/-- The composition `R ×_U R ⟶ R` is a morphism over `Y`. -/
lemma yoneda_map_rel₂Outer_comp :
    yoneda.map (rel₂Outer B S hS w pr₁ pr₂ hsq) ≫ relBase B S hS w pr₁ =
      rel₂Base B S hS w pr₁ pr₂ := by
  rw [rel₂Base, relBase, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    rel₂Outer_comp_pr₁, CategoryTheory.Functor.map_comp, Category.assoc]


/-! ### The chart normalizations and the induced relation -/

variable [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]

/-- The morphism of chart normalizations induced by the first projection of `R = U ×_Y U`. -/
def normRelFst : chartNorm B S hS (hrep.snd (relBase B S hS w pr₁)) ⟶
    chartNorm B S hS (hrep.snd w) :=
  normChartMap B S hS hrep pr₁ (yoneda_map_pr₁_comp B S hS w pr₁)

/-- The morphism of chart normalizations induced by the second projection of `R = U ×_Y U`. -/
def normRelSnd : chartNorm B S hS (hrep.snd (relBase B S hS w pr₁)) ⟶
    chartNorm B S hS (hrep.snd w) :=
  normChartMap B S hS hrep pr₂ (yoneda_map_pr₂_comp B S hS w pr₁ pr₂ hsq)

/-- The morphism of chart normalizations induced by the diagonal of `R = U ×_Y U`. -/
def normRelDiag : chartNorm B S hS (hrep.snd w) ⟶
    chartNorm B S hS (hrep.snd (relBase B S hS w pr₁)) :=
  normChartMap B S hS hrep (relDiag B S hS w pr₁ pr₂ hsq)
    (yoneda_map_relDiag_comp B S hS w pr₁ pr₂ hsq)

/-- The morphism of chart normalizations induced by the swap of `R = U ×_Y U`. -/
def normRelSwap : chartNorm B S hS (hrep.snd (relBase B S hS w pr₁)) ⟶
    chartNorm B S hS (hrep.snd (relBase B S hS w pr₁)) :=
  normChartMap B S hS hrep (relSwap B S hS w pr₁ pr₂ hsq)
    (yoneda_map_relSwap_comp B S hS w pr₁ pr₂ hsq)

/-- The morphism of chart normalizations induced by the first projection of `R ×_U R`. -/
def normRel₂Fst : chartNorm B S hS (hrep.snd (rel₂Base B S hS w pr₁ pr₂)) ⟶
    chartNorm B S hS (hrep.snd (relBase B S hS w pr₁)) :=
  normChartMap B S hS hrep (Limits.pullback.fst pr₂ pr₁)
    (yoneda_map_rel₂Fst_comp B S hS w pr₁ pr₂)

/-- The morphism of chart normalizations induced by the second projection of `R ×_U R`. -/
def normRel₂Snd : chartNorm B S hS (hrep.snd (rel₂Base B S hS w pr₁ pr₂)) ⟶
    chartNorm B S hS (hrep.snd (relBase B S hS w pr₁)) :=
  normChartMap B S hS hrep (Limits.pullback.snd pr₂ pr₁)
    (yoneda_map_rel₂Snd_comp B S hS w pr₁ pr₂ hsq)

/-- The morphism of chart normalizations induced by the composition of `R ×_U R`. -/
def normRel₂Outer : chartNorm B S hS (hrep.snd (rel₂Base B S hS w pr₁ pr₂)) ⟶
    chartNorm B S hS (hrep.snd (relBase B S hS w pr₁)) :=
  normChartMap B S hS hrep (rel₂Outer B S hS w pr₁ pr₂ hsq)
    (yoneda_map_rel₂Outer_comp B S hS w pr₁ pr₂ hsq)

/-! ### Reflexivity, symmetry and the cocycle identities -/

/-- The composite of two induced morphisms of chart normalizations is the one induced by any
morphism of the bases equal to the composite. -/
private lemma normChartMap_comp_eq {W₁ W₂ W₃ : BigFppfOver B S hS}
    {w₁ : yoneda.obj W₁ ⟶ Y} {w₂ : yoneda.obj W₂ ⟶ Y} {w₃ : yoneda.obj W₃ ⟶ Y}
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w₁))]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w₁))]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w₂))]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w₂))]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w₃))]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w₃))]
    (k : W₂ ⟶ W₁) (hk : yoneda.map k ≫ w₁ = w₂) (k' : W₃ ⟶ W₂) (hk' : yoneda.map k' ≫ w₂ = w₃)
    (m : W₃ ⟶ W₁) (hm : yoneda.map m ≫ w₁ = w₃) (h : k' ≫ k = m) :
    normChartMap B S hS hrep k' hk' ≫ normChartMap B S hS hrep k hk =
      normChartMap B S hS hrep m hm :=
  (normChartMap_comp B S hS hrep k hk k' hk').trans (normChartMap_congr B S hS hrep _ _ _ _ h)

omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))] in
/-- Reflexivity of the induced relation, for the first projection. -/
lemma normRelDiag_comp_normRelFst :
    normRelDiag B S hS hrep w pr₁ pr₂ hsq ≫ normRelFst B S hS hrep w pr₁ =
      𝟙 (chartNorm B S hS (hrep.snd w)) := by
  exact (normChartMap_comp_eq B S hS hrep _ _ _ _ _ (by simp)
    (relDiag_comp_pr₁ B S hS w pr₁ pr₂ hsq)).trans (normChartMap_id B S hS hrep)

omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))] in
/-- Reflexivity of the induced relation, for the second projection. -/
lemma normRelDiag_comp_normRelSnd :
    normRelDiag B S hS hrep w pr₁ pr₂ hsq ≫ normRelSnd B S hS hrep w pr₁ pr₂ hsq =
      𝟙 (chartNorm B S hS (hrep.snd w)) := by
  exact (normChartMap_comp_eq B S hS hrep _ _ _ _ _ (by simp)
    (relDiag_comp_pr₂ B S hS w pr₁ pr₂ hsq)).trans (normChartMap_id B S hS hrep)

omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))] in
/-- Symmetry of the induced relation: the swap followed by the first projection is the second
projection. -/
lemma normRelSwap_comp_normRelFst :
    normRelSwap B S hS hrep w pr₁ pr₂ hsq ≫ normRelFst B S hS hrep w pr₁ =
      normRelSnd B S hS hrep w pr₁ pr₂ hsq := by
  exact normChartMap_comp_eq B S hS hrep _ _ _ _ _ _ (relSwap_comp_pr₁ B S hS w pr₁ pr₂ hsq)

omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))] in
/-- Symmetry of the induced relation: the swap followed by the second projection is the first
projection. -/
lemma normRelSwap_comp_normRelSnd :
    normRelSwap B S hS hrep w pr₁ pr₂ hsq ≫ normRelSnd B S hS hrep w pr₁ pr₂ hsq =
      normRelFst B S hS hrep w pr₁ := by
  exact normChartMap_comp_eq B S hS hrep _ _ _ _ _ _ (relSwap_comp_pr₂ B S hS w pr₁ pr₂ hsq)

/-- The two projections of the triple chart normalization agree on the middle factor. -/
lemma normRel₂Snd_comp_normRelFst :
    normRel₂Snd B S hS hrep w pr₁ pr₂ hsq ≫ normRelFst B S hS hrep w pr₁ =
      normRel₂Fst B S hS hrep w pr₁ pr₂ ≫ normRelSnd B S hS hrep w pr₁ pr₂ hsq := by
  rw [normRel₂Snd, normRelFst, normChartMap_comp, normRel₂Fst, normRelSnd, normChartMap_comp]
  exact normChartMap_congr B S hS hrep _ _ _ _ Limits.pullback.condition.symm

/-- Transitivity of the induced relation, for the second projection. -/
lemma normRel₂Outer_comp_normRelSnd :
    normRel₂Outer B S hS hrep w pr₁ pr₂ hsq ≫ normRelSnd B S hS hrep w pr₁ pr₂ hsq =
      normRel₂Snd B S hS hrep w pr₁ pr₂ hsq ≫ normRelSnd B S hS hrep w pr₁ pr₂ hsq := by
  rw [normRel₂Outer, normRelSnd, normChartMap_comp, normRel₂Snd, normChartMap_comp]
  exact normChartMap_congr B S hS hrep _ _ _ _ (rel₂Outer_comp_pr₂ B S hS w pr₁ pr₂ hsq)

/-- Transitivity of the induced relation, for the first projection. -/
lemma normRel₂Outer_comp_normRelFst :
    normRel₂Outer B S hS hrep w pr₁ pr₂ hsq ≫ normRelFst B S hS hrep w pr₁ =
      normRel₂Fst B S hS hrep w pr₁ pr₂ ≫ normRelFst B S hS hrep w pr₁ := by
  rw [normRel₂Outer, normRelFst, normChartMap_comp, normRel₂Fst, normChartMap_comp]
  exact normChartMap_congr B S hS hrep _ _ _ _ (rel₂Outer_comp_pr₁ B S hS w pr₁ pr₂ hsq)


/-! ### Étaleness of the projections -/

variable (hwet : (MorphismProperty.inverseImage
  (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
  (BigFppfOver.toScheme B S hS)).presheaf w)

/-- The base change of an étale morphism of the big fppf site is étale on underlying schemes. -/
private lemma etale_toScheme_map_of_isPullback {A C D E : BigFppfOver B S hS} {a : E ⟶ C}
    {b : E ⟶ A} {c : C ⟶ D} {d : A ⟶ D} (sq : IsPullback a b c d)
    (h : Etale ((BigFppfOver.toScheme B S hS).map c)) :
    Etale ((BigFppfOver.toScheme B S hS).map b) :=
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @AlgebraicGeometry.Etale.{u})
    (sq.map (BigFppfOver.toScheme B S hS)) h

include hsq hwet in
/-- The second projection of `R = U ×_Y U` is étale, being a base change of the chart. -/
lemma etale_toScheme_map_pr₂ : Etale ((BigFppfOver.toScheme B S hS).map pr₂) :=
  hwet.property w (yoneda.map pr₁) pr₂ hsq

include hsq hwet in
/-- The first projection of `R = U ×_Y U` is étale, being a base change of the chart. -/
lemma etale_toScheme_map_pr₁ : Etale ((BigFppfOver.toScheme B S hS).map pr₁) :=
  hwet.property w (yoneda.map pr₂) pr₁ hsq.flip

include hsq hwet in
/-- The first projection of `R ×_U R` is étale, being a base change of the first projection
of `R`. -/
lemma etale_toScheme_map_rel₂Fst :
    Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst pr₂ pr₁)) := by
  exact etale_toScheme_map_of_isPullback B S hS (IsPullback.of_hasPullback pr₂ pr₁).flip
    (etale_toScheme_map_pr₁ B S hS w pr₁ pr₂ hsq hwet)

include hsq hwet in
/-- The second projection of `R ×_U R` is étale, being a base change of the second projection
of `R`. -/
lemma etale_toScheme_map_rel₂Snd :
    Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd pr₂ pr₁)) := by
  exact etale_toScheme_map_of_isPullback B S hS (IsPullback.of_hasPullback pr₂ pr₁)
    (etale_toScheme_map_pr₂ B S hS w pr₁ pr₂ hsq hwet)

/-! ### The cartesian squares of the chart normalizations -/

include hsq hwet in
omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))] in
/-- The square of the first projection of the relation and the two normalization morphisms is
cartesian. -/
lemma isPullback_normRelFst :
    IsPullback (normRelFst B S hS hrep w pr₁)
      (chartNormProj B S hS (hrep.snd (relBase B S hS w pr₁)))
      (chartNormProj B S hS (hrep.snd w)) pr₁ := by
  have _ : Etale ((BigFppfOver.toScheme B S hS).map pr₁) :=
    etale_toScheme_map_pr₁ B S hS w pr₁ pr₂ hsq hwet
  exact isPullback_normChartMap B S hS hrep pr₁ (yoneda_map_pr₁_comp B S hS w pr₁)

include hsq hwet in
omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))] in
/-- The square of the second projection of the relation and the two normalization morphisms is
cartesian. -/
lemma isPullback_normRelSnd :
    IsPullback (normRelSnd B S hS hrep w pr₁ pr₂ hsq)
      (chartNormProj B S hS (hrep.snd (relBase B S hS w pr₁)))
      (chartNormProj B S hS (hrep.snd w)) pr₂ := by
  have _ : Etale ((BigFppfOver.toScheme B S hS).map pr₂) :=
    etale_toScheme_map_pr₂ B S hS w pr₁ pr₂ hsq hwet
  exact isPullback_normChartMap B S hS hrep pr₂ (yoneda_map_pr₂_comp B S hS w pr₁ pr₂ hsq)

include hsq hwet in
omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w))] in
/-- The square of the first projection of `R ×_U R` and the two normalization morphisms is
cartesian. -/
lemma isPullback_normRel₂Fst :
    IsPullback (normRel₂Fst B S hS hrep w pr₁ pr₂)
      (chartNormProj B S hS (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))
      (chartNormProj B S hS (hrep.snd (relBase B S hS w pr₁))) (Limits.pullback.fst pr₂ pr₁) := by
  have _ : Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst pr₂ pr₁)) :=
    etale_toScheme_map_rel₂Fst B S hS w pr₁ pr₂ hsq hwet
  exact isPullback_normChartMap B S hS hrep (Limits.pullback.fst pr₂ pr₁)
    (yoneda_map_rel₂Fst_comp B S hS w pr₁ pr₂)

include hsq hwet in
omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w))] in
/-- The square of the second projection of `R ×_U R` and the two normalization morphisms is
cartesian. -/
lemma isPullback_normRel₂Snd :
    IsPullback (normRel₂Snd B S hS hrep w pr₁ pr₂ hsq)
      (chartNormProj B S hS (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))
      (chartNormProj B S hS (hrep.snd (relBase B S hS w pr₁))) (Limits.pullback.snd pr₂ pr₁) := by
  have _ : Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd pr₂ pr₁)) :=
    etale_toScheme_map_rel₂Snd B S hS w pr₁ pr₂ hsq hwet
  exact isPullback_normChartMap B S hS hrep (Limits.pullback.snd pr₂ pr₁)
    (yoneda_map_rel₂Snd_comp B S hS w pr₁ pr₂ hsq)

include hsq hwet in
/-- **The triple chart normalization is the fibre product of two copies of the relation's.**
This is the limiting cone which the transitivity of the relation needs. -/
lemma isPullback_normRel₂ :
    IsPullback (normRel₂Snd B S hS hrep w pr₁ pr₂ hsq) (normRel₂Fst B S hS hrep w pr₁ pr₂)
      (normRelFst B S hS hrep w pr₁) (normRelSnd B S hS hrep w pr₁ pr₂ hsq) := by
  have houter := (isPullback_normRel₂Snd B S hS hrep w pr₁ pr₂ hsq hwet).paste_vert
    (IsPullback.of_hasPullback pr₂ pr₁).flip
  rw [← (isPullback_normRel₂Fst B S hS hrep w pr₁ pr₂ hsq hwet).w,
    ← (isPullback_normRelFst B S hS hrep w pr₁ pr₂ hsq hwet).w] at houter
  exact houter.of_bot (normRel₂Snd_comp_normRelFst B S hS hrep w pr₁ pr₂ hsq)
    (isPullback_normRelSnd B S hS hrep w pr₁ pr₂ hsq hwet)

/-! ### The equivalence relation -/

include hsq hwet in
omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (rel₂Base B S hS w pr₁ pr₂)))] in
/-- **The two induced morphisms of chart normalizations are jointly monic.** A morphism into
the chart normalization of the relation is determined by its composites with the two
projections: the first because the square over the first projection is cartesian, and the
component in the relation because `R = U ×_Y U`. -/
lemma jointlyMono₂_normRel :
    JointlyMono₂ (yoneda.map (normRelSnd B S hS hrep w pr₁ pr₂ hsq))
      (yoneda.map (normRelFst B S hS hrep w pr₁)) := by
  have hA := (isPullback_normRelFst B S hS hrep w pr₁ pr₂ hsq hwet).map yoneda
  have hB := (isPullback_normRelSnd B S hS hrep w pr₁ pr₂ hsq hwet).map yoneda
  refine ⟨fun Z a b h₁ h₂ => hA.hom_ext h₂ (hsq.hom_ext ?_ ?_)⟩
  · rw [Category.assoc, Category.assoc, ← hA.w, ← Category.assoc, ← Category.assoc, h₂]
  · rw [Category.assoc, Category.assoc, ← hB.w, ← Category.assoc, ← Category.assoc, h₁]

include hsq hwet in
/-- **The chart normalizations along the presentation form an internal equivalence relation of
presheaves.** -/
def equivalenceRelation_normRel :
    EquivalenceRelation (yoneda.map (normRelSnd B S hS hrep w pr₁ pr₂ hsq))
      (yoneda.map (normRelFst B S hS hrep w pr₁)) where
  __ := jointlyMono₂_normRel B S hS hrep w pr₁ pr₂ hsq hwet
  r := yoneda.map (normRelDiag B S hS hrep w pr₁ pr₂ hsq)
  reflexivity₁ := by
    rw [← CategoryTheory.Functor.map_comp, normRelDiag_comp_normRelSnd,
      CategoryTheory.Functor.map_id]
  reflexivity₂ := by
    rw [← CategoryTheory.Functor.map_comp, normRelDiag_comp_normRelFst,
      CategoryTheory.Functor.map_id]
  s := yoneda.map (normRelSwap B S hS hrep w pr₁ pr₂ hsq)
  symmetry₁ := by
    rw [← CategoryTheory.Functor.map_comp, normRelSwap_comp_normRelSnd]
  symmetry₂ := by
    rw [← CategoryTheory.Functor.map_comp, normRelSwap_comp_normRelFst]
  c := ((isPullback_normRel₂ B S hS hrep w pr₁ pr₂ hsq hwet).map yoneda).cone
  isLimit := ((isPullback_normRel₂ B S hS hrep w pr₁ pr₂ hsq hwet).map yoneda).isLimit
  t := yoneda.map (normRel₂Outer B S hS hrep w pr₁ pr₂ hsq)
  transitivity₁ := by
    change yoneda.map (normRel₂Outer B S hS hrep w pr₁ pr₂ hsq) ≫
        yoneda.map (normRelSnd B S hS hrep w pr₁ pr₂ hsq) =
      yoneda.map (normRel₂Snd B S hS hrep w pr₁ pr₂ hsq) ≫
        yoneda.map (normRelSnd B S hS hrep w pr₁ pr₂ hsq)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      normRel₂Outer_comp_normRelSnd]
  transitivity₂ := by
    change yoneda.map (normRel₂Outer B S hS hrep w pr₁ pr₂ hsq) ≫
        yoneda.map (normRelFst B S hS hrep w pr₁) =
      yoneda.map (normRel₂Fst B S hS hrep w pr₁ pr₂) ≫
        yoneda.map (normRelFst B S hS hrep w pr₁)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      normRel₂Outer_comp_normRelFst]


include hsq hwet in
/-- **The chart normalizations along an étale presentation of `Y` form an étale equivalence
relation over `S`**, in the sense of Tag 02WS. -/
theorem isEtaleEquivalenceRelation_normRel :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (relation B S hS (normRelFst B S hS hrep w pr₁)
        (normRelSnd B S hS hrep w pr₁ pr₂ hsq)) := by
  have _ : Etale ((BigFppfOver.toScheme B S hS).map pr₁) :=
    etale_toScheme_map_pr₁ B S hS w pr₁ pr₂ hsq hwet
  have _ : Etale ((BigFppfOver.toScheme B S hS).map pr₂) :=
    etale_toScheme_map_pr₂ B S hS w pr₁ pr₂ hsq hwet
  refine isEtaleEquivalenceRelation_of_embedding B S hS _ _ yoneda (Iso.refl _) ?_
    (etale_toScheme_map_normChartMap B S hS hrep pr₂ (yoneda_map_pr₂_comp B S hS w pr₁ pr₂ hsq))
    (etale_toScheme_map_normChartMap B S hS hrep pr₁ (yoneda_map_pr₁_comp B S hS w pr₁))
  simp only [Iso.refl_hom, Category.id_comp]
  exact (equivalenceRelation_normRel B S hS hrep w pr₁ pr₂ hsq hwet).isEquivalenceRelation

end AlgebraicGeometry.Space.NormalizationGluing

end
