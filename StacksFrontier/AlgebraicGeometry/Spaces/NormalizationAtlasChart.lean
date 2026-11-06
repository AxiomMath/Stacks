module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleAtlasClause
public import StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremQuasiFinite

/-!
# The chart condition of the glued normalization at an arbitrary étale chart

Let `f : X ⟶ Y` be a quasi-finite separated morphism of algebraic spaces and let `Q` be an
algebraic space through which `f` factors, with a surjective étale chart `qm : N(U) ⟶ Q` from the
chart normalization of `f` over a surjective étale chart `w : h_U ⟶ Y` of `Y`, exhibiting `N(U)`
as `Q ×_Y U`. Then for every étale chart `w' : h_W ⟶ Y` the chart normalization `N(W)` maps to
`Q`, cartesianly over `W` and compatibly with the canonical morphism from `X`: this is the chart
condition of `AlgebraicGeometry.Space.NormalizationInData`.

## Main results

* `AlgebraicGeometry.Space.NormalizationGluing.quasiCompact_hrep_snd` and
  `AlgebraicGeometry.Space.NormalizationGluing.quasiSeparated_hrep_snd`: the chart of a
  quasi-finite separated morphism is quasi-compact and quasi-separated.
* `AlgebraicGeometry.Space.NormalizationGluing.isIntegralHom_base`: the normalization morphism
  `Q ⟶ Y` is integral.
* `AlgebraicGeometry.Space.NormalizationGluing.exists_chartMapToSpace`: the chart condition at an
  étale chart `W` of `Y`, given a refinement `V = W ×_Y U` of `W` by the atlas.

## Implementation notes

Over a chart `w' : h_W ⟶ Y` the identification is obtained by descent along the surjective étale
morphism `V = W ×_Y U ⟶ W`: over `V` the chart factors through `w`, so the identification there
is the one over `U` base changed by Tag 03GV, and the comparison morphism over `W` is an open
immersion and surjective, hence an isomorphism, because its base change to `V` is an isomorphism.

## References

* [Stacks Project, Tag 03GV](https://stacks.math.columbia.edu/tag/03GV)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.NormalizationGluing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
  (hrep : yoneda.relativelyRepresentable f)

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_NormalizationAtlasChart :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_NormalizationAtlasChart
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The charts of a quasi-finite separated morphism are quasi-compact and quasi-separated -/

/-- The chart of a quasi-finite morphism of algebraic spaces over an object of the site is
quasi-compact. -/
theorem quasiCompact_hrep_snd (hqf : IsQuasiFinite B S hS f) {V : BigFppfOver B S hS}
    (v : yoneda.obj V ⟶ Y) :
    QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd v)) :=
  ((presheaf_quasiCompact_iff_isQuasiCompact B S hS hrep).2 hqf.2).property v (hrep.fst v)
    (hrep.snd v) (hrep.isPullback v)

/-- The chart of a separated morphism of algebraic spaces over an object of the site is
separated. -/
theorem isSeparated_hrep_snd (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hsep : IsSeparated B S hS f) {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y) :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd v)) :=
  ((isSeparated_iff_presheaf B S hS f hX hY hrep).1 hsep).property v (hrep.fst v) (hrep.snd v)
    (hrep.isPullback v)

/-- The chart of a separated morphism of algebraic spaces over an object of the site is
quasi-separated. -/
theorem quasiSeparated_hrep_snd (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hsep : IsSeparated B S hS f)
    {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y) :
    QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd v)) :=
  have _ := isSeparated_hrep_snd B S hS hrep hX hY hsep v
  inferInstance

/-! ### Integrality of the normalization morphism of a chart -/

/-- The normalization morphism of a chart is integral. -/
theorem isIntegralHom_toScheme_map_chartNormProj {V XV : BigFppfOver B S hS} (pv : XV ⟶ V)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map pv)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map pv)] :
    _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map (chartNormProj B S hS pv)) := by
  rw [toScheme_map_chartNormProj]
  exact inferInstanceAs (_root_.AlgebraicGeometry.IsIntegralHom
    ((BigFppfOver.toScheme B S hS).map pv).fromNormalization)

/-! ### The glued normalization

The results below concern an algebraic space `Q` with the two legs `tn : X ⟶ Q` and `ν : Q ⟶ Y`
of a factorization of `f`, and a surjective étale chart `qm` from the chart normalization `N(U)`
whose kernel pair is the relation and which exhibits `N(U)` as `Q ×_Y U`. -/

variable {U R : BigFppfOver B S hS} (w : yoneda.obj U ⟶ Y) (pr₁ pr₂ : R ⟶ U)
  (hsq : IsPullback (yoneda.map pr₁) (yoneda.map pr₂) w w)
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))]
  {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
  (ν : Q ⟶ Y) (tn : X ⟶ Q)
  (qm : yoneda.obj (chartNorm B S hS (hrep.snd w)) ⟶ Q)
  (hqmsurj : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf qm)
  (hqmet : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf qm)
  (hker : IsPullback (yoneda.map (normRelSnd B S hS hrep w pr₁ pr₂ hsq))
    (yoneda.map (normRelFst B S hS hrep w pr₁)) qm qm)
  (hchart : IsPullback qm (yoneda.map (chartNormProj B S hS (hrep.snd w))) ν w)
  (hunit : yoneda.map (chartNormUnit B S hS (hrep.snd w)) ≫ qm = hrep.fst w ≫ tn)
  (hwsurj : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w)
  (hwet : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w)
  (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
  (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f)

omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))] in
include hsq hQ hchart hwsurj hwet hY in
/-- **The normalization morphism of the glued object is integral.** -/
theorem isIntegralHom_base : IsIntegralHom B S hS ν := by
  have hq := isIntegralHom_toScheme_map_chartNormProj B S hS (hrep.snd w)
  have hrelq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (Limits.pullback.snd ν w) := by
    refine (((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda).cancel_left_of_respectsIso
      hchart.isoPullback.hom (Limits.pullback.snd ν w)).mp ?_
    rw [hchart.isoPullback_hom_snd]
    exact AlgebraicGeometry.Space.relative_isIntegralHom_yoneda_map
      (chartNormProj B S hS (hrep.snd w)) hq
  have hUspace : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hPull : IsAlgebraicSpace B S hS (Limits.pullback ν w) :=
    isAlgebraicSpace_pullback B S hS ν w hQ hUspace hY
  exact (isIntegralHom_iff_etaleChart B S hS ν hQ hY).2
    ⟨U, w, hwsurj, hwet,
      (isIntegralHom_iff_representable B S hS (Limits.pullback.snd ν w) hPull hUspace).2
        ⟨hrelq.1, hrelq⟩⟩

omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))] in
include hsq hQ hchart hwsurj hwet hY in
/-- The normalization morphism of the glued object is representable with integral represented
base changes. -/
theorem presheaf_isIntegralHom_base :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ν :=
  ((isIntegralHom_iff_representable B S hS ν hQ hY).1
    (isIntegralHom_base B S hS hrep w pr₁ pr₂ hsq hQ ν qm hchart hwsurj hwet hY)).2

omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (relBase B S hS w pr₁)))] in
include hsq hQ hchart hwsurj hwet hY in
/-- The fibre product of the glued object with an arbitrary chart of `Y` is representable with
integral projection. -/
theorem presheaf_isIntegralHom_pullback_snd {W : BigFppfOver B S hS} (w' : yoneda.obj W ⟶ Y) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (Limits.pullback.snd ν w') := by
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback ν w')
    (presheaf_isIntegralHom_base B S hS hrep w pr₁ pr₂ hsq hQ ν qm hchart hwsurj hwet hY)


/-! ### An arbitrary étale chart and its refinement by the atlas -/

section ArbitraryChart

variable {W V : BigFppfOver B S hS} (w' : yoneda.obj W ⟶ Y)
  (hw'et : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w')
  (j : V ⟶ W) (k : V ⟶ U)
  (hjk : IsPullback (yoneda.map j) (yoneda.map k) w' w)
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w'))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w'))]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd (yoneda.map k ≫ w)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd (yoneda.map k ≫ w)))]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd
    (yoneda.map (Limits.pullback.fst j j) ≫ yoneda.map k ≫ w)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd
    (yoneda.map (Limits.pullback.fst j j) ≫ yoneda.map k ≫ w)))]

include hjk hw'et in
/-- The refinement of an arbitrary chart by the atlas is an étale chart of the atlas. -/
theorem etale_toScheme_map_k : Etale ((BigFppfOver.toScheme B S hS).map k) :=
  hw'et.property w (yoneda.map j) k hjk

include hjk hwet in
/-- The refinement of an arbitrary chart by the atlas is étale over that chart. -/
theorem etale_toScheme_map_j : Etale ((BigFppfOver.toScheme B S hS).map j) :=
  hwet.property w' (yoneda.map k) j hjk.flip

include hjk hwsurj in
/-- The refinement of an arbitrary chart by the atlas is surjective onto that chart. -/
theorem surjective_toScheme_map_j : Surjective ((BigFppfOver.toScheme B S hS).map j) :=
  hwsurj.property w' (yoneda.map k) j hjk.flip

include hjk hwet in
/-- The two projections of the self-fibre-product of the refinement over the chart agree over
the atlas. -/
theorem rel_refine_middle :
    yoneda.map (Limits.pullback.snd j j) ≫ yoneda.map k ≫ w =
      yoneda.map (Limits.pullback.fst j j) ≫ yoneda.map k ≫ w := by
  rw [← hjk.w, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Limits.pullback.condition]

omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd
    (yoneda.map (Limits.pullback.fst j j) ≫ yoneda.map k ≫ w)))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd
    (yoneda.map (Limits.pullback.fst j j) ≫ yoneda.map k ≫ w)))] in
include hjk hwet hwsurj in
/-- The transition morphism of the refinement is a surjective étale chart of the chart
normalization of `W`. -/
theorem surjective_etale_normChartMap_j :
    (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (normChartMap B S hS hrep j hjk.w)) ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (normChartMap B S hS hrep j hjk.w)) := by
  have _ : Etale ((BigFppfOver.toScheme B S hS).map j) :=
    etale_toScheme_map_j B S hS w hwet w' j k hjk
  have hA := isPullback_toScheme_map_normChartMap B S hS hrep j hjk.w
  refine ⟨(BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2 ?_,
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2 ?_⟩
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Surjective.{u}) hA.flip
      (surjective_toScheme_map_j B S hS w hwsurj w' j k hjk)
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Etale.{u}) hA.flip inferInstance

omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w))] in
include hjk hwet in
/-- **The chart normalization of the self-fibre-product of the refinement is the kernel pair of
the transition morphism.** -/
theorem isPullback_normChartMap_refine_self :
    IsPullback (normChartMap B S hS hrep (Limits.pullback.fst j j) rfl)
      (normChartMap B S hS hrep (Limits.pullback.snd j j)
        (rel_refine_middle B S hS w hwet w' j k hjk))
      (normChartMap B S hS hrep j hjk.w) (normChartMap B S hS hrep j hjk.w) := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : Etale ((BigFppfOver.toScheme B S hS).map j) :=
    etale_toScheme_map_j B S hS w hwet w' j k hjk
  have hpb := (IsPullback.of_hasPullback j j).map (BigFppfOver.toScheme B S hS)
  have _ : Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd j j)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Etale.{u}) hpb inferInstance
  have _ : Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst j j)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Etale.{u}) hpb.flip inferInstance
  have hA := isPullback_normChartMap B S hS hrep j hjk.w
  have hD := isPullback_normChartMap B S hS hrep (w₁ := yoneda.map k ≫ w)
    (Limits.pullback.fst j j) rfl
  have hC := isPullback_normChartMap B S hS hrep (Limits.pullback.snd j j)
    (rel_refine_middle B S hS w hwet w' j k hjk)
  have houter := hD.paste_vert (IsPullback.of_hasPullback j j)
  rw [← hC.w, ← hA.w] at houter
  refine houter.of_bot ?_ hA
  rw [normChartMap_comp B S hS hrep j hjk.w (Limits.pullback.fst j j) rfl,
    normChartMap_comp B S hS hrep j hjk.w (Limits.pullback.snd j j)
      (rel_refine_middle B S hS w hwet w' j k hjk)]
  exact normChartMap_congr B S hS hrep _ _ _ _ Limits.pullback.condition

include hjk hwet in
/-- The two projections of the self-fibre-product of the refinement, followed by `k`, agree
over `Y`. -/
theorem rel_refine_comm :
    yoneda.map (Limits.pullback.fst j j ≫ k) ≫ w =
      yoneda.map (Limits.pullback.snd j j ≫ k) ≫ w := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Category.assoc]
  exact (rel_refine_middle B S hS w hwet w' j k hjk).symm

/-- The morphism from the self-fibre-product of the refinement into the relation `U ×_Y U`. -/
def relRefine : Limits.pullback j j ⟶ R :=
  yoneda.preimage (hsq.lift (yoneda.map (Limits.pullback.fst j j ≫ k))
    (yoneda.map (Limits.pullback.snd j j ≫ k))
    (rel_refine_comm B S hS w hwet w' j k hjk))

/-- `relRefine` followed by the first projection of the relation is the first projection of the
self-fibre-product followed by `k`. -/
lemma relRefine_comp_pr₁ :
    relRefine B S hS w pr₁ pr₂ hsq hwet w' j k hjk ≫ pr₁ =
      Limits.pullback.fst j j ≫ k :=
  yoneda.map_injective (by
    rw [CategoryTheory.Functor.map_comp, relRefine, yoneda.map_preimage, hsq.lift_fst])

/-- `relRefine` followed by the second projection of the relation is the second projection of the
self-fibre-product followed by `k`. -/
lemma relRefine_comp_pr₂ :
    relRefine B S hS w pr₁ pr₂ hsq hwet w' j k hjk ≫ pr₂ =
      Limits.pullback.snd j j ≫ k :=
  yoneda.map_injective (by
    rw [CategoryTheory.Functor.map_comp, relRefine, yoneda.map_preimage, hsq.lift_snd])

/-- `relRefine` followed by the structure morphism `relBase` of the relation to `Y` is the first
projection of the self-fibre-product followed by `k` and `w`. -/
lemma yoneda_map_relRefine_comp :
    yoneda.map (relRefine B S hS w pr₁ pr₂ hsq hwet w' j k hjk) ≫ relBase B S hS w pr₁ =
      yoneda.map (Limits.pullback.fst j j) ≫ yoneda.map k ≫ w := by
  rw [relBase, ← Category.assoc, ← CategoryTheory.Functor.map_comp, relRefine_comp_pr₁,
    CategoryTheory.Functor.map_comp, Category.assoc]

omit [QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w'))]
  [QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w'))] in
include hjk hwet hker in
/-- **The transition morphism to the atlas chart normalization is invariant under the kernel
pair of the refinement.** -/
theorem invariant_normChartMap_refine :
    yoneda.map (normChartMap B S hS hrep (w₁ := yoneda.map k ≫ w)
          (Limits.pullback.fst j j) rfl) ≫
        yoneda.map (normChartMap B S hS hrep (w₁ := w) k rfl) ≫ qm =
      yoneda.map (normChartMap B S hS hrep (Limits.pullback.snd j j)
          (rel_refine_middle B S hS w hwet w' j k hjk)) ≫
        yoneda.map (normChartMap B S hS hrep (w₁ := w) k rfl) ≫ qm := by
  have e1 : normChartMap B S hS hrep
        (relRefine B S hS w pr₁ pr₂ hsq hwet w' j k hjk)
        (yoneda_map_relRefine_comp B S hS w pr₁ pr₂ hsq hwet w' j k hjk) ≫
          normRelFst B S hS hrep w pr₁ =
      normChartMap B S hS hrep (w₁ := yoneda.map k ≫ w) (Limits.pullback.fst j j) rfl ≫
        normChartMap B S hS hrep (w₁ := w) k rfl := by
    rw [normRelFst, normChartMap_comp, normChartMap_comp]
    exact normChartMap_congr B S hS hrep _ _ _ _
      (relRefine_comp_pr₁ B S hS w pr₁ pr₂ hsq hwet w' j k hjk)
  have e2 : normChartMap B S hS hrep
        (relRefine B S hS w pr₁ pr₂ hsq hwet w' j k hjk)
        (yoneda_map_relRefine_comp B S hS w pr₁ pr₂ hsq hwet w' j k hjk) ≫
          normRelSnd B S hS hrep w pr₁ pr₂ hsq =
      normChartMap B S hS hrep (Limits.pullback.snd j j)
          (rel_refine_middle B S hS w hwet w' j k hjk) ≫
        normChartMap B S hS hrep (w₁ := w) k rfl := by
    rw [normRelSnd, normChartMap_comp, normChartMap_comp]
    exact normChartMap_congr B S hS hrep _ _ _ _
      (relRefine_comp_pr₂ B S hS w pr₁ pr₂ hsq hwet w' j k hjk)
  simp only [← Functor.map_comp_assoc, ← e1, ← e2]
  simp only [Functor.map_comp_assoc, hker.w]

include hjk hw'et hwet hwsurj hker hQ in
/-- **The chart normalization of an arbitrary chart maps to the glued object.** There is a
unique morphism `d : N(W) ⟶ Q` whose composite with the transition morphism `N(V) ⟶ N(W)` is the
transition morphism `N(V) ⟶ N(U)` followed by `qm`. -/
theorem existsUnique_chartMapToSpace :
    ∃! d : yoneda.obj (chartNorm B S hS (hrep.snd w')) ⟶ Q,
      yoneda.map (normChartMap B S hS hrep j hjk.w) ≫ d =
        yoneda.map (normChartMap B S hS hrep (w₁ := w) k rfl) ≫ qm :=
  existsUnique_desc_of_surjective_etale_atlas B S hS
    (isAlgebraicSpace_yoneda B S hS (chartNorm B S hS (hrep.snd w'))).isSheaf _
    ((isPullback_normChartMap_refine_self B S hS hrep w hwet w' j k hjk).map yoneda)
    (surjective_etale_normChartMap_j B S hS hrep w hwsurj hwet w' j k hjk).1
    (surjective_etale_normChartMap_j B S hS hrep w hwsurj hwet w' j k hjk).2
    hQ.isSheaf _
    (invariant_normChartMap_refine B S hS hrep w pr₁ pr₂ hsq qm hker hwet w' j k hjk)

include hjk hw'et hwet hwsurj hker hQ hchart hunit hY in
/-- **The chart condition at an arbitrary étale chart, granted a refinement by the atlas.**
The chart normalization of `W` maps to the glued object, cartesianly over the chart, and
compatibly with the canonical morphism from the source. -/
theorem exists_chartMapToSpace :
    ∃ b : yoneda.obj (chartNorm B S hS (hrep.snd w')) ⟶ Q,
      IsPullback b (yoneda.map (chartNormProj B S hS (hrep.snd w'))) ν w' ∧
      yoneda.map (chartNormUnit B S hS (hrep.snd w')) ≫ b = hrep.fst w' ≫ tn := by
  classical
  obtain ⟨bW, hbW, -⟩ := existsUnique_chartMapToSpace B S hS hrep w pr₁ pr₂ hsq hQ qm hker
    hwsurj hwet w' hw'et j k hjk
  have hαsurj := (surjective_etale_normChartMap_j B S hS hrep w hwsurj hwet w' j k hjk).1
  have hαet := (surjective_etale_normChartMap_j B S hS hrep w hwsurj hwet w' j k hjk).2
  have hNWsheaf := (isAlgebraicSpace_yoneda B S hS (chartNorm B S hS (hrep.snd w'))).isSheaf
  have hbWν : bW ≫ ν = yoneda.map (chartNormProj B S hS (hrep.snd w')) ≫ w' := by
    refine hom_ext_of_etale_atlas B S hS hNWsheaf hY.isSheaf
      (yoneda.map (normChartMap B S hS hrep j hjk.w)) hαsurj hαet ?_
    calc yoneda.map (normChartMap B S hS hrep j hjk.w) ≫ bW ≫ ν
        = (yoneda.map (normChartMap B S hS hrep j hjk.w) ≫ bW) ≫ ν :=
          (Category.assoc _ _ _).symm
      _ = (yoneda.map (normChartMap B S hS hrep (w₁ := w) k rfl) ≫ qm) ≫ ν := by rw [hbW]
      _ = yoneda.map (normChartMap B S hS hrep (w₁ := w) k rfl) ≫ qm ≫ ν :=
          Category.assoc _ _ _
      _ = yoneda.map (normChartMap B S hS hrep (w₁ := w) k rfl) ≫
            yoneda.map (chartNormProj B S hS (hrep.snd w)) ≫ w := by rw [hchart.w]
      _ = yoneda.map (normChartMap B S hS hrep (w₁ := w) k rfl ≫
            chartNormProj B S hS (hrep.snd w)) ≫ w := by
            rw [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = yoneda.map (chartNormProj B S hS (hrep.snd (yoneda.map k ≫ w)) ≫ k) ≫ w := by
            rw [normChartMap_comp_chartNormProj]
      _ = yoneda.map (chartNormProj B S hS (hrep.snd (yoneda.map k ≫ w))) ≫
            yoneda.map k ≫ w := by rw [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = yoneda.map (chartNormProj B S hS (hrep.snd (yoneda.map k ≫ w))) ≫
            yoneda.map j ≫ w' := by rw [hjk.w]
      _ = yoneda.map (chartNormProj B S hS (hrep.snd (yoneda.map k ≫ w)) ≫ j) ≫ w' := by
            rw [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = yoneda.map (normChartMap B S hS hrep j hjk.w ≫
            chartNormProj B S hS (hrep.snd w')) ≫ w' := by
            rw [normChartMap_comp_chartNormProj]
      _ = yoneda.map (normChartMap B S hS hrep j hjk.w) ≫
            yoneda.map (chartNormProj B S hS (hrep.snd w')) ≫ w' := by
            rw [CategoryTheory.Functor.map_comp, Category.assoc]
  have hXsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (chartMap B S hS hrep j hjk.w)) := by
    have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
      preservesLimitsOfShape_walkingCospan_toScheme B S hS
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @AlgebraicGeometry.Surjective.{u})
        (((isPullback_chartMap B S hS hrep j hjk.w).map
          (BigFppfOver.toScheme B S hS)).flip) ?_)
    exact surjective_toScheme_map_j B S hS w hwsurj w' j k hjk
  have hXet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (chartMap B S hS hrep j hjk.w)) := by
    have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
      preservesLimitsOfShape_walkingCospan_toScheme B S hS
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @AlgebraicGeometry.Etale.{u})
        (((isPullback_chartMap B S hS hrep j hjk.w).map
          (BigFppfOver.toScheme B S hS)).flip) ?_)
    exact etale_toScheme_map_j B S hS w hwet w' j k hjk
  have hbWunit : yoneda.map (chartNormUnit B S hS (hrep.snd w')) ≫ bW =
      hrep.fst w' ≫ tn := by
    refine hom_ext_of_etale_atlas B S hS
      (isAlgebraicSpace_yoneda B S hS (hrep.pullback w')).isSheaf hQ.isSheaf
      (yoneda.map (chartMap B S hS hrep j hjk.w)) hXsurj hXet ?_
    calc yoneda.map (chartMap B S hS hrep j hjk.w) ≫
          yoneda.map (chartNormUnit B S hS (hrep.snd w')) ≫ bW
        = yoneda.map (chartMap B S hS hrep j hjk.w ≫
            chartNormUnit B S hS (hrep.snd w')) ≫ bW := by
            rw [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = yoneda.map (chartNormUnit B S hS (hrep.snd (yoneda.map k ≫ w)) ≫
            normChartMap B S hS hrep j hjk.w) ≫ bW := by
            rw [chartNormUnit_comp_normChartMap]
      _ = yoneda.map (chartNormUnit B S hS (hrep.snd (yoneda.map k ≫ w))) ≫
            yoneda.map (normChartMap B S hS hrep j hjk.w) ≫ bW := by
            rw [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = yoneda.map (chartNormUnit B S hS (hrep.snd (yoneda.map k ≫ w))) ≫
            yoneda.map (normChartMap B S hS hrep (w₁ := w) k rfl) ≫ qm := by rw [hbW]
      _ = yoneda.map (chartNormUnit B S hS (hrep.snd (yoneda.map k ≫ w)) ≫
            normChartMap B S hS hrep (w₁ := w) k rfl) ≫ qm := by
            rw [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = yoneda.map (chartMap B S hS hrep (w₁ := w) k rfl ≫
            chartNormUnit B S hS (hrep.snd w)) ≫ qm := by
            rw [chartNormUnit_comp_normChartMap]
      _ = yoneda.map (chartMap B S hS hrep (w₁ := w) k rfl) ≫
            yoneda.map (chartNormUnit B S hS (hrep.snd w)) ≫ qm := by
            rw [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = yoneda.map (chartMap B S hS hrep (w₁ := w) k rfl) ≫ hrep.fst w ≫ tn := by
            rw [hunit]
      _ = (yoneda.map (chartMap B S hS hrep (w₁ := w) k rfl) ≫ hrep.fst w) ≫ tn :=
          (Category.assoc _ _ _).symm
      _ = hrep.fst (yoneda.map k ≫ w) ≫ tn := by rw [yoneda_map_chartMap_comp_fst]
      _ = (yoneda.map (chartMap B S hS hrep j hjk.w) ≫ hrep.fst w') ≫ tn := by
            rw [yoneda_map_chartMap_comp_fst]
      _ = yoneda.map (chartMap B S hS hrep j hjk.w) ≫ hrep.fst w' ≫ tn :=
          Category.assoc _ _ _
  have _ : Etale ((BigFppfOver.toScheme B S hS).map k) :=
    etale_toScheme_map_k B S hS w w' hw'et j k hjk
  have _ : Etale ((BigFppfOver.toScheme B S hS).map j) :=
    etale_toScheme_map_j B S hS w hwet w' j k hjk
  have hαsq := (isPullback_normChartMap B S hS hrep j hjk.w).map yoneda
  have hchartV : IsPullback
      (yoneda.map (normChartMap B S hS hrep (w₁ := w) k rfl) ≫ qm)
      (yoneda.map (chartNormProj B S hS (hrep.snd (yoneda.map k ≫ w)))) ν
      (yoneda.map k ≫ w) :=
    ((isPullback_normChartMap B S hS hrep (w₁ := w) k rfl).map yoneda).paste_horiz hchart
  have hPsheaf := (isAlgebraicSpace_pullback B S hS ν w' hQ
    (isAlgebraicSpace_yoneda B S hS W) hY).isSheaf
  have hβfst : Limits.pullback.lift bW
      (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν ≫
        Limits.pullback.fst ν w' = bW := Limits.pullback.lift_fst _ _ _
  have hβsnd : Limits.pullback.lift bW
      (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν ≫
        Limits.pullback.snd ν w' = yoneda.map (chartNormProj B S hS (hrep.snd w')) :=
    Limits.pullback.lift_snd _ _ _
  have hX' : IsPullback
      (yoneda.map (normChartMap B S hS hrep j hjk.w) ≫ Limits.pullback.lift bW
        (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν)
      (yoneda.map (chartNormProj B S hS (hrep.snd (yoneda.map k ≫ w))))
      (Limits.pullback.snd ν w') (yoneda.map j) := by
    refine IsPullback.of_right (h₁₂ := Limits.pullback.fst ν w') (v₁₃ := ν) (h₂₂ := w') ?_ ?_
      (IsPullback.of_hasPullback ν w')
    · have he : (yoneda.map (normChartMap B S hS hrep j hjk.w) ≫ Limits.pullback.lift bW
          (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν) ≫
            Limits.pullback.fst ν w' =
          yoneda.map (normChartMap B S hS hrep (w₁ := w) k rfl) ≫ qm := by
        rw [Category.assoc, hβfst, hbW]
      rw [he, hjk.w]
      exact hchartV
    · rw [Category.assoc, hβsnd, ← CategoryTheory.Functor.map_comp,
        normChartMap_comp_chartNormProj, CategoryTheory.Functor.map_comp]
  have hrel := presheaf_isIntegralHom_pullback_snd B S hS hrep w pr₁ pr₂ hsq hQ ν qm hchart
    hwsurj hwet hY w'
  have hrelsq := hrel.1.isPullback (𝟙 (yoneda.obj W))
  have _ : IsIso (hrel.1.fst (𝟙 (yoneda.obj W))) := isIso_fst_of_isPullback_id B S hS hrelsq
  have hcsq : IsPullback
      (yoneda.map (Limits.pullback.fst (hrel.1.snd (𝟙 (yoneda.obj W))) j) ≫
        hrel.1.fst (𝟙 (yoneda.obj W)))
      (yoneda.map (Limits.pullback.snd (hrel.1.snd (𝟙 (yoneda.obj W))) j))
      (Limits.pullback.snd ν w') (yoneda.map j) := by
    have hp := ((IsPullback.of_hasPullback (hrel.1.snd (𝟙 (yoneda.obj W))) j).map
      yoneda).paste_horiz hrelsq
    rwa [Category.comp_id] at hp
  have hδiso : IsIso (hX'.isoIsPullback _ _ hcsq).hom := inferInstance
  have hδfst := hX'.isoIsPullback_hom_fst _ _ hcsq
  have hδsnd := hX'.isoIsPullback_hom_snd _ _ hcsq
  have hβc : IsPullback (yoneda.map (normChartMap B S hS hrep j hjk.w))
      (hX'.isoIsPullback _ _ hcsq).hom
      (Limits.pullback.lift bW (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν)
      (yoneda.map (Limits.pullback.fst (hrel.1.snd (𝟙 (yoneda.obj W))) j) ≫
        hrel.1.fst (𝟙 (yoneda.obj W))) := by
    refine IsPullback.of_bot ?_ hδfst.symm hcsq
    rw [hδsnd, hβsnd]
    exact hαsq
  obtain ⟨e, he⟩ : ∃ e : yoneda.obj (chartNorm B S hS (hrep.snd (yoneda.map k ≫ w))) ≅
      Limits.pullback (Limits.pullback.lift bW
        (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν)
        (yoneda.map (Limits.pullback.fst (hrel.1.snd (𝟙 (yoneda.obj W))) j) ≫
          hrel.1.fst (𝟙 (yoneda.obj W))),
      e.hom ≫ Limits.pullback.snd (Limits.pullback.lift bW
        (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν)
        (yoneda.map (Limits.pullback.fst (hrel.1.snd (𝟙 (yoneda.obj W))) j) ≫
          hrel.1.fst (𝟙 (yoneda.obj W))) = (hX'.isoIsPullback _ _ hcsq).hom :=
    ⟨hβc.isoPullback, hβc.isoPullback_hom_snd⟩
  have hpsiso : IsIso (Limits.pullback.snd (Limits.pullback.lift bW
        (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν)
        (yoneda.map (Limits.pullback.fst (hrel.1.snd (𝟙 (yoneda.obj W))) j) ≫
          hrel.1.fst (𝟙 (yoneda.obj W)))) := by
    have h2 : Limits.pullback.snd (Limits.pullback.lift bW
        (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν)
        (yoneda.map (Limits.pullback.fst (hrel.1.snd (𝟙 (yoneda.obj W))) j) ≫
          hrel.1.fst (𝟙 (yoneda.obj W))) = e.inv ≫ (hX'.isoIsPullback _ _ hcsq).hom := by
      rw [← he, Iso.inv_hom_id_assoc]
    rw [h2]
    infer_instance
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hqj := ((IsPullback.of_hasPullback (hrel.1.snd (𝟙 (yoneda.obj W))) j).map
    (BigFppfOver.toScheme B S hS)).flip
  have hc₁s : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (Limits.pullback.fst (hrel.1.snd (𝟙 (yoneda.obj W))) j) ≫
        hrel.1.fst (𝟙 (yoneda.obj W))) := by
    refine (MorphismProperty.cancel_right_of_respectsIso _ _ _).2
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2
        (MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := @AlgebraicGeometry.Surjective.{u}) hqj ?_))
    exact surjective_toScheme_map_j B S hS w hwsurj w' j k hjk
  have hc₁e : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (Limits.pullback.fst (hrel.1.snd (𝟙 (yoneda.obj W))) j) ≫
        hrel.1.fst (𝟙 (yoneda.obj W))) := by
    refine (MorphismProperty.cancel_right_of_respectsIso _ _ _).2
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2
        (MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := @AlgebraicGeometry.Etale.{u}) hqj inferInstance))
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u}) := MorphismProperty.RespectsIso.inf _ _
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities := ⟨fun Z => by
    show AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map (𝟙 Z))
    rw [CategoryTheory.Functor.map_id]
    infer_instance⟩
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities := ⟨fun Z => by
    show AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (𝟙 Z))
    rw [CategoryTheory.Functor.map_id]
    infer_instance⟩
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities := ⟨fun Z => by
    refine ⟨?_, ?_⟩
    · show _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map (𝟙 Z))
      rw [CategoryTheory.Functor.map_id]
      infer_instance
    · show LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map (𝟙 Z))
      rw [CategoryTheory.Functor.map_id]
      infer_instance⟩
  have hβOI : IsOpenImmersion B S hS (Limits.pullback.lift bW
      (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν) :=
    presheaf_of_surjectiveEtaleChart
      (isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion B S hS) hNWsheaf hPsheaf
      hc₁s hc₁e (MorphismProperty.presheaf_of_isIso _ _)
  have hβsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (Limits.pullback.lift bW
      (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν) :=
    (presheaf_surjective_and_etale_of_surjectiveEtaleChart_unconditional B S hS hNWsheaf
      hPsheaf hc₁s hc₁e (MorphismProperty.presheaf_of_isIso _ _)
      (MorphismProperty.presheaf_of_isIso _ _) (MorphismProperty.presheaf_of_isIso _ _)).1
  have _ : IsIso (Limits.pullback.lift bW
      (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν) :=
    isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS _ hβOI hβsurj
  exact ⟨bW, IsPullback.of_iso_pullback ⟨hbWν⟩
    (asIso (Limits.pullback.lift bW
      (yoneda.map (chartNormProj B S hS (hrep.snd w'))) hbWν)) hβfst hβsnd, hbWunit⟩


end ArbitraryChart

end AlgebraicGeometry.Space.NormalizationGluing

end
