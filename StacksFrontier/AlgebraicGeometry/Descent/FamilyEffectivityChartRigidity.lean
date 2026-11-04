module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityChartTransport

/-!
# Rigidity of the charts of a descent datum relative to a family

Let `𝒰 = {X i ⟶ S}` be a family of morphisms of schemes with fixed target and let `D` be a
descent datum relative to it. A chart of `D`, in the sense of
`AlgebraicGeometry.DescentData.Chart`, is a scheme over `S` exhibiting every component of `D` as
its base change, compatibly with the gluing isomorphisms. This file records how rigid a chart
is: as soon as the canonical-descent-datum functor of the family is faithful — which along a
covering family for the fpqc topology it always is — a morphism *out of* the scheme a chart is
built on is determined by its composites with the projections of that chart, and two charts of
one datum are isomorphic over the base compatibly with their projections. It also computes the
projections of the charts `AlgebraicGeometry.DescentData.Chart.ofIso` and
`AlgebraicGeometry.DescentData.Chart.pulledBack`.

## Main definitions

* `AlgebraicGeometry.DescentData.Chart.chartHom` and
  `AlgebraicGeometry.DescentData.Chart.isoOfCharts`: the comparison morphism, respectively
  isomorphism, between the schemes two charts of one datum are built on.

## Main results

* `AlgebraicGeometry.DescentData.Chart.hom_ext_of_proj_comp_eq` and
  `AlgebraicGeometry.DescentData.Chart.hom_ext_of_proj_comp_eq_of_fpqc`: **a morphism over the
  base out of the scheme a chart is built on is determined by its composites with the projections
  of that chart.** Unlike `AlgebraicGeometry.DescentData.Chart.eq_of_proj_comp_eq` the target is
  an arbitrary scheme over the base, carrying no chart of its own.
* `AlgebraicGeometry.DescentData.Chart.proj_comp_isoOfCharts_hom`: the comparison isomorphism of
  two charts is compatible with their projections.
* `AlgebraicGeometry.DescentData.Chart.ofIso_proj` and
  `AlgebraicGeometry.DescentData.Chart.pulledBack_proj`: the projections of the transport of a
  chart along an isomorphism of descent data, respectively of the chart of a pulled-back datum.

## References

* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

namespace DescentData

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}

namespace Chart

section Projections

attribute [local implicit_reducible] CanonicalDatum.datum CanonicalDatum.functor

/-- The projections of the chart read off an isomorphism of the datum with the canonical descent
datum of a prescribed scheme over the base: the components of the isomorphism, followed by the
projection of the chosen fibre product onto that scheme. -/
lemma ofIsoCanonicalDatum_proj {D : DescentData f} (W : Over S)
    (e : D ≅ (canonicalFamilyDescentFunctor f).functor.obj W) (i : ι) :
    (ofIsoCanonicalDatum W e).proj i = (e.hom.hom i).left ≫ pullback.fst W.hom (f i) := by
  show (e.hom.hom i).left ≫ (eqToHom ((canonicalFamilyDescentFunctor f).obj W i)).left ≫
      pullback.fst W.hom (f i) = _
  simp only [eqToHom_refl, Over.id_left, Category.id_comp]

/-- The projections of the transport of a chart along an isomorphism of descent data are the
components of the inverse isomorphism followed by the original projections. -/
lemma ofIso_proj {D E : DescentData f} (e : D ≅ E) (C : D.Chart) (i : ι) :
    (ofIso e C).proj i = (e.inv.hom i).left ≫ C.proj i := by
  refine (ofIsoCanonicalDatum_proj C.base (e.symm ≪≫ C.isoCanonicalDatum) i).trans ?_
  simp only [Iso.trans_hom, Iso.symm_hom, DescentData.comp_hom, Over.comp_left, Category.assoc,
    isoCanonicalDatum_hom_hom, C.objIso_hom_left_fst]
  rfl

end Projections

/-! ### Extensionality -/

/-- **A morphism out of the scheme a chart is built on is determined by its composites with the
projections of the chart**, as soon as the canonical-descent-datum functor of the family is
faithful. The target is an arbitrary scheme over the base; no chart on it is needed. -/
theorem hom_ext_of_proj_comp_eq (hfaith : (canonicalFamilyDescentFunctor f).functor.Faithful)
    {D : DescentData f} (C : D.Chart) {T : Over S} {a b : C.base ⟶ T}
    (h : ∀ i, C.proj i ≫ a.left = C.proj i ≫ b.left) : a = b := by
  have := hfaith
  refine (canonicalFamilyDescentFunctor f).functor.map_injective (DescentData.hom_ext fun i ↦ ?_)
  have hmap : ∀ e : C.base ⟶ T, ((canonicalFamilyDescentFunctor f).functor.map e).hom i =
      (Over.pullback (f i)).map e := fun _ ↦ rfl
  rw [hmap, hmap]
  have hiso : IsIso (C.objIso i).hom.left := (Over.forget (X i)).map_isIso (C.objIso i).hom
  refine Over.OverMorphism.ext (pullback.hom_ext ?_
    (by simp only [Over.pullback_map_left, pullback.lift_snd]))
  rw [← cancel_epi (C.objIso i).hom.left]
  simp only [Over.pullback_map_left, pullback.lift_fst]
  rw [C.objIso_hom_left_fst_assoc, C.objIso_hom_left_fst_assoc]
  exact h i

/-- **A morphism out of the scheme a chart is built on is determined by its composites with the
projections of the chart**, for a datum relative to a covering family for the fpqc topology. -/
theorem hom_ext_of_proj_comp_eq_of_fpqc {𝒰 : PreZeroHypercover.{u} S}
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) {D : DescentData 𝒰.f}
    (C : D.Chart) {T : Over S} {a b : C.base ⟶ T}
    (h : ∀ i, C.proj i ≫ a.left = C.proj i ≫ b.left) : a = b :=
  (canonicalFamilyDescentFunctor_fullyFaithful_of_fpqc h𝒰).elim fun hff ↦
    hom_ext_of_proj_comp_eq hff.faithful C h

/-! ### Comparison of two charts -/

variable {𝒰 : PreZeroHypercover.{u} S}

/-- The morphism over the base between the schemes two charts of one datum relative to a covering
family for the fpqc topology are built on, compatible with their projections. -/
def chartHom (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) {D : DescentData 𝒰.f}
    (C C' : D.Chart) : C.base ⟶ C'.base :=
  (existsUnique_hom_comp_proj_eq_of_fpqc h𝒰 C C').exists.choose

/-- The morphism `chartHom` between the schemes two charts are built on intertwines their
projections: its composite with each projection of the first chart is the corresponding projection
of the second. -/
@[reassoc]
lemma proj_comp_chartHom (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S)
    {D : DescentData 𝒰.f} (C C' : D.Chart) (i : 𝒰.I₀) :
    C.proj i ≫ (chartHom h𝒰 C C').left = C'.proj i :=
  (existsUnique_hom_comp_proj_eq_of_fpqc h𝒰 C C').exists.choose_spec i

/-- **Two charts of one datum relative to a covering family for the fpqc topology are isomorphic
over the base**, compatibly with their projections. -/
def isoOfCharts (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S)
    {D : DescentData 𝒰.f} (C C' : D.Chart) : C.base ≅ C'.base where
  hom := chartHom h𝒰 C C'
  inv := chartHom h𝒰 C' C
  hom_inv_id := hom_ext_of_proj_comp_eq_of_fpqc h𝒰 C fun i ↦ by
    rw [Over.comp_left, Over.id_left, Category.comp_id, ← Category.assoc,
      proj_comp_chartHom, proj_comp_chartHom]
  inv_hom_id := hom_ext_of_proj_comp_eq_of_fpqc h𝒰 C' fun i ↦ by
    rw [Over.comp_left, Over.id_left, Category.comp_id, ← Category.assoc,
      proj_comp_chartHom, proj_comp_chartHom]

/-- The comparison isomorphism `isoOfCharts` of two charts intertwines their projections: its
composite with each projection of the first chart is the corresponding projection of the second. -/
@[reassoc]
lemma proj_comp_isoOfCharts_hom (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S)
    {D : DescentData 𝒰.f} (C C' : D.Chart) (i : 𝒰.I₀) :
    C.proj i ≫ (isoOfCharts h𝒰 C C').hom.left = C'.proj i :=
  proj_comp_chartHom h𝒰 C C' i

/-! ### The chart of a pulled-back datum -/

section PulledBackComponent

attribute [local implicit_reducible] MorphismOfSchemeFamilies.pullbackFunctor
  CanonicalDatum.datum CanonicalDatum.functor

/-- The components of the identification of the pullback of a canonical descent datum with the
canonical descent datum of the base change. -/
lemma pullbackFunctorCanonicalObjIsoOver_hom_hom (F : MorphismOfSchemeFamilies.{u})
    (W : Over F.targetBase) (i : F.sourceFamily.I₀) :
    (pullbackFunctorCanonicalObjIsoOver F W).hom.hom i =
      (pulledBackCanonicalObjIsoOver F W i).hom := by
  simp [pullbackFunctorCanonicalObjIsoOver, pulledBackCanonicalDatumIsoOver,
    DescentData.isoCanonicalDatum, DescentData.toCanonicalDatum]

end PulledBackComponent

section PulledBack

attribute [local implicit_reducible] MorphismOfSchemeFamilies.pullbackFunctor
  MorphismOfSchemeFamilies.pulledBackDatum CanonicalDatum.datum CanonicalDatum.functor

/-- **The projections of the chart of a pulled-back datum.** The chart of the pullback of `E`
along a morphism of families `F` is built on the base change of the chart of `E` along the
morphism of base schemes; projecting a component of the pulled-back datum onto it and then onto
the original scheme over the base is projecting onto the corresponding component of `E` and then
applying the original projection. -/
@[reassoc]
lemma pulledBack_proj (F : MorphismOfSchemeFamilies.{u}) {E : DescentData F.targetFamily.f}
    (C : E.Chart) (i : F.sourceFamily.I₀) :
    (pulledBack F C).proj i ≫ pullback.fst C.base.hom F.baseHom =
      (MorphismOfSchemeFamilies.pulledBackDatumObjIso F E i).hom.left ≫
        pullback.fst (E.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i) ≫
        C.proj (F.familyHom.s₀ i) := by
  have h1 : (((MorphismOfSchemeFamilies.pullbackFunctor F).functor.mapIso C.isoCanonicalDatum ≪≫
        pullbackFunctorCanonicalObjIsoOver F C.base).hom.hom i).left =
      ((Over.pullback (F.familyHom.h₀ i)).map (C.objIso (F.familyHom.s₀ i)).hom).left ≫
        (pulledBackCanonicalObjIsoOver F C.base i).hom.left := by
    rw [Iso.trans_hom, DescentData.comp_hom, Over.comp_left, Functor.mapIso_hom,
      pullbackFunctor_map_hom, isoCanonicalDatum_hom_hom,
      pullbackFunctorCanonicalObjIsoOver_hom_hom]
  have h2 : (MorphismOfSchemeFamilies.pulledBackDatumObjIso F
      (CanonicalDatum.datum F.targetFamily.f C.base) i).hom.left = 𝟙 _ := rfl
  show (ofIsoCanonicalDatum ((Over.pullback F.baseHom).obj C.base)
      ((MorphismOfSchemeFamilies.pullbackFunctor F).functor.mapIso C.isoCanonicalDatum ≪≫
        pullbackFunctorCanonicalObjIsoOver F C.base)).proj i ≫ _ = _
  rw [ofIsoCanonicalDatum_proj, h1]
  dsimp only [ofIsoCanonicalDatum_base, Over.pullback_obj_left, Over.pullback_obj_hom]
  simp only [Category.assoc]
  rw [pulledBackCanonicalObjIsoOver_hom_left_fst_fst F C.base i, h2, Category.id_comp]
  dsimp only [CanonicalDatum.datum, Over.pullback_obj_left, Over.pullback_obj_hom]
  simp only [Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst_assoc,
    Category.assoc]
  rw [C.objIso_hom_left_fst]
  rfl

end PulledBack

end Chart

end DescentData

end AlgebraicGeometry

end

end
