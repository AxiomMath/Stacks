module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.PullbackSquare
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelationRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjDescent

/-!
# The relative Proj of an algebraic space, by étale descent

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `𝒜` be a quasi-coherent graded
`𝒪_X`-algebra. The relative homogeneous spectrum `Proj_X(𝒜)` is glued from the relative Proj of a
scheme along an étale presentation of `X`: on a surjective étale chart `U ⟶ X` with relation
`R = U ×_X U` the algebra gives relative Proj situations on `U` and on `R`, whose relative Projs
are schemes `P_U` and `P_R`; the two base changes of `P_U` along `R ⇉ U` are both `P_R`, and
`Proj_X(𝒜)` is the quotient of `P_U` by the resulting étale equivalence relation. Its structure
morphism `π : Proj_X(𝒜) ⟶ X` descends `P_U ⟶ U ⟶ X`, and over the chart it recovers `P_U`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjGlueingData`: the glueing datum, an étale presentation of
  the base, the two relative Proj situations, the two relative Projs as objects of the site, and
  the descent datum relating them.
* `AlgebraicGeometry.Space.RelativeProjGlueingData.presentationRelativeProj`: the presentation of
  `Proj_X(𝒜)` by `(P_U, P_R)`.
* `AlgebraicGeometry.Space.RelativeProjGlueingData.baseQuotient`: the quotient `U/R` of the
  relation of the presentation of the base.
* `AlgebraicGeometry.Space.RelativeProjGlueingData.toBaseQuotient`: the structure morphism
  `Proj_X(𝒜) ⟶ U/R`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjGlueingData.isPullback_chart`: the square formed by the
  chart `P_U ⟶ Proj_X(𝒜)`, the structure morphism `P_U ⟶ U`, the structure morphism to `U/R` and
  the chart `U ⟶ U/R` is cartesian.
* `AlgebraicGeometry.Space.RelativeProjGlueingData.exists_iso_baseQuotient`: the base is isomorphic
  to `U/R`, by an isomorphism carrying the atlas to the quotient map.
* `AlgebraicGeometry.Space.RelativeProjGlueingData.isPullback_chart_toBase`: the square formed by
  the chart, the structure morphism of `P_U` over `U`, the structure morphism `π` and the atlas
  `U ⟶ X` is cartesian, so `P_U = Proj_X(𝒜) ×_X U`.

## References

* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 02WV](https://stacks.math.columbia.edu/tag/02WV)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Glueing data for the relative Proj of an algebraic space: an étale presentation `(U, R)` of
`X`, the relative Proj situations that the graded algebra induces on the presenting scheme and on
the relation scheme, their relative Projs `P_U` and `P_R` as objects of the site, and the descent
datum exhibiting `P_R` as the base change of `P_U` along each of the two maps of the relation. -/
structure RelativeProjGlueingData (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) extends ProjDescentData B S hS X hX where
  /-- The relative Proj situation the algebra induces on the presenting scheme. -/
  chartSituation : Stacks.RelativeProj.Situation.{u}
  /-- The relative Proj situation the algebra induces on the relation scheme. -/
  relationSituation : Stacks.RelativeProj.Situation.{u}
  /-- The presenting scheme is the base of its situation. -/
  chartBaseIso :
    (BigFppfOver.toScheme B S hS).obj presentation.U ≅ chartSituation.base
  /-- The relation scheme is the base of its situation. -/
  relationBaseIso :
    (BigFppfOver.toScheme B S hS).obj presentation.R ≅ relationSituation.base
  /-- `P_U` is the relative Proj of the situation on the chart. -/
  projChartIso :
    (BigFppfOver.toScheme B S hS).obj projChart ≅ chartSituation.relativeProj
  /-- The structure morphism is that of the relative Proj. -/
  projChartHom_comp :
    (BigFppfOver.toScheme B S hS).map projChartHom ≫ chartBaseIso.hom =
      projChartIso.hom ≫ Stacks.RelativeProj.Situation.relativeProjToBase chartSituation
  /-- `P_R` is the relative Proj of the situation on the relation scheme. -/
  projRelationIso :
    (BigFppfOver.toScheme B S hS).obj projRelation ≅ relationSituation.relativeProj
  /-- The structure morphism is that of the relative Proj. -/
  projRelationHom_comp :
    (BigFppfOver.toScheme B S hS).map projRelationHom ≫ relationBaseIso.hom =
      projRelationIso.hom ≫ Stacks.RelativeProj.Situation.relativeProjToBase relationSituation

namespace RelativeProjGlueingData

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
  (d : RelativeProjGlueingData B S hS X hX)

/-- A cartesian square of objects of the big fppf site over `S` stays cartesian in the category of
`S`-schemes. -/
theorem isPullback_post {W Y Z T : BigFppfOver B S hS} {f : W ⟶ Y} {g : W ⟶ Z}
    {h : Y ⟶ T} {i : Z ⟶ T} (H : IsPullback f g h i) :
    IsPullback ((Over.post B.inclusion).map f) ((Over.post B.inclusion).map g)
      ((Over.post B.inclusion).map h) ((Over.post B.inclusion).map i) :=
  IsPullback.of_map_of_faithful (Over.forget _)
    ((BigFppfOver.toScheme B S hS).map_isPullback H)

/-- The relation of the presentation of the base, as a pre-relation on `U`. -/
noncomputable abbrev baseRel : PreRelation ((Over.post B.inclusion).obj d.presentation.R)
    ((Over.post B.inclusion).obj d.presentation.U) :=
  relation B S hS d.presentation.source d.presentation.target

/-- The target map of the pre-relation on `U` is the target map of the presentation. -/
theorem baseRel_target :
    d.baseRel.target = (Over.post B.inclusion).map d.presentation.target :=
  prod.lift_fst _ _

/-- The source map of the pre-relation on `U` is the source map of the presentation. -/
theorem baseRel_source :
    d.baseRel.source = (Over.post B.inclusion).map d.presentation.source :=
  prod.lift_snd _ _

/-- The relation of the presentation is an étale equivalence relation on `U`. -/
instance isEtaleEquivalenceRelation_baseRel : IsEtaleEquivalenceRelation d.baseRel :=
  d.presentation.isEtaleEquivalenceRelation

/-- `P_R ⟶ R ⟶ U` along the source map agrees with `P_R ⟶ P_U ⟶ U`. -/
theorem projRelationHom_comp_baseRel_source :
    (Over.post B.inclusion).map d.projRelationHom ≫ d.baseRel.source =
      d.pre.source ≫ (Over.post B.inclusion).map d.projChartHom := by
  rw [d.baseRel_source, d.pre_source, ← Functor.map_comp, ← Functor.map_comp,
    d.isPullback_projSource.w]

/-- `P_R ⟶ R ⟶ U` along the target map agrees with `P_R ⟶ P_U ⟶ U`. -/
theorem projRelationHom_comp_baseRel_target :
    (Over.post B.inclusion).map d.projRelationHom ≫ d.baseRel.target =
      d.pre.target ≫ (Over.post B.inclusion).map d.projChartHom := by
  rw [d.baseRel_target, d.pre_target, ← Functor.map_comp, ← Functor.map_comp,
    d.isPullback_projTarget.w]

/-- The square on source maps of the morphism of relations `(P_R ⇉ P_U) ⟶ (R ⇉ U)` is
cartesian, read in the category of `S`-schemes. -/
theorem isPullback_pre_source :
    IsPullback ((Over.post B.inclusion).map d.projRelationHom) d.pre.source
      d.baseRel.source ((Over.post B.inclusion).map d.projChartHom) := by
  rw [d.pre_source, d.baseRel_source]
  exact isPullback_post d.isPullback_projSource.flip

section Quotient

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The étale presentation of the relative Proj by `(P_U, P_R)`. -/
noncomputable def presentationRelativeProj :
    Presentation B S hS d.relativeProj d.isAlgebraicSpace_relativeProj :=
  quotientPresentation_unconditional B S hS d.projSource d.projTarget

/-! ### The base as the quotient of the presentation, and the cartesian chart square -/

/-- The base, read as the quotient of the relation of its presentation. -/
noncomputable def baseQuotient : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) d.baseRel).obj

/-- The quotient of the relation of the presentation is an algebraic space over `S`. -/
theorem isAlgebraicSpace_baseQuotient : IsAlgebraicSpace B S hS d.baseQuotient :=
  isAlgebraicSpace_quotient_unconditional B S hS d.presentation.source d.presentation.target

/-- The canonical map from the presenting scheme to the quotient of its relation. -/
noncomputable def baseChart : yoneda.obj d.presentation.U ⟶ d.baseQuotient :=
  quotientMap B S hS d.presentation.source d.presentation.target

/-- The chart of the base, read through the comparison between the presheaf represented by
`U` and its restricted functor of points. -/
theorem baseChart_eq : d.baseChart = yonedaToPoints (Over.post B.inclusion) d.presentation.U ≫
    toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) d.baseRel :=
  yonedaEquiv_symm_app_toQuotientSheaf _ _ _ _

/-- The structure morphism of the relative Proj to the quotient of the relation of the
presentation, induced by the morphism of relations `(P_R ⇉ P_U) ⟶ (R ⇉ U)`. -/
noncomputable def toBaseQuotient : d.relativeProj ⟶ d.baseQuotient :=
  (quotientSheafMap (BigFppfOver.topology B S hS) (Over.post B.inclusion) d.pre d.baseRel
    ((Over.post B.inclusion).map d.projRelationHom)
    ((Over.post B.inclusion).map d.projChartHom)
    d.projRelationHom_comp_baseRel_source d.projRelationHom_comp_baseRel_target).hom

/-- The square formed by the chart `P_U ⟶ Proj_X(𝒜)`, the structure morphism `P_U ⟶ U`, the
structure morphism to `U/R` and the chart `U ⟶ U/R` is cartesian. -/
theorem isPullback_chart :
    IsPullback d.chart (yoneda.map d.projChartHom) d.toBaseQuotient d.baseChart := by
  refine (isPullback_toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    d.pre d.baseRel _ _ d.projRelationHom_comp_baseRel_source
    d.projRelationHom_comp_baseRel_target d.isPullback_pre_source
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS _)
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS _)).of_iso'
    (asIso (yonedaToPoints (Over.post B.inclusion) d.projChart)) (Iso.refl _)
    (asIso (yonedaToPoints (Over.post B.inclusion) d.presentation.U)) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · exact d.chart_eq.symm.trans (Category.comp_id _).symm
  · exact yonedaToPoints_naturality (Over.post B.inclusion) d.projChartHom
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact d.baseChart_eq.symm.trans (Category.comp_id _).symm

/-- The structure morphism to the quotient of the presentation is the induced map on quotient
sheaves. -/
theorem toBaseQuotient_eq :
    d.toBaseQuotient = (quotientSheafMap (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      d.pre d.baseRel ((Over.post B.inclusion).map d.projRelationHom)
      ((Over.post B.inclusion).map d.projChartHom)
      d.projRelationHom_comp_baseRel_source d.projRelationHom_comp_baseRel_target).hom :=
  rfl

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- A map out of `U` to a sheaf identifying the two projections of `R` factors uniquely through the
atlas `U ⟶ X`. -/
theorem existsUnique_desc_toSpace (A : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (k : yoneda.obj d.presentation.U ⟶ A.obj)
    (hk : yoneda.map d.presentation.source ≫ k = yoneda.map d.presentation.target ≫ k) :
    ∃! c : X ⟶ A.obj, d.presentation.toSpace ≫ c = k :=
  existsUnique_desc_of_surjective_etale_atlas B S hS hX.isSheaf d.presentation.toSpace
    d.presentation.isPullback.flip d.presentation.surjective d.presentation.etale
    A.property k hk

/-- The base is isomorphic to the quotient of the relation of its presentation, by an
isomorphism carrying the atlas to the quotient map. -/
theorem exists_iso_baseQuotient :
    ∃ e : X ≅ d.baseQuotient, d.presentation.toSpace ≫ e.hom = d.baseChart := by
  obtain ⟨e, he⟩ := exists_iso_quotientSheaf_of_descent (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) d.presentation.source d.presentation.target
    d.baseRel_source d.baseRel_target hX.isSheaf d.presentation.toSpace
    d.presentation.isPullback.w.symm d.existsUnique_desc_toSpace
  exact ⟨e, he.trans d.baseChart_eq.symm⟩

/-- The square formed by the chart `P_U ⟶ Proj_X(𝒜)`, the structure morphism `P_U ⟶ U`, the
structure morphism `π : Proj_X(𝒜) ⟶ X` and the atlas `U ⟶ X` is cartesian: over an étale chart of
the base the relative Proj of the algebraic space is the relative Proj of a scheme. -/
theorem isPullback_chart_toBase :
    IsPullback d.chart (yoneda.map d.projChartHom) d.toBase d.presentation.toSpace := by
  obtain ⟨e, he⟩ := d.exists_iso_baseQuotient
  have hff : (Over.post B.inclusion).op.whiskerLeft
        (yoneda.map ((Over.post B.inclusion).map d.projChartHom)) ≫
      inv (yonedaToPoints (Over.post B.inclusion) d.presentation.U) =
      inv (yonedaToPoints (Over.post B.inclusion) d.projChart) ≫
        yoneda.map d.projChartHom := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact yonedaToPoints_naturality (Over.post B.inclusion) d.projChartHom
  have hbase : toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        d.baseRel ≫ e.inv =
      inv (yonedaToPoints (Over.post B.inclusion) d.presentation.U) ≫
        d.presentation.toSpace := by
    rw [← cancel_epi (yonedaToPoints (Over.post B.inclusion) d.presentation.U),
      IsIso.hom_inv_id_assoc]
    exact ((reassoc_of% d.baseChart_eq) e.inv).symm.trans (by simp [← he])
  have hmap : toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) d.pre ≫
      d.toBaseQuotient = (Over.post B.inclusion).op.whiskerLeft
        (yoneda.map ((Over.post B.inclusion).map d.projChartHom)) ≫
      toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) d.baseRel :=
    toQuotientSheaf_comp_quotientSheafMap (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) d.pre d.baseRel _ _
      d.projRelationHom_comp_baseRel_source d.projRelationHom_comp_baseRel_target
  have hfac : toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) d.pre ≫
      d.toBaseQuotient ≫ e.inv =
      inv (yonedaToPoints (Over.post B.inclusion) d.projChart) ≫
        yoneda.map d.projChartHom ≫ d.presentation.toSpace :=
    ((reassoc_of% hmap) e.inv).trans
      ((congrArg (_ ≫ ·) hbase).trans ((reassoc_of% hff) d.presentation.toSpace))
  have hTo : d.toBase = d.toBaseQuotient ≫ e.inv :=
    d.toBase_eq.trans (Sheaf.hom_ext_iff.mp (quotientSheafDesc_unique
      (BigFppfOver.topology B S hS) (Over.post B.inclusion) d.pre ⟨X, hX.isSheaf⟩ _
      d.sourceMap_comp ⟨d.toBaseQuotient ≫ e.inv⟩ hfac)).symm
  rw [hTo]
  exact d.isPullback_chart.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm
    (by simp) (by simp) (by simp) (by simp [← he])

end Quotient

end RelativeProjGlueingData

end AlgebraicGeometry.Space

end
