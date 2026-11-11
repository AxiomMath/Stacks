module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.PullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelationRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional

/-!
# Étale descent of a scheme over a presentation of an algebraic space

This file gives a generic étale-descent quotient construction. The input is an étale
presentation `(U, R)` of an algebraic space `X`, objects `P_U` over `U` and `P_R` over `R` of
the site, two maps `P_R ⇉ P_U` exhibiting `P_R` as the base change of `P_U` along each of the
two maps `R ⇉ U`, and the condition that these two maps form an equivalence relation. The output
is the quotient sheaf of the étale equivalence relation `P_R ⇉ P_U`, which is an algebraic space,
together with its morphism to `X`.

Nothing here refers to a graded algebra: `P_U` and `P_R` are arbitrary. The construction is the
glueing description of the relative Proj that follows Stacks 084C when `P_U` and `P_R` are the
relative Projs over `U` and `R`, which is where the names come from. The relative Proj
`Proj_X(𝒜)` of Stacks 084C itself, the algebraic space `F` of Stacks 084B, is
`AlgebraicGeometry.Space.RelativeProjSituation.Proj`.

## Main definitions

* `AlgebraicGeometry.Space.ProjDescentData`: the descent datum.
* `AlgebraicGeometry.Space.ProjDescentData.relativeProj`: the quotient of `P_U` by `P_R`.
* `AlgebraicGeometry.Space.ProjDescentData.toBase`: its morphism to the base.

## Main results

* `AlgebraicGeometry.Space.ProjDescentData.isAlgebraicSpace_relativeProj`: the quotient is an
  algebraic space.
* `AlgebraicGeometry.Space.ProjDescentData.chart_comp_toBase`: the morphism to the base
  restricted to the chart is `P_U ⟶ U ⟶ X`.
* `AlgebraicGeometry.Space.ProjDescentData.chart_isKernelPair`: `P_U ×_Q P_U = P_R` for the
  quotient `Q`.

## References

* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C), the glueing description
  following the definition
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Étale descent data over a presentation of an algebraic space.** An étale presentation
`(U, R)` of `X`, objects `P_U` and `P_R` of the site over the presenting scheme and the relation
scheme, and the descent datum exhibiting `P_R` as the base change of `P_U` along each of the two
maps of the relation. The objects are arbitrary; for the relative Projs `P_U` and `P_R` this is
the glueing datum following Stacks 084C. -/
structure ProjDescentData (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) where
  /-- An étale presentation of the base. -/
  presentation : Presentation B S hS X hX
  /-- The object `P_U` over the chart, as an object of the site. -/
  projChart : BigFppfOver B S hS
  /-- Its structure morphism to the chart. -/
  projChartHom : projChart ⟶ presentation.U
  /-- The object `P_R` over the relation scheme, as an object of the site. -/
  projRelation : BigFppfOver B S hS
  /-- Its structure morphism to the relation scheme. -/
  projRelationHom : projRelation ⟶ presentation.R
  /-- The target projection `P_R ⟶ P_U`. -/
  projTarget : projRelation ⟶ projChart
  /-- The source projection `P_R ⟶ P_U`. -/
  projSource : projRelation ⟶ projChart
  /-- `P_R` is the base change of `P_U` along the target map of the relation. -/
  isPullback_projTarget :
    IsPullback projTarget projRelationHom projChartHom presentation.target
  /-- `P_R` is the base change of `P_U` along the source map of the relation. -/
  isPullback_projSource :
    IsPullback projSource projRelationHom projChartHom presentation.source
  /-- The two projections of `P_R` onto `P_U` form an internal equivalence relation: the
  normalisation and cocycle conditions of the descent datum. -/
  projIsEquivalenceRelation : CategoryTheory.IsEquivalenceRelation
    ((Over.post B.inclusion).map projTarget) ((Over.post B.inclusion).map projSource)

namespace ProjDescentData

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
  (d : ProjDescentData B S hS X hX)

/-- The pre-relation on `P_U` given by the two projections of `P_R`. -/
noncomputable abbrev pre : PreRelation ((Over.post B.inclusion).obj d.projRelation)
    ((Over.post B.inclusion).obj d.projChart) :=
  relation B S hS d.projSource d.projTarget

/-- The target map of the pre-relation on `P_U` is the first projection of `P_R`. -/
theorem pre_target : d.pre.target = (Over.post B.inclusion).map d.projTarget :=
  prod.lift_fst _ _

/-- The source map of the pre-relation on `P_U` is the second projection of `P_R`. -/
theorem pre_source : d.pre.source = (Over.post B.inclusion).map d.projSource :=
  prod.lift_snd _ _

/-- The source map of the presentation is étale. -/
theorem etale_map_source :
    Etale ((BigFppfOver.toScheme B S hS).map d.presentation.source) := by
  have h := d.presentation.isEtaleEquivalenceRelation.etale_source
  have e : PreRelation.source (prod.lift ((Over.post B.inclusion).map d.presentation.target)
      ((Over.post B.inclusion).map d.presentation.source)) =
      (Over.post B.inclusion).map d.presentation.source := prod.lift_snd _ _
  rwa [e] at h

/-- The target map of the presentation is étale. -/
theorem etale_map_target :
    Etale ((BigFppfOver.toScheme B S hS).map d.presentation.target) := by
  have h := d.presentation.isEtaleEquivalenceRelation.etale_target
  have e : PreRelation.target (prod.lift ((Over.post B.inclusion).map d.presentation.target)
      ((Over.post B.inclusion).map d.presentation.source)) =
      (Over.post B.inclusion).map d.presentation.target := prod.lift_fst _ _
  rwa [e] at h

/-- The base change of an étale morphism of the site is étale. -/
private theorem etale_map_of_isPullback {P Q T V : BigFppfOver B S hS} {f : P ⟶ Q} {g : P ⟶ T}
    {h : Q ⟶ V} {k : T ⟶ V} (hp : IsPullback f g h k)
    (hk : Etale ((BigFppfOver.toScheme B S hS).map k)) :
    Etale ((BigFppfOver.toScheme B S hS).map f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (((BigFppfOver.toScheme B S hS).map_isPullback hp).flip) hk

/-- The source projection of `P_R` onto `P_U` is étale. -/
theorem etale_map_projSource :
    Etale ((BigFppfOver.toScheme B S hS).map d.projSource) :=
  etale_map_of_isPullback d.isPullback_projSource d.etale_map_source

/-- The target projection of `P_R` onto `P_U` is étale. -/
theorem etale_map_projTarget :
    Etale ((BigFppfOver.toScheme B S hS).map d.projTarget) :=
  etale_map_of_isPullback d.isPullback_projTarget d.etale_map_target

/-- The two projections of `P_R` onto `P_U` form an étale equivalence relation. -/
instance isEtaleEquivalenceRelation_pre :
    IsEtaleEquivalenceRelation (relation B S hS d.projSource d.projTarget) := by
  have hEq : CategoryTheory.IsEquivalenceRelation
      (PreRelation.target (relation B S hS d.projSource d.projTarget))
      (PreRelation.source (relation B S hS d.projSource d.projTarget)) := by
    rw [d.pre_target, d.pre_source]; exact d.projIsEquivalenceRelation
  have hs : Etale (PreRelation.source
      (relation B S hS d.projSource d.projTarget)).left := by
    rw [d.pre_source]; exact d.etale_map_projSource
  have ht : Etale (PreRelation.target
      (relation B S hS d.projSource d.projTarget)).left := by
    rw [d.pre_target]; exact d.etale_map_projTarget
  exact ⟨⟩

/-- The composite `P_U ⟶ U ⟶ X` identifies the two projections of `P_R`. -/
theorem map_comp_toSpace :
    yoneda.map d.projSource ≫ yoneda.map d.projChartHom ≫ d.presentation.toSpace =
      yoneda.map d.projTarget ≫ yoneda.map d.projChartHom ≫ d.presentation.toSpace := by
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, d.isPullback_projSource.w,
    d.isPullback_projTarget.w, Functor.map_comp_assoc, Functor.map_comp_assoc,
    d.presentation.isPullback.w]

section Quotient

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- The étale-descent quotient: the quotient sheaf of `P_U` by the étale equivalence relation
`P_R ⇉ P_U` that the descent datum provides. When `P_U` and `P_R` are the relative Projs over
`U` and `R` this is the glueing description of the relative Proj following Stacks 084C; the
relative Proj itself is `AlgebraicGeometry.Space.RelativeProjSituation.Proj`. -/
noncomputable def relativeProj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS d.projSource d.projTarget)).obj

/-- The étale-descent quotient is an algebraic space over the base scheme. -/
theorem isAlgebraicSpace_relativeProj : IsAlgebraicSpace B S hS d.relativeProj :=
  isAlgebraicSpace_quotient_unconditional B S hS d.projSource d.projTarget

/-- The étale chart `P_U ⟶ Q` of the étale-descent quotient `Q`. -/
noncomputable def chart : yoneda.obj d.projChart ⟶ d.relativeProj :=
  quotientMap B S hS d.projSource d.projTarget

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The map `P_U ⟶ U ⟶ X`, read on the restricted functor of points, identifies the two
projections of `P_R`. -/
theorem sourceMap_comp :
    Stacks.Groupoids.sourceMap (Over.post B.inclusion)
          (relation B S hS d.projSource d.projTarget) ≫
        (inv (yonedaToPoints (Over.post B.inclusion) d.projChart) ≫
          yoneda.map d.projChartHom ≫ d.presentation.toSpace) =
      Stacks.Groupoids.targetMap (Over.post B.inclusion)
          (relation B S hS d.projSource d.projTarget) ≫
        (inv (yonedaToPoints (Over.post B.inclusion) d.projChart) ≫
          yoneda.map d.projChartHom ≫ d.presentation.toSpace) := by
  rw [← cancel_epi (yonedaToPoints (Over.post B.inclusion) d.projRelation), ← Category.assoc,
    yonedaToPoints_comp_sourceMap (Over.post B.inclusion) d.projSource d.pre_source,
    ← Category.assoc (yonedaToPoints (Over.post B.inclusion) d.projRelation),
    yonedaToPoints_comp_targetMap (Over.post B.inclusion) d.projTarget d.pre_target,
    Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc]
  exact d.map_comp_toSpace

/-- The morphism `Q ⟶ X` from the étale-descent quotient `Q` to the base: the descent of
`P_U ⟶ U ⟶ X` along the quotient map. -/
noncomputable def toBase : d.relativeProj ⟶ X :=
  (quotientSheafDesc (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS d.projSource d.projTarget) ⟨X, hX.isSheaf⟩
    (inv (yonedaToPoints (Over.post B.inclusion) d.projChart) ≫
      yoneda.map d.projChartHom ≫ d.presentation.toSpace) d.sourceMap_comp).hom

/-- The chart of the quotient, read through the comparison between the presheaf
represented by `P_U` and its restricted functor of points. -/
theorem chart_eq : d.chart = yonedaToPoints (Over.post B.inclusion) d.projChart ≫
    toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) d.pre :=
  yonedaEquiv_symm_app_toQuotientSheaf _ _ _ _

/-- The morphism of the quotient to the base is the descent of `P_U ⟶ U ⟶ X` along
`toQuotientSheaf`. -/
theorem toBase_eq : d.toBase = (quotientSheafDesc (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) d.pre ⟨X, hX.isSheaf⟩
    (inv (yonedaToPoints (Over.post B.inclusion) d.projChart) ≫
      yoneda.map d.projChartHom ≫ d.presentation.toSpace) d.sourceMap_comp).hom :=
  rfl

/-- The morphism of the quotient to the base restricts along the chart to the structure
morphism of `P_U` over `U` followed by the atlas of the base. -/
theorem chart_comp_toBase :
    d.chart ≫ d.toBase = yoneda.map d.projChartHom ≫ d.presentation.toSpace := by
  rw [d.chart_eq, d.toBase_eq]
  exact (Category.assoc _ _ _).trans ((yonedaToPoints (Over.post B.inclusion) d.projChart ≫=
    toQuotientSheaf_quotientSheafDesc _ _ _ _ _ _).trans (IsIso.hom_inv_id_assoc _ _))

/-- The chart `P_U ⟶ Q` is surjective after every representable base change. -/
theorem chart_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) d.chart :=
  quotientMap_surjective_unconditional B S hS d.projSource d.projTarget

/-- The chart `P_U ⟶ Q` is étale after every representable base change. -/
theorem chart_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) d.chart :=
  quotientMap_etale_unconditional B S hS d.projSource d.projTarget

/-- The two projections `P_R ⇉ P_U` form the kernel pair of the chart:
`P_U ×_Q P_U = P_R`. -/
theorem chart_isKernelPair :
    IsPullback (yoneda.map d.projTarget) (yoneda.map d.projSource) d.chart d.chart :=
  quotientMap_isPullback B S hS d.projSource d.projTarget

end Quotient

end ProjDescentData

end AlgebraicGeometry.Space
