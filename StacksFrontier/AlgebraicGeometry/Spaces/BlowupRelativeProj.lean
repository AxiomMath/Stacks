module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesPullbackFlat
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjGlueing

/-!
# The blowing up of an algebraic space along a closed subspace

Let `S` be a scheme, let `X` be an algebraic space over `S`, let `ℐ ⊆ 𝒪_X` be a quasi-coherent
sheaf of ideals and let `Z ⊆ X` be the closed subspace it cuts out. The *blowing up of `X` along
`Z`* is the structure morphism

`b : Proj_X(⨁_{n ≥ 0} ℐⁿ) ⟶ X`

of the relative homogeneous spectrum of the Rees algebra of `ℐ`; its *exceptional divisor* is the
inverse image `b⁻¹(Z)`, and `Z` is called its *centre*.

For a surjective étale presentation `(U, R)` of `X`, the sheaf of ideals `ℐ` induces sheaves of
ideals `ℐ|_U` on `U` and `ℐ|_R` on `R`, whose Rees algebras are relative Proj situations with
relative Projs `P_U` and `P_R`. Both legs `R ⇉ U` of the relation carry `ℐ|_U` to `ℐ|_R`, both base
changes of `P_U` along them are `P_R`, and the blowup is the quotient of `P_U` by the equivalence
relation `P_R ⇉ P_U` on the big fppf site. The condition that `P_R ⇉ P_U` is an equivalence
relation is a hypothesis `heq` of the construction.

## Main definitions

* `Stacks.Blowup.reesSituationBaseChange` is the comparison morphism identifying the relative Proj
  of the Rees algebra of an inverse image ideal with the base change of the relative Proj of the
  Rees algebra, for a flat morphism of schemes.
* `AlgebraicGeometry.Space.presentationChart` and
  `AlgebraicGeometry.Space.presentationRelationChart` read the presenting scheme and the relation
  scheme of an étale presentation as étale charts of the algebraic space, and
  `AlgebraicGeometry.Space.presentationRelationSourceHom` and
  `AlgebraicGeometry.Space.presentationRelationTargetHom` are the two legs of the relation as
  morphisms of charts.
* `AlgebraicGeometry.Space.reesChartSituation` and `AlgebraicGeometry.Space.reesRelationSituation`
  are the Rees algebras of the induced sheaves of ideals on those two schemes, as relative Proj
  situations.
* `AlgebraicGeometry.Space.reesProjChart`, `AlgebraicGeometry.Space.reesProjRelation`,
  `AlgebraicGeometry.Space.reesProjSource` and `AlgebraicGeometry.Space.reesProjTarget` are `P_U`
  and `P_R` as objects of the big fppf site over `S`, together with the two projections of `P_R`
  onto `P_U`.
* `AlgebraicGeometry.Space.reesGlueingData` assembles all of these into the glueing datum of the
  relative Proj of an algebraic space.
* `AlgebraicGeometry.Space.blowUp` is the blowup of `X` along the closed subspace cut out by a
  quasi-coherent sheaf of ideals, `AlgebraicGeometry.Space.blowUpToBase` is its structure morphism,
  and `AlgebraicGeometry.Space.blowUpSpace` and `AlgebraicGeometry.Space.blowUpHom` are the two of
  them read in the category of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.blowUpAlong`, `AlgebraicGeometry.Space.blowUpAlongHom` and
  `AlgebraicGeometry.Space.exceptionalDivisor` are the blowup of `X` along a closed subspace `Z`,
  its structure morphism `b`, and the exceptional divisor `b⁻¹(Z)`.

## Main results

* `Stacks.Blowup.isPullback_reesSituationBaseChange`: for a flat morphism of schemes the relative
  Proj of the Rees algebra of the inverse image ideal is the base change of the relative Proj of
  the Rees algebra.
* `AlgebraicGeometry.Space.isPullback_reesProjSource` and
  `AlgebraicGeometry.Space.isPullback_reesProjTarget`: `P_R` is the base change of `P_U` along the
  source and along the target leg of the relation.
* `AlgebraicGeometry.Space.comap_reesChartIdeal_source` and
  `AlgebraicGeometry.Space.comap_reesChartIdeal_target`: both legs of the relation carry the
  induced sheaf of ideals on `U` to the induced sheaf of ideals on `R`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_blowUp`: the blowup is an algebraic space over `S`.

## References

* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Blowup

/-! ### The base change of the relative Proj of a Rees algebra -/

/-- The comparison `Φ` for the Rees algebras of an ideal and of its inverse image, read at a sheaf
of ideals `J` on the source presented as the inverse image of `ℐ`. -/
def reesSituationTransportedPullbackHom {Z X : Scheme.{u}} (g : Z ⟶ X)
    (I : X.IdealSheafData) {J : Z.IdealSheafData} (h : I.comap g = J) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.Conormal.gradedPullback g (reesSituation I).algebra)
      (reesSituation J).algebra :=
  h ▸ reesSituationGradedPullbackHom g I

/-- For a flat morphism the transported comparison is invertible in every nonnegative
degree. -/
lemma isIso_reesSituationTransportedPullbackHom_app {Z X : Scheme.{u}} (g : Z ⟶ X)
    [AlgebraicGeometry.Flat g] (I : X.IdealSheafData) {J : Z.IdealSheafData}
    (h : I.comap g = J) (m : ℕ) :
    IsIso ((reesSituationTransportedPullbackHom g I h).app (m : ℤ)) := by
  subst h
  exact isIso_reesSituationGradedPullbackHom_app g I m

/-- The comparison morphism `Proj_Z(⨁ₙ Jⁿ) ⟶ Proj_X(⨁ₙ ℐⁿ)` attached to a flat morphism `g : Z ⟶ X`
of schemes and a presentation of the sheaf of ideals `J` as the inverse image of `ℐ`. -/
def reesSituationBaseChange {Z X : Scheme.{u}} (g : Z ⟶ X)
    [AlgebraicGeometry.Flat g] (I : X.IdealSheafData) {J : Z.IdealSheafData}
    (h : I.comap g = J) :
    (reesSituation J).relativeProj ⟶ (reesSituation I).relativeProj :=
  Stacks.RelativeProj.Situation.relativeProjBaseChange g
    (reesSituationTransportedPullbackHom g I h)
    (fun m ↦ isIso_reesSituationTransportedPullbackHom_app g I h m)

/-- The relative Proj of the Rees algebra of an inverse image ideal is a base change: for a flat
`g : Z ⟶ X` the square formed by the comparison morphism, the two structure morphisms and `g` is
cartesian, so `Proj_Z(⨁ₙ (ℐ𝒪_Z)ⁿ) = Z ×_X Proj_X(⨁ₙ ℐⁿ)`. -/
theorem isPullback_reesSituationBaseChange {Z X : Scheme.{u}} (g : Z ⟶ X)
    [AlgebraicGeometry.Flat g] (I : X.IdealSheafData) {J : Z.IdealSheafData}
    (h : I.comap g = J) :
    IsPullback (reesSituationBaseChange g I h) (reesSituation J).relativeProjToBase
      (reesSituation I).relativeProjToBase g :=
  @Stacks.RelativeProj.Situation.isPullback_relativeProjBaseChange
    (reesSituation I) (reesSituation J) g (reesSituationTransportedPullbackHom g I h)
    (fun m ↦ isIso_reesSituationTransportedPullbackHom_app g I h m)

/-- The comparison morphism is a morphism over `g`. -/
theorem reesSituationBaseChange_comp_relativeProjToBase {Z X : Scheme.{u}} (g : Z ⟶ X)
    [AlgebraicGeometry.Flat g] (I : X.IdealSheafData) {J : Z.IdealSheafData}
    (h : I.comap g = J) :
    reesSituationBaseChange g I h ≫ (reesSituation I).relativeProjToBase =
      (reesSituation J).relativeProjToBase ≫ g :=
  (isPullback_reesSituationBaseChange g I h).w

end Stacks.Blowup

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS}

/-! ### The legs of an étale presentation -/

/-- The source leg of the relation of an étale presentation is an étale morphism of
schemes. -/
theorem etale_toScheme_map_presentation_source (P : Presentation B S hS X.obj X.property) :
    Etale ((BigFppfOver.toScheme B S hS).map P.source) := by
  have h := P.isEtaleEquivalenceRelation.etale_source
  have e : Stacks.Groupoids.PreRelation.source
      (Limits.prod.lift ((Over.post B.inclusion).map P.target)
        ((Over.post B.inclusion).map P.source)) =
      (Over.post B.inclusion).map P.source := Limits.prod.lift_snd _ _
  rwa [e] at h

/-- The target leg of the relation of an étale presentation is an étale morphism of
schemes. -/
theorem etale_toScheme_map_presentation_target (P : Presentation B S hS X.obj X.property) :
    Etale ((BigFppfOver.toScheme B S hS).map P.target) := by
  have h := P.isEtaleEquivalenceRelation.etale_target
  have e : Stacks.Groupoids.PreRelation.target
      (Limits.prod.lift ((Over.post B.inclusion).map P.target)
        ((Over.post B.inclusion).map P.source)) =
      (Over.post B.inclusion).map P.target := Limits.prod.lift_fst _ _
  rwa [e] at h

/-- The source leg of the relation of an étale presentation is flat. -/
theorem flat_toScheme_map_presentation_source (P : Presentation B S hS X.obj X.property) :
    AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map P.source) :=
  have := etale_toScheme_map_presentation_source P
  inferInstance

/-- The target leg of the relation of an étale presentation is flat. -/
theorem flat_toScheme_map_presentation_target (P : Presentation B S hS X.obj X.property) :
    AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map P.target) :=
  have := etale_toScheme_map_presentation_target P
  inferInstance

variable (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
  (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
  (P : Presentation B S hS X.obj X.property)

/-- The presenting scheme of an étale presentation, read as an étale chart of the algebraic
space through the atlas. -/
def presentationChart : SmallEtale B S hS X.obj := ⟨CostructuredArrow.mk P.toSpace, P.etale⟩

/-- The relation scheme of an étale presentation, read as an étale chart of the algebraic space
through the source leg followed by the atlas. -/
def presentationRelationChart : SmallEtale B S hS X.obj :=
  ⟨CostructuredArrow.mk (yoneda.map P.source ≫ P.toSpace),
    etale_comp_of_scheme B S hS P.source P.toSpace
      (etale_toScheme_map_presentation_source P) P.etale⟩

/-- The source leg of the relation, as a morphism of étale charts. -/
def presentationRelationSourceHom : presentationRelationChart P ⟶ presentationChart P :=
  ObjectProperty.homMk (CostructuredArrow.homMk P.source rfl)

/-- The target leg of the relation, as a morphism of étale charts. -/
def presentationRelationTargetHom : presentationRelationChart P ⟶ presentationChart P :=
  ObjectProperty.homMk (CostructuredArrow.homMk P.target P.isPullback.w)

/-! ### The Rees algebras on the presenting scheme and on the relation scheme -/

/-- The sheaf of ideals that a quasi-coherent sheaf of ideals of `𝒪_X` induces on the
presenting scheme of an étale presentation. -/
abbrev reesChartIdeal : ((BigFppfOver.toScheme B S hS).obj P.U).IdealSheafData :=
  idealSheafDataOfChart B S hS X N hN (presentationChart P)

/-- The sheaf of ideals that a quasi-coherent sheaf of ideals of `𝒪_X` induces on the relation
scheme of an étale presentation. -/
abbrev reesRelationIdeal : ((BigFppfOver.toScheme B S hS).obj P.R).IdealSheafData :=
  idealSheafDataOfChart B S hS X N hN (presentationRelationChart P)

/-- The Rees algebra `⨁_{n ≥ 0} (ℐ|_U)ⁿ` on the presenting scheme, as a relative Proj
situation. -/
abbrev reesChartSituation : Stacks.RelativeProj.Situation.{u} :=
  Stacks.Blowup.reesSituation (reesChartIdeal N hN P)

/-- The Rees algebra `⨁_{n ≥ 0} (ℐ|_R)ⁿ` on the relation scheme, as a relative Proj
situation. -/
abbrev reesRelationSituation : Stacks.RelativeProj.Situation.{u} :=
  Stacks.Blowup.reesSituation (reesRelationIdeal N hN P)

/-- The source leg of the relation carries `ℐ|_U` to `ℐ|_R`. -/
theorem comap_reesChartIdeal_source :
    (reesChartIdeal N hN P).comap ((BigFppfOver.toScheme B S hS).map P.source) =
      reesRelationIdeal N hN P :=
  comap_idealSheafDataOfChart B S hS X N hN (presentationRelationSourceHom P)

/-- The target leg of the relation carries `ℐ|_U` to `ℐ|_R`. -/
theorem comap_reesChartIdeal_target :
    (reesChartIdeal N hN P).comap ((BigFppfOver.toScheme B S hS).map P.target) =
      reesRelationIdeal N hN P :=
  comap_idealSheafDataOfChart B S hS X N hN (presentationRelationTargetHom P)

/-! ### The two relative Projs as objects of the site -/

variable (hcU : B.Contains (reesChartSituation N hN P).relativeProj)
  (hcR : B.Contains (reesRelationSituation N hN P).relativeProj)

/-- `P_U`, the relative Proj of the Rees algebra on the presenting scheme, as an object of the
big fppf site over `S`. -/
def reesProjChart : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hcU
    ((reesChartSituation N hN P).relativeProjToBase ≫ B.inclusion.map P.U.hom)

/-- `P_R`, the relative Proj of the Rees algebra on the relation scheme, as an object of the
big fppf site over `S`. -/
def reesProjRelation : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hcR
    ((reesRelationSituation N hN P).relativeProjToBase ≫ B.inclusion.map P.R.hom)

/-- The structure morphism `P_U ⟶ U`. -/
def reesProjChartHom : reesProjChart N hN P hcU ⟶ P.U :=
  Over.homMk (ObjectProperty.homMk (reesChartSituation N hN P).relativeProjToBase)
    (ObjectProperty.hom_ext _ rfl)

/-- The structure morphism `P_R ⟶ R`. -/
def reesProjRelationHom : reesProjRelation N hN P hcR ⟶ P.R :=
  Over.homMk (ObjectProperty.homMk (reesRelationSituation N hN P).relativeProjToBase)
    (ObjectProperty.hom_ext _ rfl)

/-- A comparison morphism `P_R ⟶ P_U` over a leg of the relation is a morphism over `S`. -/
theorem reesSituationBaseChange_comp_structureMap {g : P.R ⟶ P.U}
    [AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map g)]
    (h : (reesChartIdeal N hN P).comap ((BigFppfOver.toScheme B S hS).map g) =
      reesRelationIdeal N hN P) :
    (ObjectProperty.homMk (Stacks.Blowup.reesSituationBaseChange
          ((BigFppfOver.toScheme B S hS).map g) (reesChartIdeal N hN P) h) :
        (reesProjRelation N hN P hcR).left ⟶ (reesProjChart N hN P hcU).left) ≫
        (reesProjChart N hN P hcU).hom =
      (reesProjRelation N hN P hcR).hom := by
  refine ObjectProperty.hom_ext _ ?_
  show Stacks.Blowup.reesSituationBaseChange _ (reesChartIdeal N hN P) h ≫
      (reesChartSituation N hN P).relativeProjToBase ≫ B.inclusion.map P.U.hom =
    (reesRelationSituation N hN P).relativeProjToBase ≫ B.inclusion.map P.R.hom
  have hw : (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map P.U.hom =
      B.inclusion.map P.R.hom :=
    (Functor.map_comp _ _ _).symm.trans (congrArg B.inclusion.map (Over.w g))
  exact ((reassoc_of% (Stacks.Blowup.reesSituationBaseChange_comp_relativeProjToBase _ _ h))
    _).trans (congrArg (_ ≫ ·) hw)

/-- The source projection `P_R ⟶ P_U`, the comparison morphism of relative Projs over the
source leg of the relation. -/
def reesProjSource : reesProjRelation N hN P hcR ⟶ reesProjChart N hN P hcU :=
  haveI := flat_toScheme_map_presentation_source P
  Over.homMk (ObjectProperty.homMk (Stacks.Blowup.reesSituationBaseChange
      ((BigFppfOver.toScheme B S hS).map P.source) (reesChartIdeal N hN P)
      (comap_reesChartIdeal_source N hN P)))
    (reesSituationBaseChange_comp_structureMap N hN P hcU hcR (comap_reesChartIdeal_source N hN P))

/-- The target projection `P_R ⟶ P_U`, the comparison morphism of relative Projs over the
target leg of the relation. -/
def reesProjTarget : reesProjRelation N hN P hcR ⟶ reesProjChart N hN P hcU :=
  haveI := flat_toScheme_map_presentation_target P
  Over.homMk (ObjectProperty.homMk (Stacks.Blowup.reesSituationBaseChange
      ((BigFppfOver.toScheme B S hS).map P.target) (reesChartIdeal N hN P)
      (comap_reesChartIdeal_target N hN P)))
    (reesSituationBaseChange_comp_structureMap N hN P hcU hcR (comap_reesChartIdeal_target N hN P))

/-- `P_R` is the base change of `P_U` along a flat leg `g` of the relation carrying `ℐ|_U` to
`ℐ|_R`. -/
private theorem isPullback_reesProj_of_comap {g : P.R ⟶ P.U}
    [AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map g)]
    (h : (reesChartIdeal N hN P).comap ((BigFppfOver.toScheme B S hS).map g) =
      reesRelationIdeal N hN P) :
    IsPullback
      (Over.homMk (ObjectProperty.homMk (Stacks.Blowup.reesSituationBaseChange
        ((BigFppfOver.toScheme B S hS).map g) (reesChartIdeal N hN P) h))
        (reesSituationBaseChange_comp_structureMap N hN P hcU hcR h) :
        reesProjRelation N hN P hcR ⟶ reesProjChart N hN P hcU)
      (reesProjRelationHom N hN P hcR) (reesProjChartHom N hN P hcU) g :=
  IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (Stacks.Blowup.isPullback_reesSituationBaseChange _ _ h)

/-- `P_R` is the base change of `P_U` along the source leg of the relation. -/
theorem isPullback_reesProjSource :
    IsPullback (reesProjSource N hN P hcU hcR) (reesProjRelationHom N hN P hcR)
      (reesProjChartHom N hN P hcU) P.source :=
  have := flat_toScheme_map_presentation_source P
  isPullback_reesProj_of_comap N hN P hcU hcR (comap_reesChartIdeal_source N hN P)

/-- `P_R` is the base change of `P_U` along the target leg of the relation. -/
theorem isPullback_reesProjTarget :
    IsPullback (reesProjTarget N hN P hcU hcR) (reesProjRelationHom N hN P hcR)
      (reesProjChartHom N hN P hcU) P.target :=
  have := flat_toScheme_map_presentation_target P
  isPullback_reesProj_of_comap N hN P hcU hcR (comap_reesChartIdeal_target N hN P)

/-! ### The glueing datum and the blowup -/

/-- The glueing datum of the relative Proj of the Rees algebra of a quasi-coherent sheaf of ideals
on an algebraic space, given that the two projections `P_R ⇉ P_U` form an equivalence relation. -/
def reesGlueingData
    (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR))) :
    RelativeProjGlueingData B S hS X.obj X.property where
  presentation := P
  chartSituation := reesChartSituation N hN P
  relationSituation := reesRelationSituation N hN P
  chartBaseIso := Iso.refl _
  relationBaseIso := Iso.refl _
  projChart := reesProjChart N hN P hcU
  projChartIso := Iso.refl _
  projChartHom := reesProjChartHom N hN P hcU
  projChartHom_comp := (Category.comp_id _).trans (Category.id_comp _).symm
  projRelation := reesProjRelation N hN P hcR
  projRelationIso := Iso.refl _
  projRelationHom := reesProjRelationHom N hN P hcR
  projRelationHom_comp := (Category.comp_id _).trans (Category.id_comp _).symm
  projTarget := reesProjTarget N hN P hcU hcR
  projSource := reesProjSource N hN P hcU hcR
  isPullback_projTarget := isPullback_reesProjTarget N hN P hcU hcR
  isPullback_projSource := isPullback_reesProjSource N hN P hcU hcR
  projIsEquivalenceRelation := heq

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- The blowup of an algebraic space in the closed subspace cut out by a quasi-coherent sheaf of
ideals `ℐ`: the relative Proj `Proj_X(⨁_{n ≥ 0} ℐⁿ)` of the Rees algebra of `ℐ`, glued from the
relative Proj of the Rees algebra on an étale chart. -/
def blowUp
    (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR))) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (reesGlueingData N hN P hcU hcR heq).relativeProj

/-- The blowup is an algebraic space over `S`. -/
theorem isAlgebraicSpace_blowUp
    (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR))) :
    IsAlgebraicSpace B S hS (blowUp N hN P hcU hcR heq) :=
  (reesGlueingData N hN P hcU hcR heq).isAlgebraicSpace_relativeProj

/-- The structure morphism `b` of the blowup, the descent of `P_U ⟶ U ⟶ X`. -/
def blowUpToBase
    (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR))) :
    blowUp N hN P hcU hcR heq ⟶ X.obj :=
  (reesGlueingData N hN P hcU hcR heq).toBase

/-- The blowup, as an object of the category of algebraic spaces over `S`. -/
def blowUpSpace
    (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR))) :
    AlgebraicSpaces B S hS :=
  ⟨blowUp N hN P hcU hcR heq, isAlgebraicSpace_blowUp N hN P hcU hcR heq⟩

/-- The structure morphism of the blowup, as a morphism of algebraic spaces over `S`. -/
def blowUpHom
    (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR))) :
    blowUpSpace N hN P hcU hcR heq ⟶ X :=
  ObjectProperty.homMk (blowUpToBase N hN P hcU hcR heq)

/-! ### The blowup along a closed subspace, and its exceptional divisor -/

section Centre

variable (Z : ClosedSubspaces B S hS X.obj) (P : Presentation B S hS X.obj X.property)

/-- The defining ideal sheaf `𝓘_Z ⊆ 𝒪_X` of a closed subspace, which is the sheaf of ideals
whose Rees algebra the blowup along that subspace is the relative Proj of. -/
abbrev centreIdeal : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule :=
  definingIdealSheaf B S hS X Z

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The defining ideal sheaf of a closed subspace is cartesian on affine charts. -/
theorem isCartesianOnAffineCharts_centreIdeal :
    IsCartesianOnAffineCharts (centreIdeal Z).toSheafOfModules :=
  definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z

variable
  (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR)))

/-- The blowing up of an algebraic space `X` along a closed subspace `Z ⊆ X`: the relative Proj
`Proj_X(⨁_{n ≥ 0} 𝓘_Zⁿ)` of the Rees algebra of the defining ideal sheaf of `Z`, as an algebraic
space over `S`. The subspace `Z` is the centre. -/
@[stacks 085Q "the blowup as the relative Proj of the Rees algebra, with the descent datum's \
equivalence-relation field carried as a parameter; Φ and its invertibility and both pullback \
squares are supplied from the Rees comparison"]
def blowUpAlong : AlgebraicSpaces B S hS :=
  blowUpSpace (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR heq

/-- The blowing up `b : Proj_X(⨁_{n ≥ 0} 𝓘_Zⁿ) ⟶ X` of an algebraic space `X` along a closed
subspace `Z ⊆ X`, as a morphism of algebraic spaces over `S`. -/
@[stacks 085Q "the morphism b of the blowup, with the descent datum's equivalence-relation \
field carried as a parameter"]
def blowUpAlongHom : blowUpAlong Z P hcU hcR heq ⟶ X :=
  blowUpHom (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR heq

/-- The exceptional divisor `b⁻¹(Z)` of the blowing up of `X` along `Z`: the inverse image of the
centre along the structure morphism of the blowup, as a closed subspace of the blowup. -/
@[stacks 085Q "the exceptional divisor b⁻¹(Z) of the blowup, and the centre Z"]
def exceptionalDivisor : ClosedSubspaces B S hS (blowUpAlong Z P hcU hcR heq).obj :=
  preimageClosedSubspace (blowUpAlongHom Z P hcU hcR heq) Z

end Centre

end AlgebraicGeometry.Space

end
