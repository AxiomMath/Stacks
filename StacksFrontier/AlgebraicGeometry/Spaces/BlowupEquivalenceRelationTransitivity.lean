module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationNormalisation

/-!
# Transitivity of the two projections of the relative Proj of a Rees algebra

`StacksFrontier/AlgebraicGeometry/Spaces/BlowupEquivalenceRelationNormalisation.lean` discharges the
reflexivity and symmetry equations of
`AlgebraicGeometry.Space.isEquivalenceRelation_post_reesProj_of_normalisation` from the
composition law `Stacks.Blowup.reesSituationBaseChange_comp`. This file discharges the third, the
cocycle condition, and therefore the whole equivalence-relation condition carried by Tag 085Q.

## What transitivity needs that the other two did not

Reflexivity and symmetry live over the charts `U` and `R` that the presentation already supplies.
Transitivity lives over the composable pairs `R ×_U R`, which it does not. That fibre product
**does** exist as an object of the big fppf category over `S`: the category of schemes of size
below the site's cutoff has fibre products, by
`AlgebraicGeometry.Scheme.size_pullback_lt`, and the slice over `S` inherits them. Its two
projections are base changes of the two étale legs, hence étale; the composition leg
`κ : R ×_U R ⟶ R` exists because `R` is the kernel pair of the atlas at the level of presheaves,
and is étale because `κ` followed by the target leg is the first projection followed by the target
leg. So `R ×_U R` is a fourth étale chart of `X`, it carries the sheaf of ideals that
`AlgebraicGeometry.Space.idealSheafDataOfChart` produces there, and all three of `pr₁`, `pr₂` and
`κ` carry `ℐ|_R` to it.

The relative Proj `P_{R ×_U R}` of the Rees algebra of that sheaf of ideals is asked to be an
object of the site, exactly as `P_U` and `P_R` are: the hypothesis `hcRR` below is the third
instance of the same set-theoretic side condition that
`AlgebraicGeometry.Space.relativeProjChartOfSituation` takes, and that `hcU` and `hcR` already
carry. **Carrying a third is not a weakening**; it is the same condition at one more chart, and
the source's set-theoretic conventions provide it.

What is then proved is not an identification of `P_R ×_{P_U} P_R` with `P_{R ×_U R}` — only the
one direction of it that is needed. The cone
`AlgebraicGeometry.Space.reesProjTransitivityCone` maps to `P_{R ×_U R}` by the universal property
of the cartesian square over `R ×_U R ⟶ U`, and composing that map with the comparison morphism
over `κ` produces a witness satisfying both conditions of
`Stacks.Descent.eq_transHom`. Uniqueness of the transitivity witness finishes it.

## Main definitions

* `AlgebraicGeometry.Space.presentationDouble`, `presentationDoubleFst`, `presentationDoubleSnd`:
  the composable pairs `R ×_U R` of the relation of an étale presentation, with its two
  projections.
* `AlgebraicGeometry.Space.presentationComp`: the composition leg `κ : R ×_U R ⟶ R`.
* `AlgebraicGeometry.Space.presentationDoubleChart` and
  `AlgebraicGeometry.Space.reesDoubleIdeal`: `R ×_U R` as an étale chart of `X`, and the sheaf of
  ideals it induces.
* `AlgebraicGeometry.Space.reesProjDouble` and `AlgebraicGeometry.Space.reesProjDoubleHom`:
  `P_{R ×_U R}` as an object of the big fppf site over `S`, with its structure morphism.
* `AlgebraicGeometry.Space.reesProjDoubleFst`, `reesProjDoubleSnd`, `reesProjDoubleComp` and
  `reesProjDoubleRho`: the comparison morphisms over `pr₁`, `pr₂`, `κ` and `pr₁ ≫ s`.

## Main results

* `AlgebraicGeometry.Space.etale_toScheme_map_presentationComp`: the composition leg is étale.
* `AlgebraicGeometry.Space.transitivity_post_reesProj`: **the third equation.**
* `AlgebraicGeometry.Space.isEquivalenceRelation_post_reesProj`: **the two projections
  `P_R ⇉ P_U` form an internal equivalence relation**, with no hypothesis beyond the
  presentation, the sheaf of ideals and the three containment conditions.

## Implementation notes

The composition leg is produced at the level of presheaves, where
`AlgebraicGeometry.Space.Presentation.isPullback` lives, and transported by the fullness of
`CategoryTheory.yoneda`, exactly as the diagonal and the symmetry are in the normalisation file.

The sheaf of ideals that `pr₂` and `κ` pull back is the *same* one that `pr₁` pulls back, because
all three are morphisms of étale charts into the relation chart: their composites with the atlas
agree, the two legs of the relation having the same composite with it. That is the one place the
kernel-pair property is used beyond producing `κ`.

The four `hKK` hypotheses that `Stacks.Blowup.reesSituationBaseChange_comp` asks for are proved
from `AlgebraicGeometry.Scheme.IdealSheafData.comap_comp` rather than by exhibiting four more
morphisms of charts; the chart morphisms are needed only for the three legs out of `R ×_U R` into
`R`.

Three global instances are added, the flatness of the three legs out of `R ×_U R`, for the same
reason as in the normalisation file: the comparison morphisms cannot be written down without
them.

No `@[stacks]` attribute is attached here. The `heq`-free restatements of Tag 085Q are in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupEquivalenceRelationClosed.lean`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS}

/-! ### The composable pairs of the relation -/

/-- **The composable pairs `R ×_U R`** of the relation of an étale presentation: the fibre
product of the source leg against the target leg, formed in the big fppf category over `S`. -/
def presentationDouble (P : Presentation B S hS X.obj X.property) : BigFppfOver B S hS :=
  pullback P.source P.target

/-- The first projection `R ×_U R ⟶ R`, which records the second of a composable pair. -/
def presentationDoubleFst (P : Presentation B S hS X.obj X.property) :
    presentationDouble P ⟶ P.R := pullback.fst P.source P.target

/-- The second projection `R ×_U R ⟶ R`, which records the first of a composable pair. -/
def presentationDoubleSnd (P : Presentation B S hS X.obj X.property) :
    presentationDouble P ⟶ P.R := pullback.snd P.source P.target

/-- The composable pairs are the fibre product of the source leg against the target leg. -/
theorem isPullback_presentationDouble (P : Presentation B S hS X.obj X.property) :
    IsPullback (presentationDoubleFst P) (presentationDoubleSnd P) P.source P.target :=
  IsPullback.of_hasPullback _ _

/-- The defining identity of a composable pair: the source of the second is the target of the
first. -/
theorem presentationDoubleFst_comp_source (P : Presentation B S hS X.obj X.property) :
    presentationDoubleFst P ≫ P.source = presentationDoubleSnd P ≫ P.target :=
  (isPullback_presentationDouble P).w

/-- The fibre product square of composable pairs, read on the underlying schemes. -/
theorem isPullback_toScheme_map_presentationDouble
    (P : Presentation B S hS X.obj X.property) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P))
      ((BigFppfOver.toScheme B S hS).map (presentationDoubleSnd P))
      ((BigFppfOver.toScheme B S hS).map P.source)
      ((BigFppfOver.toScheme B S hS).map P.target) :=
  (isPullback_presentationDouble P).map (BigFppfOver.toScheme B S hS)

/-- The first projection is étale: it is the base change of the étale target leg. -/
theorem etale_toScheme_map_presentationDoubleFst
    (P : Presentation B S hS X.obj X.property) :
    Etale ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P)) :=
  MorphismProperty.of_isPullback (P := @Etale)
    (isPullback_toScheme_map_presentationDouble P).flip
    (etale_toScheme_map_presentation_target P)

/-- The second projection is étale: it is the base change of the étale source leg. -/
theorem etale_toScheme_map_presentationDoubleSnd
    (P : Presentation B S hS X.obj X.property) :
    Etale ((BigFppfOver.toScheme B S hS).map (presentationDoubleSnd P)) :=
  MorphismProperty.of_isPullback (P := @Etale)
    (isPullback_toScheme_map_presentationDouble P)
    (etale_toScheme_map_presentation_source P)

/-- The first projection is flat: it is étale. -/
instance flat_toScheme_map_presentationDoubleFst
    (P : Presentation B S hS X.obj X.property) :
    AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P)) :=
  have := etale_toScheme_map_presentationDoubleFst P
  inferInstance

/-- The second projection is flat: it is étale. -/
instance flat_toScheme_map_presentationDoubleSnd
    (P : Presentation B S hS X.obj X.property) :
    AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map (presentationDoubleSnd P)) :=
  have := etale_toScheme_map_presentationDoubleSnd P
  inferInstance

/-! ### The composition leg -/

/-- The two candidate structure morphisms of a composable pair over the algebraic space agree:
the target of the first and the source of the second have the same composite with the atlas,
because the two legs of the relation do. -/
theorem yoneda_map_presentationDouble_comp_toSpace
    (P : Presentation B S hS X.obj X.property) :
    yoneda.map (presentationDoubleFst P ≫ P.target) ≫ P.toSpace =
      yoneda.map (presentationDoubleSnd P ≫ P.source) ≫ P.toSpace := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Category.assoc, P.isPullback.w, ← Category.assoc, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    presentationDoubleFst_comp_source, CategoryTheory.Functor.map_comp, Category.assoc,
    P.isPullback.w, CategoryTheory.Functor.map_comp, Category.assoc]

/-- **The composition leg `κ : R ×_U R ⟶ R`.** The relation scheme is the kernel pair of the
atlas, so the pair consisting of the target of the first factor and the source of the second
factors through it; the factorisation exists in the big fppf category because
`CategoryTheory.yoneda` is full. -/
def presentationComp (P : Presentation B S hS X.obj X.property) :
    presentationDouble P ⟶ P.R :=
  yoneda.preimage (P.isPullback.lift (yoneda.map (presentationDoubleFst P ≫ P.target))
    (yoneda.map (presentationDoubleSnd P ≫ P.source))
    (yoneda_map_presentationDouble_comp_toSpace P))

/-- The target of a composite is the target of the first factor. -/
theorem presentationComp_comp_target (P : Presentation B S hS X.obj X.property) :
    presentationComp P ≫ P.target = presentationDoubleFst P ≫ P.target := by
  refine yoneda.map_injective ?_
  rw [CategoryTheory.Functor.map_comp, presentationComp, yoneda.map_preimage,
    P.isPullback.lift_fst]

/-- The source of a composite is the source of the second factor. -/
theorem presentationComp_comp_source (P : Presentation B S hS X.obj X.property) :
    presentationComp P ≫ P.source = presentationDoubleSnd P ≫ P.source := by
  refine yoneda.map_injective ?_
  rw [CategoryTheory.Functor.map_comp, presentationComp, yoneda.map_preimage,
    P.isPullback.lift_snd]

/-- The structure morphism `R ×_U R ⟶ U` of the composable pairs is étale. -/
theorem etale_toScheme_map_presentationDoubleRho
    (P : Presentation B S hS X.obj X.property) :
    Etale ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P ≫ P.source)) := by
  have := etale_toScheme_map_presentationDoubleFst P
  have := etale_toScheme_map_presentation_source P
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- The structure morphism `R ×_U R ⟶ U` of the composable pairs is flat: it is étale. -/
instance flat_toScheme_map_presentationDoubleRho
    (P : Presentation B S hS X.obj X.property) :
    AlgebraicGeometry.Flat
      ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P ≫ P.source)) :=
  have := etale_toScheme_map_presentationDoubleRho P
  inferInstance

/-- **The composition leg is étale**: composed with the étale target leg it is the first
projection composed with the target leg, which is étale. -/
theorem etale_toScheme_map_presentationComp (P : Presentation B S hS X.obj X.property) :
    Etale ((BigFppfOver.toScheme B S hS).map (presentationComp P)) := by
  have := etale_toScheme_map_presentationDoubleFst P
  have := etale_toScheme_map_presentation_target P
  have : Etale ((BigFppfOver.toScheme B S hS).map (presentationComp P) ≫
      (BigFppfOver.toScheme B S hS).map P.target) := by
    rw [← CategoryTheory.Functor.map_comp, presentationComp_comp_target,
      CategoryTheory.Functor.map_comp]
    infer_instance
  exact Etale.of_comp _ ((BigFppfOver.toScheme B S hS).map P.target)

/-- The composition leg is flat: it is étale. -/
instance flat_toScheme_map_presentationComp (P : Presentation B S hS X.obj X.property) :
    AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map (presentationComp P)) :=
  have := etale_toScheme_map_presentationComp P
  inferInstance

/-! ### The composable pairs as a fourth étale chart -/

/-- The composable pairs, read as an étale chart of the algebraic space through the first
projection, the source leg and the atlas. -/
def presentationDoubleChart (P : Presentation B S hS X.obj X.property) :
    SmallEtale B S hS X.obj :=
  ⟨CostructuredArrow.mk (yoneda.map (presentationDoubleFst P ≫ P.source) ≫ P.toSpace),
    etale_comp_of_scheme B S hS (presentationDoubleFst P ≫ P.source) P.toSpace
      (etale_toScheme_map_presentationDoubleRho P) P.etale⟩

/-- The first projection, as a morphism of étale charts. -/
def presentationDoubleFstHom (P : Presentation B S hS X.obj X.property) :
    presentationDoubleChart P ⟶ presentationRelationChart P :=
  ObjectProperty.homMk (CostructuredArrow.homMk (presentationDoubleFst P) (by
    change yoneda.map (presentationDoubleFst P) ≫ yoneda.map P.source ≫ P.toSpace =
      yoneda.map (presentationDoubleFst P ≫ P.source) ≫ P.toSpace
    rw [CategoryTheory.Functor.map_comp, Category.assoc]))

/-- The second projection, as a morphism of étale charts: its composite with the source leg and
the atlas agrees with that of the first projection, because the two legs of the relation have the
same composite with the atlas. -/
def presentationDoubleSndHom (P : Presentation B S hS X.obj X.property) :
    presentationDoubleChart P ⟶ presentationRelationChart P :=
  ObjectProperty.homMk (CostructuredArrow.homMk (presentationDoubleSnd P) (by
    change yoneda.map (presentationDoubleSnd P) ≫ yoneda.map P.source ≫ P.toSpace =
      yoneda.map (presentationDoubleFst P ≫ P.source) ≫ P.toSpace
    rw [presentationDoubleFst_comp_source, CategoryTheory.Functor.map_comp, Category.assoc,
      P.isPullback.w]))

/-- The composition leg, as a morphism of étale charts. -/
def presentationCompHom (P : Presentation B S hS X.obj X.property) :
    presentationDoubleChart P ⟶ presentationRelationChart P :=
  ObjectProperty.homMk (CostructuredArrow.homMk (presentationComp P) (by
    change yoneda.map (presentationComp P) ≫ yoneda.map P.source ≫ P.toSpace =
      yoneda.map (presentationDoubleFst P ≫ P.source) ≫ P.toSpace
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, presentationComp_comp_source,
      presentationDoubleFst_comp_source, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, P.isPullback.w]))

variable (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
  (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
  (P : Presentation B S hS X.obj X.property)

/-- The sheaf of ideals that a quasi-coherent sheaf of ideals of `𝒪_X` induces on the scheme of
composable pairs of an étale presentation. -/
abbrev reesDoubleIdeal :
    ((BigFppfOver.toScheme B S hS).obj (presentationDouble P)).IdealSheafData :=
  idealSheafDataOfChart B S hS X N hN (presentationDoubleChart P)

/-- The Rees algebra `⨁_{n ≥ 0} (ℐ|_{R ×_U R})ⁿ` on the scheme of composable pairs, as a relative
Proj situation. -/
abbrev reesDoubleSituation : Stacks.RelativeProj.Situation.{u} :=
  Stacks.Blowup.reesSituation (reesDoubleIdeal N hN P)

/-- **The first projection carries `ℐ|_R` to `ℐ|_{R ×_U R}`.** -/
theorem comap_reesRelationIdeal_doubleFst :
    (reesRelationIdeal N hN P).comap
        ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P))
      = reesDoubleIdeal N hN P :=
  comap_idealSheafDataOfChart B S hS X N hN (presentationDoubleFstHom P)

/-- **The second projection carries `ℐ|_R` to `ℐ|_{R ×_U R}`.** -/
theorem comap_reesRelationIdeal_doubleSnd :
    (reesRelationIdeal N hN P).comap
        ((BigFppfOver.toScheme B S hS).map (presentationDoubleSnd P))
      = reesDoubleIdeal N hN P :=
  comap_idealSheafDataOfChart B S hS X N hN (presentationDoubleSndHom P)

/-- **The composition leg carries `ℐ|_R` to `ℐ|_{R ×_U R}`.** -/
theorem comap_reesRelationIdeal_comp :
    (reesRelationIdeal N hN P).comap ((BigFppfOver.toScheme B S hS).map (presentationComp P))
      = reesDoubleIdeal N hN P :=
  comap_idealSheafDataOfChart B S hS X N hN (presentationCompHom P)

/-- The structure morphism `R ×_U R ⟶ U` carries `ℐ|_U` to `ℐ|_{R ×_U R}`. -/
theorem comap_reesChartIdeal_doubleRho :
    (reesChartIdeal N hN P).comap
        ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P ≫ P.source))
      = reesDoubleIdeal N hN P := by
  rw [CategoryTheory.Functor.map_comp, Scheme.IdealSheafData.comap_comp,
    comap_reesChartIdeal_source N hN P, comap_reesRelationIdeal_doubleFst N hN P]

/-- The first projection followed by the target leg carries `ℐ|_U` to `ℐ|_{R ×_U R}`. -/
theorem comap_reesChartIdeal_doubleFstTarget :
    (reesChartIdeal N hN P).comap
        ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P) ≫
          (BigFppfOver.toScheme B S hS).map P.target)
      = reesDoubleIdeal N hN P := by
  rw [Scheme.IdealSheafData.comap_comp, comap_reesChartIdeal_target N hN P,
    comap_reesRelationIdeal_doubleFst N hN P]

/-- The second projection followed by the source leg carries `ℐ|_U` to `ℐ|_{R ×_U R}`. -/
theorem comap_reesChartIdeal_doubleSndSource :
    (reesChartIdeal N hN P).comap
        ((BigFppfOver.toScheme B S hS).map (presentationDoubleSnd P) ≫
          (BigFppfOver.toScheme B S hS).map P.source)
      = reesDoubleIdeal N hN P := by
  rw [Scheme.IdealSheafData.comap_comp, comap_reesChartIdeal_source N hN P,
    comap_reesRelationIdeal_doubleSnd N hN P]

/-- The second projection followed by the target leg carries `ℐ|_U` to `ℐ|_{R ×_U R}`. -/
theorem comap_reesChartIdeal_doubleSndTarget :
    (reesChartIdeal N hN P).comap
        ((BigFppfOver.toScheme B S hS).map (presentationDoubleSnd P) ≫
          (BigFppfOver.toScheme B S hS).map P.target)
      = reesDoubleIdeal N hN P := by
  rw [Scheme.IdealSheafData.comap_comp, comap_reesChartIdeal_target N hN P,
    comap_reesRelationIdeal_doubleSnd N hN P]

/-- The composition leg followed by the target leg carries `ℐ|_U` to `ℐ|_{R ×_U R}`. -/
theorem comap_reesChartIdeal_compTarget :
    (reesChartIdeal N hN P).comap
        ((BigFppfOver.toScheme B S hS).map (presentationComp P) ≫
          (BigFppfOver.toScheme B S hS).map P.target)
      = reesDoubleIdeal N hN P := by
  rw [Scheme.IdealSheafData.comap_comp, comap_reesChartIdeal_target N hN P,
    comap_reesRelationIdeal_comp N hN P]

/-- The composition leg followed by the source leg carries `ℐ|_U` to `ℐ|_{R ×_U R}`. -/
theorem comap_reesChartIdeal_compSource :
    (reesChartIdeal N hN P).comap
        ((BigFppfOver.toScheme B S hS).map (presentationComp P) ≫
          (BigFppfOver.toScheme B S hS).map P.source)
      = reesDoubleIdeal N hN P := by
  rw [Scheme.IdealSheafData.comap_comp, comap_reesChartIdeal_source N hN P,
    comap_reesRelationIdeal_comp N hN P]

/-! ### The relative Proj over the composable pairs -/

variable (hcU : B.Contains (reesChartSituation N hN P).relativeProj)
  (hcR : B.Contains (reesRelationSituation N hN P).relativeProj)
  (hcRR : B.Contains (reesDoubleSituation N hN P).relativeProj)

/-- `P_{R ×_U R}`, the relative Proj of the Rees algebra on the scheme of composable pairs, as an
object of the big fppf site over `S`. -/
def reesProjDouble : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hcRR
    ((reesDoubleSituation N hN P).relativeProjToBase ≫
      B.inclusion.map (presentationDouble P).hom)

/-- The structure morphism `P_{R ×_U R} ⟶ R ×_U R`. -/
def reesProjDoubleHom : reesProjDouble N hN P hcRR ⟶ presentationDouble P :=
  Over.homMk (ObjectProperty.homMk (reesDoubleSituation N hN P).relativeProjToBase)
    (ObjectProperty.hom_ext _ rfl)

/-- The comparison morphism `P_{R ×_U R} ⟶ P_R` over the first projection. -/
def reesProjDoubleFst : reesProjDouble N hN P hcRR ⟶ reesProjRelation N hN P hcR :=
  BigFppfOver.homMk B S hS hcR
    ((reesRelationSituation N hN P).relativeProjToBase ≫ B.inclusion.map P.R.hom)
    (Stacks.Blowup.reesSituationBaseChange
      ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P))
      (reesRelationIdeal N hN P) (comap_reesRelationIdeal_doubleFst N hN P))
    (reesSituationBaseChange_comp_str (reesRelationIdeal N hN P) (presentationDoubleFst P)
      (comap_reesRelationIdeal_doubleFst N hN P))

/-- The comparison morphism `P_{R ×_U R} ⟶ P_R` over the second projection. -/
def reesProjDoubleSnd : reesProjDouble N hN P hcRR ⟶ reesProjRelation N hN P hcR :=
  BigFppfOver.homMk B S hS hcR
    ((reesRelationSituation N hN P).relativeProjToBase ≫ B.inclusion.map P.R.hom)
    (Stacks.Blowup.reesSituationBaseChange
      ((BigFppfOver.toScheme B S hS).map (presentationDoubleSnd P))
      (reesRelationIdeal N hN P) (comap_reesRelationIdeal_doubleSnd N hN P))
    (reesSituationBaseChange_comp_str (reesRelationIdeal N hN P) (presentationDoubleSnd P)
      (comap_reesRelationIdeal_doubleSnd N hN P))

/-- The comparison morphism `P_{R ×_U R} ⟶ P_R` over the composition leg. -/
def reesProjDoubleComp : reesProjDouble N hN P hcRR ⟶ reesProjRelation N hN P hcR :=
  BigFppfOver.homMk B S hS hcR
    ((reesRelationSituation N hN P).relativeProjToBase ≫ B.inclusion.map P.R.hom)
    (Stacks.Blowup.reesSituationBaseChange
      ((BigFppfOver.toScheme B S hS).map (presentationComp P))
      (reesRelationIdeal N hN P) (comap_reesRelationIdeal_comp N hN P))
    (reesSituationBaseChange_comp_str (reesRelationIdeal N hN P) (presentationComp P)
      (comap_reesRelationIdeal_comp N hN P))

/-- The comparison morphism `P_{R ×_U R} ⟶ P_U` over the structure morphism `R ×_U R ⟶ U`. -/
def reesProjDoubleRho : reesProjDouble N hN P hcRR ⟶ reesProjChart N hN P hcU :=
  BigFppfOver.homMk B S hS hcU
    ((reesChartSituation N hN P).relativeProjToBase ≫ B.inclusion.map P.U.hom)
    (Stacks.Blowup.reesSituationBaseChange
      ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P ≫ P.source))
      (reesChartIdeal N hN P) (comap_reesChartIdeal_doubleRho N hN P))
    (reesSituationBaseChange_comp_str (reesChartIdeal N hN P)
      (presentationDoubleFst P ≫ P.source) (comap_reesChartIdeal_doubleRho N hN P))

/-- **`P_{R ×_U R}` is the base change of `P_U` along `R ×_U R ⟶ U`.** -/
theorem isPullback_reesProjDoubleRho :
    IsPullback (reesProjDoubleRho N hN P hcU hcRR) (reesProjDoubleHom N hN P hcRR)
      (reesProjChartHom N hN P hcU) (presentationDoubleFst P ≫ P.source) :=
  IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (@Stacks.Blowup.isPullback_reesSituationBaseChange _ _
      ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P ≫ P.source)) _
      (reesChartIdeal N hN P) _ (comap_reesChartIdeal_doubleRho N hN P))

/-- The comparison morphism over the first projection is a morphism over `R`. -/
theorem reesProjDoubleFst_comp_reesProjRelationHom :
    reesProjDoubleFst N hN P hcR hcRR ≫ reesProjRelationHom N hN P hcR =
      reesProjDoubleHom N hN P hcRR ≫ presentationDoubleFst P := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact Stacks.Blowup.reesSituationBaseChange_comp_relativeProjToBase _ _
    (comap_reesRelationIdeal_doubleFst N hN P)

/-- The comparison morphism over the second projection is a morphism over `R`. -/
theorem reesProjDoubleSnd_comp_reesProjRelationHom :
    reesProjDoubleSnd N hN P hcR hcRR ≫ reesProjRelationHom N hN P hcR =
      reesProjDoubleHom N hN P hcRR ≫ presentationDoubleSnd P := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact Stacks.Blowup.reesSituationBaseChange_comp_relativeProjToBase _ _
    (comap_reesRelationIdeal_doubleSnd N hN P)

/-! ### The four composite identities -/

/-- The Rees base change along `q` followed by the one along `g` is the one along any morphism
equal to `q ≫ g`. -/
private theorem reesSituationBaseChange_comp_of_eq {Y Z X : Scheme.{u}} (q : Y ⟶ Z) (g : Z ⟶ X)
    {q' : Y ⟶ X} [AlgebraicGeometry.Flat q] [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Flat q'] (e : q ≫ g = q') (I : X.IdealSheafData) {J : Z.IdealSheafData}
    (hJ : I.comap g = J) {K : Y.IdealSheafData} (hK : J.comap q = K) (hK' : I.comap q' = K) :
    Stacks.Blowup.reesSituationBaseChange q J hK ≫ Stacks.Blowup.reesSituationBaseChange g I hJ =
      Stacks.Blowup.reesSituationBaseChange q' I hK' := by
  subst e
  exact Stacks.Blowup.reesSituationBaseChange_comp q g I hJ hK hK'

/-- The first projection comparison followed by the source projection is the comparison over the
structure morphism `R ×_U R ⟶ U`. -/
theorem reesProjDoubleFst_comp_reesProjSource :
    reesProjDoubleFst N hN P hcR hcRR ≫ reesProjSource N hN P hcU hcR =
      reesProjDoubleRho N hN P hcU hcRR := by
  have := flat_toScheme_map_presentation_source P
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [CategoryTheory.Functor.map_comp]
  exact reesSituationBaseChange_comp_of_eq _ _ (CategoryTheory.Functor.map_comp _ _ _).symm _
    (comap_reesChartIdeal_source N hN P) (comap_reesRelationIdeal_doubleFst N hN P)
    (comap_reesChartIdeal_doubleRho N hN P)

/-- The second projection comparison followed by the target projection is the comparison over the
structure morphism `R ×_U R ⟶ U`. -/
theorem reesProjDoubleSnd_comp_reesProjTarget :
    reesProjDoubleSnd N hN P hcR hcRR ≫ reesProjTarget N hN P hcU hcR =
      reesProjDoubleRho N hN P hcU hcRR := by
  have := flat_toScheme_map_presentation_target P
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [CategoryTheory.Functor.map_comp]
  exact reesSituationBaseChange_comp_of_eq _ _
    (by rw [← CategoryTheory.Functor.map_comp, presentationDoubleFst_comp_source]) _
    (comap_reesChartIdeal_target N hN P) (comap_reesRelationIdeal_doubleSnd N hN P)
    (comap_reesChartIdeal_doubleRho N hN P)

/-- The composition comparison followed by the target projection is the first projection
comparison followed by the target projection. -/
theorem reesProjDoubleComp_comp_reesProjTarget :
    reesProjDoubleComp N hN P hcR hcRR ≫ reesProjTarget N hN P hcU hcR =
      reesProjDoubleFst N hN P hcR hcRR ≫ reesProjTarget N hN P hcU hcR := by
  have := flat_toScheme_map_presentation_target P
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact (reesSituationBaseChange_comp_of_eq _ _
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        presentationComp_comp_target]) _
      (comap_reesChartIdeal_target N hN P) (comap_reesRelationIdeal_comp N hN P)
      (comap_reesChartIdeal_doubleFstTarget N hN P)).trans
    (reesSituationBaseChange_comp_of_eq _ _ rfl _ (comap_reesChartIdeal_target N hN P)
      (comap_reesRelationIdeal_doubleFst N hN P)
      (comap_reesChartIdeal_doubleFstTarget N hN P)).symm

/-- The composition comparison followed by the source projection is the second projection
comparison followed by the source projection. -/
theorem reesProjDoubleComp_comp_reesProjSource :
    reesProjDoubleComp N hN P hcR hcRR ≫ reesProjSource N hN P hcU hcR =
      reesProjDoubleSnd N hN P hcR hcRR ≫ reesProjSource N hN P hcU hcR := by
  have := flat_toScheme_map_presentation_source P
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact (reesSituationBaseChange_comp_of_eq _ _
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        presentationComp_comp_source]) _
      (comap_reesChartIdeal_source N hN P) (comap_reesRelationIdeal_comp N hN P)
      (comap_reesChartIdeal_doubleSndSource N hN P)).trans
    (reesSituationBaseChange_comp_of_eq _ _ rfl _ (comap_reesChartIdeal_source N hN P)
      (comap_reesRelationIdeal_doubleSnd N hN P)
      (comap_reesChartIdeal_doubleSndSource N hN P)).symm

/-! ### Transitivity of the two projections -/

/-- A composable pair of points of the two projections `P_R ⇉ P_U` gives a point of the scheme
`R ×_U R` of composable pairs of the relation. -/
def reesProjTransitivityBase :
    (reesProjTransitivityCone N hN P hcU hcR).pt ⟶
      (Over.post B.inclusion).obj (presentationDouble P) :=
  (RelativeProjGlueingData.isPullback_post (isPullback_presentationDouble P)).lift
    ((reesProjTransitivityCone N hN P hcU hcR).fst ≫
      (Over.post B.inclusion).map (reesProjRelationHom N hN P hcR))
    ((reesProjTransitivityCone N hN P hcU hcR).snd ≫
      (Over.post B.inclusion).map (reesProjRelationHom N hN P hcR))
    (Stacks.Descent.transBase_condition (isPullback_post_reesProjTarget N hN P hcU hcR)
      (isPullback_post_reesProjSource N hN P hcU hcR)
      (reesProjTransitivityCone N hN P hcU hcR))

/-- The point of `R ×_U R` given by a composable pair, followed by the first projection, is the
first component of the pair followed by `P_R ⟶ R`. -/
@[simp] theorem reesProjTransitivityBase_comp_fst :
    reesProjTransitivityBase N hN P hcU hcR ≫
        (Over.post B.inclusion).map (presentationDoubleFst P) =
      (reesProjTransitivityCone N hN P hcU hcR).fst ≫
        (Over.post B.inclusion).map (reesProjRelationHom N hN P hcR) :=
  (RelativeProjGlueingData.isPullback_post (isPullback_presentationDouble P)).lift_fst _ _ _

/-- The point of `R ×_U R` given by a composable pair, followed by the second projection, is the
second component of the pair followed by `P_R ⟶ R`. -/
@[simp] theorem reesProjTransitivityBase_comp_snd :
    reesProjTransitivityBase N hN P hcU hcR ≫
        (Over.post B.inclusion).map (presentationDoubleSnd P) =
      (reesProjTransitivityCone N hN P hcU hcR).snd ≫
        (Over.post B.inclusion).map (reesProjRelationHom N hN P hcR) :=
  (RelativeProjGlueingData.isPullback_post (isPullback_presentationDouble P)).lift_snd _ _ _

/-- **The cone of composable pairs maps to `P_{R ×_U R}`.** This is the universal property of
the cartesian square exhibiting `P_{R ×_U R}` as the base change of `P_U` along
`R ×_U R ⟶ U`, applied to the first component of a composable pair and to
`AlgebraicGeometry.Space.reesProjTransitivityBase`. -/
def reesProjTransitivityLift :
    (reesProjTransitivityCone N hN P hcU hcR).pt ⟶
      (Over.post B.inclusion).obj (reesProjDouble N hN P hcRR) :=
  (RelativeProjGlueingData.isPullback_post
      (isPullback_reesProjDoubleRho N hN P hcU hcRR)).lift
    ((reesProjTransitivityCone N hN P hcU hcR).fst ≫
      (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR))
    (reesProjTransitivityBase N hN P hcU hcR)
    (by
      rw [Category.assoc, (isPullback_post_reesProjSource N hN P hcU hcR).w, ← Category.assoc,
        ← reesProjTransitivityBase_comp_fst N hN P hcU hcR, Category.assoc,
        ← CategoryTheory.Functor.map_comp])

/-- The lift to `P_{R ×_U R}` followed by its projection to `P_U` is the first component of the
composable pair followed by the source projection `P_R ⟶ P_U`. -/
@[simp] theorem reesProjTransitivityLift_comp_reesProjDoubleRho :
    reesProjTransitivityLift N hN P hcU hcR hcRR ≫
        (Over.post B.inclusion).map (reesProjDoubleRho N hN P hcU hcRR) =
      (reesProjTransitivityCone N hN P hcU hcR).fst ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) :=
  (RelativeProjGlueingData.isPullback_post
    (isPullback_reesProjDoubleRho N hN P hcU hcRR)).lift_fst _ _ _

/-- The lift to `P_{R ×_U R}` followed by its structure morphism to `R ×_U R` is
`AlgebraicGeometry.Space.reesProjTransitivityBase`. -/
@[simp] theorem reesProjTransitivityLift_comp_reesProjDoubleHom :
    reesProjTransitivityLift N hN P hcU hcR hcRR ≫
        (Over.post B.inclusion).map (reesProjDoubleHom N hN P hcRR) =
      reesProjTransitivityBase N hN P hcU hcR :=
  (RelativeProjGlueingData.isPullback_post
    (isPullback_reesProjDoubleRho N hN P hcU hcRR)).lift_snd _ _ _

/-- The lift followed by the first projection comparison is the first component of the
composable pair: the two agree after the source projection and after the structure morphism to
`R`, and the square over the source leg separates them. -/
theorem reesProjTransitivityLift_comp_reesProjDoubleFst :
    reesProjTransitivityLift N hN P hcU hcR hcRR ≫
        (Over.post B.inclusion).map (reesProjDoubleFst N hN P hcR hcRR) =
      (reesProjTransitivityCone N hN P hcU hcR).fst := by
  refine (isPullback_post_reesProjSource N hN P hcU hcR).hom_ext ?_ ?_
  · rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
      reesProjDoubleFst_comp_reesProjSource]
    exact reesProjTransitivityLift_comp_reesProjDoubleRho N hN P hcU hcR hcRR
  · rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
      reesProjDoubleFst_comp_reesProjRelationHom, CategoryTheory.Functor.map_comp,
      ← Category.assoc, reesProjTransitivityLift_comp_reesProjDoubleHom,
      reesProjTransitivityBase_comp_fst]

/-- The lift followed by the second projection comparison is the second component of the
composable pair. -/
theorem reesProjTransitivityLift_comp_reesProjDoubleSnd :
    reesProjTransitivityLift N hN P hcU hcR hcRR ≫
        (Over.post B.inclusion).map (reesProjDoubleSnd N hN P hcR hcRR) =
      (reesProjTransitivityCone N hN P hcU hcR).snd := by
  refine (isPullback_post_reesProjTarget N hN P hcU hcR).hom_ext ?_ ?_
  · rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
      reesProjDoubleSnd_comp_reesProjTarget]
    exact (reesProjTransitivityLift_comp_reesProjDoubleRho N hN P hcU hcR hcRR).trans
      (reesProjTransitivityCone N hN P hcU hcR).condition
  · rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
      reesProjDoubleSnd_comp_reesProjRelationHom, CategoryTheory.Functor.map_comp,
      ← Category.assoc, reesProjTransitivityLift_comp_reesProjDoubleHom,
      reesProjTransitivityBase_comp_snd]

/-- **The transitivity witness for the two projections `P_R ⇉ P_U`:** the lift of a composable
pair into `P_{R ×_U R}`, followed by the comparison morphism over the composition leg. -/
def reesProjTransitivityHom :
    (reesProjTransitivityCone N hN P hcU hcR).pt ⟶
      (Over.post B.inclusion).obj (reesProjRelation N hN P hcR) :=
  reesProjTransitivityLift N hN P hcU hcR hcRR ≫
    (Over.post B.inclusion).map (reesProjDoubleComp N hN P hcR hcRR)

/-- The transitivity witness has the target of the first component. -/
theorem reesProjTransitivityHom_comp_reesProjTarget :
    reesProjTransitivityHom N hN P hcU hcR hcRR ≫
        (Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR) =
      (reesProjTransitivityCone N hN P hcU hcR).fst ≫
        (Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR) := by
  rw [reesProjTransitivityHom, Category.assoc, ← CategoryTheory.Functor.map_comp,
    reesProjDoubleComp_comp_reesProjTarget, CategoryTheory.Functor.map_comp, ← Category.assoc,
    reesProjTransitivityLift_comp_reesProjDoubleFst]

/-- The transitivity witness has the source of the second component. -/
theorem reesProjTransitivityHom_comp_reesProjSource :
    reesProjTransitivityHom N hN P hcU hcR hcRR ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) =
      (reesProjTransitivityCone N hN P hcU hcR).snd ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) := by
  rw [reesProjTransitivityHom, Category.assoc, ← CategoryTheory.Functor.map_comp,
    reesProjDoubleComp_comp_reesProjSource, CategoryTheory.Functor.map_comp, ← Category.assoc,
    reesProjTransitivityLift_comp_reesProjDoubleSnd]

include hcRR in
/-- **The transitivity equation.** The canonical transitivity candidate of the two projections
satisfies its condition against the source projection:
`AlgebraicGeometry.Space.reesProjTransitivityHom` satisfies both conditions, and the transitivity
witness of a pulled-back relation is unique. -/
theorem transitivity_post_reesProj
    (e : EquivalenceRelation ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source)) :
    Stacks.Descent.transHom e.toTransitiveRelation
        (isPullback_post_reesProjTarget N hN P hcU hcR)
        (isPullback_post_reesProjSource N hN P hcU hcR)
        (reesProjTransitivityCone N hN P hcU hcR) ≫
      (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) =
    (reesProjTransitivityCone N hN P hcU hcR).snd ≫
      (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) := by
  rw [← Stacks.Descent.eq_transHom e.toTransitiveRelation
    (isPullback_post_reesProjTarget N hN P hcU hcR)
    (isPullback_post_reesProjSource N hN P hcU hcR)
    (reesProjTransitivityCone N hN P hcU hcR)
    (reesProjTransitivityHom_comp_reesProjTarget N hN P hcU hcR hcRR)
    (reesProjTransitivityHom_comp_reesProjSource N hN P hcU hcR hcRR)]
  exact reesProjTransitivityHom_comp_reesProjSource N hN P hcU hcR hcRR

/-! ### The equivalence-relation condition, discharged -/

include hcRR in
/-- **The two projections `P_R ⇉ P_U` of the relative Proj of the Rees algebra of a
quasi-coherent sheaf of ideals form an internal equivalence relation.** All four conditions are
now proved: joint monicity is
`AlgebraicGeometry.Space.jointlyMono₂_post_reesProj`, and the three equations that
`AlgebraicGeometry.Space.isEquivalenceRelation_post_reesProj_of_normalisation` reduces the rest to
are `AlgebraicGeometry.Space.reflexivity_post_reesProj`,
`AlgebraicGeometry.Space.symmetry_post_reesProj` and
`AlgebraicGeometry.Space.transitivity_post_reesProj`.

This is the hypothesis `heq` that the blowup of an algebraic space carries as a parameter; nothing
is assumed here beyond the presentation, the quasi-coherent sheaf of ideals, and the three
containment conditions `hcU`, `hcR` and `hcRR` asking that the three relative Projs be objects of
the site. -/
theorem isEquivalenceRelation_post_reesProj :
    CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR)) :=
  isEquivalenceRelation_post_reesProj_of_normalisation N hN P hcU hcR
    (presentationEquivalenceRelation P)
    (reflexivity_post_reesProj N hN P hcU hcR (presentationEquivalenceRelation P))
    (symmetry_post_reesProj N hN P hcU hcR (presentationEquivalenceRelation P))
    (transitivity_post_reesProj N hN P hcU hcR hcRR (presentationEquivalenceRelation P))

end AlgebraicGeometry.Space

end
