module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction

/-!
# Restriction of a chart presentation of a lifting problem to a smaller chart

Let `B`, `X'` and `Y` be algebraic spaces over a scheme `S`, let `X ⊆ X'` be a subspace and let
`a : X ⟶ Y` be a morphism over `B`.  A
`AlgebraicGeometry.Space.ChartLiftPresentation` presents a lift of `a` over an affine étale scheme
chart `U'` of `X'` by a morphism into an affine chart square `W ⟶ V` of `q : Y ⟶ B`.  This file
restricts such a presentation along a morphism `m : V' ⟶ U'` of étale charts of `X'` and proves
that the action of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction` commutes with the
restriction maps of `AlgebraicGeometry.Space.liftsSubfunctor`.

## What the restriction datum is, and why it is data

The chart square of `q` is kept: the restricted presentation has the same `W`, `V` and the same
chart morphisms, and its presented lift is the restriction `V' ⟶ U' ⟶ W` of the presented one.
What cannot be kept is the *chart thickening* `X ×_{X'} U' ⟶ U'`, which has to be replaced by
`X ×_{X'} V' ⟶ V'`.  That fibre product is not formed anywhere in this development — the big fppf
site is not assumed to have the relevant pullbacks, and
`AlgebraicGeometry.Space.ChartLiftPresentation` therefore takes the cartesian square presenting it
as data rather than constructing it.  So the restriction takes the same thing as data, bundled as
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction`; the datum is never an obstruction,
because
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.exists_of_isFirstOrderThickening`
produces one over every affine étale chart of a first-order thickening.

Everything else about the restriction is then *determined*: the morphism
`X ×_{X'} V' ⟶ X ×_{X'} U'` of the two chart thickenings is the one the cartesian square of the
original presentation produces,
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap`.

## Main definitions

* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction`: the datum restricting a chart
  presentation along a morphism of étale charts of `X'` — the morphism of charts together with a
  cartesian square presenting the chart thickening at the smaller chart.
* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.presentation`: **the restricted chart
  presentation.**
* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap`: the induced morphism of the
  two closed subschemes, and
  `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.restrictConormal`: the induced
  `Γ(W, ⊤)`-linear map of the two conormal modules, which is restriction of regular functions.
* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.restrictDeriv`: the restriction of
  the acting derivations, which is `restrictConormal` on coefficients, and
  `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.restrictActionSection`: the
  restriction of the acting sections of the chart presentation, characterised by its attached
  derivation.

## Main results

* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.translateScheme_restrictDeriv`: **the
  translate of the restriction is the restriction of the translate**, as morphisms of schemes.
* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.map_translateSection`: **the action
  commutes with the restriction maps of the sheaf of lifts** — the restriction to the smaller
  chart of the translate of the presented lift by `δ` is the translate of the restricted
  presented lift by the restricted derivation.  This is the naturality clause that an action of
  sheaves asks for, on the side of the acting derivations, and
  `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.map_translateActionSection` is the
  same statement for the acting sections.
* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.exists_of_isFirstOrderThickening`: a
  restriction datum exists along every morphism into the presented chart whose source is an
  affine étale chart of a first-order thickening, so none of the statements above is empty.

## Implementation notes

`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.presentation` is an `abbrev`: the
restricted presentation shares the fields `tgt`, `bse`, `tgtChart`, `bseChart`, `chartHom` and
`chartSq` with the original one, and the statements below are about derivations of
`Γ(W, ⊤)` over `Γ(V, ⊤)` for *both* presentations at once, so the two spellings of those rings
have to be identified by projection of a constructor rather than by a transport.  The same
reduction is why `AlgebraicGeometry.Space.presentedSubspaceChart` is an `abbrev`.

The conormal restriction is a map of *kernels of maps of global sections*, not of sheaves: the
acting group of a chart presentation is
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`, whose target is
`RingHom.ker i^♯`.  Its `Γ(W, ⊤)`-linearity is `Stacks.Smooth.moduleOfAppLE_smul_ker` on both
sides — the action of a section of the chart of `Y` on a conormal element is multiplication by
its image under the presented lift, and restriction of regular functions is multiplicative.

No `@[stacks]` attribute is claimed: [Stacks Project, Tag 061D]'s sheaf of lifts and its acting
sheaf are registered where they are built, and what is proved here is the compatibility of the
chartwise action of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction` with restriction, which is
a step of [Stacks Project, Tag 04AM] and not an assertion of either tag.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {B X' Y : AlgebraicSpaces C S hS}

namespace ChartLiftPresentation

variable {C S hS} {p : X' ⟶ B} {q : Y ⟶ B} {X : Subfunctor X'.1} {a : X.toFunctor ⟶ Y.1}
  {U' : SmallEtale C S hS X'.1}

/-- The action of a global section of the chart of `Y` on a conormal element of the chart
thickening is multiplication by the image of that section under the presented lift.  This is
`Stacks.Smooth.moduleOfAppLE_smul_ker` at a chart presentation. -/
theorem coe_smul_conormal (P : ChartLiftPresentation C S hS p q a U')
    (r : Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens))) (x : P.conormal) :
    letI := P.isAffineAmbient
    letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
    letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
    ((r • x : P.conormal) : Γ(P.ambientScheme, (⊤ : P.ambientScheme.Opens)))
      = P.liftHomScheme.appTop.hom r *
        (x : Γ(P.ambientScheme, (⊤ : P.ambientScheme.Opens))) := by
  let := P.isAffineAmbient
  let := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
  let := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
  rw [Stacks.Smooth.moduleOfAppLE_smul_ker P.isFirstOrderThickening P.sub_le_preimage
    P.incl_comp_liftHomScheme P.ambient_le_preimage_tgt r x, Stacks.Smooth.appLE_top_top,
    Submodule.coe_smul, smul_eq_mul]

/-- **The datum restricting a chart presentation of a lifting problem to a smaller étale
chart.**  A morphism `m : V' ⟶ U'` of étale charts of `X'` together with a cartesian square
presenting the chart thickening `X ×_{X'} V' ⟶ V'` by a square-zero closed immersion of the
site, and affineness of the smaller chart.

The cartesian square is data for the same reason it is data in
`AlgebraicGeometry.Space.ChartLiftPresentation`: no fibre product of the big fppf site is formed
in this development.  It is never an obstruction — see
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.exists_of_isFirstOrderThickening`. -/
structure Restriction (P : ChartLiftPresentation C S hS p q a U')
    (V' : SmallEtale C S hS X'.1) where
  /-- the morphism of étale charts of `X'` along which the presentation is restricted -/
  chartMap : V' ⟶ U'
  /-- the closed subscheme of the smaller chart -/
  sub : BigFppfOver C S hS
  /-- its inclusion into the smaller chart -/
  incl : sub ⟶ (SmallEtale.toOver C S hS X'.1).obj V'
  /-- the chart morphism of the closed subscheme -/
  subChart : yoneda.obj sub ⟶ X.toFunctor
  /-- the square presenting `X ×_{X'} V'` is cartesian -/
  isPullback : IsPullback (yoneda.map incl) subChart V'.1.hom X.ι
  /-- the inclusion is a square-zero closed immersion -/
  squareZero : IsSquareZeroClosedImmersion C S hS incl
  /-- the smaller chart is affine -/
  isAffineAmbient :
    IsAffine ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj V'))

namespace Restriction

variable {P : ChartLiftPresentation C S hS p q a U'} {V' : SmallEtale C S hS X'.1}
  (R : Restriction P V')

/-- The morphism of the two ambient charts, as a morphism of the big fppf site. -/
abbrev ambientMap : (SmallEtale.toOver C S hS X'.1).obj V' ⟶
    (SmallEtale.toOver C S hS X'.1).obj U' :=
  (SmallEtale.toOver C S hS X'.1).map R.chartMap

/-- The smaller chart lies over `X'` through the bigger one. -/
theorem ambientMap_comp_chart :
    yoneda.map R.ambientMap ≫ U'.1.hom = V'.1.hom :=
  CostructuredArrow.w _

/-- The square presenting the smaller chart thickening commutes over `X'` through the bigger
chart: this is the hypothesis under which the cartesian square of `P` produces the morphism of
the two closed subschemes. -/
theorem incl_ambientMap_comp_chart :
    yoneda.map (R.incl ≫ R.ambientMap) ≫ U'.1.hom = R.subChart ≫ X.ι := by
  rw [Functor.map_comp, Category.assoc, R.ambientMap_comp_chart]
  exact R.isPullback.w

/-- **The restricted chart presentation.**  The chart square of `q` and the base chart are those
of `P`; the presented lift is the presented lift of `P` restricted along the morphism of charts,
which is again a lift by `AlgebraicGeometry.Space.IsChartLift.restrict`; and the chart thickening
is the one carried by the restriction datum. -/
abbrev presentation : ChartLiftPresentation C S hS p q a V' where
  sub := R.sub
  incl := R.incl
  subChart := R.subChart
  isPullback := R.isPullback
  squareZero := R.squareZero
  isAffineAmbient := R.isAffineAmbient
  tgt := P.tgt
  isAffineTgt := P.isAffineTgt
  bse := P.bse
  isAffineBse := P.isAffineBse
  tgtChart := P.tgtChart
  bseChart := P.bseChart
  chartHom := P.chartHom
  chartSq := P.chartSq
  liftHom := R.ambientMap ≫ P.liftHom
  isLift := by
    have h := P.isLift.restrict C S hS R.chartMap
    rwa [Functor.map_comp, Category.assoc]

/-! ### The morphism of the two chart thickenings -/

/-- **The induced morphism of the two closed subschemes.**  It is produced by the cartesian
square of `P`: the inclusion of the smaller closed subscheme followed by the morphism of charts
lands in `X`, so it factors uniquely through `X ×_{X'} U'`. -/
def subMap : R.sub ⟶ P.sub :=
  yoneda.preimage
    (P.isPullback.lift (yoneda.map (R.incl ≫ R.ambientMap)) R.subChart
      R.incl_ambientMap_comp_chart)

/-- The morphism of presheaves underlying
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap`. -/
theorem yoneda_map_subMap :
    yoneda.map R.subMap =
      P.isPullback.lift (yoneda.map (R.incl ≫ R.ambientMap)) R.subChart
        R.incl_ambientMap_comp_chart :=
  yoneda.map_preimage _

/-- The induced morphism of closed subschemes commutes with the two inclusions. -/
theorem subMap_comp_incl : R.subMap ≫ P.incl = R.incl ≫ R.ambientMap :=
  yoneda.map_injective (by
    rw [Functor.map_comp, R.yoneda_map_subMap]
    exact P.isPullback.lift_fst _ _ _)

/-- The induced morphism of closed subschemes commutes with the two chart morphisms into `X`. -/
theorem subMap_comp_subChart : yoneda.map R.subMap ≫ P.subChart = R.subChart := by
  rw [R.yoneda_map_subMap]
  exact P.isPullback.lift_snd _ _ _

/-- The morphism of the two ambient charts, as a morphism of schemes. -/
abbrev ambientMapScheme : R.presentation.ambientScheme ⟶ P.ambientScheme :=
  (BigFppfOver.toScheme C S hS).map R.ambientMap

/-- The morphism of the two closed subschemes, as a morphism of schemes. -/
abbrev subMapScheme : R.presentation.subScheme ⟶ P.subScheme :=
  (BigFppfOver.toScheme C S hS).map R.subMap

/-- The square of the two chart thickenings commutes, as a square of schemes. -/
theorem subMapScheme_comp_inclScheme :
    R.subMapScheme ≫ P.inclScheme = R.presentation.inclScheme ≫ R.ambientMapScheme := by
  rw [← Functor.map_comp, ← Functor.map_comp, R.subMap_comp_incl]

/-- The presented lift of the restriction is the presented lift of `P` precomposed with the
morphism of charts, as a morphism of schemes. -/
theorem ambientMapScheme_comp_liftHomScheme :
    R.ambientMapScheme ≫ P.liftHomScheme = R.presentation.liftHomScheme := by
  rw [← Functor.map_comp]

/-- **The reduction of the presented lift of the restriction is the reduction of the presented
lift of `P` precomposed with the morphism of the two closed subschemes**, as a morphism of the
site.  This is the factorization through which the restricted presentation's chart composite
factors, and it is what a naturality square in the chart of the source is stated at; the
corresponding statement for schemes is
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMapScheme_comp_redHomScheme`, which
is this under `AlgebraicGeometry.BigFppfOver.toScheme`. -/
theorem subMap_comp_redHom :
    R.subMap ≫ P.incl ≫ P.liftHom = R.presentation.incl ≫ R.presentation.liftHom := by
  rw [← Category.assoc, R.subMap_comp_incl, Category.assoc]

/-- The reduction of the presented lift of the restriction is the reduction of the presented
lift of `P` precomposed with the morphism of the two closed subschemes. -/
theorem subMapScheme_comp_redHomScheme :
    R.subMapScheme ≫ P.redHomScheme = R.presentation.redHomScheme := by
  rw [← Functor.map_comp]
  exact congrArg _ R.subMap_comp_redHom

/-! ### Restriction of the conormal data -/

/-- Restriction of regular functions along the morphism of ambient charts carries the conormal
data of the chart thickening of `P` into that of the restriction: the square of the two chart
thickenings commutes. -/
theorem mem_conormal_appTop (x : P.conormal) :
    R.ambientMapScheme.appTop.hom (x : Γ(P.ambientScheme, (⊤ : P.ambientScheme.Opens)))
      ∈ RingHom.ker R.presentation.inclScheme.appTop.hom := by
  rw [RingHom.mem_ker, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← R.subMapScheme_comp_inclScheme, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    RingHom.mem_ker.mp x.2, map_zero]

/-- **Restriction of the conormal data of the chart thickening.**  Restriction of regular
functions along the morphism of ambient charts is a `Γ(W, ⊤)`-linear map from the conormal data
of the chart thickening of `P` to that of the restriction, the two module structures being the
ones the acting derivations use. -/
noncomputable def restrictConormal :
    letI := P.isAffineAmbient
    letI := R.isAffineAmbient
    letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
    letI := Stacks.Smooth.thickeningKerModule R.presentation.isFirstOrderThickening
    letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
    letI := Stacks.Smooth.moduleOfAppLE R.presentation.redHomScheme
      R.presentation.sub_le_preimage R.presentation.conormal
    P.conormal →ₗ[Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens))] R.presentation.conormal :=
  letI := P.isAffineAmbient
  letI := R.isAffineAmbient
  letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
  letI := Stacks.Smooth.thickeningKerModule R.presentation.isFirstOrderThickening
  letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.moduleOfAppLE R.presentation.redHomScheme
    R.presentation.sub_le_preimage R.presentation.conormal
  { toFun := fun x => ⟨R.ambientMapScheme.appTop.hom
      (x : Γ(P.ambientScheme, (⊤ : P.ambientScheme.Opens))), R.mem_conormal_appTop x⟩
    map_add' := fun x y => Subtype.ext (map_add _ _ _)
    map_smul' := fun r x => Subtype.ext (by
      rw [RingHom.id_apply]
      change R.ambientMapScheme.appTop.hom ((r • x : P.conormal) : Γ(P.ambientScheme, _))
        = ((r • ⟨R.ambientMapScheme.appTop.hom (x : Γ(P.ambientScheme, _)),
            R.mem_conormal_appTop x⟩ : R.presentation.conormal) :
          Γ(R.presentation.ambientScheme, _))
      rw [coe_smul_conormal P r x, map_mul,
        coe_smul_conormal R.presentation r ⟨R.ambientMapScheme.appTop.hom
          (x : Γ(P.ambientScheme, _)), R.mem_conormal_appTop x⟩,
        ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        R.ambientMapScheme_comp_liftHomScheme]) }

/-- The value of `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.restrictConormal` is
restriction of regular functions along the morphism of ambient charts. -/
theorem coe_restrictConormal (x : P.conormal) :
    letI := P.isAffineAmbient
    letI := R.isAffineAmbient
    letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
    letI := Stacks.Smooth.thickeningKerModule R.presentation.isFirstOrderThickening
    letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
    letI := Stacks.Smooth.moduleOfAppLE R.presentation.redHomScheme
      R.presentation.sub_le_preimage R.presentation.conormal
    ((R.restrictConormal x : R.presentation.conormal) :
        Γ(R.presentation.ambientScheme, (⊤ : R.presentation.ambientScheme.Opens)))
      = R.ambientMapScheme.appTop.hom
        (x : Γ(P.ambientScheme, (⊤ : P.ambientScheme.Opens))) :=
  rfl

/-! ### Restriction of the acting derivations -/

/-- **Restriction of the acting derivations.**  Both presentations act by `Γ(V, ⊤)`-derivations of
`Γ(W, ⊤)` — the chart square of `q` is the same — so the restriction is composition with the
restriction of the conormal data. -/
noncomputable def restrictDeriv (δ : P.Deriv) : R.presentation.Deriv :=
  letI := P.isAffineAmbient
  letI := R.isAffineAmbient
  letI := Stacks.Smooth.algebraAppLE P.chartHomScheme P.tgt_le_preimage
  letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
  letI := Stacks.Smooth.thickeningKerModule R.presentation.isFirstOrderThickening
  letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.moduleOfAppLE R.presentation.redHomScheme
    R.presentation.sub_le_preimage R.presentation.conormal
  letI := Stacks.Smooth.moduleOfAppLEBase P.chartHomScheme P.redHomScheme P.tgt_le_preimage
    P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.moduleOfAppLEBase R.presentation.chartHomScheme
    R.presentation.redHomScheme R.presentation.tgt_le_preimage R.presentation.sub_le_preimage
    R.presentation.conormal
  letI := Stacks.Smooth.isScalarTowerOfAppLEBase P.chartHomScheme P.redHomScheme
    P.tgt_le_preimage P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.isScalarTowerOfAppLEBase R.presentation.chartHomScheme
    R.presentation.redHomScheme R.presentation.tgt_le_preimage R.presentation.sub_le_preimage
    R.presentation.conormal
  R.restrictConormal.compDer δ

/-- The value of the restricted derivation is the restriction of the value. -/
theorem coe_restrictDeriv_apply (δ : P.Deriv)
    (x : Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens))) :
    ((R.restrictDeriv δ x : R.presentation.conormal) :
        Γ(R.presentation.ambientScheme, (⊤ : R.presentation.ambientScheme.Opens)))
      = R.ambientMapScheme.appTop.hom
        ((δ x : P.conormal) : Γ(P.ambientScheme, (⊤ : P.ambientScheme.Opens))) :=
  rfl

/-! ### The action commutes with restriction -/

/-- The translated structure map of the restriction is the translated structure map of `P`
followed by restriction of regular functions along the morphism of ambient charts. -/
theorem translateHom_restrictDeriv (δ : P.Deriv) :
    R.presentation.translateHom (R.restrictDeriv δ) =
      P.translateHom δ ≫ R.ambientMapScheme.appTop := by
  let := P.isAffineAmbient
  let := R.isAffineAmbient
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  show (R.presentation.translateHom (R.restrictDeriv δ)).hom x
    = R.ambientMapScheme.appTop.hom ((P.translateHom δ).hom x)
  simp only [translateHom, Stacks.Smooth.addDerivationHom_apply]
  rw [map_add, R.coe_restrictDeriv_apply δ x, Stacks.Smooth.appLE_top_top,
    Stacks.Smooth.appLE_top_top, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    R.ambientMapScheme_comp_liftHomScheme]

/-- **The translate of the restriction is the restriction of the translate.**  The translate of
the restricted presented lift by the restricted derivation is the translate of the presented lift
precomposed with the morphism of ambient charts. -/
theorem translateScheme_restrictDeriv (δ : P.Deriv) :
    R.presentation.translateScheme (R.restrictDeriv δ) =
      R.ambientMapScheme ≫ P.translateScheme δ := by
  let := P.isAffineTgt
  refine Stacks.Smooth.homEquivOfIsAffine.injective ?_
  rw [Stacks.Smooth.homEquivOfIsAffine_apply, Stacks.Smooth.homEquivOfIsAffine_apply,
    Scheme.Hom.comp_appTop, R.presentation.translateScheme_appTop, P.translateScheme_appTop]
  exact R.translateHom_restrictDeriv δ

/-- The translate of the restriction is the restriction of the translate, as morphisms of the
big fppf site. -/
theorem translate_restrictDeriv (δ : P.Deriv) :
    R.presentation.translate (R.restrictDeriv δ) = R.ambientMap ≫ P.translate δ :=
  (BigFppfOver.toScheme C S hS).map_injective (by
    rw [Functor.map_comp, R.presentation.toScheme_map_translate, P.toScheme_map_translate]
    exact R.translateScheme_restrictDeriv δ)

/-- **The action of the chart derivations commutes with the restriction maps of the sheaf of
lifts.**  Restricting the translate of the presented lift by `δ` to the smaller chart gives the
translate, by the restricted derivation, of the presented lift of the restricted presentation.

This is the naturality clause an action of sheaves asks for, read on the acting derivations; the
form of it for the sections of the acting sheaf itself is in
`StacksDraft.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSectionRestriction`. -/
theorem map_translateSection (δ : P.Deriv) :
    (liftsSubfunctor C S hS p q a).toFunctor.map R.chartMap.op (P.translateSection δ) =
      R.presentation.translateSection (R.restrictDeriv δ) := by
  refine Subtype.ext ?_
  show Y.1.map R.ambientMap.op (P.translateValue δ) = R.presentation.translateValue _
  simp only [translateValue]
  rw [yonedaEquiv_naturality, ← Category.assoc, ← Functor.map_comp,
    ← R.translate_restrictDeriv δ]

/-! ### Restriction of the acting sections -/

/-- **Restriction of the acting sections of a chart presentation.**  The unique
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` of the restricted presentation
whose attached derivation is the restriction of the derivation attached to the given one.

It exists and is unique because `θ ↦ θ ∘ d` is a bijection onto the acting derivations,
`AlgebraicGeometry.Space.ChartLiftPresentation.derivOfActionSection_bijective`, which is
`Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module` at the restricted
presentation. -/
noncomputable def restrictActionSection (θ : P.ActionSection) : R.presentation.ActionSection :=
  (Equiv.ofBijective _ R.presentation.derivOfActionSection_bijective).symm
    (R.restrictDeriv (P.derivOfActionSection θ))

/-- **The characterising equation of the restriction of an acting section**: its attached
derivation is the restriction of the attached derivation. -/
theorem derivOfActionSection_restrictActionSection (θ : P.ActionSection) :
    R.presentation.derivOfActionSection (R.restrictActionSection θ) =
      R.restrictDeriv (P.derivOfActionSection θ) :=
  (Equiv.ofBijective _ R.presentation.derivOfActionSection_bijective).apply_symm_apply _

/-- The restriction of an acting section is the only acting section of the restricted
presentation with that attached derivation. -/
theorem eq_restrictActionSection {θ : P.ActionSection} {θ' : R.presentation.ActionSection}
    (h : R.presentation.derivOfActionSection θ' =
      R.restrictDeriv (P.derivOfActionSection θ)) :
    θ' = R.restrictActionSection θ :=
  R.presentation.derivOfActionSection_bijective.1
    (h.trans (R.derivOfActionSection_restrictActionSection θ).symm)

/-- **The action of the acting sections commutes with the restriction maps of the sheaf of
lifts.**  Restricting the translate of the presented lift by `θ` to the smaller chart gives the
translate, by the restricted acting section, of the presented lift of the restricted
presentation. -/
theorem map_translateActionSection (θ : P.ActionSection) :
    (liftsSubfunctor C S hS p q a).toFunctor.map R.chartMap.op (P.translateActionSection θ) =
      R.presentation.translateActionSection (R.restrictActionSection θ) := by
  rw [translateActionSection, translateActionSection,
    R.derivOfActionSection_restrictActionSection θ, R.map_translateSection]

end Restriction

/-! ### Existence of a restriction datum -/

/-- **A restriction datum exists along every morphism of affine étale charts of a first-order
thickening.**  So the restricted presentation of
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.presentation` is available at every
morphism of charts a covering family can produce, and none of the compatibility statements above
is empty.

The cartesian square presenting the chart thickening at the smaller chart is supplied by
`AlgebraicGeometry.Space.exists_squareZeroChart_of_isFirstOrderThickening`, exactly as it is for
the presentation itself. -/
theorem Restriction.exists_of_isFirstOrderThickening (P : ChartLiftPresentation C S hS p q a U')
    (hX : IsFirstOrderThickening C S hS X' X) {V' : SmallEtale C S hS X'.1} (m : V' ⟶ U')
    (hV' : IsAffine
      ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj V'))) :
    ∃ R : Restriction P V', R.chartMap = m := by
  obtain ⟨T₀, i₀, u₀, hpb, -, -, hsz⟩ :=
    exists_squareZeroChart_of_isFirstOrderThickening C S hS hX
      ((SmallEtale.toOver C S hS X'.1).obj V') V'.1.hom
      ((isEtale_iff_presheaf_of_yoneda C S hS V'.1.hom).2 V'.property) hV'
  exact ⟨{ chartMap := m
           sub := T₀
           incl := i₀
           subChart := u₀
           isPullback := hpb
           squareZero := hsz
           isAffineAmbient := hV' }, rfl⟩

end ChartLiftPresentation

end AlgebraicGeometry.Space

end
