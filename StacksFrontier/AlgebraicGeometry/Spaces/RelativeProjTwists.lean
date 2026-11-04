module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.DischargedEtaleDescent
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.Statement
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelationRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjDescent

/-!
# The twisting sheaves on the relative Proj of an algebraic space

In Situation 0849 let `X` be an algebraic space over a scheme `S` and `𝒜` a quasi-coherent
graded `𝒪_X`-algebra, and let `π : P = Proj_X(𝒜) ⟶ X` be its relative homogeneous spectrum of
Stacks 084C.  Stacks 084D asserts that `P` carries a quasi-coherent sheaf of `ℤ`-graded
`𝒪_P`-algebras `⨁_{n ∈ ℤ} 𝒪_P(n)` together with a canonical homomorphism of graded algebras
`ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)`, whose base change to any scheme over `X` agrees with the twists
of Constructions, Stacks 01NR.

The source proves this by descent along the presentation that follows Stacks 084C: on a
surjective étale scheme chart `U ⟶ X` with relation `R = U ×_X U` the algebra gives relative
Proj situations on `U` and on `R`, whose relative Projs are schemes `P_U` and `P_R`; the twists
on `P_U` exist by Stacks 01NR, their pullbacks along the two projections `P_R ⇉ P_U` are
identified with the twists on `P_R` by Stacks 01O3, and Stacks 03M3 descends the result to `P`.

**This file does not prove Stacks 084D.**  The full statement is
`AlgebraicGeometry.Space.RelativeProjSituation.twistGradedAlgebra_psi_baseChange`, in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraOfProj`.  What is here
is the glueing datum over the sheaf-level substrate, its quotient and chart, and the two descent
inputs below for the homogeneous pieces; see `## What is not done here`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSheafGlueingData` is the glueing datum of Stacks 084C
  over the *sheaf-level* substrate of Situation 01NN: an étale presentation of `X`, the graded
  algebras it induces on the chart and on the relation scheme as
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, their relative Projs as
  objects of the site, and the descent datum relating them.
* `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.relativeProj` is `Proj_X(𝒜)`,
  `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.toBase` its structure morphism
  `π : Proj_X(𝒜) ⟶ X` and
  `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.chart` the étale chart
  `P_U ⟶ Proj_X(𝒜)`;
  `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.chartObject` is that chart read as an
  object of the small étale site of `Proj_X(𝒜)`, and
  `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.projPresentation` the étale presentation
  of `Proj_X(𝒜)` by `(P_U, P_R)`, with `P_U` and `P_R` as its presenting and relation objects on
  the nose.
* `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.chartTwist` is the `n`-th twist of
  Stacks 01NR on the chart, read on the scheme of `P_U`, and
  `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.groupoidTwist` the same module read on
  the object scheme of the groupoid of the presentation.
* `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.HasTwistDescentDatum` and
  `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.IsEffectiveEtaleDescent` are the two
  granted inputs, discussed one by one in the implementation notes.
* `AlgebraicGeometry.Space.isoOfPullbackEqToHom`: pullback of modules along
  `CategoryTheory.eqToHom` of an equality of schemes reflects isomorphisms.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.isAlgebraicSpace_relativeProj`,
  `…chart_surjective`, `…chart_etale` and `…chart_isKernelPair` are Stacks 084C and 02WW for the
  glueing datum over the sheaf-level substrate, carried over from
  `AlgebraicGeometry.Space.RelativeProjGlueingData` by the same quotient apparatus.
* `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.chart_comp_toBase`: the structure
  morphism `π` restricts along the chart to the structure morphism of `P_U` over `U` followed by
  the atlas of `X`.  This is what exhibits the quotient as the relative Proj *over `X`*, and it
  is why a comparison on the chart with the twists of Stacks 01NR on `P_U` is the chart case of
  the base-change clause of Stacks 084D.  The cartesian square
  `P_U = Proj_X(𝒜) ×_X U` itself is not repeated here; it is
  `AlgebraicGeometry.Space.RelativeProjGlueingData.isPullback_chart_toBase` for the parallel
  datum, and its proof uses only the site-level fields, which the two data carry identically.

## Implementation notes

**Why a second glueing datum.**  Situation 01NN is formalized twice in this library, and the two
formalizations share no declarations.  `Stacks.RelativeProj.Situation` is the substrate of
`AlgebraicGeometry.Space.RelativeProjGlueingData`, the glueing datum of Stacks 084C already in
the tree; `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` is the substrate over
which `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`, the structure Stacks 01NR
produces, is stated.  Neither statement can be deduced from the other: the carriers of the two
rings of homogeneous sections agree but their `CommRing` instances do not, one being
`DirectSum.instGCommRing` and the other obtained from a `Classical.choice` — this is recorded in
`StacksFrontier/AlgebraicGeometry/RelativeProjBridge/GeneratedInDegreeOne.lean` — and the only
bridge between them,
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.toGradedAlgebra`, runs from the
sheaf-level datum to the affine-open one, which is the direction that does not help here.  So
`AlgebraicGeometry.Space.RelativeProjSheafGlueingData` repeats the *shape* of
`AlgebraicGeometry.Space.RelativeProjGlueingData` over the sheaf-level substrate, so that a
`TwistData` types against its chart algebra directly.  Nothing is lost by the repetition:
`AlgebraicGeometry.Space.RelativeProjGlueingData` has no consumer outside its own file, and the
declarations of this file that produce `Proj_X(𝒜)` use only the *site-level* fields — the
presentation, the two relative Projs as objects of the site, the two cartesian squares of
Stacks 084B and the equivalence-relation condition — which the two data carry identically.  One
field is dropped: the isomorphism of the chart with the base of its situation is unnecessary
here, the chart algebra being stated over the scheme of the chart itself.

**The chart as an object of the small étale site.**  The objects of
`AlgebraicGeometry.Space.SmallEtale` are the étale charts of a presheaf, that is the objects of
`CategoryTheory.CostructuredArrow yoneda` whose structure morphism is representable with étale
base changes — which is exactly what
`AlgebraicGeometry.Space.RelativeProjSheafGlueingData.chart_etale` provides for the quotient
map.  So `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.chartObject` costs nothing, and
`AlgebraicGeometry.Space.chartScheme` of it is the scheme of `P_U` by `rfl`.  That is what makes
`AlgebraicGeometry.Space.restrictToChartScheme` usable to compare an `𝒪_P`-module with a module
on the *scheme* `P_U`, where the twists of Stacks 01NR live; no comparison between the small
étale site of a scheme and the small étale site of the algebraic space it represents is needed,
and in particular the conditional equivalence of Stacks 03DX is not used.

**The two granted inputs, and why neither contains the conclusion.**

`HasTwistDescentDatum` says: in every degree the `n`-th twist on the chart, read on the object
scheme of the groupoid of the presentation of `Proj_X(𝒜)`, is the underlying module of a
quasi-coherent module on that groupoid scheme in the sense of Stacks 03LI — that is, it carries
a descent isomorphism `α : t^*𝒪_{P_U}(n) ⟶ s^*𝒪_{P_U}(n)` satisfying the cocycle law and the
normalisation along the identity.  This is what the source's appeals to Stacks 01O3 and to the
uniqueness clause of Stacks 01NR supply: Stacks 01O3 identifies each of the two pullbacks of the
chart twists with the twists on `P_R`, which gives `α`, and the uniqueness clause of Stacks 01NR
is what makes the two conditions hold.  It does not contain the conclusion.  Every object it
mentions is a scheme or a module on a scheme: the groupoid of a presentation is a
`Stacks.Groupoids.GroupoidScheme`, its object and arrow schemes are the schemes of `P_U` and
`P_R`, and the hypothesis quantifies over no sheaf on `Proj_X(𝒜)` and over no grading,
multiplication, unit or `ψ`.  And it is *implied* by the conclusion, hence strictly weaker: from
a quasi-coherent `𝒪_P`-module whose chart restriction is the `n`-th twist,
`Stacks.Groupoids.GroupoidScheme.quasicoherentModuleOfBase` — which is proved in this library,
unconditionally, for a groupoid scheme over a scheme target — produces precisely such a
groupoid module, its descent isomorphism being the canonical comparison of the two pullbacks of
a module pulled back from the quotient.  Note that it is weaker still than the pair of
hypotheses the reconnaissance for this file proposed: it does not ask for a `TwistData` on the
relation scheme, nor for the two identifications of Stacks 01O3 separately, nor for the
compatibility of `α` with them — it asks only that *some* descent datum exist on the chart
twists, which is all the descent step consumes.

`IsEffectiveEtaleDescent` is Stacks 03M3 for the presentation of `Proj_X(𝒜)` by `(P_U, P_R)`, in
its essential-surjectivity half: every quasi-coherent module on the groupoid of the presentation
is the chart restriction of a quasi-coherent `𝒪_P`-module.  Stacks 03M3 asserts an equivalence
between the quasi-coherent `𝒪_P`-modules and the quasi-coherent modules on the groupoid of a
presentation, so this is one half of it, quantified over *all* quasi-coherent modules on the
groupoid, with no mention of a grading, of a multiplication, of a unit, of `ψ`, or of the twists
at all.  It therefore cannot contain the conclusion of Stacks 084D: it is a statement about an
arbitrary quasi-coherent module and says nothing about the existence of any particular one.  In
this library Stacks 03M3 is available only for a scheme target and only in its functor direction
(`Stacks.Groupoids.GroupoidScheme.quasicoherentModuleOfBaseFunctor`); the equivalence for an
algebraic-space target is not proved anywhere, which is why it is carried as a binder — the same
device as the Stacks 02O5 hypothesis of
`Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_rightDerivedPlus_of_isProperOver_supp`
and the Stacks 03M3/07TU presentation of
`AlgebraicGeometry.Space.exists_isFiltered_coherentSubmoduleColimit`.

Neither hypothesis is refutable and the statement is not vacuous: both are consequences of true
theorems — the first of Stacks 01O3 and 01NR, the second of Stacks 03M3 — so no choice of the
data makes the antecedent unsatisfiable.

**Transport along the groupoid identification.**  The groupoid of a presentation is obtained
from `AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation`, so its object scheme is only
*equal*, not definitionally equal, to the scheme of the presenting object; the equality is
`AlgebraicGeometry.Space.Presentation.relationGroupoid_objects_left`.  Modules are carried across
it by pullback along `CategoryTheory.eqToHom`, and `AlgebraicGeometry.Space.isoOfPullbackEqToHom`
brings an isomorphism back: the equality of schemes is substituted away, after which the
pullback is the pullback along an identity.  Substituting the equality away is what avoids the
`CategoryTheory.eqToHom` algebra that a `rewrite` on a motive mentioning the section groups of a
sheaf of modules does not admit.

## What is not done here

**The graded-algebra structure and `ψ` are not constructed over this substrate.**  What is
missing, and why:

* The multiplication `𝒪_P(i) × 𝒪_P(j) ⟶ 𝒪_P(i + j)` and the unit.  A
  `SheafOfModules.GradedAlgebra` carries its multiplication as a `Stacks.BilinearMap`, that is
  as a bilinear map on the sections over each object of the site.  Descending one along the
  presentation is not a consequence of Stacks 03M3: an equivalence of categories transports
  morphisms, not bilinear maps, and there is no tensor product of quasi-coherent modules on an
  algebraic space in this library through which a bilinear map could be presented as a morphism.
  The library has no declaration that glues or descends a bilinear map of sheaves of modules
  along a covering family or along a surjective étale morphism at all; the only locality
  mechanism for bilinear maps is extension along a locally bijective morphism
  (`Stacks.BilinearMap.compLeftEquiv` and `Stacks.BilinearMap.compRightEquiv`), which is
  sheafification, not descent.  Correspondingly no `SheafOfModules.GradedAlgebra` anywhere in
  this library is built by descent or by glueing: the constructions that exist are
  sheafification (`Stacks.GradedAlgebra.sheafify`) and functorial transport.
* `ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)`.  Its source needs the pullback of the graded algebra on `X`
  along `π`, and the comparison of the restriction of that pullback to the chart with
  `π_U^*(𝒜|_U)` needs the restriction of a graded algebra on the small étale site of an
  algebraic space to a scheme chart.  Only the single-module case of that restriction exists
  (`AlgebraicGeometry.Space.restrictToChartScheme`); there is no graded version, which is the
  obstruction already recorded in `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProj.lean` and
  in `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjGlueing.lean`.
* The base-change clause of Stacks 084D for an arbitrary scheme `Z ⟶ X`.  The source itself
  writes that it omits the verification; here it is not stated.

The relation algebra `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.relationAlgebra` and
the two isomorphisms identifying the schemes of `P_U` and `P_R` with the relative Projs are
fields of the glueing datum that the two descent inputs do not consume: the descent datum is
stated directly on the chart twists, so the twists on `P_R` never need to be named.  They are
retained because they are what the datum of Stacks 084C consists of, and because they are what
the descent datum is to be built from.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03LI](https://stacks.math.columbia.edu/tag/03LI)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)

/-! ### Transport along an equality of schemes -/

/-- **Pullback of modules along `CategoryTheory.eqToHom` of an equality of schemes reflects
isomorphisms.**  The equality of schemes is substituted away, after which the pullback is the
pullback along an identity morphism. -/
noncomputable def isoOfPullbackEqToHom {Y Z : Scheme.{u}} (h : Y = Z) (M N : Z.Modules)
    (e : (Scheme.Modules.pullback (eqToHom h)).obj M ≅
      (Scheme.Modules.pullback (eqToHom h)).obj N) :
    M ≅ N := by
  subst h
  have f : ∀ P : Y.Modules, (Scheme.Modules.pullback (eqToHom (rfl : Y = Y))).obj P ≅ P :=
    fun P =>
      (Scheme.Modules.pullbackCongr (eqToHom_refl Y rfl)).app P ≪≫
        (Scheme.Modules.pullbackId Y).app P
  exact (f M).symm ≪≫ e ≪≫ f N

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The glueing datum of Stacks 084C over the sheaf-level substrate -/

/-- **Glueing data for the relative Proj of an algebraic space, over the sheaf-level substrate
of Situation 01NN.**  An étale presentation `(U, R)` of `X`, the quasi-coherent graded algebras
the algebra on `X` induces on the presenting scheme and on the relation scheme as
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, their relative Projs `P_U` and
`P_R` of Stacks 01NQ as objects of the site, and the descent datum exhibiting `P_R` as the base
change of `P_U` along each of the two maps of the relation.

This is `AlgebraicGeometry.Space.RelativeProjGlueingData` restated over the substrate on which
the twists of Stacks 01NR are stated; see the implementation notes of this file for why the two
cannot be shared. -/
structure RelativeProjSheafGlueingData (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) extends ProjDescentData B S hS X hX where
  /-- The graded algebra the algebra on `X` induces on the presenting scheme. -/
  chartAlgebra : SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj presentation.U)
  /-- The graded algebra the algebra on `X` induces on the relation scheme. -/
  relationAlgebra : SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj presentation.R)
  /-- Its scheme is the relative Proj of the chart algebra. -/
  projChartIso :
    (BigFppfOver.toScheme B S hS).obj projChart ≅ (relativeProj chartAlgebra).scheme
  /-- That structure morphism is the structure morphism of the relative Proj. -/
  projChartHom_comp : (BigFppfOver.toScheme B S hS).map projChartHom =
    projChartIso.hom ≫ (relativeProj chartAlgebra).toBase
  /-- Its scheme is the relative Proj of the relation algebra. -/
  projRelationIso :
    (BigFppfOver.toScheme B S hS).obj projRelation ≅ (relativeProj relationAlgebra).scheme
  /-- That structure morphism is the structure morphism of the relative Proj. -/
  projRelationHom_comp : (BigFppfOver.toScheme B S hS).map projRelationHom =
    projRelationIso.hom ≫ (relativeProj relationAlgebra).toBase

namespace RelativeProjSheafGlueingData

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
  (d : RelativeProjSheafGlueingData B S hS X hX)

section Quotient

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-! ### The relative Proj and its chart -/

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **The étale presentation of `Proj_X(𝒜)` by `(P_U, P_R)`**, with `P_U` and `P_R` as its
presenting and relation objects on the nose. -/
noncomputable def projPresentation :
    Presentation B S hS d.relativeProj d.isAlgebraicSpace_relativeProj where
  U := d.projChart
  R := d.projRelation
  target := d.projTarget
  source := d.projSource
  isEtaleEquivalenceRelation := d.isEtaleEquivalenceRelation_pre
  toSpace := d.chart
  surjective := d.chart_surjective
  etale := d.chart_etale
  isPullback := d.chart_isKernelPair

/-- The chart `P_U ⟶ Proj_X(𝒜)`, read as an object of the small étale site of `Proj_X(𝒜)`: an
étale chart of a presheaf is an object of `CategoryTheory.CostructuredArrow yoneda` whose
structure morphism is representable with étale base changes, which is
`AlgebraicGeometry.Space.RelativeProjSheafGlueingData.chart_etale`. -/
noncomputable def chartObject : SmallEtale B S hS d.relativeProj :=
  ⟨CostructuredArrow.mk d.chart, d.chart_etale⟩

/-- The scheme underlying the chart object is the scheme of `P_U`. -/
theorem chartScheme_chartObject :
    chartScheme d.chartObject = (BigFppfOver.toScheme B S hS).obj d.projChart :=
  rfl

/-- The groupoid scheme of the presentation of `Proj_X(𝒜)` by `(P_U, P_R)`, that is, the unique
groupoid scheme extending the relation `P_R ⇉ P_U`. -/
noncomputable abbrev projGroupoid : GroupoidScheme S :=
  d.projPresentation.relationGroupoid B S hS

/-- The object scheme of that groupoid is the scheme of `P_U`. -/
theorem projGroupoid_objects_left :
    d.projGroupoid.objects.left = (BigFppfOver.toScheme B S hS).obj d.projChart :=
  d.projPresentation.relationGroupoid_objects_left B S hS

/-! ### The twists on the chart -/

variable (DU : Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData d.chartAlgebra)

/-- **The `n`-th twist of Stacks 01NR on the chart**, read on the scheme of `P_U` through the
identification of that scheme with the relative Proj of the chart algebra. -/
noncomputable def chartTwist (n : ℤ) : (chartScheme d.chartObject).Modules :=
  (Scheme.Modules.pullback d.projChartIso.hom).obj (DU.algebra.piece n)

/-- The `n`-th twist on the chart, read on the object scheme of the groupoid of the presentation
of `Proj_X(𝒜)`. -/
noncomputable def groupoidTwist (n : ℤ) : d.projGroupoid.objects.left.Modules :=
  (Scheme.Modules.pullback (eqToHom d.projGroupoid_objects_left)).obj (d.chartTwist DU n)

/-! ### The two granted inputs -/

/-- **The descent datum for the chart twists**, as a named hypothesis: in every degree the
`n`-th twist of Stacks 01NR on the chart underlies a quasi-coherent module on the groupoid of
the presentation of `Proj_X(𝒜)` in the sense of Stacks 03LI — a descent isomorphism between its
two pullbacks to `P_R`, satisfying the cocycle law and the normalisation along the identity.

This is what the source's appeal to Stacks 01O3, together with the uniqueness clause of
Stacks 01NR, supplies.  It mentions only schemes and modules on schemes, and it is implied by
the conclusion of Stacks 084D through
`Stacks.Groupoids.GroupoidScheme.quasicoherentModuleOfBase`; see the implementation notes. -/
def HasTwistDescentDatum : Prop :=
  ∀ n : ℤ, ∃ N : GroupoidScheme.QuasicoherentModule d.projGroupoid,
    Nonempty (N.module ≅ d.groupoidTwist DU n)

/-- **Stacks 03M3 for the presentation of `Proj_X(𝒜)`, essential surjectivity**, as a named
hypothesis: every quasi-coherent module on the groupoid of the presentation is the restriction
to the chart of a quasi-coherent `𝒪_{Proj_X(𝒜)}`-module.

This is one half of the equivalence of Stacks 03M3, quantified over all quasi-coherent modules
on the groupoid.  In this library Stacks 03M3 is proved only for a scheme target and only in its
functor direction, so it is carried as a binder. -/
def IsEffectiveEtaleDescent : Prop :=
  ∀ N : GroupoidScheme.QuasicoherentModule d.projGroupoid,
    ∃ M : Modules.{u, u} B S hS d.relativeProj d.isAlgebraicSpace_relativeProj,
      M.IsQuasicoherentOnSite ∧
      Nonempty (N.module ≅
        (Scheme.Modules.pullback (eqToHom d.projGroupoid_objects_left)).obj
          (restrictToChartScheme B S hS d.relativeProj
            d.isAlgebraicSpace_relativeProj M d.chartObject))

end Quotient

end RelativeProjSheafGlueingData

end AlgebraicGeometry.Space

end
