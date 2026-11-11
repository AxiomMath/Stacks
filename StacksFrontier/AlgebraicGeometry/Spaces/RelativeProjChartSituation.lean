module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.FiniteTypeDegreeQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.GradedAlgebraChartSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet

/-!
# The chart situation of a relative Proj on an algebraic space, pinned to its graded algebra

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `𝒜` be a quasi-coherent
graded `𝒪_X`-algebra — the relative Proj situation of Stacks 0849.  The results on the relative
Proj of `X` in `StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj` are stated for a morphism
`π : P ⟶ X` carrying a `AlgebraicGeometry.Space.RelativeProjChart`: a surjective étale scheme
chart `V` of `X`, a relative Proj situation `t` of Stacks 01NN on the scheme of `V`, and the
cartesian square of Stacks 084B identifying `P ×_X V` with `Proj_V(t)`.

In that structure the chart-level situation `t` is **not tied to `𝒜` by any field**: nothing says
that `t` is the restriction `𝒜|_V`.  The implementation notes of that file record the reason —
the transport of a graded algebra on the small étale site of `X` to a scheme chart did not exist.
It does now, as `AlgebraicGeometry.Space.chartSheafAlgebra`, and this file supplies the missing
tie: it builds the situation of Stacks 01NN **out of** `𝒜` on an étale chart, so that a
`AlgebraicGeometry.Space.RelativeProjChart` can be taken for that situation and for no other.

## Main definitions

* `AlgebraicGeometry.Space.relativeProjChartSituation`: **the tie.**  The relative Proj situation
  of Stacks 01NN on an étale scheme chart `V` of `X` whose graded algebra is the restriction
  `𝒜|_V`.  Its three conditions — commutativity, concentration in nonnegative degrees,
  quasi-coherence of the pieces — are transported from the corresponding fields of the space-level
  situation.
* `AlgebraicGeometry.Space.relativeProjChartSheafAlgebra`: the same restriction `𝒜|_V`, in the
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` form that the scheme-level
  theory of closed subschemes of a relative Proj consumes.
* `AlgebraicGeometry.Space.RelativeProjSituationChart`: a chart presentation of `π : P ⟶ X`
  **whose chart situation is the restriction of `𝒜`** — a
  `AlgebraicGeometry.Space.RelativeProjChart` for `relativeProjChartSituation`, which is the
  structure of `StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj` with the missing field added.

## Main results

* `AlgebraicGeometry.Space.relativeProjChartSituation_algebra_piece` and
  `AlgebraicGeometry.Space.relativeProjChartSheafAlgebra_piece`: the homogeneous pieces of the
  chart situation are the module restrictions `AlgebraicGeometry.Space.restrictToChartScheme` of
  the pieces of `𝒜`.  These hold by definition, and they are what makes every statement below a
  statement about `𝒜` rather than about an unrelated graded algebra on the chart.
* `AlgebraicGeometry.Space.isSeparated_relativeProj_of_chart`,
  `AlgebraicGeometry.Space.isQuasiCompact_relativeProj_of_chart` and
  `AlgebraicGeometry.Space.isFiniteType_relativeProj_of_chart`: **Stacks 084E, 084F and 084G with
  the chart situation pinned to `𝒜`.**  Their hypotheses are now conditions on the restriction
  `𝒜|_V`, which is what the source's hypotheses on `𝒜` restrict to; the versions in
  `StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj` can only state them for a free situation.
* `AlgebraicGeometry.Space.exists_affine_relativeProjChartSituation`: for a quasi-compact
  algebraic space the chart may be taken affine and covering, by Stacks 03H6.  This is the chart
  the proof of Stacks 085M chooses.
* `AlgebraicGeometry.Space.exists_finiteType_chartDegreeSubmodule`: **Stacks 085M on the chart.**
  For a closed subscheme of finite presentation of the relative Proj of `𝒜|_V` over an *affine*
  chart `V`, there are a degree `d > 0` and a quasi-coherent finite type submodule
  `ℱ' ⊆ (𝒜_d)|_V` with `Z = Proj_V((𝒜|_V)/ℱ'(𝒜|_V))`.  The submodule is a submodule of the chart
  restriction of `𝒜_d` *on the nose*, which is the form the globalization of the source's proof
  consumes.

## Implementation notes

**What the tie is, and why it is a definition and not a hypothesis.**
`AlgebraicGeometry.Space.relativeProjChartSituation` is built from `𝒜` by
`AlgebraicGeometry.Space.chartSheafAlgebra`; its `mul_comm` field is the situation's own
`mul_comm` transported by `AlgebraicGeometry.Space.chartSheafAlgebra_isCommutative`, its
`negative_isZero` field is the situation's own `negative_isZero` read on sections by
`AlgebraicGeometry.Space.section_eq_zero_of_isZero` and transported by
`AlgebraicGeometry.Space.chartSheafAlgebra_vanishesInNegativeDegrees`.  So no clause of
Stacks 01NN is assumed on the chart: each is derived from the corresponding clause of Stacks 0849
on `X`.

**Quasi-coherence on the chart.**  Quasi-coherence of the pieces of `𝒜` is quasi-coherence on
the small étale site of `X`, while the restriction lives on the Zariski site of the chart's
scheme; the comparison is the étale-to-Zariski direction of Descent, Stacks 03DX, in the form
`AlgebraicGeometry.Space.chartSheafAlgebra_isQuasicoherent`.  So the `isQuasicoherent` field of
the chart situation is the situation's own `isQuasicoherent` field, transported, and the chart
situation is a function of the space-level situation and the chart alone.

**Stacks 085M on the chart.**  The scheme-level Stacks 0802,
`Stacks.AlgebraicGeometry.RelativeProjTwists.exists_finiteType_degreeQuotientPresentation`,
carries no hypothesis beyond the tag's own: the graded-ideal presentation of Stacks 0801 that it
used to ask for is `…RelativeProjTwists.gradedQuotientPresentation`, built in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/VanishingPresentation.lean`.  So
`AlgebraicGeometry.Space.exists_finiteType_chartDegreeSubmodule` carries none either.  What the
chart statement does *not* take as an input is the chart algebra: that is the restriction of `𝒜`,
by the tie, so the submodule the conclusion produces is a submodule of `(𝒜_d)|_V`.  Compactness
and quasi-separatedness of the chart's scheme are discharged from affineness of the chart, which
Stacks 03H6 supplies.

## What is not proved

**The globalization of Stacks 085M is not proved here, and nothing below claims it.**  The source
passes from the chart-level submodule `ℱ' ⊆ (𝒜_d)|_U` to a finite type quasi-coherent
`ℱ ⊆ 𝒜_d` on `X` with `ℱ' ⊆ ℱ|_U` by the colimit clause of Limits of Spaces, Stacks 0829.  That
clause is `AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone_of_07V9` in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsDirected`, and it still
rests on Stacks 07V9; only the directedness clause,
`AlgebraicGeometry.Space.isFiltered_finiteTypeQuasicoherentSubobject`, is unconditional.  The
direct alternative fails: a submodule of a module on the small étale site is stable under
restriction along *every* arrow into `U`, so the submodule generated by finitely many sections
over `U` is not generated on the slice at `U` by those sections and `{U}` does not witness
`SheafOfModules.IsFiniteType` for it.

**The descent of the chart-level presentation to `X` is not proved either.**  Even granted the
globalization, turning the chart-level
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.DegreeQuotientPresentation` into the space-level
`AlgebraicGeometry.Space.ClosedSubspaceDegreeQuotientPresentation` of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceFiniteType` needs an operation
taking a graded algebra on an algebraic space to its relative Proj, which this repository does not
have; that is why both structures carry their space as a datum.

**The two scheme-level relative Projs are not compared.**  `Stacks.RelativeProj.Situation`, which
`AlgebraicGeometry.Space.RelativeProjChart` is stated for, has its own relative Proj
`Stacks.RelativeProj.Situation.relativeProj`, glued over the affine opens of the base; the
scheme-level theory of Stacks 0801–0803 is stated for
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` and its
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj`, glued over the affine Zariski site.  No
declaration in this repository identifies the two.  Accordingly the chart presentation of this
file ties the chart *situation* to `𝒜` and `exists_finiteType_chartDegreeSubmodule` is stated for
the relative Proj of the chart *sheaf graded algebra*; both are the restriction `𝒜|_V`, by
`AlgebraicGeometry.Space.relativeProjChartSheafAlgebra_piece_eq`, but the closed subscheme of the
latter is not transported from a closed subspace of `P` through the cartesian square of the
former.

## References

* [Stacks Project, Tag 085M](https://stacks.math.columbia.edu/tag/085M)
* [Stacks Project, Tag 0802](https://stacks.math.columbia.edu/tag/0802)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084E](https://stacks.math.columbia.edu/tag/084E)
* [Stacks Project, Tag 084F](https://stacks.math.columbia.edu/tag/084F)
* [Stacks Project, Tag 084G](https://stacks.math.columbia.edu/tag/084G)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

universe u

namespace AlgebraicGeometry.Space

section Sections

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS}

/-- **Every local section of a zero module vanishes.**  The converse of
`Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.isZero_of_forall_eq_zero`, read on the small
étale site: a zero object has `𝟙 = 0`, and the identity acts on sections as the identity while
the zero morphism acts as zero.

This is what turns the `negative_isZero` field of `AlgebraicGeometry.Space.RelativeProjSituation`
into the sectionwise form that the chart restriction consumes. -/
theorem section_eq_zero_of_isZero (M : Modules.{u, u} B S hS X.1 X.2) (h : IsZero M)
    (W : (SmallEtale B S hS X.1)ᵒᵖ) (y : M.val.obj W) : y = 0 := by
  have h1 : (𝟙 M : M ⟶ M) = 0 := (IsZero.iff_id_eq_zero M).1 h
  have h2 := congrArg (fun φ : M ⟶ M => φ.val.app W y) h1
  have e1 : ((𝟙 M : M ⟶ M)).val.app W y = y := rfl
  have e2 : ((0 : M ⟶ M)).val.app W y = 0 := rfl
  rw [e1, e2] at h2
  exact h2

end Sections

section ChartSituation

variable (s : RelativeProjSituation.{u, u})

/-- The homogeneous pieces of negative degree of a relative Proj situation have no nonzero local
sections: the `negative_isZero` field of Stacks 0849, read on sections. -/
theorem relativeProjSituation_section_eq_zero (n : ℤ) (hn : n < 0)
    (W : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (y : (s.algebra.piece n).val.obj W) : y = 0 :=
  section_eq_zero_of_isZero (s.algebra.piece n) (s.negative_isZero n hn) W y

variable (V : SmallEtale s.site s.base s.containsBase s.space.1)

/-- **The tie: the relative Proj situation of Stacks 01NN carried by the restriction of `𝒜` to an
étale scheme chart.**

The base is the scheme underlying the chart and the graded algebra is the restriction `𝒜|_V` of
`AlgebraicGeometry.Space.chartSheafAlgebra`.  Commutativity and concentration in nonnegative
degrees and quasi-coherence of the pieces are the corresponding fields of the space-level
situation, transported; quasi-coherence passes from the small étale site of `X` to the Zariski
site of the chart's scheme by Stacks 03DX.

This is the datum that `AlgebraicGeometry.Space.RelativeProjChart` lacks: that structure takes an
arbitrary situation `t` on the chart, with no field relating it to the graded algebra on the
space. -/
@[stacks 01NN "the relative Proj situation on an étale scheme chart of an algebraic space: the \
chart's scheme with the restriction of the quasi-coherent graded algebra of Situation 0849, which \
is quasi-coherent, commutative and concentrated in nonnegative degrees"]
def relativeProjChartSituation : Stacks.RelativeProj.Situation.{u} where
  base := chartScheme V
  algebra := chartSheafAlgebra s.algebra V
  mul_comm := chartSheafAlgebra_isCommutative s.algebra V s.mul_comm
  negative_isZero n hn :=
    isZero_piece_of_neg _
      (chartSheafAlgebra_vanishesInNegativeDegrees s.algebra V
        (relativeProjSituation_section_eq_zero s)) n hn
  isQuasicoherent := chartSheafAlgebra_isQuasicoherent s.algebra V s.isQuasicoherent

/-- The base of the chart situation is the scheme underlying the chart. -/
theorem relativeProjChartSituation_base :
    (relativeProjChartSituation s V).base = chartScheme V :=
  rfl

/-- **The homogeneous pieces of the chart situation are the module restrictions of the pieces of
`𝒜`.**  This holds by definition, and it is the whole point of the tie: every statement about the
chart situation is a statement about `𝒜`. -/
theorem relativeProjChartSituation_algebra_piece (n : ℤ) :
    (relativeProjChartSituation s V).algebra.piece n =
      restrictToChartScheme s.site s.base s.containsBase s.space.1 s.space.2
        (s.algebra.piece n) V :=
  rfl

/-- The restriction `𝒜|_V` as sheaf-level graded algebra data of Stacks 01NN, which is the form
the scheme-level theory of closed subschemes of a relative Proj consumes.  Its clauses are the
clauses of the chart situation. -/
def relativeProjChartSheafAlgebra : SheafGradedAlgebra (chartScheme V) :=
  relativeProjChartAlgebra s.algebra V s.mul_comm
    (relativeProjSituation_section_eq_zero s) s.isQuasicoherent

/-- The homogeneous pieces of the chart sheaf graded algebra are the module restrictions of the
pieces of `𝒜`. -/
theorem relativeProjChartSheafAlgebra_piece (n : ℤ) :
    (relativeProjChartSheafAlgebra s V).piece n =
      restrictToChartScheme s.site s.base s.containsBase s.space.1 s.space.2
        (s.algebra.piece n) V :=
  rfl

/-- The chart sheaf graded algebra and the chart situation carry the same graded algebra: both are
the restriction `𝒜|_V`. -/
theorem relativeProjChartSheafAlgebra_piece_eq (n : ℤ) :
    (relativeProjChartSheafAlgebra s V).piece n =
      (relativeProjChartSituation s V).algebra.piece n :=
  rfl

end ChartSituation

/-! ### The chart presentation with the tie -/

section Chart

variable (s : RelativeProjSituation.{u, u})

/-- **The relative Proj of an algebraic space, presented on an étale scheme chart whose situation
is the restriction of `𝒜`.**

This is `AlgebraicGeometry.Space.RelativeProjChart` with the field it lacks: the chart is an
object of the small étale site of `X`, and the chart-level situation of Stacks 01NN is not free
but is `AlgebraicGeometry.Space.relativeProjChartSituation`, the restriction `𝒜|_V`.  The
cartesian square of Stacks 084B is carried, as it must be: the construction of the relative Proj
of an algebraic space is not in this library. -/
structure RelativeProjSituationChart {P : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u}
    (π : P ⟶ s.space.1) where
  /-- The étale chart of `X`, as an object of its small étale site. -/
  chart : SmallEtale s.site s.base s.containsBase s.space.1
  /-- The chart presentation of Stacks 084B, for the situation carried by `𝒜|_V` and for no
  other. -/
  toChart : RelativeProjChart s.site s.base s.containsBase π
    (relativeProjChartSituation s chart)

namespace RelativeProjSituationChart

variable {s} {P : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {π : P ⟶ s.space.1}
    (c : RelativeProjSituationChart s π)

/-- The chart situation of the presentation, abbreviated. -/
def situation : Stacks.RelativeProj.Situation.{u} :=
  relativeProjChartSituation s c.chart

/-- The homogeneous pieces of the chart situation are the module restrictions of the pieces of
`𝒜`. -/
theorem situation_algebra_piece (n : ℤ) :
    c.situation.algebra.piece n =
      restrictToChartScheme s.site s.base s.containsBase s.space.1 s.space.2
        (s.algebra.piece n) c.chart :=
  rfl

end RelativeProjSituationChart

/-- **Stacks 084E, with the chart situation pinned to `𝒜`.** The structure morphism of the
relative Proj is separated, with no hypothesis on the graded algebra.

This is `AlgebraicGeometry.Space.isSeparated_relativeProj` read on the chart presentation whose
situation is the restriction `𝒜|_V`. -/
@[stacks 084E "for a chart presentation whose chart situation is the restriction of the graded \
algebra of the space, rather than an unrelated situation on the chart",
  ega "II 8.14.1" "more general"]
theorem isSeparated_relativeProj_of_chart
    {P : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace s.site s.base s.containsBase P) (π : P ⟶ s.space.1)
    (c : RelativeProjSituationChart s π) :
    IsSeparated s.site s.base s.containsBase π :=
  isSeparated_relativeProj s.site s.base s.containsBase hP π c.toChart

/-- **Stacks 084F, with the chart situation pinned to `𝒜`.** The structure morphism of the
relative Proj is quasi-compact as soon as the restriction `𝒜|_V` satisfies one of the three
conditions of Stacks 07ZX.

The three conditions of the source are affine-local on the base, so for a quasi-coherent graded
algebra on `X` they hold exactly when they hold for the restriction to a surjective étale chart;
the version in `StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj` can only state them for a
situation unrelated to `𝒜`. -/
@[stacks 084F "with the three conditions read on the restriction of the graded algebra of the \
space to the chart, rather than on an unrelated situation on the chart"]
theorem isQuasiCompact_relativeProj_of_chart
    {P : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace s.site s.base s.containsBase P) (π : P ⟶ s.space.1)
    (c : RelativeProjSituationChart s π)
    (h : c.situation.IsFiniteTypeOverDegreeZero ∨
      c.situation.IsFinitelyGeneratedInDegreeOne ∨ c.situation.HasNilpotentPositiveQuotient) :
    IsQuasiCompact s.site s.base s.containsBase π :=
  isQuasiCompact_relativeProj s.site s.base s.containsBase hP s.space.2 π c.toChart h

/-- **Stacks 084G, with the chart situation pinned to `𝒜`.** The structure morphism of the
relative Proj is of finite type as soon as the restriction `𝒜|_V` is of finite type as a sheaf of
algebras. -/
@[stacks 084G "with the finite type condition read on the restriction of the graded algebra of \
the space to the chart, rather than on an unrelated situation on the chart"]
theorem isFiniteType_relativeProj_of_chart
    {P : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace s.site s.base s.containsBase P) (π : P ⟶ s.space.1)
    (c : RelativeProjSituationChart s π) (h : c.situation.IsFiniteType) :
    IsFiniteType s.site s.base s.containsBase π :=
  isFiniteType_relativeProj s.site s.base s.containsBase hP s.space.2 π c.toChart h

end Chart

/-! ### The affine chart of Stacks 03H6 -/

section AffineChart

variable (s : RelativeProjSituation.{u, u})

/-- **The affine surjective étale chart the proof of Stacks 085M chooses.**  For a quasi-compact
algebraic space there is an object of the small étale site with affine underlying scheme which
covers the site by itself, and it carries the chart situation of the restriction `𝒜|_V`.

This is Stacks 03H6 in the form
`AlgebraicGeometry.Space.SmallEtale.exists_affineObject_coversTop`, read for the algebraic
space of the relative Proj situation. -/
theorem exists_affine_relativeProjChartSituation
    (hqcs : IsQuasiCompactSpace s.site s.base s.containsBase s.space.1) :
    ∃ V : SmallEtale s.site s.base s.containsBase s.space.1,
      IsAffine (chartScheme V) ∧
        (SmallEtale.topology s.site s.base s.containsBase s.space.1).CoversTop
          (fun _ : PUnit.{u + 2} => V) := by
  obtain ⟨V, hVaff, hcov⟩ := SmallEtale.exists_affineObject_coversTop s.site s.base
    s.containsBase s.space.1 s.space.2 hqcs
  exact ⟨V, hVaff, hcov⟩

end AffineChart

/-! ### Stacks 085M on the chart -/

section ChartDegreeSubmodule

open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

variable (s : RelativeProjSituation.{u, u})
    (V : SmallEtale s.site s.base s.containsBase s.space.1)

/-- **Stacks 085M on an affine étale chart.**

Let `𝒜` be the quasi-coherent graded `𝒪_X`-algebra of a relative Proj situation on an algebraic
space `X`, let `V` be an étale chart of `X` with affine underlying scheme, and let `𝒜|_V` be the
restriction of Stacks 01NN carried by `AlgebraicGeometry.Space.relativeProjChartSheafAlgebra`.
For a closed subscheme `i : Z ⟶ Proj_V(𝒜|_V)` of finite presentation with `Proj_V(𝒜|_V) ⟶ V`
quasi-compact there are a degree `d > 0` and a quasi-coherent finite type submodule
`ℱ ⊆ (𝒜_d)|_V` of the **module restriction of `𝒜_d`** with `Z = Proj_V((𝒜|_V)/ℱ(𝒜|_V))`.

This is the step of the source's proof reading "by the case of schemes, Divisors 0802, applied
over `U`".  Compactness and quasi-separatedness of the base, which Stacks 0802 asks for, are
discharged from affineness of the chart; the graded algebra is not an input but the restriction of
`𝒜`, by `AlgebraicGeometry.Space.relativeProjChartSheafAlgebra_piece`, which is what makes the
submodule a submodule of `(𝒜_d)|_V`.

Neither the globalization of `ℱ` to a submodule of `𝒜_d` on `X` nor the descent of the
presentation to `X` is claimed; see *What is not proved* in the module documentation. -/
@[stacks 085M "the chart half: over an affine étale chart V of X there are d > 0 and a \
quasi-coherent finite type submodule ℱ of the module restriction (𝒜_d)|_V cutting out a closed \
subscheme of finite presentation of Proj_V(𝒜|_V), with no hypothesis beyond the tag's own, \
exactly as the scheme case Tag 0802. The globalization of ℱ \
to a submodule of 𝒜_d on X — the colimit clause of Tag 0829, still \
resting on Tag 07V9 — and the descent of the presentation to X are NOT claimed, so the existence \
assertion of Tag 085M on X is not delivered here"]
theorem exists_finiteType_chartDegreeSubmodule
    (hV : _root_.AlgebraicGeometry.IsAffine (chartScheme V)) {Z : Scheme.{u}}
    (i : Z ⟶ (relativeProj (relativeProjChartSheafAlgebra s V)).scheme)
    [_root_.AlgebraicGeometry.IsClosedImmersion i]
    [_root_.AlgebraicGeometry.QuasiCompact
      (relativeProj (relativeProjChartSheafAlgebra s V)).toBase]
    (hi : _root_.AlgebraicGeometry.FinitePresentation i) :
    ∃ d : ℕ, 0 < d ∧
      ∃ ℱ : (restrictToChartScheme s.site s.base s.containsBase s.space.1 s.space.2
          (s.algebra.piece (d : ℤ)) V).Submodule,
        ℱ.toSheafOfModules.IsQuasicoherent ∧
          SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
            Nonempty (DegreeQuotientPresentation
              (relativeProjChartSheafAlgebra s V) i ℱ) :=
  have : _root_.AlgebraicGeometry.IsAffine (chartScheme V) := hV
  Stacks.AlgebraicGeometry.RelativeProjTwists.exists_finiteType_degreeQuotientPresentation
    (relativeProjChartSheafAlgebra s V) i hi

end ChartDegreeSubmodule

end AlgebraicGeometry.Space

end
