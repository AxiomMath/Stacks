module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocusFinitePresentation

/-!
# Clause (3) of Stacks 0CZS joins the equivalence, and the clauses become literal

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, let `F`
be a quasi-coherent `𝒪_X`-module and let `x̄` be a geometric point of `X` with image `ȳ` in `Y`.
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreEtaleFreeLocus.lean` constructs the geometric
fibre `X_ȳ = X ×_{Y, ȳ} Spec(κ(ȳ))` and the canonical lift `x̄'` of `x̄` to it, and proves clause
(3) of Stacks 0CZS — `F_ȳ` is finite free in an étale neighbourhood of `x̄` inside `X_ȳ` — from
clause (4).  Its implementation notes report the reverse implication as unavailable, on the ground
that the source's `(3) ⟹ (2)` identifies the stalk of `F_ȳ` at `x̄` with the quotient
`F_x̄ / 𝔪_ȳ F_x̄` in which clauses (1) and (2) are carried there, and that identification is
condition (2) of Stacks 05WY, which
`StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessGeometricPoint.lean` does not state.

**That identification is not needed.**  The defining square of `X_ȳ` is cartesian, so clause (1)
for `f` at `x̄` and clause (1) for the structure morphism `X_ȳ ⟶ Spec(κ(ȳ))` at the lift `x̄'` are
*the same condition*, by
`AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_modulePullback_iff` — a
comparison of two quotients, which places no hypothesis on the square and identifies no stalk.
Clause (3) is clause (4) for `F_ȳ` on `X_ȳ` over that structure morphism, so the implications
`(4) ⟹ (2) ⟹ (1)` applied on the fibre give clause (1) at `x̄'`, and the comparison carries it
down to clause (1) at `x̄`; the converse runs the same comparison the other way and applies
`(1) ⟹ (4)` on the fibre, whose hypotheses are the base changes of the source's own.

With clause (3) in the equivalence, clauses (1) and (2) also become available in their **literal**
form — flatness, respectively freeness, of the honest geometric stalk of `F_ȳ` on `X_ȳ` at `x̄'`
over the honest étale local ring `𝒪_{X_ȳ, x̄'}`, with no quotient anywhere.  Clause (3) sits
between the two forms and ties them together: a trivialization on an étale neighbourhood of `x̄'`
makes the geometric stalk on `X_ȳ` free, and conversely.  So all four clauses of Stacks 0CZS are
equivalent, and clauses (1) and (2) hold in both readings.

## Main results

* `AlgebraicGeometry.Space.geometricPointMap_geometricFibreToSource_geometricFibrePoint`: the lift
  of a geometric point to the geometric fibre maps back to it — not merely to its image point.
* `AlgebraicGeometry.Space.isFiniteFreeNearGeometricPoint_iff_free_geometricModuleStalk`: for a
  quasi-coherent module of finite presentation on charts, finite freeness on an étale
  neighbourhood of a geometric point is freeness of the geometric stalk.
* `AlgebraicGeometry.Space.free_geometricModuleStalk_of_flat_geometricModuleStalk`: **Stacks 00NZ
  at the geometric stalk** — for such a module a flat geometric stalk is free.
* `AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_of_isFiniteFreeNearGeometricFibrePoint`:
  **Stacks 0CZS, (3) implies (1)**, with no hypothesis on `f` or `F` beyond quasi-coherence.
* `AlgebraicGeometry.Space.isFiniteFreeNearGeometricFibrePoint_of_flat_geometricFibreModuleStalk`:
  **Stacks 0CZS, (1) implies (3)**, under the source's own hypotheses.
* `AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_geometricFibre_tfae`: **Stacks 0CZS,
  the equivalence of clauses (1), (2), (3) and (4)**, with clauses (1) and (2) in both the
  quotient form and the literal form on the geometric fibre.
* `AlgebraicGeometry.Space.mem_etaleFiniteFreeLocus_of_mem_etaleFiniteFreeLocus_geometricFibre`:
  **Stacks 0CZS, (3) implies (4)** with both clauses in the small-étale-site reading of the locus
  of Stacks 0CZT.

## Implementation notes

**Which reading of clause (3).**  Clause (3) is read here as
`AlgebraicGeometry.Space.IsFiniteFreeNearGeometricPoint` at the lift `x̄'`, for the inverse image
of `F` along `X_ȳ ⟶ X` — that is, in the source's own Zariski-chart sense of an étale
neighbourhood, the sense in which clause (4) is read throughout this development: an étale
*scheme* chart of `X_ȳ` carrying a lift of `x̄'`, and a Zariski open of it containing the point
under that lift, on which the chart restriction becomes free of finite rank.  The small-étale-site
reading, membership of the image of `x̄'` in `AlgebraicGeometry.Space.etaleFiniteFreeLocus`, is the
reading
`AlgebraicGeometry.Space.mem_etaleFiniteFreeLocus_geometricFibre_of_isFiniteFreeNearGeometricPoint`
concludes in; the two are compared in only one direction at a *given* geometric point
(`AlgebraicGeometry.Space.mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint`), the
converse being available only with the geometric point chosen
(`AlgebraicGeometry.Space.exists_isFiniteFreeNearGeometricPoint_of_mem_etaleFiniteFreeLocus`).  So
the equivalence below is at the Zariski-chart reading, and the locus reading appears separately as
an implication between the two loci, where the chosen point does no harm because only its image
point enters the conclusion.  That implication is the one place the source's flatness hypothesis
has to be strengthened to flatness of `F` over `Y` everywhere: the chosen geometric point over the
image of `x̄'` need not be `x̄`, and flatness at a geometric point is not known here to depend only
on its image point.

**The lift maps back to the point itself.**  What the fibre construction records is
`AlgebraicGeometry.Space.pointsMap_geometricFibreToSource_geometricFibrePoint`, an equality of
*image points*; the comparison across the cartesian square is indexed by *geometric* points, so it
is the stronger equality of geometric points that is needed, and it holds: the lift has the same
field, containment witness and structure morphism as `x̄` by construction, and its section is
carried to the section of `x̄` by the universal property, so the two field-valued points agree
field by field.  The proof below is the same computation as that of the image-point equality, read
one level up.

**Why no hypotheses are needed for `(3) ⟹ (1)`.**  Its three inputs —
`AlgebraicGeometry.Space.free_geometricFibreModuleStalk_of_isFiniteFreeNearGeometricPoint`,
`AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_of_free` and the base-change comparison —
each generalise the source by dropping its flatness and finite-presentation hypotheses.  The
converse `(1) ⟹ (3)` does use them, through
`AlgebraicGeometry.Space.isFiniteFreeNearGeometricPoint_of_flat_geometricFibreModuleStalk` applied
on the fibre, which needs the structure morphism `X_ȳ ⟶ Spec(κ(ȳ))` to be locally of finite
presentation and the inverse image of `F` to be of finite presentation on charts of `X_ȳ` and flat
over `Spec(κ(ȳ))` at `x̄'`.  All three are base changes of the source's own hypotheses:
local finite presentation is stable under base change by Stacks 03XR
(`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isStableUnderBaseChange`), finite
presentation on the small étale site passes to an inverse image, and relative flatness at a point
passes to an inverse image by Stacks 05VW (1)
(`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback`).

**The two literal clauses.**  `isFiniteFreeNearGeometricPoint_iff_free_geometricModuleStalk` is the
step the existing `(4) ⟹ (2)` already takes internally, stated on its own and completed by its
converse: freeness of the Zariski stalk of a chart and freeness of the geometric stalk agree for a
module of finite presentation on charts
(`AlgebraicGeometry.Space.free_chartZariskiModuleStalk_iff_free_geometricModuleStalk`), and Stacks
0B8J turns a free Zariski stalk into a trivialization on a Zariski open of the chart.  Applied on
`X_ȳ` it reads clause (3) as the literal clause (2), and
`free_geometricModuleStalk_of_flat_geometricModuleStalk` — flatness of the geometric stalk
descends to the chart, where Stacks 00NZ makes a finitely presented flat module free, and freeness
ascends again — reads it as the literal clause (1).

## References

* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The lift of a geometric point to the geometric fibre maps back to it -/

/-- **The lift of a geometric point to the geometric fibre maps back to the point itself.**  This
sharpens `AlgebraicGeometry.Space.pointsMap_geometricFibreToSource_geometricFibrePoint`, which
records the equality of the image points, to an equality of geometric points.

The lift `AlgebraicGeometry.Space.geometricFibrePoint` is built with the field, containment
witness and structure morphism of `x̄`, so the two field-valued points differ only in their
sections, and the universal property of the fibre carries the section of the lift to the section
of `x̄`. -/
theorem geometricPointMap_geometricFibreToSource_geometricFibrePoint
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (xbar : GeometricPoint B S hS X.1) :
    geometricPointMap (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar)).hom
      (geometricFibrePoint B S hS f xbar) = xbar := by
  have hval : (FieldValuedPoint.map B S hS _
      (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar)).hom
      (geometricFibrePoint B S hS f xbar).val).value = xbar.val.value :=
    (congrArg yonedaEquiv
        ((isPullback_geometricFibre B S hS f (geometricPointMap f.hom xbar)).lift_fst
          (yonedaEquiv.symm xbar.val.value) (𝟙 _)
          ((yonedaEquiv_symm_value_comp B S hS f xbar).trans
            (Category.id_comp _).symm))).trans
      (Equiv.apply_symm_apply yonedaEquiv _)
  exact Subtype.ext (congrArg (fun v =>
    ({ carrier := xbar.val.carrier, field := xbar.val.field,
       contained := xbar.val.contained, toBase := xbar.val.toBase,
       value := v } : FieldValuedPoint B S hS X.1)) hval)

/-! ### Finite freeness near a geometric point, read on the geometric stalk -/

/-- **Finite freeness on an étale neighbourhood of a geometric point is freeness of the geometric
stalk**, for a quasi-coherent module of finite presentation on charts.

Both directions pass through the Zariski stalk of an étale scheme chart, where freeness agrees
with freeness of the geometric stalk by
`AlgebraicGeometry.Space.free_chartZariskiModuleStalk_iff_free_geometricModuleStalk`: a
trivialization on a Zariski open of a chart makes that stalk free
(`AlgebraicGeometry.Space.free_chartZariskiModuleStalk_of_over_iso_free`), and conversely Stacks
0B8J produces a trivialization on a Zariski open from a free stalk
(`AlgebraicGeometry.Space.exists_over_iso_free_of_free_chartZariskiModuleStalk`), on any étale
scheme chart through the point.  The forward direction needs no finite presentation and is the
step `AlgebraicGeometry.Space.free_geometricFibreModuleStalk_of_isFiniteFreeNearGeometricPoint`
takes internally. -/
theorem isFiniteFreeNearGeometricPoint_iff_free_geometricModuleStalk
    {X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hfp : IsFinitePresentationOnCharts B S hS X.2 F)
    (xbar : GeometricPoint B S hS X.1) :
    IsFiniteFreeNearGeometricPoint B S hS xbar F ↔
      Module.Free ↥(etaleLocalRing B S hS X.1 xbar)
        ↥(geometricModuleStalk B S hS X xbar F) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨N, r, W, hW, ⟨e⟩⟩ := h
    exact free_geometricModuleStalk_of_free_chartZariskiModuleStalk B S hS N F
      (free_chartZariskiModuleStalk_of_over_iso_free B S hS N F W hW e)
  · obtain ⟨N⟩ := nonempty_smallEtaleNeighborhood X.2 xbar
    obtain ⟨r, W, hW, he⟩ := exists_over_iso_free_of_free_chartZariskiModuleStalk B S hS N F hfp
      (free_chartZariskiModuleStalk_of_free_geometricModuleStalk B S hS N F hfp h)
    exact ⟨N, r, W, hW, he⟩

/-- **Stacks 00NZ at the geometric stalk.**  For a quasi-coherent `𝒪_X`-module of finite
presentation on charts, a flat geometric stalk is a free geometric stalk.

Flatness descends to the Zariski stalk of an étale scheme chart
(`AlgebraicGeometry.Space.flat_chartZariskiModuleStalk_of_flat_geometricModuleStalk`), where the
stalk is a finitely presented module over the local ring of the chart, so Stacks 00NZ makes it
free; freeness then ascends back to the geometric stalk by Stacks 05VP. -/
theorem free_geometricModuleStalk_of_flat_geometricModuleStalk
    {X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hfp : IsFinitePresentationOnCharts B S hS X.2 F)
    (xbar : GeometricPoint B S hS X.1)
    (h : Module.Flat ↥(etaleLocalRing B S hS X.1 xbar)
      ↥(geometricModuleStalk B S hS X xbar F)) :
    Module.Free ↥(etaleLocalRing B S hS X.1 xbar)
      ↥(geometricModuleStalk B S hS X xbar F) := by
  obtain ⟨N⟩ := nonempty_smallEtaleNeighborhood X.2 xbar
  have : Module.FinitePresentation ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) :=
    finitePresentation_chartZariskiModuleStalk B S hS N F hfp
  have : Module.Finite ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) := inferInstance
  have : Module.Flat ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) :=
    flat_chartZariskiModuleStalk_of_flat_geometricModuleStalk B S hS N F h
  exact free_geometricModuleStalk_of_free_chartZariskiModuleStalk B S hS N F
    Module.free_of_flat_of_isLocalRing

/-! ### Clause (3) implies clause (1) -/

/-- The inverse image of a finitely presented module to the geometric fibre is finitely presented
on charts. -/
private theorem isFinitePresentationOnCharts_modulePullback_geometricFibre
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] [SheafOfModules.IsFinitePresentationOnSite F]
    (xbar : GeometricPoint B S hS X.1) :
    IsFinitePresentationOnCharts B S hS
      (geometricFibre B S hS f (geometricPointMap f.hom xbar)).2
      ((modulePullback B S hS
        (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar))).obj F) :=
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar)) F inferInstance
  isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS _ _ this
    (isFinitePresentationOnSite_modulePullback B S hS _ F inferInstance)

/-- **Stacks 0CZS, (3) implies (1).**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`,
let `F` be a quasi-coherent `𝒪_X`-module and let `x̄` be a geometric point of `X` with image `ȳ`.
If the inverse image of `F` to the geometric fibre `X_ȳ` is finite free in an étale neighbourhood
of the lift of `x̄` — clause (3) — then the fibre stalk `(F_ȳ)_x̄` is a flat
`𝒪_{X_ȳ, x̄}`-module, which is clause (1).

The defining square of `X_ȳ` is cartesian, so clause (1) for `f` at `x̄` and clause (1) for the
structure morphism `X_ȳ ⟶ Spec(κ(ȳ))` at the lift are the same condition
(`AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_modulePullback_iff`).
Clause (3) is clause (4) for the inverse image on the fibre, so `(4) ⟹ (2) ⟹ (1)` on the fibre
gives clause (1) at the lift, and the comparison carries it down.  Condition (2) of Stacks 05WY —
the identification of the fibre stalk with the stalk on `X_ȳ` — is not used: both sides of the
comparison are taken in the quotient form.

Neither flatness of `F` over `Y`, nor local finite presentation of `f`, nor finite presentation of
`F` is assumed, which generalises the source. -/
@[stacks 0CZS "(3) implies (1), with the geometric fibre X_ybar formed as the fibre product of f \
with ybar = f o xbar in the category of algebraic spaces over S (02X2), clause (3) read as finite \
freeness of the inverse image of F to X_ybar on a Zariski open of an etale SCHEME chart of X_ybar \
around a point above the canonical lift of xbar, and the fibre stalk of clause (1) in the \
QUOTIENT FORM F_xbar / m_ybar F_xbar over O_{X, xbar} / m_ybar O_{X, xbar}; flatness of F over Y, \
local finite presentation of f and finite presentation of F are not assumed"]
theorem flat_geometricFibreModuleStalk_of_isFiniteFreeNearGeometricFibrePoint
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (xbar : GeometricPoint B S hS X.1)
    (h : IsFiniteFreeNearGeometricPoint B S hS (geometricFibrePoint B S hS f xbar)
      ((modulePullback B S hS
        (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar))).obj F)) :
    Module.Flat (geometricFibreLocalRing B S hS f xbar)
      (geometricFibreModuleStalk B S hS f F xbar) := by
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar)) F inferInstance
  have h1 := flat_geometricFibreModuleStalk_of_free B S hS
    (geometricFibreToPoint B S hS f (geometricPointMap f.hom xbar)) _
    (geometricFibrePoint B S hS f xbar)
    (free_geometricFibreModuleStalk_of_isFiniteFreeNearGeometricPoint B S hS
      (geometricFibreToPoint B S hS f (geometricPointMap f.hom xbar)) _
      (geometricFibrePoint B S hS f xbar) h)
  have h2 := (flat_geometricFibreModuleStalk_modulePullback_iff B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f
      (geometricPointHom (geometricPointMap f.hom xbar))) F
    (geometricFibrePoint B S hS f xbar)).2 h1
  rwa [geometricPointMap_geometricFibreToSource_geometricFibrePoint B S hS f xbar] at h2

/-! ### Clause (1) implies clause (3) -/

/-- **Stacks 0CZS, (1) implies (3).**  Let `f : X ⟶ Y` be locally of finite presentation, let `F`
be a finitely presented quasi-coherent `𝒪_X`-module and let `x̄` be a geometric point of `X` with
image `ȳ`.  If `F` is flat at `x` over `Y` and the fibre stalk `(F_ȳ)_x̄` is a flat
`𝒪_{X_ȳ, x̄}`-module, then the inverse image of `F` to the geometric fibre `X_ȳ` is finite free in
an étale neighbourhood of the lift of `x̄`, which is clause (3).

Clause (1) at `x̄` is clause (1) for the structure morphism `X_ȳ ⟶ Spec(κ(ȳ))` at the lift, by the
comparison across the cartesian defining square of `X_ȳ`, and `(1) ⟹ (4)` applied on the fibre is
clause (3).  Its hypotheses there are the base changes of the hypotheses here: Stacks 03XR for
local finite presentation of the structure morphism, the inverse image of a finitely presented
module for finite presentation on charts, and Stacks 05VW (1) for flatness at the lift. -/
@[stacks 0CZS "(1) implies (3), with the geometric fibre X_ybar formed as the fibre product of f \
with ybar = f o xbar in the category of algebraic spaces over S (02X2), the fibre stalk of clause \
(1) in the QUOTIENT FORM F_xbar / m_ybar F_xbar over O_{X, xbar} / m_ybar O_{X, xbar}, and clause \
(3) read as finite freeness of the inverse image of F to X_ybar on a Zariski open of an etale \
SCHEME chart of X_ybar around a point above the canonical lift of xbar"]
theorem isFiniteFreeNearGeometricFibrePoint_of_flat_geometricFibreModuleStalk
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] [SheafOfModules.IsFinitePresentationOnSite F]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (xbar : GeometricPoint B S hS X.1)
    (hflat : IsFlatOverAtGeometricPoint B S hS f F xbar)
    (hfibre : Module.Flat (geometricFibreLocalRing B S hS f xbar)
      (geometricFibreModuleStalk B S hS f F xbar)) :
    IsFiniteFreeNearGeometricPoint B S hS (geometricFibrePoint B S hS f xbar)
      ((modulePullback B S hS
        (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar))).obj F) := by
  have heq := geometricPointMap_geometricFibreToSource_geometricFibrePoint B S hS f xbar
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar)) F inferInstance
  have hfp' := isFinitePresentationOnCharts_modulePullback_geometricFibre B S hS f F xbar
  have hf' : IsLocallyOfFinitePresentation B S hS
      (geometricFibreToPoint B S hS f (geometricPointMap f.hom xbar)).hom :=
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f
        (geometricPointHom (geometricPointMap f.hom xbar))) hf
  have hflat' := isFlatOverAtGeometricPoint_modulePullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f
      (geometricPointHom (geometricPointMap f.hom xbar))) F
    (geometricFibrePoint B S hS f xbar) (by rw [heq]; exact hflat)
  have hfibre' := (flat_geometricFibreModuleStalk_modulePullback_iff B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f
      (geometricPointHom (geometricPointMap f.hom xbar))) F
    (geometricFibrePoint B S hS f xbar)).1 (by rw [heq]; exact hfibre)
  exact isFiniteFreeNearGeometricPoint_of_flat_geometricFibreModuleStalk B S hS
    (geometricFibreToPoint B S hS f (geometricPointMap f.hom xbar)) _ hf' hfp'
    (geometricFibrePoint B S hS f xbar) hflat' hfibre'

/-! ### Stacks 0CZS: clauses (1), (2), (3) and (4) -/

/-- **Stacks 0CZS, the equivalence of all four clauses.**  Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite presentation, let `F` be a finitely presented
quasi-coherent `𝒪_X`-module and let `x̄` be a geometric point of `X` with image `ȳ`.  If `F` is
flat at `x` over `Y`, then

1. `(F_ȳ)_x̄` is a flat `𝒪_{X_ȳ, x̄}`-module,
2. `(F_ȳ)_x̄` is a free `𝒪_{X_ȳ, x̄}`-module,
3. `F_ȳ` is finite free in an étale neighbourhood of `x̄` in `X_ȳ`,
4. `F` is finite free in an étale neighbourhood of `x` in `X`

are equivalent.  Clauses (1) and (2) appear twice: in the quotient form
`F_x̄ / 𝔪_ȳ F_x̄` over `𝒪_{X, x̄} / 𝔪_ȳ 𝒪_{X, x̄}` in which this development carries them, and in
the literal form on the geometric fibre `X_ȳ` of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreEtaleFreeLocus.lean` — the honest geometric
stalk of the inverse image of `F` at the canonical lift of `x̄`, over the honest étale local ring
of `X_ȳ` there.  The entries are, in order: clause (1) in the quotient form, clause (2) in the
quotient form, clause (1) in the literal form, clause (2) in the literal form, clause (3), and
clause (4).

The equivalence of the two forms of clauses (1) and (2) is *not* condition (2) of Stacks 05WY, and
does not supply it: no identification of the quotient with the stalk on `X_ȳ` is produced, only
the agreement of the flatness and freeness conditions, which clause (3) mediates. -/
@[stacks 0CZS "clauses (1), (2), (3) and (4) are equivalent, under the source's own hypotheses; \
the geometric fibre X_ybar is formed as the fibre product of f with ybar = f o xbar in the \
category of algebraic spaces over S (02X2), clauses (3) and (4) are read as finite freeness on a \
Zariski open of an etale SCHEME chart around a point above the relevant geometric point, and \
clauses (1) and (2) appear BOTH in the QUOTIENT FORM F_xbar / m_ybar F_xbar over \
O_{X, xbar} / m_ybar O_{X, xbar} and in the LITERAL FORM on X_ybar, i.e. the geometric stalk of \
the inverse image of F at the canonical lift of xbar over the etale local ring of X_ybar there; \
the agreement of the two forms is a consequence of the equivalence and is NOT condition (2) of \
Stacks 05WY, which stays unavailable"]
theorem flat_geometricFibreModuleStalk_geometricFibre_tfae
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] [SheafOfModules.IsFinitePresentationOnSite F]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (xbar : GeometricPoint B S hS X.1)
    (hflat : IsFlatOverAtGeometricPoint B S hS f F xbar) :
    [Module.Flat (geometricFibreLocalRing B S hS f xbar)
        (geometricFibreModuleStalk B S hS f F xbar),
      Module.Free (geometricFibreLocalRing B S hS f xbar)
        (geometricFibreModuleStalk B S hS f F xbar),
      Module.Flat
        ↥(etaleLocalRing B S hS (geometricFibre B S hS f (geometricPointMap f.hom xbar)).1
          (geometricFibrePoint B S hS f xbar))
        ↥(geometricModuleStalk B S hS (geometricFibre B S hS f (geometricPointMap f.hom xbar))
          (geometricFibrePoint B S hS f xbar)
          ((modulePullback B S hS
            (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar))).obj F)),
      Module.Free
        ↥(etaleLocalRing B S hS (geometricFibre B S hS f (geometricPointMap f.hom xbar)).1
          (geometricFibrePoint B S hS f xbar))
        ↥(geometricModuleStalk B S hS (geometricFibre B S hS f (geometricPointMap f.hom xbar))
          (geometricFibrePoint B S hS f xbar)
          ((modulePullback B S hS
            (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar))).obj F)),
      IsFiniteFreeNearGeometricPoint B S hS (geometricFibrePoint B S hS f xbar)
        ((modulePullback B S hS
          (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar))).obj F),
      IsFiniteFreeNearGeometricPoint B S hS xbar F].TFAE := by
  have hfp : IsFinitePresentationOnCharts B S hS X.2 F :=
    isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS X F inferInstance
      inferInstance
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar)) F inferInstance
  have hfp' := isFinitePresentationOnCharts_modulePullback_geometricFibre B S hS f F xbar
  tfae_have 1 → 6 := fun h =>
    isFiniteFreeNearGeometricPoint_of_flat_geometricFibreModuleStalk B S hS f F hf hfp xbar
      hflat h
  tfae_have 6 → 2 := fun h =>
    free_geometricFibreModuleStalk_of_isFiniteFreeNearGeometricPoint B S hS f F xbar h
  tfae_have 2 → 1 := fun h => flat_geometricFibreModuleStalk_of_free B S hS f F xbar h
  tfae_have 1 → 5 := fun h =>
    isFiniteFreeNearGeometricFibrePoint_of_flat_geometricFibreModuleStalk B S hS f F hf
      xbar hflat h
  tfae_have 5 → 1 := fun h =>
    flat_geometricFibreModuleStalk_of_isFiniteFreeNearGeometricFibrePoint B S hS f F
      xbar h
  tfae_have 5 → 4 := fun h =>
    (isFiniteFreeNearGeometricPoint_iff_free_geometricModuleStalk B S hS _ hfp'
      (geometricFibrePoint B S hS f xbar)).1 h
  tfae_have 4 → 5 := fun h =>
    (isFiniteFreeNearGeometricPoint_iff_free_geometricModuleStalk B S hS _ hfp'
      (geometricFibrePoint B S hS f xbar)).2 h
  tfae_have 4 → 3 := fun h => have := h; Module.Flat.of_free
  tfae_have 3 → 4 := fun h =>
    free_geometricModuleStalk_of_flat_geometricModuleStalk B S hS _ hfp'
      (geometricFibrePoint B S hS f xbar) h
  tfae_finish

/-! ### Clause (3) implies clause (4) at the locus of Stacks 0CZT -/

/-- **Stacks 0CZS, (3) implies (4), both clauses in the small-étale-site reading of the locus of
Stacks 0CZT.**  Let `f : X ⟶ Y` be locally of finite presentation, let `F` be a quasi-coherent
`𝒪_X`-module of finite presentation on charts which is flat over `Y`, and let `x̄` be a geometric
point of `X` with image `ȳ`.  If the image of the canonical lift of `x̄` lies in the finite-free
étale locus of the inverse image of `F` to the geometric fibre `X_ȳ`, then the image of `x̄` lies
in the finite-free étale locus of `F`.

This is the reverse inclusion of the base-change clause of Stacks 0CZT —
`AlgebraicGeometry.Space.mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint_modulePullback`
— at the cartesian defining square of `X_ȳ`, with the Zariski-chart reading upstairs supplied at a
*chosen* geometric point over the image of the lift
(`AlgebraicGeometry.Space.exists_isFiniteFreeNearGeometricPoint_of_mem_etaleFiniteFreeLocus`);
only the image point of the chosen point enters the conclusion, and it is the image of the lift,
which is the image of `x̄`.

Because the chosen point need not be `x̄`, the source's hypothesis of flatness of `F` over `Y` *at
`x`* is strengthened here to flatness over `Y` everywhere.  The equivalence
`AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_geometricFibre_tfae` carries the source's
own hypothesis, at the Zariski-chart reading of clause (3). -/
@[stacks 0CZS "(3) implies (4) with BOTH clauses in the SMALL-ETALE-SITE reading, i.e. membership \
in the locus of Stacks 0CZT on the geometric fibre X_ybar and on X respectively, X_ybar being the \
fibre product of f with ybar = f o xbar in the category of algebraic spaces over S (02X2); the \
source's flatness of F over Y at x is STRENGTHENED to flatness of F over Y everywhere, because \
the Zariski-chart reading upstairs is recovered only at a geometric point chosen over the image \
of the lift of xbar"]
theorem mem_etaleFiniteFreeLocus_of_mem_etaleFiniteFreeLocus_geometricFibre
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F)
    (hF : IsFlatOver B S hS X.2 f.hom F) (xbar : GeometricPoint B S hS X.1)
    (h : (geometricFibrePoint B S hS f xbar).image ∈ etaleFiniteFreeLocus B S hS
      ((modulePullback B S hS
        (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar))).obj F)) :
    xbar.image ∈ etaleFiniteFreeLocus B S hS F := by
  obtain ⟨wbar, hw, hnear⟩ := exists_isFiniteFreeNearGeometricPoint_of_mem_etaleFiniteFreeLocus
    B S hS _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ F inferInstance) h
  have hres := mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint_modulePullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f
      (geometricPointHom (geometricPointMap f.hom xbar))) F hf hfp hF wbar hnear
  rwa [hw, pointsMap_geometricFibreToSource_geometricFibrePoint B S hS f xbar] at hres

end AlgebraicGeometry.Space

end
