module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StructureSectionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# Global functions on a limit of algebraic spaces: Stacks 07SI for the structure sheaf

Stacks 07SI reads, verbatim:

> Notation and assumptions as in Situation 084R. Suppose that `ℱ₀` is a quasi-coherent sheaf
> on `X₀`. Set `ℱᵢ = f_{0i}^*ℱ₀` for `i ≥ 0` and set `ℱ = f_0^*ℱ₀`. Then
> `Γ(X, ℱ) = colim_{i ≥ 0} Γ(Xᵢ, ℱᵢ)`.

Stacks 07SQ consumes exactly one instance of it, the one with `ℱ₀ = 𝒪_{X₀}`: the ring
`A = Γ(X, 𝒪_X)` is the directed colimit of the rings `Aᵢ = Γ(Xᵢ, 𝒪_{Xᵢ})`. **This file states
that instance**, on the situation Stacks 07SQ is to be stated on, and records which of its
clauses follow formally and which do not.

The coefficient being the structure sheaf is a genuine simplification and not merely a special
case. For a general `ℱ₀` the transition maps `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` are built from the
inverse-image comparison `AlgebraicGeometry.Space.modulePullbackCompIso` and compose only up to
a canonical isomorphism, which is why
`AlgebraicGeometry.Space.LimitSituation.IsSectionsColimit` in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitDescent.lean` is stated
elementwise over maps carrying their own coherence. For the structure sheaf the transition maps
are `AlgebraicGeometry.Space.globalFunctionsMap`, which is *strictly* functorial
(`AlgebraicGeometry.Space.globalFunctionsMap_comp`), so the system is an honest diagram and the
compatibility clause is a one-line consequence. That is `ι_trans_globalFunctionsMap` below.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.stage`,
  `AlgebraicGeometry.Space.DescentSituation.limitSpace`,
  `AlgebraicGeometry.Space.DescentSituation.transition` and
  `AlgebraicGeometry.Space.DescentSituation.projection` read a descent situation in the
  category of algebraic spaces over the base, as
  `AlgebraicGeometry.Space.LimitSituation` is already read in
  `StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitDescent.lean`.
* `AlgebraicGeometry.Space.DescentSituation.IsGlobalFunctionsColimit` is **the assertion of
  Stacks 07SI for the structure sheaf**: that the rings of global regular functions of the
  stages have the ring of global regular functions of the limit as their filtered colimit,
  along `AlgebraicGeometry.Space.globalFunctionsMap`, taken elementwise as
  `Stacks.IsStagesColimit`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.projection_comp_transition` — a projection followed
  by a transition morphism is a projection, in the category of algebraic spaces.
* `AlgebraicGeometry.Space.DescentSituation.ι_trans_globalFunctionsMap` — **the compatibility
  clause of Stacks 07SI for the structure sheaf**, proved: the maps to the limit are compatible
  with the transition maps.
* `AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit_iff` — the assertion,
  unfolded into the three clauses, one of which is the previous result, so that the two that
  remain are visible as statements rather than as a name.
* `AlgebraicGeometry.Space.DescentSituation.ringPackage_of_isGlobalFunctionsColimit` — the
  assertion is exactly the hypothesis package the commutative-algebra core of Stacks 07SQ
  takes.
* `AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit` — **the assertion
  itself**, for an index set in the universe of the site under the size hypothesis of Stacks
  07SF. It is the base's
  `AlgebraicGeometry.Space.DescentSituation.isStagesColimit_globalFunctions` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Limits/StructureSectionsColimit.lean`, read in the
  spelling of this file.

## What this file does and does not prove

**Stacks 07SI for the structure sheaf is proved here**, as
`AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit`, for an index set lying in
the universe of the site and under the size hypothesis `#I < B.cutoff.ord.cof` of Stacks 07SF.
The proof is the base's
`AlgebraicGeometry.Space.DescentSituation.isStagesColimit_globalFunctions`, whose two
substantive clauses are instances of the approximation of morphisms into the affine line
described below.

**No `@[stacks 07SI]` attribute appears here.** Stacks 07SI asserts the colimit for an arbitrary
quasi-coherent `ℱ₀`, and what is proved here is the case `ℱ₀ = 𝒪_{X₀}` — the case Stacks 07SQ
consumes, and the only one — so the tag would overclaim. Stacks 07SQ itself is proved from this
file in
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/AffineStage.lean` and carries its tag
there, on `AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj`.

*What the rest of the library already supplies.* The relation system and the equalizer
presentations are both available:

* The **relation system exists**. `AlgebraicGeometry.Space.LimitSituation.chartSystem` builds
  `j ↦ Xⱼ ×_{X₀} V` for an *arbitrary* affine scheme-valued point `V ⟶ X₀` — it asks neither
  étaleness nor surjectivity — and
  `AlgebraicGeometry.Space.LimitSituation.chartLimitBridge` is its limit. Applied to
  `R₀ = U₀ ×_{X₀} U₀` it is the relation system, `R₀` being affine at a separated stage by
  `AlgebraicGeometry.Space.LimitSituation.exists_affine_relationChart_of_isAbsolutelySeparated`.
  Both live in `StacksFrontier/AlgebraicGeometry/Spaces/Limits/SeparatedRelationSystem.lean`.
* **Both equalizer presentations exist**, for the structure sheaf:
  `AlgebraicGeometry.Space.LimitSituation.chartEqualizerPresentation` stagewise and
  `AlgebraicGeometry.Space.LimitSituation.chartLimitEqualizerPresentation` at the limit, in
  `StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartLimitEqualizerPresentation.lean`, built on
  `AlgebraicGeometry.Space.structureSectionsEquivEqualizer` (Stacks 03M8 for the structure
  sheaf) in `StacksFrontier/AlgebraicGeometry/Spaces/Limits/StructureSectionsEqualizer.lean`.
* So on the **module route** — the route through
  `AlgebraicGeometry.Space.LimitSituation.IsSectionsColimit` at
  `SheafOfModules.unit (structureRingSheaf …)` — Stacks 07SI for the structure sheaf is reduced
  to exactly two naturality statements, `he` and `heT`, by
  `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_naturality_of_unit`. Those two
  are blocked on one coherence fact: that the components of
  `AlgebraicGeometry.Space.modulePullbackUnitIso` are compatible with
  `AlgebraicGeometry.Space.modulePullbackCompIso`, which is unavailable because the former is
  built by `CategoryTheory.CorepresentableBy.uniqueUpToIso` and so is characterised only
  through a corepresentability bijection.

*Why this file takes the other route.* That coherence obligation is an artefact of expressing
the structure sheaf inside the module formalism. `IsGlobalFunctionsColimit` does not: its
transition maps are `AlgebraicGeometry.Space.globalFunctionsMap`, which is strictly functorial,
so there is no comparison isomorphism to be coherent about and no analogue of `he`/`heT` arises.
What that route needs instead is the compatibility of chart restriction with
`globalFunctionsMap`, which is `globalFunctionsMap_val` above — **proved**, and the one input
the separation clause needs.

*The route, and the single statement it reduces to.* Global regular functions on an algebraic
space **are** its morphisms to the affine line, naturally in the space:
`AlgebraicGeometry.Space.globalFunctionsHomEquiv` and
`AlgebraicGeometry.Space.globalFunctionsHomEquiv_natural` in
`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/BigEtaleStructureSheaf.lean`. So
`IsGlobalFunctionsColimit` *is* the assertion
`Hom(X, 𝔸¹_S) = colim Hom(Xᵢ, 𝔸¹_S)` for `X = lim Xᵢ`, and both of its clauses are instances
of morphisms out of a limit into a fixed target. Both are proved, unconditionally, in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/RelativeLimitApproximation.lean`:
`AlgebraicGeometry.Space.exists_stage_map_of_relativelyLimitPreserving` is the surjectivity
clause and `AlgebraicGeometry.Space.exists_stage_eq_of_relativelyLimitPreserving` the
separation clause, for a target locally of finite presentation, over hypotheses that are the
fields of `AlgebraicGeometry.Space.DescentSituation` together with the size bound
`#I < B.cutoff.ord.cof`.

The target hypothesis those two results ask of `𝔸¹_S` is
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_affineLineToBase`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/StructureSectionsColimit.lean` alongside the colimit
statement itself.

*The chart-system route, which this file does not take.* The chart system
(`AlgebraicGeometry.Space.LimitSituation.chartSystem`, `.stagesSchemeDiagram`,
`.isLimit_stagesSchemeCone`), the relation system, both equalizer presentations and the affine
and qcqs cases of Stacks 01Z0 would give the two clauses by the source's own argument, and
`globalFunctionsMap_val_of_chartHom` above is the step of it that intertwines chart
restriction with `globalFunctionsMap` across the system's Cartesian squares. That route is
left in place and is not needed; it would additionally require injectivity of chart
restriction at a surjective étale chart in the `globalFunctions'` spelling, for which
`AlgebraicGeometry.Space.injective_globalFunctionsChartRestriction_of_isSurjective` is stated
in the `AlgebraicGeometry.Space.globalFunctions` spelling, the two not being known here to be
interchangeable.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe v u

namespace AlgebraicGeometry.Space

/-! ### Chart restriction against pullback of global functions -/

section ChartCompatibility

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The two spellings of the ring of global regular functions are the same type.**
`AlgebraicGeometry.Space.globalFunctions` is the sections of
`AlgebraicGeometry.Space.structurePresheaf`, and
`AlgebraicGeometry.Space.globalFunctions'` the sections of
`AlgebraicGeometry.Space.SmallEtale.structurePresheaf`; those two presheaves are the same
term, `(SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ`, declared
twice in different namespaces, so the two rings are definitionally equal.

This matters because the two halves of the development are written in different spellings.
`AlgebraicGeometry.Space.globalFunctionsMap` and
`AlgebraicGeometry.Space.globalFunctionsHomEquiv`, through which Stacks 07SI for the structure
sheaf is proved below, are stated for the primed one; while
`AlgebraicGeometry.Space.globalFunctionsChartRestriction`,
`AlgebraicGeometry.Space.injective_globalFunctionsChartRestriction_of_isSurjective` and —
needed by Stacks 07SQ, which must take `Spec` of the ring and so needs a `u`-model —
`AlgebraicGeometry.Space.globalFunctionsModel` and
`AlgebraicGeometry.Space.globalFunctionsModelEquiv` are stated for the unprimed one. Being
`rfl`, this lemma lets either be used where the other is expected. -/
theorem globalFunctions_eq_globalFunctions' (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    globalFunctions B S hS F = globalFunctions' B S hS F := rfl

/-- **Pullback of global regular functions is precomposition of charts.** The value of
`AlgebraicGeometry.Space.globalFunctionsMap f s` at a scheme chart `j` of the source is the
value of `s` at the chart `j ≫ f` of the target.

This is the compatibility of chart restriction with pullback, and it is stated over *all scheme
charts* rather than over the étale charts because that is where it is true: an étale chart `W`
of `V` composed with a morphism `f : V ⟶ U` of algebraic spaces is an étale chart of `U` only
when `f` is itself étale, whereas it is always a scheme chart. This is exactly why
`AlgebraicGeometry.Space.globalFunctionsMap` is defined through
`AlgebraicGeometry.Space.chartFunctions` and the bijection
`AlgebraicGeometry.Space.globalFunctionsChartEquiv`, and the step back to the étale charts is
that bijection's own defining property. -/
theorem globalFunctionsChartEquiv_globalFunctionsMap_val
    {U V : AlgebraicSpaces B S hS} (f : V ⟶ U) (s : globalFunctions' B S hS U.obj)
    (j : (CostructuredArrow yoneda V.obj)ᵒᵖ) :
    ((globalFunctionsChartEquiv B S hS V).val (globalFunctionsMap B S hS f s)).val j
      = ((globalFunctionsChartEquiv B S hS U).val s).val
          ((CostructuredArrow.map f.hom).op.obj j) := by
  rw [globalFunctionsMap_chart]
  rfl

/-- **The value of a global regular function at an étale chart is the value of its all-charts
extension there.** This is the defining property of
`AlgebraicGeometry.Space.globalFunctionsChartEquiv`, read elementwise. -/
theorem globalFunctionsChartEquiv_val_inclusion
    (U : AlgebraicSpaces B S hS) (s : globalFunctions' B S hS U.obj)
    (W : (SmallEtale B S hS U.obj)ᵒᵖ) :
    ((globalFunctionsChartEquiv B S hS U).val s).val
        ((SmallEtale.inclusion B S hS U.obj).op.obj W) = s.val W :=
  congrFun (congrArg Subtype.val ((globalFunctionsChartEquiv B S hS U).property s)) W

/-- **Chart restriction against pullback of global functions, at an étale chart.** The value at
an étale chart `W` of `V` of the pullback of `s` along `f : V ⟶ U` is the value of the
all-charts extension of `s` at the scheme chart of `U` obtained by composing `W` with `f`.

This is the form the separation clause of Stacks 07SI for the structure sheaf consumes: taking
`W` to be a chart of a stage coming from the chart system, the right-hand side is a restriction
of `s`'s value at the chart of the earlier stage, because the chart system's squares make the
two composites agree. -/
theorem globalFunctionsMap_val
    {U V : AlgebraicSpaces B S hS} (f : V ⟶ U) (s : globalFunctions' B S hS U.obj)
    (W : (SmallEtale B S hS V.obj)ᵒᵖ) :
    (globalFunctionsMap B S hS f s).val W
      = ((globalFunctionsChartEquiv B S hS U).val s).val
          ((CostructuredArrow.map f.hom).op.obj
            ((SmallEtale.inclusion B S hS V.obj).op.obj W)) := by
  rw [← globalFunctionsChartEquiv_val_inclusion B S hS V (globalFunctionsMap B S hS f s) W,
    globalFunctionsChartEquiv_globalFunctionsMap_val]

/-- **The chart-square identification.** Let `f : V ⟶ U` be a morphism of algebraic spaces,
`W` an étale chart of `V` and `W'` an étale chart of `U`, and suppose the scheme chart
`W ⟶ V ⟶ U` factors through `W'` by a morphism `γ` of charts of `U`. Then the value at `W` of
the pullback of `s` along `f` is the restriction along `γ` of the value of `s` at `W'`.

This is the form in which the separation clause of Stacks 07SI for the structure sheaf uses
`AlgebraicGeometry.Space.globalFunctionsMap_val`: taking `f` to be a transition morphism
`Xⱼ ⟶ Xᵢ` of the situation and `W`, `W'` the charts `Uⱼ`, `Uᵢ` of the chart system, the
Cartesian square of the system supplies `γ`, and the conclusion says that chart restriction
intertwines `AlgebraicGeometry.Space.globalFunctionsMap` with the transition map of the chart
system — which is exactly what lets the affine case of Stacks 01Z0 be applied to the chart
system and the conclusion carried back.

The hypothesis is a morphism of charts rather than an equation of charts because that is what
the Cartesian square gives and what the compatibility of the all-charts family consumes: the
family `AlgebraicGeometry.Space.globalFunctionsChartEquiv` produces is a section of the
presheaf of charts, so it converts any morphism of charts into a restriction identity. -/
theorem globalFunctionsMap_val_of_chartHom
    {U V : AlgebraicSpaces B S hS} (f : V ⟶ U) (s : globalFunctions' B S hS U.obj)
    (W : SmallEtale B S hS V.obj) (W' : SmallEtale B S hS U.obj)
    (γ : (CostructuredArrow.map f.hom).obj ((SmallEtale.inclusion B S hS V.obj).obj W) ⟶
      (SmallEtale.inclusion B S hS U.obj).obj W') :
    (globalFunctionsMap B S hS f s).val (op W)
      = ((BigFppfOver.toScheme B S hS).map γ.left).appTop.hom (s.val (op W')) := by
  rw [globalFunctionsMap_val, ← globalFunctionsChartEquiv_val_inclusion B S hS U s (op W')]
  exact (((globalFunctionsChartEquiv B S hS U).val s).property γ.op).symm

end ChartCompatibility

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-! ### The assertion of Stacks 07SI for the structure sheaf -/

/-- **The assertion of Stacks 07SI for the structure sheaf.** In Situation 084R, the ring of
global regular functions of the limit is the filtered colimit of the rings of global regular
functions of the stages, along `AlgebraicGeometry.Space.globalFunctionsMap`, taken elementwise
as `Stacks.IsStagesColimit`.

The colimit is taken over the whole index set rather than over the stages at or beyond the
chosen index, as the source takes it. Those agree: the source restricts to `i ≥ 0` only because
its coefficient `ℱᵢ = f_{0i}^*ℱ₀` is defined only there, and the structure sheaf is defined at
every stage. The index set of a descent situation is directed, so the restriction would in any
case change nothing.

This **is proved in this library**, under the size hypothesis of Stacks 07SF and for an index
set lying in the universe of the site:
`AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit`, at the end of this file. -/
def IsGlobalFunctionsColimit : Prop :=
  Stacks.IsStagesColimit
    (G := fun i : I => globalFunctions' B S hS (D.stage i).obj)
    (T := globalFunctions' B S hS D.limitSpace.obj)
    (fun _ _ h s => globalFunctionsMap B S hS (D.transition h) s)
    (fun i s => globalFunctionsMap B S hS (D.projection i) s)

/-- **The compatibility clause of Stacks 07SI for the structure sheaf.** Pulling a global
regular function on a stage back to a later stage and then to the limit is pulling it back to
the limit.

This is the one clause of the assertion that is formal, and it is formal because pullback of
global regular functions is *strictly* functorial: it is
`AlgebraicGeometry.Space.globalFunctionsMap_comp` applied to
`AlgebraicGeometry.Space.DescentSituation.projection_comp_transition`. For a general
quasi-coherent coefficient the corresponding maps compose only up to the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` and the clause is not formal. -/
theorem ι_trans_globalFunctionsMap {i j : I} (h : i ≤ j)
    (s : globalFunctions' B S hS (D.stage i).obj) :
    globalFunctionsMap B S hS (D.projection j)
        (globalFunctionsMap B S hS (D.transition h) s)
      = globalFunctionsMap B S hS (D.projection i) s := by
  rw [← RingHom.comp_apply, ← globalFunctionsMap_comp, D.projection_comp_transition h]

/-- **The assertion of Stacks 07SI for the structure sheaf, unfolded into its three clauses**,
the first of which is `AlgebraicGeometry.Space.DescentSituation.ι_trans_globalFunctionsMap` and
therefore holds. What the assertion still asks for is the other two: that every global regular
function on the limit comes from a stage, and that a global regular function on a stage which
vanishes on the limit already vanishes at a later stage. -/
theorem isGlobalFunctionsColimit_iff :
    D.IsGlobalFunctionsColimit ↔
      ((∀ t : globalFunctions' B S hS D.limitSpace.obj,
          ∃ (i : I) (s : globalFunctions' B S hS (D.stage i).obj),
            globalFunctionsMap B S hS (D.projection i) s = t) ∧
        ∀ (i : I) (s s' : globalFunctions' B S hS (D.stage i).obj),
          globalFunctionsMap B S hS (D.projection i) s
              = globalFunctionsMap B S hS (D.projection i) s' →
            ∃ (j : I) (h : i ≤ j),
              globalFunctionsMap B S hS (D.transition h) s
                = globalFunctionsMap B S hS (D.transition h) s') := by
  refine ⟨fun h => ⟨h.exists_stage, h.exists_trans_eq⟩, fun ⟨hs, ht⟩ => ?_⟩
  exact ⟨fun _ _ h s => D.ι_trans_globalFunctionsMap h s, hs, ht⟩

/-- **Both clauses of Stacks 07SI for the structure sheaf need only be proved at the stages at
or beyond the chosen index.** If every global regular function on the limit comes from such a
stage, and if two global regular functions on such a stage with the same image at the limit
already agree at a later stage, then the same holds at *every* stage, and
`AlgebraicGeometry.Space.DescentSituation.IsGlobalFunctionsColimit` follows.

This is what removes the need to re-base the chart system. The chart system of Stacks 07SI,
`AlgebraicGeometry.Space.LimitSituation.chartSystem`, is built at the chosen index and is
indexed by the stages at or beyond it, whereas `IsGlobalFunctionsColimit` quantifies over the
whole index set; a re-basing of the situation at an arbitrary stage would reconcile the two,
and none is needed, because the index set is directed.

For the separation clause the argument is: given `s`, `s'` at a stage `i`, choose `k` above
both `i` and the chosen index. The images of `s` and `s'` at `k` have the same image at the
limit, by `AlgebraicGeometry.Space.DescentSituation.ι_trans_globalFunctionsMap`, so the
hypothesis applies at `k` and produces a stage `j ≥ k` at which they agree; and agreeing at
`j` over `k` is agreeing at `j` over `i`, the transition morphisms composing by
`AlgebraicGeometry.Space.DescentSituation.transition_comp`. The surjectivity clause needs
nothing but forgetting the constraint.

**This reduction is not used by the route described in this file's module documentation**, and
a reader should not have to work out whether it is load-bearing: it is not.
`AlgebraicGeometry.Space.exists_stage_map_of_relativelyLimitPreserving` and
`AlgebraicGeometry.Space.exists_stage_eq_of_relativelyLimitPreserving` are already stated at an
arbitrary stage, so the confinement to the stages at or beyond the chosen index that this lemma
removes does not arise there. It is kept because it is independently true, and because it is
what any argument routed through the chart system — which *is* built at the chosen index —
would need. -/
theorem isGlobalFunctionsColimit_of_stages
    (hsurj : ∀ t : globalFunctions' B S hS D.limitSpace.obj,
      ∃ (i : I) (_ : D.base ≤ i) (s : globalFunctions' B S hS (D.stage i).obj),
        globalFunctionsMap B S hS (D.projection i) s = t)
    (hsep : ∀ (i : I), D.base ≤ i →
      ∀ s s' : globalFunctions' B S hS (D.stage i).obj,
        globalFunctionsMap B S hS (D.projection i) s
            = globalFunctionsMap B S hS (D.projection i) s' →
          ∃ (j : I) (h : i ≤ j),
            globalFunctionsMap B S hS (D.transition h) s
              = globalFunctionsMap B S hS (D.transition h) s') :
    D.IsGlobalFunctionsColimit := by
  refine D.isGlobalFunctionsColimit_iff.mpr ⟨fun t => ?_, fun i s s' hss => ?_⟩
  · obtain ⟨i, -, s, hs⟩ := hsurj t
    exact ⟨i, s, hs⟩
  · obtain ⟨k, hik, hbk⟩ := exists_ge_ge i D.base
    have hproj : globalFunctionsMap B S hS (D.projection k)
          (globalFunctionsMap B S hS (D.transition hik) s)
        = globalFunctionsMap B S hS (D.projection k)
          (globalFunctionsMap B S hS (D.transition hik) s') := by
      rw [D.ι_trans_globalFunctionsMap hik s, D.ι_trans_globalFunctionsMap hik s']
      exact hss
    obtain ⟨j, hkj, hj⟩ := hsep k hbk _ _ hproj
    refine ⟨j, hik.trans hkj, ?_⟩
    have hcomp : globalFunctionsMap B S hS (D.transition (hik.trans hkj))
        = (globalFunctionsMap B S hS (D.transition hkj)).comp
            (globalFunctionsMap B S hS (D.transition hik)) := by
      rw [← globalFunctionsMap_comp, D.transition_comp hik hkj (hik.trans hkj)]
    rw [hcomp]
    exact hj

/-- **Stacks 07SI for the structure sheaf is exactly the hypothesis package of the
commutative-algebra core of Stacks 07SQ.** The three clauses `hφ`, `hsurj` and `hzero` taken as
hypotheses by `MvPolynomial.exists_ge_etale_quotient_of_directed`,
`MvPolynomial.exists_ge_isUnit_detJacobian_of_directed` and
`MvPolynomial.exists_ge_surjective_comap_quotient_of_directed` — steps (2), (3) and (4) of the
proof of Stacks 07SQ, proved unconditionally in `StacksFrontier/RingTheory/` for an arbitrary
directed system of rings satisfying them — are supplied by this assertion and by nothing else
that is missing.

This is the precise sense in which Stacks 07SI for the structure sheaf is the whole of what
Stacks 07SQ still lacks. -/
theorem ringPackage_of_isGlobalFunctionsColimit (h : D.IsGlobalFunctionsColimit) :
    (∀ (i j : I) (hij : i ≤ j) (s : globalFunctions' B S hS (D.stage i).obj),
        globalFunctionsMap B S hS (D.projection j)
          (globalFunctionsMap B S hS (D.transition hij) s)
          = globalFunctionsMap B S hS (D.projection i) s) ∧
      (∀ t : globalFunctions' B S hS D.limitSpace.obj,
        ∃ (i : I) (s : globalFunctions' B S hS (D.stage i).obj),
          globalFunctionsMap B S hS (D.projection i) s = t) ∧
      ∀ (i : I) (s : globalFunctions' B S hS (D.stage i).obj),
        globalFunctionsMap B S hS (D.projection i) s = 0 →
          ∃ (j : I) (hij : i ≤ j), globalFunctionsMap B S hS (D.transition hij) s = 0 :=
  ⟨fun _ _ hij s => D.ι_trans_globalFunctionsMap hij s, h.exists_stage,
    Stacks.IsStagesColimit.hzero h⟩

/-! ### Transport to the limit-situation machinery -/

section Transport

variable {B' : BigFppfSite.{u}} {S' : Scheme.{u}} {hS' : B'.Contains S'}
  {hZ' : B'.Contains (⊤_ Scheme.{u})} {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
  (E : DescentSituation B' S' hS' hZ' J)

/-- **The reading of a descent situation in the category of algebraic spaces agrees with the
reading of the limit situation it becomes.** The stages, the limit, the transition morphisms
and the projections defined above are those that
`AlgebraicGeometry.Space.LimitSituation.stage` and its companions give for
`AlgebraicGeometry.Space.DescentSituation.toLimitSituation`.

All four hold by `rfl`, `AlgebraicGeometry.Space.DescentSituation.toLimitSituation` carrying
the inverse system and the cone over unchanged. They are stated because the chart-system
machinery of Stacks 07SI — `AlgebraicGeometry.Space.LimitSituation.chartSystem`,
`.chartLimitBridge`, `.stagesSchemeDiagram`, `.chartEqualizerPresentation` and
`.chartLimitEqualizerPresentation` — lives on `AlgebraicGeometry.Space.LimitSituation`, while
Stacks 07SQ and its consumers are stated on `AlgebraicGeometry.Space.DescentSituation`, so
every application of that machinery to
`AlgebraicGeometry.Space.DescentSituation.IsGlobalFunctionsColimit` crosses this bridge.

The index set must lie in the universe of the site for the passage to exist at all: a limit
situation carries its index set as a field, so
`AlgebraicGeometry.Space.DescentSituation.toLimitSituation` is available only for
`J : Type u`. The statement of `IsGlobalFunctionsColimit` itself imposes no such
restriction. -/
theorem toLimitSituation_stage (i : J) : E.toLimitSituation.stage i = E.stage i := rfl

/-- The limit of the limit situation of a descent situation is its limit. See
`AlgebraicGeometry.Space.DescentSituation.toLimitSituation_stage`. -/
theorem toLimitSituation_limitSpace :
    E.toLimitSituation.limitSpace E.limitAlgebraicSpace = E.limitSpace := rfl

/-- The transition morphisms of the limit situation of a descent situation are its transition
morphisms. See `AlgebraicGeometry.Space.DescentSituation.toLimitSituation_stage`. -/
theorem toLimitSituation_transition {i j : J} (h : i ≤ j) :
    E.toLimitSituation.transition h = E.transition h := rfl

/-- The projections of the limit situation of a descent situation are its projections. See
`AlgebraicGeometry.Space.DescentSituation.toLimitSituation_stage`. -/
theorem toLimitSituation_projection (i : J) :
    E.toLimitSituation.projection E.limitAlgebraicSpace i = E.projection i := rfl

end Transport

/-! ### The assertion, from Stacks 07SI for the structure sheaf -/

section Wiring

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Stacks 07SI for the structure sheaf**, for a descent situation whose index set lies in
the universe of the site: the ring of global regular functions of the limit is the filtered
colimit of the rings of global regular functions of the stages.

This is `AlgebraicGeometry.Space.DescentSituation.isStagesColimit_globalFunctions` of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/StructureSectionsColimit.lean`: `stage`,
`limitSpace`, `transition` and `projection` unfold to its spelling. The hypothesis `hI` is the
size bound of Stacks 07SF. -/
theorem isGlobalFunctionsColimit (hI : #I < B.cutoff.ord.cof) :
    D.IsGlobalFunctionsColimit :=
  D.isStagesColimit_globalFunctions hI

end Wiring

end DescentSituation

end AlgebraicGeometry.Space

end
