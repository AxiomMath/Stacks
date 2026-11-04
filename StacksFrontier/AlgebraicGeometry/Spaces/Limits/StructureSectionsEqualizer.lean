module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleSectionsEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit

/-!
# The equalizer presentation of the global sections of the structure sheaf

Stacks 07SG presents the global sections of the inverse image `ℱᵢ = f_{0i}^*ℱ₀` of a module on
the chosen stage of a limit situation as the equalizer

`Γ(Xᵢ, ℱᵢ) ≃ Ker(ℱᵢ(Uᵢ) → ℱᵢ(Rᵢ))`

over an étale chart `Uᵢ` of the stage and its relation `Rᵢ = Uᵢ ×_{Xᵢ} Uᵢ`.  This file supplies
that presentation **for the structure sheaf**, which is the case Stacks 07SQ consumes: there the
coefficients `ℱ₀` are `𝒪_{X₀}`, so the groups `ℱᵢ(Uᵢ)` are the rings `Γ(Uᵢ, 𝒪_{Uᵢ})` of global
functions on the chart.

Two identifications are involved and both are supplied.  First, the inverse image of the
structure sheaf is the structure sheaf: `f^*𝒪_Y ≅ 𝒪_X` for a morphism of algebraic spaces, which
is `AlgebraicGeometry.Space.modulePullbackUnitIso`, already in the library.  Second, the sections of the
module underlying the structure sheaf over an étale chart are the global functions on the chart's
scheme — the structure sheaf of the small étale site being, by definition, global regular
functions on the charts, this one holds by definition.

## Main definitions

* `AlgebraicGeometry.Space.structureSectionsEquivEqualizer`: **Stacks 03M8 for the structure
  sheaf**, `Γ(X, 𝒪_X) ≃ {a : Γ(U, 𝒪_U) // t^*a = s^*a}`, over a surjective étale scheme chart
  `U` and a relation chart `R` with its two projections.
* `AlgebraicGeometry.Space.LimitSituation.stageModuleUnitIso`: the module `ℱᵢ` of Stacks 07SI at
  structure-sheaf coefficients is the structure sheaf of the stage.
* `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivUnit`: the group `Γ(Xᵢ, ℱᵢ)` of
  Stacks 07SI at structure-sheaf coefficients is `Γ(Xᵢ, 𝒪_{Xᵢ})`.
* `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivEqualizer`: **the stagewise
  equalizer presentation of Stacks 07SG for the structure sheaf**, at a stage presented by a
  surjective étale scheme chart with a relation chart.

## Main results

* `AlgebraicGeometry.Space.structureSectionsEquivEqualizer_apply_val`,
  `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivUnit_val` and
  `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivEqualizer_apply_val`: the value of
  each bijection, namely evaluation at the chart, composed where relevant with the component of
  the structure-sheaf identification.  These are the statements a naturality assertion about the
  presentation has to be proved from; see
  `AlgebraicGeometry.Space.moduleSectionsEquivEqualizer_apply_val` for why the value, and not
  merely the existence, is what the proof of Stacks 07SI needs.

## Implementation notes

*Everything here is for the structure sheaf only.*  Stacks 07SG is asserted for a quasi-coherent
`ℱ₀`, and nothing below is: the equalizer presentation used is Stacks 03M8 for the sheaf of sets
underlying a module, which holds for *every* module, and the extra identification that makes the
groups of the presentation into rings of functions on the charts is available only at the unit
module.  So this is the structure-sheaf case, which is the one Stacks 07SQ needs.

*The two readings of the sections over a chart.*  The sections of the sheaf of sets underlying
the unit module of the structure ring sheaf, over an étale chart `U`, are the carrier of
`Γ(U, 𝒪_U)` by definition: the structure sheaf of the small étale site is
`AlgebraicGeometry.Space.structurePresheaf`, which is `AlgebraicGeometry.Scheme.Γ` of the
underlying scheme, and the unit module of a sheaf of rings has that same sheaf as its underlying
sheaf of sets.  Likewise restriction along a morphism of charts is `Γ` of the morphism of
schemes.  Both identifications are definitional, so
`AlgebraicGeometry.Space.structureSectionsEquivEqualizer` is
`AlgebraicGeometry.Space.moduleSectionsEquivEqualizer` with a different type ascription and no
transport.

### Not proved here

**No `@[stacks]` attribute appears in this file.**  Two things separate what is below from the
hypotheses `e` and `he` of
`isSectionsColimit_of_equalizerPresentation_of_relationChart` in the namespace
`AlgebraicGeometry.Space.LimitSituation`.  The first is supplied in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartSystemEtalePresentation.lean`, the second is
not supplied anywhere.

* **The chart of a stage is given here, not produced from the chart system.**
  `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivEqualizer` takes the surjective
  étale chart `Uᵢ` of the stage and its relation as hypotheses, in the shape Stacks 03M8 asks
  for.  The consumer's charts are instead the values of
  `AlgebraicGeometry.Space.LimitSituation.chartStagesDiagram`, the base changes
  `Uᵢ = Xᵢ ×_{X₀} U₀` of a single affine chart of the chosen stage.  Those base changes *are*
  surjective étale charts of `Xᵢ` when `U₀ ⟶ X₀` is one, and
  `AlgebraicGeometry.Space.LimitSituation.stagesEtaleChart` reads them as such — no isomorphism
  of schemes is involved, the object of the site being the chart system's own, so this file's
  presentation applies to the consumer's charts verbatim.  The result is
  `AlgebraicGeometry.Space.LimitSituation.chartEqualizerPresentation`, which is the hypothesis
  `e` of the consumer.
* **Naturality in the stage is not proved.**  The hypothesis `he` asserts that the presentation
  commutes with the transition maps `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` of Stacks 07SI.  By
  `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivEqualizer_apply_val` this is now a
  statement about *evaluation* at the charts, which is the form in which it can be attacked; but
  it also involves the components of
  `AlgebraicGeometry.Space.LimitSituation.stageModuleUnitIso`, and their compatibility with
  `AlgebraicGeometry.Space.modulePullbackCompIso` — the comparison through which
  `AlgebraicGeometry.Space.LimitSituation.stageTransition` is defined — is not established.
  Nor is there any statement in the library about how
  `AlgebraicGeometry.Space.modulePullbackSections` evaluates at an étale chart of the source,
  which is the other half of what `he` needs; that declaration has no lemmas at all.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SG](https://stacks.math.columbia.edu/tag/07SG)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 03M8 for the structure sheaf -/

/-- **Stacks 03M8 for the structure sheaf.**  Let `X` be an algebraic space, let `U` be an étale
scheme chart of `X` whose structure morphism is surjective on points, and let `R` be an étale
scheme chart with two morphisms `t, s : R ⟶ U` whose comparison images exhibit `R` as the fibre
product `U ×_X U`.  Then the global sections of the structure sheaf of `X` — the sections of the
module underlying it, that is a compatible family of regular functions on the étale charts — are
in bijection with the ring of global functions on the scheme of `U` on which the two projections
agree:

`Γ(X, 𝒪_X) ≃ {a : Γ(U, 𝒪_U) // t^*a = s^*a}`.

This is `AlgebraicGeometry.Space.moduleSectionsEquivEqualizer` at the unit module of the
structure ring sheaf, with no transport: the sections of that module over a chart are the global
functions on the chart's scheme by definition, and so is restriction along a morphism of charts.
See the implementation notes. -/
noncomputable def structureSectionsEquivEqualizer (X : AlgebraicSpaces B S hS)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    (SheafOfModules.unit (structureRingSheaf B S hS X)).sections ≃
      {a : (Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U), ⊤)
              : Type u) //
        ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS X.1).map t)).appTop.hom a
          = ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS X.1).map s)).appTop.hom a} :=
  moduleSectionsEquivEqualizer B S hS _ hU hR

/-- **The bijection of Stacks 03M8 for the structure sheaf is evaluation at the chart.**  A
global regular function on `X` — a compatible family of regular functions on the étale charts —
is carried by `AlgebraicGeometry.Space.structureSectionsEquivEqualizer` to its own member at the
chart `U`.

This is `AlgebraicGeometry.Space.moduleSectionsEquivEqualizer_apply_val` read at the unit
module. -/
theorem structureSectionsEquivEqualizer_apply_val (X : AlgebraicSpaces B S hS)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    (σ : (SheafOfModules.unit (structureRingSheaf B S hS X)).sections) :
    (structureSectionsEquivEqualizer B S hS X hU hR σ).1 = σ.val (op U) :=
  moduleSectionsEquivEqualizer_apply_val B S hS _ hU hR σ

namespace LimitSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)

/-! ### The module and the group of sections of Stacks 07SI at structure-sheaf coefficients -/

/-- **The module `ℱᵢ` of Stacks 07SI at structure-sheaf coefficients is the structure sheaf of
the stage.**  Taking the coefficients `ℱ₀` of Stacks 07SI to be the structure sheaf of the
chosen stage, read as the free module of rank one over itself, the inverse image
`ℱᵢ = f_{0i}^*ℱ₀` to a later stage is the structure sheaf of that stage.

This is `AlgebraicGeometry.Space.modulePullbackUnitIso` at the transition morphism
`f_{0i} : Xᵢ ⟶ X₀`, read in the opposite direction. -/
noncomputable def stageModuleUnitIso (i : A.Stages) :
    SheafOfModules.unit (structureRingSheaf B S hS (A.stage i.1)) ≅
      A.stageModule (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) i :=
  (modulePullbackUnitIso B S hS (A.transition i.2)).symm

/-- **The group `Γ(Xᵢ, ℱᵢ)` of Stacks 07SI at structure-sheaf coefficients is the ring of global
regular functions on the stage.**  This is the identification of modules
`AlgebraicGeometry.Space.LimitSituation.stageModuleUnitIso` read on sections. -/
noncomputable def stageSectionsEquivUnit (i : A.Stages) :
    A.stageSections (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) i ≃
      (SheafOfModules.unit (structureRingSheaf B S hS (A.stage i.1))).sections :=
  ((SheafOfModules.sectionsFunctor
    (structureRingSheaf B S hS (A.stage i.1))).mapIso (stageModuleUnitIso B S hS A i)).toEquiv.symm

/-- **The identification of `Γ(Xᵢ, ℱᵢ)` with `Γ(Xᵢ, 𝒪_{Xᵢ})` is componentwise.**  At each étale
chart of the stage it applies the component there of the inverse of
`AlgebraicGeometry.Space.LimitSituation.stageModuleUnitIso`. -/
theorem stageSectionsEquivUnit_val (i : A.Stages)
    (σ : A.stageSections
      (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) i)
    (V : (SmallEtale B S hS (A.stage i.1).obj)ᵒᵖ) :
    (stageSectionsEquivUnit B S hS A i σ).val V
      = (stageModuleUnitIso B S hS A i).inv.val.app V (σ.val V) :=
  rfl

/-! ### The stagewise equalizer presentation of Stacks 07SG for the structure sheaf -/

/-- **The stagewise equalizer presentation of Stacks 07SG for the structure sheaf.**  Let `Xᵢ` be
a stage of a limit situation, presented by an étale scheme chart `Uᵢ` whose structure morphism is
surjective on points together with a relation chart `Rᵢ` exhibiting `Uᵢ ×_{Xᵢ} Uᵢ` with its two
projections.  Then, with the coefficients `ℱ₀` of Stacks 07SI taken to be the structure sheaf of
the chosen stage, the group `Γ(Xᵢ, ℱᵢ)` of Stacks 07SI is in bijection with the ring of global
functions on the scheme of `Uᵢ` equalized by the two projections:

`Γ(Xᵢ, ℱᵢ) ≃ {a : Γ(Uᵢ, 𝒪) // t^*a = s^*a}`.

This is the identification `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivUnit` of
`Γ(Xᵢ, ℱᵢ)` with `Γ(Xᵢ, 𝒪_{Xᵢ})` followed by
`AlgebraicGeometry.Space.structureSectionsEquivEqualizer`, which is Stacks 03M8 for the
structure sheaf.

It is the stagewise half of the hypothesis `e` of
`isSectionsColimit_of_equalizerPresentation_of_relationChart` in this namespace, for a chart of
the stage given directly rather than produced from the chart system of a chart of the chosen
stage, and with no naturality in the stage; see the "Not proved here" section of this file's
module documentation. -/
noncomputable def stageSectionsEquivEqualizer (i : A.Stages)
    {U R : SmallEtale B S hS (A.stage i.1).obj}
    (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS (A.stage i.1)).map t)
      ((comparisonFunctor B S hS (A.stage i.1)).map s)
      ((SpacesEtale.isTerminal_idObj B S hS (A.stage i.1)).from
        ((comparisonFunctor B S hS (A.stage i.1)).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS (A.stage i.1)).from
        ((comparisonFunctor B S hS (A.stage i.1)).obj U))) :
    A.stageSections (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) i ≃
      {a : (Γ((BigFppfOver.toScheme B S hS).obj
                ((SmallEtale.toOver B S hS (A.stage i.1).obj).obj U), ⊤) : Type u) //
        ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS (A.stage i.1).obj).map t)).appTop.hom a
          = ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS (A.stage i.1).obj).map s)).appTop.hom a} :=
  (stageSectionsEquivUnit B S hS A i).trans
    (structureSectionsEquivEqualizer B S hS (A.stage i.1) hU hR)

/-- **The value of the stagewise equalizer presentation.**  A section of `Γ(Xᵢ, ℱᵢ)` is carried
to its own member at the chart `Uᵢ`, read through the component at `Uᵢ` of the identification of
`ℱᵢ` with the structure sheaf of the stage.

This is the form in which the naturality hypotheses `he` and `heT` of
`isSectionsColimit_of_equalizerPresentation_of_relationChart` have to be proved; the first factor
is natural in the stage for a formal reason, being evaluation of a compatible family, and what
is left is the compatibility of the components of
`AlgebraicGeometry.Space.LimitSituation.stageModuleUnitIso` with the transition maps. -/
theorem stageSectionsEquivEqualizer_apply_val (i : A.Stages)
    {U R : SmallEtale B S hS (A.stage i.1).obj}
    (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS (A.stage i.1)).map t)
      ((comparisonFunctor B S hS (A.stage i.1)).map s)
      ((SpacesEtale.isTerminal_idObj B S hS (A.stage i.1)).from
        ((comparisonFunctor B S hS (A.stage i.1)).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS (A.stage i.1)).from
        ((comparisonFunctor B S hS (A.stage i.1)).obj U)))
    (σ : A.stageSections
      (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) i) :
    (stageSectionsEquivEqualizer B S hS A i hU hR σ).1
      = (stageModuleUnitIso B S hS A i).inv.val.app (op U) (σ.val (op U)) :=
  structureSectionsEquivEqualizer_apply_val B S hS (A.stage i.1) hU hR _

end LimitSituation

end AlgebraicGeometry.Space

end
