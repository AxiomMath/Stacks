module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartLiftRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection

/-!
# The morphism of presented étale charts of the subspace attached to a restriction

A `AlgebraicGeometry.Space.ChartLiftPresentation` of a lifting problem over an étale chart `U'`
of `X'` presents an étale chart of the closed subspace `Z ⊆ X'`, namely the closed subscheme of
the chart thickening with its chart morphism,
`AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChart`.  Restricting the presentation to a
smaller chart `V' ⟶ U'` — `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction` — therefore
produces a second étale chart of `Z`, and this file supplies the morphism between them.

That morphism is the one the cartesian square of the original presentation produces,
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap`: it commutes with the two chart
morphisms into `Z`, which is exactly what a morphism of the small étale site of `Z` is.  It is
what indexes the restriction maps of the acting sheaf
`AlgebraicGeometry.Space.liftActionSheaf`, which lives on the small étale site of `Z` while the
sheaf of lifts lives on that of `X'`.

## Main definitions

* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subEtaleChartMap`: **the morphism of
  presented étale charts of `Z`.**
* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`:
  the naturality in the chart of the identification of the acting sheaf's chart sections with the
  acting group of a chart presentation — **the one thing the naturality of the action is still
  missing**, stated here rather than left to prose, with its decomposition into four
  compatibilities and a citation for each.

## Main results

* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.toOver_map_subEtaleChartMap`: its
  underlying morphism of the big fppf site is
  `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap`.
* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction` ·
  `map_translateActionSection_actionSectionEquiv`:
  **the naturality of the action of the acting sheaf on the sheaf of lifts**, granted that
  identification's naturality.  This is the `naturality` field of
  `PseudoTorsor` at a chart presentation; everything in it that does not mention
  the identification is unconditional
  (`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.map_translateActionSection`).

The factorization of the structure morphism of the smaller presented chart through the larger one
needs no statement of its own: it is
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace` at this morphism of charts.

## Implementation notes

`AlgebraicGeometry.Space.presentedSubspaceChart` is an `abbrev`, so the two presented charts are
`CostructuredArrow.mk` of the two chart morphisms on the nose and the morphism between them is
`CategoryTheory.CostructuredArrow.homMk` of
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap`, wrapped by
`CategoryTheory.ObjectProperty.homMk` for the full subcategory of étale charts.  No étaleness has
to be rechecked: both objects are étale charts already.

No `@[stacks]` attribute is claimed.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

namespace ChartLiftPresentation.Restriction

variable {C S hS} {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
  {U' : SmallEtale C S hS X'.1} {P : ChartLiftPresentation C S hS p q a.hom U'}
  {V' : SmallEtale C S hS X'.1} (R : Restriction P V')

/-- **The morphism of the two presented étale charts of the closed subspace.**  The restricted
presentation presents the étale chart `X ×_{X'} V'` of `Z` and the original one presents
`X ×_{X'} U'`; the morphism between them is
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap`, whose triangle over `Z`
commutes by
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap_comp_subChart`. -/
def subEtaleChartMap :
    (R.presentation.subEtaleChart (Z := Z) (a := a)) ⟶ P.subEtaleChart :=
  ObjectProperty.homMk (CostructuredArrow.homMk R.subMap R.subMap_comp_subChart)

/-- The morphism of the big fppf site underlying the morphism of presented charts is
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap`. -/
theorem toOver_map_subEtaleChartMap :
    (SmallEtale.toOver C S hS Z.1.toFunctor).map (R.subEtaleChartMap (Z := Z) (a := a)) =
      R.subMap :=
  rfl

/-! ### Naturality of the identification of the acting group in the chart -/

/-- **The naturality in the chart of the identification of the acting sheaf's chart sections with
the acting group of a chart presentation.**  Restricting a section of
`AlgebraicGeometry.Space.liftActionSheaf` to the chart of `Z` presented by a restriction of `P`
and then reading it as an acting section of that restricted presentation is the same as reading
it at `P` and restricting the acting section,
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.restrictActionSection`.

This is stated as a predicate because it is **not proved here**, and it is stated rather than
left to prose because the statement is the specification of what is owed.  It decomposes into
four compatibilities, of which exactly one is proved in the tree:

* the Zariski side — the identification of morphisms of associated modules on an affine with
  linear maps of global sections commutes with base change — is
  `AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap_pullbackSection`;
* the small-étale side — naturality of
  `AlgebraicGeometry.Space.smallEtaleInternalHomChartPullbackHomEquiv` in the chart, which is
  [Stacks Project, Tag 04M0] and Equation [Stacks Project, Tag 03LW] read at two charts.  The
  sections-level input is proved:
  `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_map_val_eq_homRestr` identifies the
  restriction map of the internal Hom with relocalization of the morphism on the slice, and
  `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_map_val_app_apply` is its component
  form, by `rfl`; these are `Stacks.PresheafOfModules.homRestr_app_apply` read at that
  restriction map.  The naturality itself is absent.  It is **not** to be stated against
  `AlgebraicGeometry.Space.chartSmallEtaleRestrictionPullbackIso` (Equation
  [Stacks Project, Tag 03LY]): that comparison is built
  on `AlgebraicGeometry.Space.chartModuleRestrictionComp`, hence on
  `AlgebraicGeometry.Space.modulePullbackCompIso`, the *adjoint* inverse image of
  [Stacks Project, Tag 03LU], while the equivalence it would be paired with is a reindexing, so
  relating the two is exactly
  `AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction` — which
  that structure's own docstring records this development as not having, and which the tree
  carries only as a hypothesis.  The reachable comparison is the strict one of Equation
  [Stacks Project, Tag 03LW]: iterated étale restriction
  `AlgebraicGeometry.Space.etaleModulePullbackComp`, transported along
  `AlgebraicGeometry.Space.chartMap_comp_chartToSpace`;
* the compatibility in the chart of the source comparison
  `AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso`, the composite of
  [Stacks Project, Tag 04CU] and [Stacks Project, Tag 04CS].  Absent, but the uniqueness
  principle for it exists: [Stacks Project, Tag 04CX],
  `AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`, together with the chart pasting
  `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_chartPasting`;
* the compatibility in the chart of the target comparison
  `AlgebraicGeometry.Space.ChartLiftPresentation.chartTargetIso`, the composite of
  [Stacks Project, Tag 03LU], [Stacks Project, Tag 04CO] and [Stacks Project, Tag 04G2] (1).
  Absent, and the one place where saying what is missing takes a sentence rather than a word:

  - the comparison itself is now identified with the general presented-chart comparison, by
    `AlgebraicGeometry.Space.ChartLiftPresentation.chartTargetIso_eq`, so every statement about
    the general one transfers to the presentation at the isomorphism;
  - its [Stacks Project, Tag 04CO] factor has a composition law in the étale source,
    `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_comp`, and the
    restriction data that law has to be read at is proved in
    `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartAssociatedModuleRestriction` —
    in particular `AlgebraicGeometry.Space.isPullback_presentedRangeMap`, that the two
    base-changed subspaces of the two chart spaces form a cartesian square;
  - its [Stacks Project, Tag 04G2] (1) factor
    `AlgebraicGeometry.Space.conormalModuleClosedSubspaceRangeIso` **does** have a derived lemma,
    `AlgebraicGeometry.Space.conormalModuleRepresentedIso_hom_comp`, and the naturality of that
    factor in the closed immersion is proved unconditionally at the respelling
    `AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso`, as
    `AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso_of_comp_eq`;
    part (2) at immersion generality is proved unconditionally as
    `AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso_naturality`.

  What blocks the assembly is therefore neither factor's naturality but the step between the two
  spellings of the spaces-side map: the proved naturality's left-hand column is
  `AlgebraicGeometry.Space.kernelIdealSquareMap`, while `chartTargetIso`'s
  [Stacks Project, Tag 04CO] factor is `AlgebraicGeometry.Space.conormalMap`, built from
  `AlgebraicGeometry.Space.idealSheafMap`.  **That degree-one agreement is proved**, as
  `AlgebraicGeometry.Space.kernelIdealSquareMap_one_eq_idealSheafMap` of
  `StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMapDegreeOne.lean`: the two maps are
  pinned by the same characterising property — their composite with the inclusion into the
  structure sheaf, `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` and
  `AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι`, whose right-hand sides are the same
  term — that inclusion is a monomorphism, and the two sheaves of ideals are equal by
  `AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf` together with
  `AlgebraicGeometry.Space.kernelIdealSheafZPow_one`.

  The crossing that equality forces is analysed there too: the equality holds in
  `SheafOfModules.Submodule` of
  `AlgebraicGeometry.Space.structureRingSheaf` while the inverse image is a functor out of
  `AlgebraicGeometry.Space.Modules`, and `rw` with
  `AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι` against the cancelled goal does fail,
  reporting that the target is not type-correct at the `implicit` transparency level.  What
  discharges it is not a `rw` at all: the assembly is an instantiation of
  `CategoryTheory.eq_eqToHom_comp_comp_eqToHom_of_mono`, stated at variables in an arbitrary
  category, with the two equalities carried by
  `Stacks.SheafOfModules.Submodule.eqToHom_comp_ι` and `CategoryTheory.eqToHom_map`.

  So what still blocks the assembly here is only the assembly itself, not this step. -/
def IsActionSectionRestrictionNatural
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) : Prop :=
  ∀ g : (liftActionSheaf C S hS Z q a).val.obj (op P.subEtaleChart),
    actionSectionEquiv C S hS R.presentation hw hv
        ((liftActionSheaf C S hS Z q a).val.map (R.subEtaleChartMap (Z := Z) (a := a)).op g) =
      R.restrictActionSection (actionSectionEquiv C S hS P hw hv g)

/-- **The naturality of the action of the acting sheaf on the sheaf of lifts, at a chart
presentation and a restriction of it**, granted the naturality in the chart of the identification
of the acting group.  This is the `naturality` field that
`PseudoTorsor` asks of an action of sheaves, read at the chartwise action of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction`: restricting the translate
of the presented lift by a section of the acting sheaf is translating the restricted presented
lift by the restricted section.

The part of it that does not depend on the identification is unconditional — it is
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.map_translateActionSection` — so the
one thing this needs beyond what is proved is
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`. -/
theorem map_translateActionSection_actionSectionEquiv
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (hnat : R.IsActionSectionRestrictionNatural (Z := Z) (a := a) hw hv)
    (g : (liftActionSheaf C S hS Z q a).val.obj (op P.subEtaleChart)) :
    (liftsSubfunctor C S hS p q a.hom).toFunctor.map R.chartMap.op
        (P.translateActionSection (actionSectionEquiv C S hS P hw hv g)) =
      R.presentation.translateActionSection
        (actionSectionEquiv C S hS R.presentation hw hv
          ((liftActionSheaf C S hS Z q a).val.map
            (R.subEtaleChartMap (Z := Z) (a := a)).op g)) := by
  rw [hnat g]
  exact R.map_translateActionSection _

end ChartLiftPresentation.Restriction

end AlgebraicGeometry.Space

end
