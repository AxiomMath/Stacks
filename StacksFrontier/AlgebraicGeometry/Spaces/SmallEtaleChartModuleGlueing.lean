module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# Chartwise glueing data for modules on an algebraic space

Stacks 03LY describes a sheaf of `𝒪_X`-modules on the small étale site of an algebraic space `X`
by the following data: a sheaf `F_U` of `𝒪_U`-modules on the small étale site of every étale
scheme chart `U` of `X`, and an isomorphism `c_f : f^*F_U ≅ F_V` for every morphism `f : V ⟶ U`
of charts, where `f^*` is the pullback of modules of Stacks 03LU along the represented morphism
of algebraic spaces, subject to the cocycle condition `c_g ∘ g^*c_f = c_{g ≫ f}`.  This file
supplies those data: the chartwise pullbacks, the canonical comparisons through which the cocycle
condition is stated, and the category they assemble into.

Every morphism of the small étale site of `X` represents an étale morphism of algebraic spaces
(`AlgebraicGeometry.Space.isEtale_chartMap`), so by Stacks 03LV the chartwise pullbacks are the
exact, tensor-free ones; they are nonetheless taken here to be
`AlgebraicGeometry.Space.modulePullback`, the pullback of Stacks 03LU itself, which is the
functor the source's `f_{small}^*` names and the one whose composition comparison the cocycle
condition is stated through.

## Main definitions

* `AlgebraicGeometry.Space.chartModuleRestriction` is the restriction of an `𝒪_X`-module to an
  étale scheme chart, and `AlgebraicGeometry.Space.chartModuleInverseImage` the chartwise
  pullback of modules along a morphism of charts.
* `AlgebraicGeometry.Space.ChartModuleFamily`,
  `AlgebraicGeometry.Space.ChartModuleTransitions` and
  `AlgebraicGeometry.Space.IsChartModuleCocycle` are the two data and the condition of
  Stacks 03LY, and `AlgebraicGeometry.Space.ChartModuleGlueingData` the category they form.
* `AlgebraicGeometry.Space.ChartModuleGlueingData.Hom` is a morphism of chartwise glueing data.

## Main results

* `AlgebraicGeometry.Space.chartModuleInverseImageComp`: the canonical comparison identifying
  successive chartwise pullbacks of modules with the pullback along the composite morphism of
  charts.
* `AlgebraicGeometry.Space.chartModuleRestrictionComp`: restriction of a module to a chart
  followed by the chartwise pullback along a morphism of charts is restriction to the smaller
  chart.
* `AlgebraicGeometry.Space.ChartModuleGlueingData.isIso_of_isIso_app`: a morphism of chartwise
  glueing data is invertible as soon as it is invertible on every chart.
* `AlgebraicGeometry.Space.chartModuleRestrictionComp_cocycle`,
  `AlgebraicGeometry.Space.chartModuleRestrictionComp_cocycle_app` and
  `AlgebraicGeometry.Space.isChartModuleCocycle_chartModuleRestrictionTransitionFamily`: **the
  cocycle condition of Stacks 03LY holds for the family of restrictions of an `𝒪_X`-module to
  the charts**, with `AlgebraicGeometry.Space.chartModuleRestrictionComp` as its transitions — as
  an equality of isomorphisms of functors, at a single module, and as a term of the predicate
  `AlgebraicGeometry.Space.IsChartModuleCocycle`.
* `AlgebraicGeometry.Space.chartModuleRestrictionComp_naturality` and
  `AlgebraicGeometry.Space.chartModuleRestrictionTransitions_naturality`: the transitions of that
  family are natural in the module.
* `AlgebraicGeometry.Space.canonicalChartModuleGlueingData` and
  `AlgebraicGeometry.Space.chartModuleGlueingFunctor`: **the chartwise glueing datum of an
  `𝒪_X`-module and the canonical chartwise description**, the functor whose being an equivalence
  is Stacks 03LY.

## Implementation notes

Both comparisons are the composition comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU, transported along an *equality*
of morphisms of algebraic spaces — `AlgebraicGeometry.Space.chartMap_comp` and
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace` — so the `CategoryTheory.eqToIso` in each
proof is unavoidable: the two composites of chart morphisms are equal, not merely isomorphic,
while the composition comparison is stated about the composite morphism.

The cocycle condition is a named predicate, `AlgebraicGeometry.Space.IsChartModuleCocycle`,
rather than an equation written out in the field of the structure.  Written out, it is accepted
by the elaborator but the kernel does not finish checking the resulting inductive declaration,
because the equation mentions the comparison at three charts at once.  Naming the condition keeps
the equation out of the inductive declaration, where it is checked once as the body of a
definition instead of repeatedly in the generated constructor and projections.

### Why the comparison is applied by a definition of its own

What makes a cocycle condition *indexed by objects* reachable at these concrete comparisons is
`AlgebraicGeometry.Space.chartModuleInverseImageCompApp`, through which
`AlgebraicGeometry.Space.IsChartModuleCocycle` applies
`AlgebraicGeometry.Space.chartModuleInverseImageComp` to `F_U`.  It is the same morphism as the
component of that comparison; what it changes is the spelling of its source, from the value
`(f^* ⋙ g^*).obj F_U` of a composite functor to the iterated pullback `g^*(f^*F_U)`.

The reason this matters, and the reason an earlier pass recorded the obstruction here as
unreachable, is a reduction that does not terminate.  Deciding
`(f^* ⋙ g^*).obj M = g^*(f^*M)` is cheap when `M` is given: `CategoryTheory.Functor.comp` is
unfolded once and the two sides match.  It is *not* cheap when the two sides are additionally
asked to reconcile two spellings of `M` — and that is exactly the situation at a glueing datum,
whose `sheaf` field is a function, so that `sheaf U` is a redex and not the term the cocycle was
proved about.  Then the reduction cannot match early, and `AlgebraicGeometry.Space.modulePullback`
is unfolded without bound.  Nothing about `AlgebraicGeometry.Space.chartSpace` or the comparison
equivalence of Stacks 03G1 is involved: every *individual* object-level and morphism-level
identity between the two spellings, including `HEq` of the comparison components, is checked by
`rfl` in a fraction of a second.  It is only their reconciliation inside one unification problem
that diverges.

So the passage from the functor-level coherence to the glueing datum is made in three steps, each
of which leaves nothing to reconcile:

* `CategoryTheory.Functor.cocycle_app_of_iso_of_eq` turns the functor-level coherence
  `AlgebraicGeometry.Space.chartModuleRestrictionComp_cocycle` into the identity at one module,
  with all four morphisms supplied positionally between the uncomposed objects.  On the variable
  functors of that lemma the composed and uncomposed spellings agree by one projection;
* `AlgebraicGeometry.Space.chartModuleRestrictionTransitions_cocycle` is that identity at the
  restriction family, in the spelling `(f^*(F|_U), F|_V, F|_W)`;
* `CategoryTheory.Functor.map_comp_eq_comp_of_heq` transports it to the spelling the predicate's
  instantiation produces, one object and one morphism at a time.

For the same reason `AlgebraicGeometry.Space.chartModuleRestrictionTransitions` lists the four
components of `AlgebraicGeometry.Space.chartModuleRestrictionComp` at `F` one by one instead of
handing the comparison over whole: its `hom` is then reached by a single projection rather than by
reducing `CategoryTheory.Iso.app` of a composite comparison.  And
`AlgebraicGeometry.Space.canonicalChartModuleGlueingData` is assembled from three named
declarations whose types are *syntactically* the three fields of the structure, so that the kernel
has no defeq to decide at the constructor at all.

## Where the equivalence of Stacks 03LY is proved

Not proved here is the equivalence of Stacks 03LY itself, between `𝒪_X`-modules and
`AlgebraicGeometry.Space.ChartModuleGlueingData`; what is proved here is the functor
`AlgebraicGeometry.Space.chartModuleGlueingFunctor` between them.  That functor *is* an
equivalence, and that is
`AlgebraicGeometry.Space.chartModuleGlueingEquivalence` together with
`AlgebraicGeometry.Space.chartModuleGlueingFunctor_isEquivalence`, in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartModuleGlueingEquivalence.lean`.  The rest of
this section describes the route taken there, and is a record of how the pieces fit rather than a
list of what is owed.

The remaining content is that this functor is fully faithful and essentially surjective, which the
source deduces from Stacks 03LV and Stacks 03LS.  The transport that gives it is: compose
`CategoryTheory.SiteGlueing.canonicalModuleEquivalence` — the glueing equivalence for sheaves of
modules on an arbitrary site, in
`StacksFrontier/CategoryTheory/Sites/Glueing/AbsoluteGlueingAnySite.lean` — with an equivalence
between the slice-indexed glueing data of that file and the chart-indexed data of this one.  Both
are indexed by the objects of the small étale site of `X`; they differ only in the fibre over a
chart `U`, which is `SheafOfModules` over `(AlgebraicGeometry.Space.structureRingSheaf X).over U`
on one side and `AlgebraicGeometry.Space.Modules` at `AlgebraicGeometry.Space.chartSpace` on the
other, and in the pullback along a morphism of charts.  The object-by-object dictionary between
the two is `StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleSliceComparison.lean`:
`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso` and
`AlgebraicGeometry.Space.chartModuleInverseImageSliceIso`.

The dictionary is *fibrewise an equivalence*:
`AlgebraicGeometry.Space.isEquivalence_chartModuleSliceReindex`, in the same file, which is
`SheafOfModules.pushforwardPushforwardEquivalence` at the comparison equivalence of Stacks 04M0.

What the transport needs next, and what is not supplied here, is the *coherence* of that
dictionary with the composition comparisons: that
`AlgebraicGeometry.Space.chartModuleInverseImageSliceIso` carries
`AlgebraicGeometry.Space.chartModuleInverseImageComp` to
`CategoryTheory.SiteGlueing.overMapComp`, and that
`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso` carries
`AlgebraicGeometry.Space.chartModuleRestrictionComp` to the slice-side comparison.  These are the
two squares a functor between the two categories of glueing data must have in order to carry one
cocycle condition to the other, and they are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleSliceCoherence.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionSliceCoherence.lean`.

Both squares reduce to one statement, and it is the module analogue of the *bridge* that the
corresponding development for sheaves of sets needs.  The slice side of each square is
`SheafOfModules.pushforwardComp`, which on sections is a restriction map and nothing else —
`CategoryTheory.SiteGlueing.overMapComp_hom_app_val_app` is `rfl`.  The chart side is not: both
`AlgebraicGeometry.Space.chartModuleInverseImageComp` and
`AlgebraicGeometry.Space.chartModuleRestrictionComp` are
`AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU, an adjoint mate, while the
dictionary passes to sections through
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback` of Stacks Equation 03LW, also an
adjoint mate.  So what the two squares rest on is their compatibility: that for étale morphisms
`k` and `l` of algebraic spaces, the comparison of Stacks 03LW at `k`, then at `l`, agrees with
the comparison at `k ≫ l` through `AlgebraicGeometry.Space.modulePullbackCompIso` on one side and
through the *strict* composition of the étale restrictions on the other —

`modulePullbackCompIso k l ≪≫ (03LW at k ≫ l)`
  `= whiskerRight (03LW at l) _ ≪≫ whiskerLeft _ (03LW at k)`

modulo the identification of the two composite étale restrictions, which is an equality of
functors because `AlgebraicGeometry.Space.smallEtalePostcomp` composes strictly.

That is `AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompIsoEtaleRestriction.lean`, whose
one hypothesis is that the two adjunctions of étale restriction along the composite — the one
assembled from the two factors through
`AlgebraicGeometry.Space.modulePushforwardCompIso`, which is
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction`, and
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` at the composite — have the same unit.
That hypothesis is proved for any composable pair of étale morphisms, with no representability,
by `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit` in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleUnitCompJoin.lean`.  The route through the chart
projection, whose ingredients are in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompUnitEq.lean`, reached it only at
a representable morphism: both units are morphisms into the direct image along the composite,
hence determined by their chart projections, and both chart projections are restriction of
sections along the
cartesian projection.  Representability is no restriction for Stacks 03LY, where the squares are
needed only at `AlgebraicGeometry.Space.chartMap` and
`AlgebraicGeometry.Space.chartToSpace`, both relatively representable
(`AlgebraicGeometry.Space.relativelyRepresentable_chartMap`,
`AlgebraicGeometry.Space.relativelyRepresentable_chartToSpace`); so
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleSliceDictionarySquares.lean` discharges the
hypothesis and states both squares unconditionally.

On that the four-step assembly that the corresponding statement for sheaves of sets performs in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartGlueingEquivalence.lean` goes through for
modules, in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartModuleGlueingEquivalence.lean`: the chartwise
reading of a slice-indexed datum, its faithfulness and fullness from the fibrewise equivalence
`AlgebraicGeometry.Space.isEquivalence_chartModuleSliceReindex`, its essential surjectivity from
a quasi-inverse datum, and the identification of
`AlgebraicGeometry.Space.chartModuleGlueingFunctor` with
`CategoryTheory.SiteGlueing.canonicalModuleFunctor` read chartwise.

## References

* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03LS](https://stacks.math.columbia.edu/tag/03LS)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The chartwise pullbacks of modules -/

/-- **Stacks 03LY.** The pullback of `𝒪`-modules of Stacks 03LU along the morphism of algebraic
spaces represented by a morphism of étale scheme charts of `X`.  This is the functor
`f_{small}^*` in which the source states the transition isomorphisms. -/
@[stacks 03LY "the chartwise pullback of modules"]
noncomputable def chartModuleInverseImage {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2 ⥤
      Modules.{u, u} B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2 :=
  modulePullback B S hS (chartMap B S hS X f)

/-- **Stacks 03LY.** The canonical comparison of successive chartwise pullbacks of modules with
the pullback along the composite morphism of charts: it is the composition comparison of
Stacks 03LU, read through the equality `chartMap g ≫ chartMap f = chartMap (g ≫ f)`.

It is this comparison that makes the cocycle condition
`AlgebraicGeometry.Space.IsChartModuleCocycle` a statement rather than a type error. -/
@[stacks 03LY "canonical comparison of chartwise pullbacks"]
noncomputable def chartModuleInverseImageComp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    chartModuleInverseImage B S hS X f ⋙ chartModuleInverseImage B S hS X g ≅
      chartModuleInverseImage B S hS X (g ≫ f) :=
  modulePullbackCompIso B S hS (chartMap B S hS X g) (chartMap B S hS X f) ≪≫
    eqToIso (congrArg (fun k ↦ modulePullback B S hS k) (chartMap_comp B S hS X f g))

/-- Restriction of an `𝒪_X`-module to an étale scheme chart, by pullback of modules along the
structure morphism of the chart. -/
noncomputable def chartModuleRestriction (U : SmallEtale B S hS X.1) :
    Modules.{u, u} B S hS X.1 X.2 ⥤
      Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2 :=
  modulePullback B S hS (chartToSpace B S hS X U)

/-- **Stacks 03LY.** Restriction of a module to a chart commutes canonically with further
chartwise pullback along a morphism of charts: the composite of the structure morphism of the
larger chart with the morphism of charts is the structure morphism of the smaller chart. -/
@[stacks 03LY "compatibility of chart restriction with the chartwise pullback"]
noncomputable def chartModuleRestrictionComp {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartModuleRestriction B S hS X U ⋙ chartModuleInverseImage B S hS X f ≅
      chartModuleRestriction B S hS X V :=
  modulePullbackCompIso B S hS (chartMap B S hS X f) (chartToSpace B S hS X U) ≪≫
    eqToIso (congrArg (fun k ↦ modulePullback B S hS k)
      (chartMap_comp_chartToSpace B S hS X f))

/-- The comparison `AlgebraicGeometry.Space.chartModuleInverseImageComp` at a single module on
the chart `U`, named so that its type is written out: a morphism *from the iterated pullback*
`g^*(f^*M)` to the pullback `(g ≫ f)^*M` along the composite, rather than from the value of the
composite functor `f^* ⋙ g^*` at `M`.

The two are the same morphism; the point is which spelling of its source is stored.  Written as
the component of the comparison of composite functors, the source is `(f^* ⋙ g^*).obj M`, and
reconciling that with `g^*(f^*M)` means reducing `AlgebraicGeometry.Space.modulePullback` twice —
which terminates when `M` is given, and does not when `M` is any term that must itself be
reduced to be recognised, such as the value of a chartwise family at `U`.  Here the
reconciliation happens once, at a variable `M`, and never again. -/
noncomputable def chartModuleInverseImageCompApp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V)
    (M : Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2) :
    (chartModuleInverseImage B S hS X g).obj ((chartModuleInverseImage B S hS X f).obj M) ⟶
      (chartModuleInverseImage B S hS X (g ≫ f)).obj M :=
  (chartModuleInverseImageComp B S hS X f g).hom.app M

/-- `AlgebraicGeometry.Space.chartModuleInverseImageCompApp` is the component of
`AlgebraicGeometry.Space.chartModuleInverseImageComp`. -/
theorem chartModuleInverseImageCompApp_eq {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V)
    (M : Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2) :
    chartModuleInverseImageCompApp B S hS X f g M =
      (chartModuleInverseImageComp B S hS X f g).hom.app M := rfl

/-! ### Chartwise glueing data -/

/-- **Datum (1) of Stacks 03LY**: a sheaf `F_U` of `𝒪_U`-modules on the small étale site of
every étale scheme chart `U` of the algebraic space `X`. -/
abbrev ChartModuleFamily := ∀ U : SmallEtale B S hS X.1,
  Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2

/-- **Datum (2) of Stacks 03LY**: for a chartwise family of modules, an isomorphism
`c_f : f^*F_U ≅ F_V` for every morphism `f : V ⟶ U` of étale scheme charts of `X`, where `f^*`
is the chartwise pullback of modules. -/
abbrev ChartModuleTransitions (sheaf : ChartModuleFamily B S hS X) :=
  ∀ {V U : SmallEtale B S hS X.1} (f : V ⟶ U),
    (chartModuleInverseImage B S hS X f).obj (sheaf U) ≅ sheaf V

/-- **The cocycle condition of Stacks 03LY**: for composable morphisms `g : W ⟶ V` and
`f : V ⟶ U` of étale scheme charts of `X`, the transition `c_g` after the chartwise pullback
`g^*c_f` of the transition `c_f` is the transition `c_{g ≫ f}`, read through the canonical
comparison `AlgebraicGeometry.Space.chartModuleInverseImageComp` of the iterated pullback with
the pullback along the composite, taken at `F_U` by
`AlgebraicGeometry.Space.chartModuleInverseImageCompApp`. -/
def IsChartModuleCocycle (sheaf : ChartModuleFamily B S hS X)
    (transition : ChartModuleTransitions B S hS X sheaf) : Prop :=
  ∀ {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V),
    (chartModuleInverseImage B S hS X g).map (transition f).hom ≫ (transition g).hom =
      chartModuleInverseImageCompApp B S hS X f g (sheaf U) ≫ (transition (g ≫ f)).hom

/-- **The data of Stacks 03LY**: a sheaf of `𝒪_U`-modules on the small étale site of every étale
scheme chart `U` of `X`, transition isomorphisms along the chartwise pullbacks of modules, and
the cocycle condition relating them. -/
@[stacks 03LY "the data (1), (2) and the cocycle condition"]
structure ChartModuleGlueingData where
  /-- the modules on the small étale sites of the charts, datum (1) -/
  sheaf : ChartModuleFamily B S hS X
  /-- the transition isomorphisms `f^*F_U ≅ F_V`, datum (2) -/
  transition : ChartModuleTransitions B S hS X sheaf
  /-- the cocycle condition `c_g ∘ g^*c_f = c_{g ≫ f}` -/
  transition_comp : IsChartModuleCocycle B S hS X sheaf transition

namespace ChartModuleGlueingData

/-- A morphism of chartwise glueing data for modules: a family of morphisms of the chart modules
commuting with the transition isomorphisms. -/
@[ext]
structure Hom (D E : ChartModuleGlueingData B S hS X) where
  /-- the morphism `F_U ⟶ G_U` of modules on the small étale site of the chart `U` -/
  app (U : SmallEtale B S hS X.1) : D.sheaf U ⟶ E.sheaf U
  /-- compatibility with the transition isomorphisms -/
  w {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartModuleInverseImage B S hS X f).map (app U) ≫ (E.transition f).hom =
      (D.transition f).hom ≫ app V

attribute [reassoc] Hom.w

/-- Chartwise glueing data for modules form a category, a morphism being a family of morphisms
of the chart modules compatible with the transition isomorphisms. -/
noncomputable instance : Category (ChartModuleGlueingData B S hS X) where
  Hom := Hom B S hS X
  id D := { app := fun _ ↦ 𝟙 _, w := fun _ ↦ by simp }
  comp α β :=
    { app := fun U ↦ α.app U ≫ β.app U
      w := fun f ↦ by
        rw [Functor.map_comp, Category.assoc, Hom.w, ← Category.assoc, Hom.w, Category.assoc] }

/-- The identity morphism of a chartwise glueing datum is the identity on every chart. -/
@[simp] lemma id_app (D : ChartModuleGlueingData B S hS X) (U : SmallEtale B S hS X.1) :
    Hom.app (𝟙 D) U = 𝟙 (D.sheaf U) := rfl

/-- Morphisms of chartwise glueing data compose chart by chart. -/
@[simp] lemma comp_app {D E F : ChartModuleGlueingData B S hS X} (α : D ⟶ E) (β : E ⟶ F)
    (U : SmallEtale B S hS X.1) :
    Hom.app (α ≫ β) U = Hom.app α U ≫ Hom.app β U := rfl

/-- Two morphisms of chartwise glueing data that agree on every chart are equal. -/
@[ext] lemma hom_ext {D E : ChartModuleGlueingData B S hS X} {α β : D ⟶ E}
    (h : ∀ U, Hom.app α U = Hom.app β U) : α = β :=
  Hom.ext (funext h)

/-- A morphism of chartwise glueing data all of whose components are isomorphisms is an
isomorphism. -/
lemma isIso_of_isIso_app {D E : ChartModuleGlueingData B S hS X} (α : D ⟶ E)
    (h : ∀ U, IsIso (Hom.app α U)) : IsIso α := by
  refine ⟨⟨{ app := fun U ↦ inv (Hom.app α U), w := fun {V U} f ↦ ?_ }, ?_, ?_⟩⟩
  · have hα := Hom.w α f
    rw [IsIso.eq_comp_inv, Category.assoc, ← hα, ← Category.assoc, ← Functor.map_comp,
      IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  · exact hom_ext B S hS X fun U ↦ IsIso.hom_inv_id (Hom.app α U)
  · exact hom_ext B S hS X fun U ↦ IsIso.inv_hom_id (Hom.app α U)

end ChartModuleGlueingData

/-! ### The cocycle condition for the chartwise restrictions of a module -/

/-- The canonical comparison of successive chartwise pullbacks is the comparison of Stacks 03LU
for a composite presented as a single morphism of algebraic spaces, read in the splitting
direction. -/
theorem chartModuleInverseImageComp_eq {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    chartModuleInverseImageComp B S hS X f g =
      (modulePullbackTriangle B S hS (chartMap_comp B S hS X f g)).symm := rfl

/-- The compatibility of chart restriction with the chartwise pullback is the comparison of
Stacks 03LU for a composite presented as a single morphism of algebraic spaces, read in the
splitting direction. -/
theorem chartModuleRestrictionComp_eq {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartModuleRestrictionComp B S hS X f =
      (modulePullbackTriangle B S hS (chartMap_comp_chartToSpace B S hS X f)).symm := rfl

/-- The cocycle condition of Stacks 03LY for the family of restrictions of an `𝒪_X`-module to
the étale scheme charts of `X`, as an equality of isomorphisms of functors: the restriction to
the smallest chart is reached the same way through either intermediate chart.

This is the associativity coherence `AlgebraicGeometry.Space.modulePullbackTriangle_assoc` of
Stacks 03LU at the three morphisms `chartMap g`, `chartMap f` and `chartToSpace U`. -/
theorem chartModuleRestrictionComp_cocycle {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    Functor.isoWhiskerLeft (chartModuleRestriction B S hS X U)
          (chartModuleInverseImageComp B S hS X f g) ≪≫
        chartModuleRestrictionComp B S hS X (g ≫ f) =
      (Functor.associator (chartModuleRestriction B S hS X U)
          (chartModuleInverseImage B S hS X f) (chartModuleInverseImage B S hS X g)).symm ≪≫
        Functor.isoWhiskerRight (chartModuleRestrictionComp B S hS X f)
          (chartModuleInverseImage B S hS X g) ≪≫
        chartModuleRestrictionComp B S hS X g := by
  have key := modulePullbackTriangle_assoc B S hS (chartMap_comp B S hS X f g)
    (chartMap_comp_chartToSpace B S hS X f) (chartMap_comp_chartToSpace B S hS X g)
    (chartMap_comp_chartToSpace B S hS X (g ≫ f))
  rw [← Iso.symm_eq_iff] at key
  rw [chartModuleInverseImageComp_eq, chartModuleRestrictionComp_eq,
    chartModuleRestrictionComp_eq, chartModuleRestrictionComp_eq]
  simpa [Functor.isoWhiskerLeft_symm, Functor.isoWhiskerRight_symm, chartModuleRestriction,
    chartModuleInverseImage] using key

/-- **Stacks 03LY, the cocycle condition for the chartwise restrictions.**  For composable
morphisms `g : W ⟶ V` and `f : V ⟶ U` of étale scheme charts of `X` and an `𝒪_X`-module `F`, the
transition `c_g` of the restriction family after the chartwise pullback `g^*c_f` of the
transition `c_f` is the transition `c_{g ≫ f}`, read through the canonical comparison
`AlgebraicGeometry.Space.chartModuleInverseImageComp`.

This is the condition that `AlgebraicGeometry.Space.IsChartModuleCocycle` names, written out at
the family of restrictions; see the discussion in the module documentation of why the term of
that predicate's type does not follow. -/
@[stacks 03LY "the cocycle condition for the chartwise restrictions of a module"]
theorem chartModuleRestrictionComp_cocycle_app (F : Modules.{u, u} B S hS X.1 X.2)
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    (chartModuleInverseImage B S hS X g).map
          ((chartModuleRestrictionComp B S hS X f).app F).hom ≫
        ((chartModuleRestrictionComp B S hS X g).app F).hom =
      (chartModuleInverseImageComp B S hS X f g).hom.app
          ((chartModuleRestriction B S hS X U).obj F) ≫
        ((chartModuleRestrictionComp B S hS X (g ≫ f)).app F).hom :=
  Functor.cocycle_app_of_iso (chartModuleRestrictionComp B S hS X f)
    (chartModuleInverseImageComp B S hS X f g) (chartModuleRestrictionComp B S hS X g)
    (chartModuleRestrictionComp B S hS X (g ≫ f))
    (chartModuleRestrictionComp_cocycle B S hS X f g) F

/-- **Datum (2) of Stacks 03LY for the family of restrictions of an `𝒪_X`-module** to the étale
scheme charts of `X`: the transitions are the comparisons
`AlgebraicGeometry.Space.chartModuleRestrictionComp`.

The four components are listed one by one rather than the comparison at `F` being handed over
whole; see the implementation notes for why that is what makes the cocycle condition
reachable. -/
noncomputable def chartModuleRestrictionTransitions (F : Modules.{u, u} B S hS X.1 X.2)
    {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartModuleInverseImage B S hS X f).obj ((chartModuleRestriction B S hS X U).obj F) ≅
      (chartModuleRestriction B S hS X V).obj F where
  hom := ((chartModuleRestrictionComp B S hS X f).app F).hom
  inv := ((chartModuleRestrictionComp B S hS X f).app F).inv
  hom_inv_id := ((chartModuleRestrictionComp B S hS X f).app F).hom_inv_id
  inv_hom_id := ((chartModuleRestrictionComp B S hS X f).app F).inv_hom_id

/-- The transition of the restriction family is the comparison
`AlgebraicGeometry.Space.chartModuleRestrictionComp` at the module, read as a morphism out of
the uncomposed object. -/
theorem chartModuleRestrictionTransitions_hom (F : Modules.{u, u} B S hS X.1 X.2)
    {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartModuleRestrictionTransitions B S hS X F f).hom =
      ((chartModuleRestrictionComp B S hS X f).app F).hom := rfl

/-- The transitions of the restriction family are natural in the module: a morphism of
`𝒪_X`-modules restricts to a morphism of the chartwise families commuting with them.  This is
the naturality of `AlgebraicGeometry.Space.chartModuleRestrictionComp`. -/
theorem chartModuleRestrictionComp_naturality {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G) :
    (chartModuleInverseImage B S hS X f).map ((chartModuleRestriction B S hS X U).map φ) ≫
        ((chartModuleRestrictionComp B S hS X f).app G).hom =
      ((chartModuleRestrictionComp B S hS X f).app F).hom ≫
        (chartModuleRestriction B S hS X V).map φ :=
  (chartModuleRestrictionComp B S hS X f).hom.naturality φ

/-- The compatibility of the restrictions of a morphism of `𝒪_X`-modules with the transitions of
the restriction family, read out of the uncomposed objects by
`CategoryTheory.Functor.comp_app_naturality_of_eq`. -/
theorem chartModuleRestrictionTransitions_naturality {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G) :
    (chartModuleInverseImage B S hS X f).map ((chartModuleRestriction B S hS X U).map φ) ≫
        (chartModuleRestrictionTransitions B S hS X G f).hom =
      (chartModuleRestrictionTransitions B S hS X F f).hom ≫
        (chartModuleRestriction B S hS X V).map φ :=
  chartModuleRestrictionComp_naturality B S hS X f φ

/-! ### The canonical chartwise glueing datum of a module -/

/-- **The cocycle condition of Stacks 03LY for the family of restrictions of an `𝒪_X`-module**,
at the transitions of that family, that is with the comparisons read as morphisms out of the
uncomposed chartwise pullback of the restriction — which is where datum (2) of Stacks 03LY
lives.

The condition itself is the associativity coherence
`AlgebraicGeometry.Space.chartModuleRestrictionComp_cocycle`; the passage from the components of
the comparisons of composite functors to morphisms out of the uncomposed objects is
`CategoryTheory.Functor.cocycle_app_of_iso_of_eq`. -/
theorem chartModuleRestrictionTransitions_cocycle (F : Modules.{u, u} B S hS X.1 X.2)
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    (chartModuleInverseImage B S hS X g).map
          (chartModuleRestrictionTransitions B S hS X F f).hom ≫
        (chartModuleRestrictionTransitions B S hS X F g).hom =
      chartModuleInverseImageCompApp B S hS X f g
          ((chartModuleRestriction B S hS X U).obj F) ≫
        (chartModuleRestrictionTransitions B S hS X F (g ≫ f)).hom :=
  Functor.cocycle_app_of_iso_of_eq (chartModuleRestrictionComp B S hS X f)
    (chartModuleInverseImageComp B S hS X f g) (chartModuleRestrictionComp B S hS X g)
    (chartModuleRestrictionComp B S hS X (g ≫ f))
    (chartModuleRestrictionComp_cocycle B S hS X f g) F
    (chartModuleRestrictionTransitions B S hS X F f).hom
    (chartModuleRestrictionTransitions B S hS X F g).hom
    (chartModuleInverseImageCompApp B S hS X f g
      ((chartModuleRestriction B S hS X U).obj F))
    (chartModuleRestrictionTransitions B S hS X F (g ≫ f)).hom rfl rfl rfl rfl

/-- **Datum (1) of Stacks 03LY for an `𝒪_X`-module**: the family of its restrictions to the
étale scheme charts of `X`. -/
noncomputable def chartModuleRestrictionFamily (F : Modules.{u, u} B S hS X.1 X.2) :
    ChartModuleFamily B S hS X :=
  fun U ↦ (chartModuleRestriction B S hS X U).obj F

/-- **Datum (2) of Stacks 03LY for an `𝒪_X`-module**: the transitions of the family of its
restrictions to the charts. -/
noncomputable def chartModuleRestrictionTransitionFamily
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ChartModuleTransitions B S hS X (chartModuleRestrictionFamily B S hS X F) :=
  fun {_ _} f ↦ chartModuleRestrictionTransitions B S hS X F f

/-- **The cocycle condition of Stacks 03LY for the chartwise restrictions of an `𝒪_X`-module, as
a term of the predicate.**  This is
`AlgebraicGeometry.Space.chartModuleRestrictionTransitions_cocycle` transported from the
spelling in which it is proved to the one the predicate's instantiation produces, by
`CategoryTheory.Functor.map_comp_eq_comp_of_heq`. -/
@[stacks 03LY "the cocycle condition for the chartwise restrictions, as a term of the predicate"]
theorem isChartModuleCocycle_chartModuleRestrictionTransitionFamily
    (F : Modules.{u, u} B S hS X.1 X.2) :
    IsChartModuleCocycle B S hS X (chartModuleRestrictionFamily B S hS X F)
      (chartModuleRestrictionTransitionFamily B S hS X F) := by
  intro W V U f g
  refine Functor.map_comp_eq_comp_of_heq (chartModuleInverseImage B S hS X g) ?_ ?_ ?_ ?_
    _ _ _ _ (chartModuleRestrictionTransitions B S hS X F f).hom
    (chartModuleRestrictionTransitions B S hS X F g).hom
    (chartModuleInverseImageCompApp B S hS X f g
      ((chartModuleRestriction B S hS X U).obj F))
    (chartModuleRestrictionTransitions B S hS X F (g ≫ f)).hom ?_ ?_ ?_ ?_
    (chartModuleRestrictionTransitions_cocycle B S hS X F f g) <;> rfl

/-- **The chartwise glueing datum of an `𝒪_X`-module**: its restrictions to the étale scheme
charts of `X`, the comparisons `AlgebraicGeometry.Space.chartModuleRestrictionComp` as the
transition isomorphisms, and the cocycle condition they satisfy. -/
@[stacks 03LY "the chartwise glueing datum of a module"]
noncomputable def canonicalChartModuleGlueingData (F : Modules.{u, u} B S hS X.1 X.2) :
    ChartModuleGlueingData B S hS X :=
  ⟨chartModuleRestrictionFamily B S hS X F,
    chartModuleRestrictionTransitionFamily B S hS X F,
    isChartModuleCocycle_chartModuleRestrictionTransitionFamily B S hS X F⟩

/-- The chartwise glueing datum of a module carries the restriction of the module to each
chart, by `rfl`. -/
theorem canonicalChartModuleGlueingData_sheaf (F : Modules.{u, u} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1) :
    (canonicalChartModuleGlueingData B S hS X F).sheaf U =
      (chartModuleRestriction B S hS X U).obj F := rfl

/-- Its transitions are `AlgebraicGeometry.Space.chartModuleRestrictionTransitions`, by `rfl`. -/
theorem canonicalChartModuleGlueingData_transition (F : Modules.{u, u} B S hS X.1 X.2)
    {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (canonicalChartModuleGlueingData B S hS X F).transition f =
      chartModuleRestrictionTransitions B S hS X F f := rfl

/-- **The canonical chartwise description of `𝒪_X`-modules**: the functor sending an
`𝒪_X`-module to the family of its restrictions to the étale scheme charts of `X`, with the
comparisons `AlgebraicGeometry.Space.chartModuleRestrictionComp` as transitions.  That this
functor is an equivalence is Stacks 03LY. -/
@[stacks 03LY "the canonical chartwise description of modules"]
noncomputable def chartModuleGlueingFunctor :
    Modules.{u, u} B S hS X.1 X.2 ⥤ ChartModuleGlueingData B S hS X where
  obj F := canonicalChartModuleGlueingData B S hS X F
  map {_ _} φ :=
    { app := fun U ↦ (chartModuleRestriction B S hS X U).map φ
      w := fun {_ _} f ↦ chartModuleRestrictionTransitions_naturality B S hS X f φ }
  map_id F := ChartModuleGlueingData.hom_ext B S hS X fun U ↦
    (chartModuleRestriction B S hS X U).map_id F
  map_comp φ ψ := ChartModuleGlueingData.hom_ext B S hS X fun U ↦
    (chartModuleRestriction B S hS X U).map_comp φ ψ

/-- The canonical chartwise description carries a module to the family of its restrictions to
the charts, by `rfl`. -/
theorem chartModuleGlueingFunctor_obj_sheaf (F : Modules.{u, u} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1) :
    ((chartModuleGlueingFunctor B S hS X).obj F).sheaf U =
      (chartModuleRestriction B S hS X U).obj F := rfl

/-- On morphisms, the canonical chartwise description is restriction to the charts, by `rfl`. -/
theorem chartModuleGlueingFunctor_map_app {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G)
    (U : SmallEtale B S hS X.1) :
    ChartModuleGlueingData.Hom.app ((chartModuleGlueingFunctor B S hS X).map φ) U =
      (chartModuleRestriction B S hS X U).map φ := rfl

end AlgebraicGeometry.Space

end
