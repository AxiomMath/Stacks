module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartGlueingEquivalence
public import StacksFrontier.CategoryTheory.Adjunction.UnitSectionProjection

/-!
# The chartwise description of modules is the slice-indexed one

Stacks 03LY describes a sheaf of `𝒪_X`-modules on the small étale site of an algebraic space `X`
by a family of modules on the small étale sites of the étale scheme charts of `X` with transition
isomorphisms satisfying a cocycle condition; the module-coefficient form of Stacks 0GWK,
`CategoryTheory.SiteGlueing.canonicalModuleEquivalence`, does the same with the slices
`X_étale/U`.  The object-by-object dictionary between the two indexings is
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleSliceComparison.lean`, and this file turns it
into an *equivalence* between slice-indexed and chartwise glueing data for modules.

The dictionary squares, saying that the dictionary is compatible with the composition comparisons
on the two sides, are hypotheses here.  Both are proved — in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleSliceCoherence.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionSliceCoherence.lean`, and with no
hypothesis in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleSliceDictionarySquares.lean` — and
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartModuleGlueingEquivalence.lean` assembles
them into the equivalence of Stacks 03LY.

## Implementation notes

**Why every comparison is applied by a definition of its own.**  Each comparison occurring below
is an isomorphism of *composite* functors, so its component at a module `T` is typed through
`(F ⋙ G).obj T`, whereas the data of a chartwise glueing datum are typed through `G.obj (F.obj T)`.
Reconciling the two is a `Functor.obj` of a semireducible definition applied to two syntactically
different arguments, and the elaborator proj-reduces before it tries congruence: at
`AlgebraicGeometry.Space.chartModuleInverseImage`, which is the pullback of modules of Stacks 03LU
and hence a sheafified tensor product, that reduction exhausts the *recursion depth*, not merely
the heartbeat budget, and `set_option maxRecDepth` is not permitted here.

So each comparison is applied by a definition whose type is written out uncomposed —
`AlgebraicGeometry.Space.chartModuleInverseImageSliceIsoApp`,
`AlgebraicGeometry.Space.overMapCompInvApp` and the existing
`AlgebraicGeometry.Space.chartModuleInverseImageCompApp` — each of which performs the
reconciliation once, at a *variable* module, where it is cheap.  Everything downstream, the
hypotheses carrying the dictionary squares included, is stated through those definitions, so that
no composite-functor spelling is ever compared with an uncomposed one again.  This is the same
device, and for the same reason, as the one recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartModuleGlueing.lean`.

**Why a square is taken as a binder and not through its definition.**  Each dictionary square is a
quantified identity, and this file names it by a `Prop`-valued definition so that it can be stated
once; a consumer must nonetheless take the identity as an explicit `∀` in its own binder and not
through that definition.  The difference is not stylistic: matching the definition's
unfolded body against the written-out statement a step has to be made at exhausts the elaborator's
*recursion depth*, and with the recursion depth raised it exhausts the heartbeats inside a single
`isDefEq` — by application, by `@`-application with every implicit argument given, by `exact` after
a `have`, and by `apply` alike, and already for the two-factor composite
`chartModuleInverseImageCompApp f g (chartModuleSliceReindex U T) ≫
chartModuleInverseImageSliceApp (g ≫ f) T`, each of whose factors matches on its own in no time at
all.  With the identical text as an explicit `∀` in the binder every step is immediate.
`AlgebraicGeometry.Space.sliceToChartModuleCocycle_step_square` and
`AlgebraicGeometry.Space.isChartModuleCocycle_sliceToChartModuleTransitionFamily` are both written
that way, and a theorem that proves a square is handed to them as `fun f g T ↦ …`.

Beyond that, every proof is one rearrangement of a composite, performed by a chain of
`Stacks.CategoryTheory.proj_congr` applications with the rearranged morphisms given positionally.
That shape builds no motive, so there is nothing for the kernel to check beyond the morphisms
themselves; the abstract rearrangement lemmas of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartGlueingEquivalence.lean`
(`CategoryTheory.comp_bridge_rearrange_cocycle` and the two like it), which do the same job for the
coefficient-free statements of Stacks 03LS, need their endpoints unified against the goal's and so
are not used here.

## References

* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The comparisons, applied at a module -/

/-- The chart-to-slice dictionary for a morphism of charts, at a module on the slice, with both
endpoints written out uncomposed.  The reconciliation of `(F ⋙ G).obj T` with `G.obj (F.obj T)`
happens here, once, at a variable `T`; see the implementation notes. -/
def chartModuleInverseImageSliceIsoApp {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    (chartModuleInverseImage B S hS X f).obj
        ((chartModuleSliceReindex B S hS X U).obj T) ≅
      (chartModuleSliceReindex B S hS X V).obj
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) :=
  (chartModuleInverseImageSliceIso B S hS X f).app T

/-- The forward direction of `AlgebraicGeometry.Space.chartModuleInverseImageSliceIsoApp`. -/
def chartModuleInverseImageSliceApp {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    (chartModuleInverseImage B S hS X f).obj
        ((chartModuleSliceReindex B S hS X U).obj T) ⟶
      (chartModuleSliceReindex B S hS X V).obj
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) :=
  (chartModuleInverseImageSliceIsoApp B S hS X f T).hom

/-- The dictionary is natural in the module on the slice, read at the uncomposed endpoints. -/
theorem chartModuleInverseImageSliceApp_naturality {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    {T T' : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)} (φ : T ⟶ T') :
    (chartModuleInverseImage B S hS X f).map ((chartModuleSliceReindex B S hS X U).map φ) ≫
        chartModuleInverseImageSliceApp B S hS X f T' =
      chartModuleInverseImageSliceApp B S hS X f T ≫
        (chartModuleSliceReindex B S hS X V).map
          ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).map φ) :=
  (chartModuleInverseImageSliceIso B S hS X f).hom.naturality φ

/-- The composition comparison of the slice pullbacks, read backwards and at a module, with both
endpoints written out uncomposed. -/
def overMapCompInvApp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V)
    (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    (SheafOfModules.overMap (structureRingSheaf B S hS X) (g ≫ f)).obj T ⟶
      (SheafOfModules.overMap (structureRingSheaf B S hS X) g).obj
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) :=
  (SiteGlueing.overMapComp (structureRingSheaf B S hS X) f g).inv.app T

/-! ### The dictionary squares, as hypotheses -/

/-- **The first dictionary square of Stacks 03LY**, for a morphism of charts: the chart-to-slice
dictionary for modules is compatible with the composition comparisons
`AlgebraicGeometry.Space.chartModuleInverseImageComp` and
`CategoryTheory.SiteGlueing.overMapComp`.  Every comparison is applied by the definitions above,
so that the statement mentions no composite-functor spelling.

A consumer must take this identity as an explicit `∀` in a binder and not through this
definition; see the implementation notes. -/
def ChartModuleInverseImageSliceSquare : Prop :=
  ∀ {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V)
    (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)),
    (chartModuleInverseImage B S hS X g).map
          (chartModuleInverseImageSliceApp B S hS X f T) ≫
        chartModuleInverseImageSliceApp B S hS X g
          ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) =
      chartModuleInverseImageCompApp B S hS X f g
          ((chartModuleSliceReindex B S hS X U).obj T) ≫
        chartModuleInverseImageSliceApp B S hS X (g ≫ f) T ≫
          (chartModuleSliceReindex B S hS X W).map (overMapCompInvApp B S hS X f g T)

/-- **The second dictionary square of Stacks 03LY**, for the structure morphism of a chart: the
dictionary carries `AlgebraicGeometry.Space.chartModuleRestrictionComp` to
`SheafOfModules.overFunctorMap`. -/
def ChartModuleRestrictionSliceSquare : Prop :=
  ∀ {V U : SmallEtale B S hS X.1} (f : V ⟶ U) (F : Modules.{u, u} B S hS X.1 X.2),
    (chartModuleInverseImage B S hS X f).map
          ((chartModuleRestrictionSliceIso B S hS X U).hom.app F) ≫
        chartModuleInverseImageSliceApp B S hS X f
            ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F) ≫
          (chartModuleSliceReindex B S hS X V).map
            ((SheafOfModules.overFunctorMap (structureRingSheaf B S hS X) f).hom.app F) =
      (chartModuleRestrictionComp B S hS X f).hom.app F ≫
        (chartModuleRestrictionSliceIso B S hS X V).hom.app F

/-! ### Slice-indexed glueing data for modules, read chartwise -/

/-- The transition isomorphism of the chartwise reading of a slice-indexed glueing datum for
modules: the chart-to-slice dictionary followed by the datum's own comparison isomorphism, read
through the comparison equivalence of Stacks 04M0 on modules. -/
def sliceToChartModuleTransition
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X))
    {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartModuleInverseImage B S hS X f).obj
        ((chartModuleSliceReindex B S hS X U).obj (D.sheaf U)) ≅
      (chartModuleSliceReindex B S hS X V).obj (D.sheaf V) :=
  chartModuleInverseImageSliceIsoApp B S hS X f (D.sheaf U) ≪≫
    (chartModuleSliceReindex B S hS X V).mapIso (D.iso f)

/-- **Datum (1) of Stacks 03LY for a slice-indexed glueing datum**: its modules on the slices,
read as modules on the small étale sites of the charts. -/
def sliceToChartModuleFamily
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X)) :
    ChartModuleFamily B S hS X :=
  fun U ↦ (chartModuleSliceReindex B S hS X U).obj (D.sheaf U)

/-- **Datum (2) of Stacks 03LY for a slice-indexed glueing datum**. -/
def sliceToChartModuleTransitionFamily
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X)) :
    ChartModuleTransitions B S hS X (sliceToChartModuleFamily B S hS X D) :=
  fun {_ _} f ↦ sliceToChartModuleTransition B S hS X D f

/-- The cocycle condition of a slice-indexed glueing datum, with the composition comparison of
the slice pullbacks inverted and applied at the module. -/
theorem overMapCompInvApp_iso_comp
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X))
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    overMapCompInvApp B S hS X f g (D.sheaf U) ≫
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map (D.iso f).hom ≫
          (D.iso g).hom) =
      (D.iso (g ≫ f)).hom := by
  rw [D.comp f g]
  simp [overMapCompInvApp]

/-- The cocycle condition of a slice-indexed glueing datum, read through the comparison
equivalence of Stacks 04M0 at the smallest chart. -/
theorem reindex_overMapCompInvApp_iso_comp
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X))
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    (chartModuleSliceReindex B S hS X W).map (overMapCompInvApp B S hS X f g (D.sheaf U)) ≫
        (chartModuleSliceReindex B S hS X W).map
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map (D.iso f).hom) ≫
          (chartModuleSliceReindex B S hS X W).map (D.iso g).hom =
      (chartModuleSliceReindex B S hS X W).map (D.iso (g ≫ f)).hom := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    overMapCompInvApp_iso_comp B S hS X D f g]

/-- The naturality of the dictionary, moved into the middle of the composite. -/
theorem sliceToChartModuleCocycle_step_nat
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X))
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    (chartModuleInverseImage B S hS X g).map
            (chartModuleInverseImageSliceApp B S hS X f (D.sheaf U)) ≫
        (chartModuleInverseImage B S hS X g).map
            ((chartModuleSliceReindex B S hS X V).map (D.iso f).hom) ≫
        chartModuleInverseImageSliceApp B S hS X g (D.sheaf V) ≫
        (chartModuleSliceReindex B S hS X W).map (D.iso g).hom =
      (chartModuleInverseImage B S hS X g).map
            (chartModuleInverseImageSliceApp B S hS X f (D.sheaf U)) ≫
        chartModuleInverseImageSliceApp B S hS X g
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj (D.sheaf U)) ≫
        (chartModuleSliceReindex B S hS X W).map
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map (D.iso f).hom) ≫
        (chartModuleSliceReindex B S hS X W).map (D.iso g).hom :=
  (Stacks.CategoryTheory.proj_congr (Category.assoc ((chartModuleInverseImage B S hS X g).map
      ((chartModuleSliceReindex B S hS X V).map (D.iso f).hom))
      (chartModuleInverseImageSliceApp B S hS X g (D.sheaf V))
      ((chartModuleSliceReindex B S hS X W).map (D.iso g).hom)).symm
      (fun m ↦ ((chartModuleInverseImage B S hS X g).map
      (chartModuleInverseImageSliceApp B S hS X f (D.sheaf U))) ≫ m)).trans
    ((Stacks.CategoryTheory.proj_congr
        (chartModuleInverseImageSliceApp_naturality B S hS X g (D.iso f).hom)
        (fun m ↦ ((chartModuleInverseImage B S hS X g).map
      (chartModuleInverseImageSliceApp B S hS X f (D.sheaf U))) ≫ m ≫
        ((chartModuleSliceReindex B S hS X W).map (D.iso g).hom))).trans
      (Stacks.CategoryTheory.proj_congr (Category.assoc (chartModuleInverseImageSliceApp B S hS X g
      ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj (D.sheaf U)))
      ((chartModuleSliceReindex B S hS X W).map
      ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map (D.iso f).hom))
      ((chartModuleSliceReindex B S hS X W).map (D.iso g).hom))
        (fun m ↦ ((chartModuleInverseImage B S hS X g).map
      (chartModuleInverseImageSliceApp B S hS X f (D.sheaf U))) ≫ m)))

/-- The datum's own cocycle condition, at the tail of the composite: a single
`Stacks.CategoryTheory.proj_congr`, which leaves the kernel no motive to check. -/
theorem sliceToChartModuleCocycle_step_comp
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X))
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    (chartModuleInverseImageCompApp B S hS X f g
      ((chartModuleSliceReindex B S hS X U).obj (D.sheaf U))) ≫
        (chartModuleInverseImageSliceApp B S hS X (g ≫ f) (D.sheaf U)) ≫
        ((chartModuleSliceReindex B S hS X W).map (overMapCompInvApp B S hS X f g (D.sheaf U))) ≫
        ((chartModuleSliceReindex B S hS X W).map
      ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map (D.iso f).hom)) ≫
        ((chartModuleSliceReindex B S hS X W).map (D.iso g).hom) =
      (chartModuleInverseImageCompApp B S hS X f g
      ((chartModuleSliceReindex B S hS X U).obj (D.sheaf U))) ≫
        (chartModuleInverseImageSliceApp B S hS X (g ≫ f) (D.sheaf U)) ≫
        ((chartModuleSliceReindex B S hS X W).map (D.iso (g ≫ f)).hom) :=
  Stacks.CategoryTheory.proj_congr (reindex_overMapCompInvApp_iso_comp B S hS X D f g)
    (fun m ↦ (chartModuleInverseImageCompApp B S hS X f g
      ((chartModuleSliceReindex B S hS X U).obj (D.sheaf U))) ≫
        (chartModuleInverseImageSliceApp B S hS X (g ≫ f) (D.sheaf U)) ≫ m)

/-- The dictionary square, at the datum's chart module and at the tail of the composite: the
middle factor of the cocycle chain.

The square is taken as an explicit `∀` in the binder and not through
`AlgebraicGeometry.Space.ChartModuleInverseImageSliceSquare`, for the reason recorded in the
implementation notes: matching a `Prop`-valued definition's unfolded body against the statement
written out here exhausts the elaborator's recursion depth, while the same identity in a binder is
immediate.  Composing it with the tail is then a chain of `Stacks.CategoryTheory.proj_congr`
applications, which leaves the kernel no motive to check. -/
theorem sliceToChartModuleCocycle_step_square
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X))
    (hsq : ∀ {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V)
      (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)),
      (chartModuleInverseImage B S hS X g).map
            (chartModuleInverseImageSliceApp B S hS X f T) ≫
          chartModuleInverseImageSliceApp B S hS X g
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) =
        chartModuleInverseImageCompApp B S hS X f g
            ((chartModuleSliceReindex B S hS X U).obj T) ≫
          chartModuleInverseImageSliceApp B S hS X (g ≫ f) T ≫
            (chartModuleSliceReindex B S hS X W).map (overMapCompInvApp B S hS X f g T))
    {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    (chartModuleInverseImage B S hS X g).map
            (chartModuleInverseImageSliceApp B S hS X f (D.sheaf U)) ≫
        chartModuleInverseImageSliceApp B S hS X g
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj (D.sheaf U)) ≫
        (chartModuleSliceReindex B S hS X W).map
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map (D.iso f).hom) ≫
        (chartModuleSliceReindex B S hS X W).map (D.iso g).hom =
      chartModuleInverseImageCompApp B S hS X f g
            ((chartModuleSliceReindex B S hS X U).obj (D.sheaf U)) ≫
        chartModuleInverseImageSliceApp B S hS X (g ≫ f) (D.sheaf U) ≫
        (chartModuleSliceReindex B S hS X W).map (overMapCompInvApp B S hS X f g (D.sheaf U)) ≫
        (chartModuleSliceReindex B S hS X W).map
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map (D.iso f).hom) ≫
        (chartModuleSliceReindex B S hS X W).map (D.iso g).hom :=
  ((Category.assoc
          ((chartModuleInverseImage B S hS X g).map
            (chartModuleInverseImageSliceApp B S hS X f (D.sheaf U)))
          (chartModuleInverseImageSliceApp B S hS X g
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj (D.sheaf U)))
          ((chartModuleSliceReindex B S hS X W).map
              ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map (D.iso f).hom) ≫
            (chartModuleSliceReindex B S hS X W).map (D.iso g).hom)).symm.trans
      (Stacks.CategoryTheory.proj_congr (hsq f g (D.sheaf U))
        (fun m ↦ m ≫ (chartModuleSliceReindex B S hS X W).map
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map (D.iso f).hom) ≫
          (chartModuleSliceReindex B S hS X W).map (D.iso g).hom))).trans
    ((Category.assoc
          (chartModuleInverseImageCompApp B S hS X f g
            ((chartModuleSliceReindex B S hS X U).obj (D.sheaf U)))
          (chartModuleInverseImageSliceApp B S hS X (g ≫ f) (D.sheaf U) ≫
            (chartModuleSliceReindex B S hS X W).map
              (overMapCompInvApp B S hS X f g (D.sheaf U)))
          ((chartModuleSliceReindex B S hS X W).map
              ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map (D.iso f).hom) ≫
            (chartModuleSliceReindex B S hS X W).map (D.iso g).hom)).trans
      (Stacks.CategoryTheory.proj_congr
        (Category.assoc (chartModuleInverseImageSliceApp B S hS X (g ≫ f) (D.sheaf U))
          ((chartModuleSliceReindex B S hS X W).map
            (overMapCompInvApp B S hS X f g (D.sheaf U)))
          ((chartModuleSliceReindex B S hS X W).map
              ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map (D.iso f).hom) ≫
            (chartModuleSliceReindex B S hS X W).map (D.iso g).hom))
        (fun m ↦ chartModuleInverseImageCompApp B S hS X f g
          ((chartModuleSliceReindex B S hS X U).obj (D.sheaf U)) ≫ m)))

/-! ### The cocycle condition of the chartwise reading, as a term of the predicate -/

/-- **The cocycle condition of Stacks 03LY for the chartwise reading of a slice-indexed glueing
datum, as a term of the predicate**, granted the cocycle identity at the comparisons the
transitions are assembled from.

The hypothesis is that identity in the spelling the three factors above leave it in: the
chart-to-slice dictionary and the datum's own comparison isomorphism are separate factors, each
applied by the definitions of this file, and the two outer factors of the chain are
`AlgebraicGeometry.Space.sliceToChartModuleCocycle_step_nat` and
`AlgebraicGeometry.Space.sliceToChartModuleCocycle_step_comp`, its middle one
`AlgebraicGeometry.Space.sliceToChartModuleCocycle_step_square`, the dictionary square at the
datum's chart module.

The proof folds the two factors of each transition back together — one
`CategoryTheory.Functor.map_comp` and one reassociation, applied positionally by
`Stacks.CategoryTheory.proj_congr` — and then transports the result to the spelling the
predicate's instantiation produces by `CategoryTheory.Functor.map_comp_eq_comp_of_heq`.  The
transport is what the passage needs, because `AlgebraicGeometry.Space.sliceToChartModuleFamily` is
a function, so its value at a chart is a redex: instantiating the predicate at the family asks for
`(f^* ⋙ g^*).obj M` to be reconciled with `g^*(f^*M)` while `M` itself is being reduced, and that
reduction does not terminate.  Matched one object and one morphism at a time, as here, every
obligation is a projection and each is checked by `rfl` or `HEq.rfl` in a fraction of a second.

The hypothesis is an explicit `∀` and not a `Prop`-valued definition, and that is not
stylistic: with the identity carried by a definition — in either direction of
`CategoryTheory.Functor.map_comp`, and whether it is instantiated by application, by `exact` or by
`apply` — matching the definition's unfolded body against the statement the fold has to be written
at exhausts the elaborator's *recursion depth*, and with the recursion depth raised it exhausts the
heartbeats inside a single `isDefEq`.  With the same identity as an explicit `∀` in the binder,
every step of the fold is immediate.  This is the same obstruction as the one
`AlgebraicGeometry.Space.sliceToChartModuleCocycle_step_square` meets, and the shape that avoids
it. -/
theorem isChartModuleCocycle_sliceToChartModuleTransitionFamily
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X))
    (hcoc : ∀ {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V),
      (chartModuleInverseImage B S hS X g).map
              (chartModuleInverseImageSliceApp B S hS X f (D.sheaf U)) ≫
          (chartModuleInverseImage B S hS X g).map
              ((chartModuleSliceReindex B S hS X V).map (D.iso f).hom) ≫
          chartModuleInverseImageSliceApp B S hS X g (D.sheaf V) ≫
          (chartModuleSliceReindex B S hS X W).map (D.iso g).hom =
        chartModuleInverseImageCompApp B S hS X f g
            ((chartModuleSliceReindex B S hS X U).obj (D.sheaf U)) ≫
          chartModuleInverseImageSliceApp B S hS X (g ≫ f) (D.sheaf U) ≫
          (chartModuleSliceReindex B S hS X W).map (D.iso (g ≫ f)).hom) :
    IsChartModuleCocycle B S hS X (sliceToChartModuleFamily B S hS X D)
      (sliceToChartModuleTransitionFamily B S hS X D) := by
  intro W V U f g
  refine Functor.map_comp_eq_comp_of_heq (chartModuleInverseImage B S hS X g) ?_ ?_ ?_ ?_
    _ _ _ _
    (chartModuleInverseImageSliceApp B S hS X f (D.sheaf U) ≫
      (chartModuleSliceReindex B S hS X V).map (D.iso f).hom)
    (chartModuleInverseImageSliceApp B S hS X g (D.sheaf V) ≫
      (chartModuleSliceReindex B S hS X W).map (D.iso g).hom)
    (chartModuleInverseImageCompApp B S hS X f g
      ((chartModuleSliceReindex B S hS X U).obj (D.sheaf U)))
    (chartModuleInverseImageSliceApp B S hS X (g ≫ f) (D.sheaf U) ≫
      (chartModuleSliceReindex B S hS X W).map (D.iso (g ≫ f)).hom)
    ?_ ?_ ?_ ?_
    ((Stacks.CategoryTheory.proj_congr
        ((chartModuleInverseImage B S hS X g).map_comp
          (chartModuleInverseImageSliceApp B S hS X f (D.sheaf U))
          ((chartModuleSliceReindex B S hS X V).map (D.iso f).hom))
        (fun m ↦ m ≫ (chartModuleInverseImageSliceApp B S hS X g (D.sheaf V) ≫
          (chartModuleSliceReindex B S hS X W).map (D.iso g).hom))).trans
      ((Category.assoc _ _ _).trans (hcoc f g))) <;>
  rfl

/-- **The cocycle condition of Stacks 03LY for the chartwise reading of a slice-indexed glueing
datum, granted the first dictionary square**: the three factors
`AlgebraicGeometry.Space.sliceToChartModuleCocycle_step_nat`,
`AlgebraicGeometry.Space.sliceToChartModuleCocycle_step_square` and
`AlgebraicGeometry.Space.sliceToChartModuleCocycle_step_comp` chained by `Eq.trans` and handed to
`AlgebraicGeometry.Space.isChartModuleCocycle_sliceToChartModuleTransitionFamily`.

The square is again a binder rather than
`AlgebraicGeometry.Space.ChartModuleInverseImageSliceSquare`, and is passed on unchanged; a
separately proved theorem is supplied here as `fun f g T ↦ …`. -/
theorem isChartModuleCocycle_sliceToChartModuleTransitionFamily_of_square
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X))
    (hsq : ∀ {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V)
      (T : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)),
      (chartModuleInverseImage B S hS X g).map
            (chartModuleInverseImageSliceApp B S hS X f T) ≫
          chartModuleInverseImageSliceApp B S hS X g
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj T) =
        chartModuleInverseImageCompApp B S hS X f g
            ((chartModuleSliceReindex B S hS X U).obj T) ≫
          chartModuleInverseImageSliceApp B S hS X (g ≫ f) T ≫
            (chartModuleSliceReindex B S hS X W).map (overMapCompInvApp B S hS X f g T)) :
    IsChartModuleCocycle B S hS X (sliceToChartModuleFamily B S hS X D)
      (sliceToChartModuleTransitionFamily B S hS X D) :=
  isChartModuleCocycle_sliceToChartModuleTransitionFamily B S hS X D
    (fun f g ↦ (sliceToChartModuleCocycle_step_nat B S hS X D f g).trans
      ((sliceToChartModuleCocycle_step_square B S hS X D hsq f g).trans
        (sliceToChartModuleCocycle_step_comp B S hS X D f g)))

/-! ### Where the squares are proved

Both dictionary squares this file carries as hypotheses are theorems.  The first,
`AlgebraicGeometry.Space.ChartModuleInverseImageSliceSquare`, is
`AlgebraicGeometry.Space.chartModuleInverseImageSliceApp_comp` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleSliceCoherence.lean`; the second,
`AlgebraicGeometry.Space.ChartModuleRestrictionSliceSquare`, is
`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso_comp` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionSliceCoherence.lean`.  Each is stated
there with the coherence of Stacks 03LU against Stacks 03LW for étale *representable* morphisms as
a hypothesis, and that coherence is itself proved —
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction_of_representable` — so
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleSliceDictionarySquares.lean` restates both
squares, and the cocycle condition
`AlgebraicGeometry.Space.isChartModuleCocycle_sliceToChartModuleTransitionFamily_unconditional`
they give, with no hypothesis at all.  From there
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartModuleGlueingEquivalence.lean` builds the
equivalence of Stacks 03LY.

A square must be handed on as an explicit `∀` in a binder, as
`AlgebraicGeometry.Space.sliceToChartModuleCocycle_step_square` and
`AlgebraicGeometry.Space.isChartModuleCocycle_sliceToChartModuleTransitionFamily` take it, and not
through the `Prop`-valued definition; that is the one hard constraint on this corner and the
implementation notes record it.
-/

end AlgebraicGeometry.Space

end
