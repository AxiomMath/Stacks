module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeComparisonBijective

/-!
# The base-change comparison across a commuting square with étale verticals

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B` and
let

`a ≫ pV = pU ≫ f`

be a commuting square of algebraic spaces whose two vertical morphisms `pU : X' ⟶ X` and
`pV : Y' ⟶ Y` are **étale**.  Restricting an `𝒪_Y`-module `M` along `pV` and pulling it back
along `a` then compares with pulling back along `f` and restricting along `pU`, the restrictions
being read as `AlgebraicGeometry.Space.etaleModulePullback`:

`a^*(M|_{Y'}) ⟶ (f^*M)|_{X'}`.

This file **constructs that comparison from the chart sections of `f`** and reduces the
presentation-free bijectivity of
`AlgebraicGeometry.Space.modulePullbackChartBaseChange B S hS f M d` over an affine chart diagram
`d` to the bijectivity of one component of it.

The point of the construction is that it needs no coherence of the comparisons of Stacks 03LU
and 03LW: a morphism *out of* a pullback of modules is a linear map of sections along `a`
(`AlgebraicGeometry.Space.modulePullbackHomFMap`, a bijection), and the linear map of sections
fed to it here is the chart section of `f` itself, read on the chart diagrams of the square.  So
the comparison carries the chart section of `a` to the chart section of `f` *by construction*,
which is exactly the compatibility a base-change comparison — the `𝒪_{X'}(U)`-linear extension
of the chart section — has to satisfy.

## Main definitions

* `AlgebraicGeometry.Space.ChartDiagram.postcomp`: a commuting square of étale scheme charts
  over `a`, postcomposed with the two étale verticals, is one over `f`.  The vertical scheme
  morphism and both underlying schemes are unchanged, so the structure rings, the algebra
  structure and the sections of the restricted module on the two sides of
  `AlgebraicGeometry.Space.ChartDiagram.postcomp` agree definitionally.
* `AlgebraicGeometry.Space.modulePullbackChartSectionFMap`: the chart sections of `f`, read as a
  linear map of sections along `a` from `(f^*M)|_{X'}` to `M|_{Y'}`.
* `AlgebraicGeometry.Space.modulePullbackFMapEquiv`: the chartwise transpose
  `AlgebraicGeometry.Space.modulePullbackHomFMap` as a bijection, which it is, being the
  composite of the Stacks 03D7 hom-set bijection with the chart correspondence of Stacks 03G4.
* `AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison`: **the comparison**, the morphism
  of `𝒪_{X'}`-modules whose chartwise transpose is that linear map of sections.

## Main results

* `AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison_chartSection`: **the defining
  property** — the comparison carries the chart section of `a` at a chart diagram `e` of the
  square to the chart section of `f` at the postcomposed chart diagram.
* `AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison_baseChange`: consequently it
  carries the base-change comparison at `(a, e)` to the base-change comparison at
  `(f, e.postcomp)`; both are the `𝒪_{X'}(e.U)`-linear extension of the same chart section.
* `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_postcomp`: so the
  base-change comparison at `(f, e.postcomp)` is bijective as soon as the one at `(a, e)` is and
  the comparison is bijective on the sections over `e.U`.
* `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_bijective_comparison`:
  **the presentation-free reduction.**  For a quasi-coherent `M` and a diagram `d` of affine
  étale charts over `f`, the canonical comparison
  `AlgebraicGeometry.Space.modulePullbackChartBaseChange B S hS f M d` is bijective as soon as
  the comparison of the chart-space square of `d` is bijective on the sections over the identity
  chart.  No presentation of `M` is assumed: the one the square's own base-change comparison
  needs lives on the chart space `AlgebraicGeometry.Space.chartSpace B S hS Y d.V`, where
  `AlgebraicGeometry.Space.exists_presentation_rightExact_app_idEtaleChart` produces it.

## What is not proved

**That the comparison is an isomorphism.**  The comparison of
`AlgebraicGeometry.Space.etaleModulePullbackChartSpaceBaseChangeIso` — the same two functors,
compared instead through `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso` and
Stacks 03LW — *is* an isomorphism, so identifying the two would settle it; but that
identification is the compatibility of the comparisons of Stacks 03LU and 03LW with the chart
component of the unit of Stacks 03D7, which this development does not have.

**It is owed in two instances, not one, and only one of them is still missing.**  The
compatibility splits by which of the two composable morphisms is étale, and the split matters
because the two instances have different proofs and different status.

*Both factors étale: proved, with no hypothesis.*
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction` proves
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction` outright,
by `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit` — the two adjunctions of
étale restriction along a composite have the same unit — fed to
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_unit`.  Its consumers are
discharged where they can reach the proof: the one consumer of
`fullyFaithfulEtaleCanonicalDescentFunctorOfIsZariskiCovering` (in the namespace
`AlgebraicGeometry.Space.QuasiCoherentDescent`) passes it in
`isEquivalence_etaleCanonicalDescentFunctorOfIsZariskiCovering_of_essSurj` (same namespace),
and `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleRestrictionComp_of_representable` takes
it from the same unit, its three representability hypotheses being unused in the proof.  So
this instance is **not** a blocker of anything, and a note that records it as one is stale.

*One factor étale, the other arbitrary: this is now proved too, and the record that said
otherwise named a refactor that was never needed.*  This is the instance the chart comparison of
Stacks 07SI needs and the one the two records below need, and all three reduce to one statement
which is **not** about charts at all: that
`AlgebraicGeometry.Space.modulePushforwardCompIso` *is* the geometric comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3), on underlying
sheaves of sets.  That statement is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`, proved by
reading the comparison on a single local section — where the identification is between two
elements of one type rather than between two sheaves of types — and it has been there, with many
consumers, longer than this record claiming it missing has.

The chart-level reading of it is `AlgebraicGeometry.Space.ModuleFMap.compOfIso_app` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleFMapCompChartFormula.lean`, which carries exactly
that statement as its one hypothesis, and from the two of them the mixed instance follows with
no étaleness on either factor:

* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_val_app_modulePullbackUnitSection` in
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackCompIsoChartSection.lean` is Stacks 03LU
  carrying a chart section of a chart section to the chart section of the composite, at arbitrary
  `f` and `g`;
* `AlgebraicGeometry.Space.moduleFMapEtaleSourceCompCorrespondence` in
  `StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModuleFMapCompDischarge.lean` discharges
  `AlgebraicGeometry.Space.ModuleFMapEtaleSourceCompCorrespondence` unconditionally, and with it
  `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite` —
  the chart bijectivity of Stacks 083K with no coherence hypothesis at all.

**`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` stays an equality of
functors.**  The statement here is proved with it as an equality, and the component-wise
natural isomorphism exists as a declaration of its own alongside the equality rather than in
place of it — `AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`, identified with
the transport by `AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward_eq_eqToIso`, in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSpellingBridge.lean`.

What is still open, and it is a different thing, is
`AlgebraicGeometry.Space.ModulePullbackEtaleSourceCoherence` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModulePullbackComparison.lean`, which nothing
constructs.  Its `comp` field is the chart-section formula above specialized to an
identity-vertical diagram and a source-postcomposed one, so what separates the two is the
transport of chart diagrams along `AlgebraicGeometry.Space.ChartDiagram.ext`, not the comparison;
its `restrict` field is the Stacks 03LW half, whose input is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`.  Its consumers are in
any case superseded: `AlgebraicGeometry.Space.ModuleFMapEtaleSourceCompCorrespondence` replaced
the pair by a single hypothesis and that hypothesis is proved.

The two remaining records that still describe the instance as missing are:

* the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraEtaleRestriction.lean`: "neither
  `AlgebraicGeometry.Space.modulePullbackCompIso` nor
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback` is described on those sections:
  both are mates of comparisons of direct images".  The sections there are the generator
  sections of a pullback of graded algebras, not chart components, so that note asks for the
  same comparison read on different sections, which the chart-section formula does not supply;
* the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModuleChartCorrespondenceComp.lean`, whose owed
  declaration is a *different* obstruction — a kernel deterministic timeout on
  `AlgebraicGeometry.Space.ModulePushforwardPresentation.comp`, with its own route around it
  through an existence statement — and not this compatibility.

The reason the chart comparison of Stacks 07SI depends on this compatibility is
`AlgebraicGeometry.Space.homEquiv_restrictToChartBaseChangeIso_hom` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChangeAdjunct.lean`: that the adjunct
of `AlgebraicGeometry.Space.restrictToChartBaseChangeIso` is
`AlgebraicGeometry.Space.restrictToChartPushforwardHom` reduces to this same compatibility and
to nothing else — four of that composite's five factors cost nothing in the adjunct, and the
fifth is `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso`, whose two instances of
`AlgebraicGeometry.Space.modulePullbackCompIso` are both of the mixed kind: the chart-space
morphism of a square of charts is not étale, so neither factor falls under the both-étale
instance.  With the mixed instance proved, what that reduction is still short of is the other
half it names: the adjunct of the *represented* base-change isomorphism, whose factors are
`have`-bound inside its own construction and have to be named before they can be peeled.

What this file removes from that blocker is everything except the bijectivity itself: the
comparison here is a morphism of modules with an elementary defining property, and the target
statement is bijectivity of its component at one chart.

## Implementation notes

Three elaboration constraints, none needing a raised limit.

*Every chart diagram is passed explicitly.*  In the fields of
`AlgebraicGeometry.Space.modulePullbackChartSectionFMap` and in
`AlgebraicGeometry.Space.modulePullbackChartSectionFMap_app`, leaving the chart diagram of
`AlgebraicGeometry.Space.modulePullbackChartFMap` to unification exhausts the heartbeat budget:
the metavariable is solved against the postcomposed diagram only after the two sides of the
`naturality` hypothesis have been unfolded, and that unification does not finish.  With the
diagram given, the hypothesis is accepted as it stands, because `SmallEtale.toOver` is unchanged
by postcomposition.

*The identification of the two tensor products is performed once, by `Eq.trans`.*  In
`AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison_baseChange` the right-hand side is
rewritten *before* the left-hand side is touched: after a rewrite on the left the goal is no
longer type-correct at `implicit` transparency — the base-change comparison at
`(f, e.postcomp)` is applied to a tensor product spelt at `(a, e)` — and `rw` refuses to work
with it, although the two spellings are definitionally equal and the kernel accepts the term.

*No `≫`-free coherence is used anywhere.*  The square enters only through the equality
`a ≫ pV = pU ≫ f` of morphisms of algebraic spaces, read on underlying natural transformations;
`AlgebraicGeometry.Space.chartSpaceMapOver_comp_chartToSpace` supplies it for the chart-space
square of a chart diagram.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Postcomposing a chart diagram with the étale verticals of a square -/

/-- **A commuting square of étale scheme charts over `a`, postcomposed with the two étale
verticals of a commuting square `a ≫ pV = pU ≫ f`, is one over `f`.**

Postcomposition `AlgebraicGeometry.Space.smallEtalePostcomp` leaves the underlying object of the
big fppf site of a chart unchanged, so the vertical scheme morphism of the diagram is carried
over unchanged and the commutation is the commutation of the given diagram composed with that of
the square. -/
def ChartDiagram.postcomp {X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (a : X' ⟶ Y')
    (pU : X' ⟶ X) (pV : Y' ⟶ Y) (hU : IsEtale B S hS pU.hom) (hV : IsEtale B S hS pV.hom)
    (hsq : a ≫ pV = pU ≫ f) (e : ChartDiagram B S hS X'.1 Y'.1 a.hom) :
    ChartDiagram B S hS X.1 Y.1 f.hom where
  U := (smallEtalePostcomp B S hS pU hU).obj e.U
  V := (smallEtalePostcomp B S hS pV hV).obj e.V
  g := e.g
  comm := by
    have h : a.hom ≫ pV.hom = pU.hom ≫ f.hom := congrArg (fun m : X' ⟶ Y ↦ m.hom) hsq
    change (e.U.1.hom ≫ pU.hom) ≫ f.hom = yoneda.map e.g ≫ e.V.1.hom ≫ pV.hom
    rw [Category.assoc, ← h, ← Category.assoc, e.comm, Category.assoc]

/-- **The chart-space square of a chart diagram postcomposes the diagram of identity charts back
to the diagram itself.**  The identity chart of the chart space of `d.U`, postcomposed with the
structure morphism of `d.U`, is `d.U`, and likewise on `Y`; the vertical morphism is `d.g` on
both sides.

This is what makes the reduction below land on the comparison at `(f, d)` on the nose, with no
transport. -/
theorem ChartDiagram.postcomp_chartSpaceIdChartDiagram (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    ChartDiagram.postcomp B S hS f (chartSpaceMapOver B S hS d.g)
        (chartToSpace B S hS X d.U) (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS X d.U) (isEtale_chartToSpace B S hS Y d.V)
        (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm)
        (chartSpaceIdChartDiagram B S hS f d) = d :=
  rfl

/-! ### The chart sections of `f`, as a linear map of sections along `a` -/

section

variable {X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (a : X' ⟶ Y') (pU : X' ⟶ X) (pV : Y' ⟶ Y) (hU : IsEtale B S hS pU.hom)
    (hV : IsEtale B S hS pV.hom) (hsq : a ≫ pV = pU ≫ f)
    (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- **The chart sections of `f`, read as a linear map of sections along `a`.**  The sections of
`M|_{Y'}` over the chart of `Y'` of a diagram of the square are the sections of `M` over the
postcomposed chart of `Y`, and likewise for `(f^*M)|_{X'}` over the chart of `X'`; so the chart
component `AlgebraicGeometry.Space.modulePullbackChartFMap` of the unit of Stacks 03D7 at the
postcomposed diagram is a map of sections of the shape a linear map of sections along `a`
demands, and its four fields are the four fields of that chart component. -/
noncomputable def modulePullbackChartSectionFMap :
    ModuleFMap B S hS a
      ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M))
      ((etaleModulePullback B S hS pV hV).obj M) where
  app e := (modulePullbackChartFMap B S hS f M).app
    (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e)
  naturality e e' i j h s := (modulePullbackChartFMap B S hS f M).naturality
    (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e)
    (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e')
    ((smallEtalePostcomp B S hS pU hU).map i) ((smallEtalePostcomp B S hS pV hV).map j) h s
  map_add e := (modulePullbackChartFMap B S hS f M).map_add
    (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e)
  map_smul e := (modulePullbackChartFMap B S hS f M).map_smul
    (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e)

/-- The values of that linear map of sections are the chart sections of `f` at the postcomposed
chart diagrams. -/
theorem modulePullbackChartSectionFMap_app (e : ChartDiagram B S hS X'.1 Y'.1 a.hom)
    (s : ((etaleModulePullback B S hS pV hV).obj M).val.obj (op e.V)) :
    (modulePullbackChartSectionFMap B S hS f a pU pV hU hV hsq M).app e s =
      modulePullbackChartSection B S hS f M
        (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e) s :=
  modulePullbackChartFMap_app B S hS f M
    (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e) s

end

/-! ### The chartwise transpose as a bijection -/

section

variable {X' Y' : AlgebraicSpaces B S hS} (a : X' ⟶ Y')
    (N : Modules.{u, u} B S hS X'.1 X'.2) (M' : Modules.{u, u} B S hS Y'.1 Y'.2)

/-- **The chartwise transpose of a morphism out of a pullback of modules is a bijection.**  It is
the hom-set bijection of the Stacks 03D7 adjunction followed by the module chart correspondence
of Stacks 03G4, both of which are bijections, so a morphism `a^*M' ⟶ N` is exactly a linear map
of sections along `a` from `N` to `M'`. -/
noncomputable def modulePullbackFMapEquiv :
    ((modulePullback B S hS a).obj M' ⟶ N) ≃ ModuleFMap B S hS a N M' :=
  ((modulePullbackAdjunction B S hS a).homEquiv M' N).trans
    (modulePushforwardHomEquiv B S hS a N M')

/-- The bijection is `AlgebraicGeometry.Space.modulePullbackHomFMap`. -/
theorem modulePullbackFMapEquiv_apply (u : (modulePullback B S hS a).obj M' ⟶ N) :
    modulePullbackFMapEquiv B S hS a N M' u = modulePullbackHomFMap B S hS a M' N u :=
  rfl

end

/-! ### The comparison of the square -/

section

variable {X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (a : X' ⟶ Y') (pU : X' ⟶ X) (pV : Y' ⟶ Y) (hU : IsEtale B S hS pU.hom)
    (hV : IsEtale B S hS pV.hom) (hsq : a ≫ pV = pU ≫ f)
    (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- **The base-change comparison of a commuting square with étale verticals**: the morphism

`a^*(M|_{Y'}) ⟶ (f^*M)|_{X'}`

of `𝒪_{X'}`-modules whose chartwise transpose is
`AlgebraicGeometry.Space.modulePullbackChartSectionFMap`, that is, the morphism which carries the
chart section of `a` to the chart section of `f`.

It is defined by the chartwise universal property of the pullback of modules alone, so nothing
about the comparisons of Stacks 03LU or 03LW enters its construction; whether it is an
isomorphism is the statement this file does not prove. -/
noncomputable def modulePullbackEtaleSquareComparison :
    (modulePullback B S hS a).obj ((etaleModulePullback B S hS pV hV).obj M) ⟶
      (etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M) :=
  (modulePullbackFMapEquiv B S hS a
      ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M))
      ((etaleModulePullback B S hS pV hV).obj M)).symm
    (modulePullbackChartSectionFMap B S hS f a pU pV hU hV hsq M)

/-- The chartwise transpose of the comparison is the linear map of sections it was built from. -/
theorem modulePullbackHomFMap_modulePullbackEtaleSquareComparison :
    modulePullbackHomFMap B S hS a ((etaleModulePullback B S hS pV hV).obj M)
        ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M))
        (modulePullbackEtaleSquareComparison B S hS f a pU pV hU hV hsq M) =
      modulePullbackChartSectionFMap B S hS f a pU pV hU hV hsq M :=
  (modulePullbackFMapEquiv B S hS a _ _).apply_symm_apply _

/-- **The defining property of the comparison: it carries the chart section of `a` to the chart
section of `f`.**

The values of the chartwise transpose of a morphism out of a pullback are its values on the
chart sections (`AlgebraicGeometry.Space.modulePullbackHomFMap_app`, through
`AlgebraicGeometry.Space.modulePullbackUnitSection_eq_modulePullbackChartSection`), and the
chartwise transpose of the comparison is the chart section of `f` at the postcomposed
diagram. -/
theorem modulePullbackEtaleSquareComparison_chartSection
    (e : ChartDiagram B S hS X'.1 Y'.1 a.hom)
    (s : ((etaleModulePullback B S hS pV hV).obj M).val.obj (op e.V)) :
    (modulePullbackEtaleSquareComparison B S hS f a pU pV hU hV hsq M).val.app (op e.U)
        (modulePullbackChartSection B S hS a
          ((etaleModulePullback B S hS pV hV).obj M) e s) =
      modulePullbackChartSection B S hS f M
        (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e) s := by
  refine Eq.trans (congrArg
    (fun w ↦ (modulePullbackEtaleSquareComparison B S hS f a pU pV hU hV hsq M).val.app
      (op e.U) w)
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS a
      ((etaleModulePullback B S hS pV hV).obj M) e s).symm) ?_
  refine Eq.trans (modulePullbackHomFMap_app B S hS a
    ((etaleModulePullback B S hS pV hV).obj M)
    ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M))
    (modulePullbackEtaleSquareComparison B S hS f a pU pV hU hV hsq M) e s).symm ?_
  refine Eq.trans (congrArg (fun ξ ↦ ModuleFMap.app ξ e s)
    (modulePullbackHomFMap_modulePullbackEtaleSquareComparison
      B S hS f a pU pV hU hV hsq M)) ?_
  exact modulePullbackChartSectionFMap_app B S hS f a pU pV hU hV hsq M e s

/-- **The comparison carries the base-change comparison at `(a, e)` to the base-change
comparison at `(f, e.postcomp)`.**

Both are the `𝒪_{X'}(e.U)`-linear extension of a chart section, and the comparison is linear on
sections, so the identity is the defining property
`AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison_chartSection` spread over the
tensor product.  The two tensor products are the same: postcomposition changes neither the
structure rings, nor the algebra structure
`AlgebraicGeometry.Space.chartDiagramAlgebra`, nor the sections of the module. -/
theorem modulePullbackEtaleSquareComparison_baseChange
    (e : ChartDiagram B S hS X'.1 Y'.1 a.hom) :
    letI := chartDiagramAlgebra B S hS a e
    ∀ z : TensorProduct (chartRing B S hS Y'.1 Y'.2 e.V) (chartRing B S hS X'.1 X'.2 e.U)
        (((etaleModulePullback B S hS pV hV).obj M).val.obj (op e.V)),
      (modulePullbackEtaleSquareComparison B S hS f a pU pV hU hV hsq M).val.app (op e.U)
          (modulePullbackChartBaseChange B S hS a
            ((etaleModulePullback B S hS pV hV).obj M) e z) =
        modulePullbackChartBaseChange B S hS f M
          (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e) z := by
  let _ := chartDiagramAlgebra B S hS a e
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b s =>
    refine Eq.trans ?_ (modulePullbackChartBaseChange_tmul B S hS f M
      (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e) b s).symm
    rw [modulePullbackChartBaseChange_tmul,
      ((modulePullbackEtaleSquareComparison B S hS f a pU pV hU hV hsq M).val.app
        (op e.U)).hom.map_smul]
    exact congrArg (fun y ↦ b • y)
      (modulePullbackEtaleSquareComparison_chartSection B S hS f a pU pV hU hV hsq M e s)
  | add z w hz hw =>
    simp only [map_add, hz, hw]
    exact (map_add _ z w).symm

/-- **The base-change comparison at the postcomposed diagram is bijective as soon as the one at
the diagram of the square is and the comparison of the square is bijective on sections.**

The first is a factor of the second through
`AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison_baseChange`, and a composite of two
bijections is a bijection. -/
theorem bijective_modulePullbackChartBaseChange_postcomp
    (e : ChartDiagram B S hS X'.1 Y'.1 a.hom)
    (hcomp : Function.Bijective
      ((modulePullbackEtaleSquareComparison B S hS f a pU pV hU hV hsq M).val.app (op e.U)))
    (hb : letI := chartDiagramAlgebra B S hS a e
      Function.Bijective (modulePullbackChartBaseChange B S hS a
        ((etaleModulePullback B S hS pV hV).obj M) e)) :
    letI := chartDiagramAlgebra B S hS f (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e)
    Function.Bijective (modulePullbackChartBaseChange B S hS f M
      (ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e)) := by
  let _ := chartDiagramAlgebra B S hS a e
  have key := modulePullbackEtaleSquareComparison_baseChange B S hS f a pU pV hU hV hsq M e
  refine ⟨fun z w hzw ↦ hb.1 (hcomp.1 ((key z).trans (hzw.trans (key w).symm))), fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hcomp.2 y
  obtain ⟨z, hz⟩ := hb.2 x
  refine ⟨z, ?_⟩
  rw [← key z, hz, hx]

end

/-! ### The presentation-free reduction over an affine chart diagram -/

/-- **The canonical base-change comparison at a quasi-coherent module over a diagram of affine
étale charts is bijective as soon as the comparison of the chart-space square of the diagram is
bijective on the sections over the identity chart.**

No presentation of `M` is assumed, which is the point: the base-change comparison the square's
own bijectivity statement is about lives over the morphism
`AlgebraicGeometry.Space.chartSpaceMapOver` of chart spaces, where the restriction of `M` does
carry a presentation which is right exact on the sections over the identity chart
(`AlgebraicGeometry.Space.exists_presentation_rightExact_app_idEtaleChart`), so
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange` applies there.  The identity
charts postcompose back to `d.U` and `d.V`
(`AlgebraicGeometry.Space.ChartDiagram.postcomp_chartSpaceIdChartDiagram`), so the conclusion is
about the comparison at `(f, d)` itself and nothing is transported. -/
theorem bijective_modulePullbackChartBaseChange_of_bijective_comparison (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (hcomp : Function.Bijective
      ((modulePullbackEtaleSquareComparison B S hS f (chartSpaceMapOver B S hS d.g)
        (chartToSpace B S hS X d.U) (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS X d.U) (isEtale_chartToSpace B S hS Y d.V)
        (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm) M).val.app
        (op (chartSpaceIdChartDiagram B S hS f d).U))) :
    letI := chartDiagramAlgebra B S hS f d
    Function.Bijective (modulePullbackChartBaseChange B S hS f M d) := by
  obtain ⟨P, hgen, -, hex⟩ :=
    exists_presentation_rightExact_app_idEtaleChart B S hS Y M hM d.V hV
  exact bijective_modulePullbackChartBaseChange_postcomp B S hS f
    (chartSpaceMapOver B S hS d.g) (chartToSpace B S hS X d.U) (chartToSpace B S hS Y d.V)
    (isEtale_chartToSpace B S hS X d.U) (isEtale_chartToSpace B S hS Y d.V)
    (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm) M
    (chartSpaceIdChartDiagram B S hS f d) hcomp
    (bijective_modulePullbackChartBaseChange B S hS (chartSpaceMapOver B S hS d.g)
      ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS Y d.V)).obj M)
      (isQuasicoherentOnSite_etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS Y d.V) M hM)
      P (chartSpaceIdChartDiagram B S hS f d) hU hV hgen hex)

end AlgebraicGeometry.Space

end
