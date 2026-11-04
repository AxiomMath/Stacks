module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSectionsExtensions
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientPrestackBackwardTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue

/-!
# The restriction map of the backward functor of Stacks 06WT, on sections

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and let `(𝒢, α)` be a quasi-coherent
module on it.  The backward functor of Stacks 06WT sends `(𝒢, α)` to the module
`ℱ(T, w) = Γ(T, w_small^*𝒢)` on the pointwise quotient `[U/_pR]`, and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuotientPrestackBackwardTransition.lean` lands
the values, their functoriality in `(𝒢, α)`, and the transition
`AlgebraicGeometry.Stack.prestackTransition` that the restriction map has to be built from —
together with both halves of its coherence.

What that file could not do is *read the transition on sections* when the morphism of `[U/_pR]`
has a nontrivial arrow `f : T' ⟶ T` of the site.  The obstruction it records is upstream: the
only route then available carried the Zariski restriction across the base change along `f` with
`AlgebraicGeometry.Space.representedZariskiRestrictionBaseChangeIso`, which was built from a
`Nonempty` through `Nonempty.some`, and nothing — no identity law, no composition law — is
provable about an arbitrary chosen element of a `Nonempty`.

This file takes the second of the two exits that obstruction leaves open: **it does not use the
base change of the Zariski restriction at all.**  The global sections of the restriction of a
module to an étale chart are its sections *over that chart*
(`AlgebraicGeometry.Space.restrictToChartTopSectionsEquiv`, canonical and with no hypothesis on
the module), and a morphism of the site acts on sections over a chart by
`AlgebraicGeometry.Space.modulePullbackChartSection`, the unit of the adjunction of Stacks 03D7
followed by the chart projection of the direct image.  Both are named maps, so the restriction
map below is determined by its arguments.

## Main definitions

* `AlgebraicGeometry.Space.representedSelfChartDiagram`: a morphism `g : T' ⟶ T` of the big fppf
  category, read as a commuting diagram of étale charts of the two represented algebraic spaces
  at their two identity charts.
* `AlgebraicGeometry.Stack.prestackPointSectionsEquiv`: **the sections of the formula of
  Stacks 06WT are the sections of `w_small^*𝒢` over the identity chart of `h_T`**, canonically.
  This is the identification which replaces the chosen witness.
* `AlgebraicGeometry.Stack.prestackChartTransition`: **the restriction map of the backward
  functor along an arbitrary morphism of `[U/_pR]`, on sections over the identity charts** — the
  canonical pullback of a section along `f` followed by the transition
  `AlgebraicGeometry.Stack.prestackTransition`.
* `AlgebraicGeometry.Stack.prestackTransitionSections`: the same map read on
  `AlgebraicGeometry.Stack.prestackPointSections`, which is the shape the packaging asks for.

## Main results

* `AlgebraicGeometry.Space.modulePullbackChartSection_square`: **a commuting square over an
  inverse image is a commuting square on chart sections.**  This is the law of the restriction
  map which *is* available, and it is the naturality in the groupoid module: instantiated at a
  morphism of quasi-coherent modules on the groupoid, with its `hcomm` discharged by
  `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_naturality` — which is where the
  compatibility field of `AlgebraicGeometry.Space.QuasicoherentModule.Hom` is consumed — it says
  that `AlgebraicGeometry.Stack.prestackChartTransition` commutes with
  `AlgebraicGeometry.Stack.prestackPointMap`.

  It is stated at a variable morphism of algebraic spaces and variable modules **and it cannot
  be restated at the representable algebraic space of a test object**, which is the
  obstruction recorded at `AlgebraicGeometry.Stack.prestackArrowTransition_eq`.  The
  specialised statement fails at four strengths: a
  `show` of it exhausts the elaborator's recursion budget; a `trans` of its two halves, and a
  `rw` with `AlgebraicGeometry.Stack.prestackTransition_eq` to put it in the general statement's
  spelling, both exhaust the `whnf` budget; and the instantiation of the general statement
  against the specialised goal exhausts the recursion budget whether the definition is unfolded
  first or not.  The obstruction is the same one in every case: reconciling the composite `≫` of
  two morphisms of `AlgebraicGeometry.Space.Modules` with its action on a section means
  unfolding the composition of that category at
  `AlgebraicGeometry.Space.yonedaSpace`.  So the law is consumed in the general form, exactly as
  the unit and composition laws of the transition itself are.

## What is still missing, precisely

The **identity and composition laws of the restriction map on sections** are not here, and the
reason is not the transition: both of its halves are proved
(`AlgebraicGeometry.Space.groupoidPullbackTransitionAt_identityArrow` and
`AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_comp`).  The missing inputs are the
two coherences of `AlgebraicGeometry.Space.modulePullbackChartSection` itself:

1. its value along an identity morphism of algebraic spaces, which would have to be the
   component at a chart of `AlgebraicGeometry.Space.modulePullbackIdIso`;
2. its value along a composite, which would have to be the component at a chart of
   `AlgebraicGeometry.Space.modulePullbackCompIso`.

Neither exists.  For the unit of the adjunction alone the composite case is available —
`AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom` — but
`modulePullbackChartSection` is that unit followed by
`AlgebraicGeometry.Space.moduleChartProjection`, the chart projection of the direct image, and
the direct image's own composition law on sections over a chart is the step that the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/StructureSheafPullbackUnitCorepresentable.lean` record as
missing: the library has the naturality of
`CategoryTheory.MorphismOfTopoi.pushforwardTerminalHomEquiv` in the sheaf but no description of
its values on sections, so the chain stops one step short of
`AlgebraicGeometry.Space.modulePushforwardCounitApp`.  So what remains is two
coherences of the chart section of an inverse image, stated against
`AlgebraicGeometry.Space.modulePullbackIdIso` and
`AlgebraicGeometry.Space.modulePullbackCompIso`, and they are a statement about the direct image
on the small étale site rather than anything about groupoids.

## No tag is registered here

Every declaration below is a component of the backward functor of Stacks 06WT, which is one of
the two functors of its proof, so none of them carries `@[stacks 06WT]`; that attribute sits on
`AlgebraicGeometry.Stack.nonempty_quasicoherentEquivalenceGroupoid_of_missingInputs` and nothing
here alters it.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of the big fppf category, read as a commuting diagram of étale charts of the
two represented algebraic spaces.**  Both charts are identity charts
(`AlgebraicGeometry.Space.selfChart`), whose underlying objects of the site are the source and
target of the morphism, so the vertical morphism of the diagram is the morphism itself and the
square commutes because both of its other two sides are identities.

This is the chart diagram at which `AlgebraicGeometry.Space.modulePullbackChartSection` gives the
pullback of a global section along a morphism of the site. -/
def representedSelfChartDiagram {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    ChartDiagram B S hS (yoneda.obj T') (yoneda.obj T)
      (representedSpaceMap B S hS g).hom where
  U := selfChart B S hS T'
  V := selfChart B S hS T
  g := g
  comm := (Category.id_comp (yoneda.map g)).trans (Category.comp_id (yoneda.map g)).symm

/-- **A commuting square over an inverse image is a commuting square on chart sections.**  Let
`g : X ⟶ Y` be a morphism of algebraic spaces, let `φ : M ⟶ M'` be a morphism of `𝒪_Y`-modules,
and let `τ`, `τ'` be morphisms out of the two inverse images which a morphism `ψ` of their
targets makes commute with `g^*φ`.  Then on sections over the two charts of a commuting diagram
of charts, `ψ` after `τ` after the chart section of `g` is `τ'` after the chart section of `g`
after `φ`.

The chart section of an inverse image is natural in the module
(`AlgebraicGeometry.Space.modulePullbackChartSection_map`), which moves `φ` across it, and the
square `hcomm` moves `ψ` across the rest.

**This is stated at variable modules and a variable morphism on purpose.**  Its one consumer,
`AlgebraicGeometry.Stack.prestackChartTransition_map`, needs it at the represented algebraic
space of a test object, and there the step cannot be taken: reconciling the composite `≫` of two
morphisms of `AlgebraicGeometry.Space.Modules` with its action on a section requires unfolding
the composition of that category, and at
`AlgebraicGeometry.Space.yonedaSpace` — every category instance in sight carrying
`AlgebraicGeometry.isAlgebraicSpace_yoneda` inside a small étale ringed site — that exhausts the
elaborator's `whnf` budget.  This happens at the `show` of the specialised statement and
again at a `trans` of its two halves.  Here there is nothing concrete to unfold, and the
specialisation is a plain instantiation. -/
theorem modulePullbackChartSection_square {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    {M M' : Modules.{u, u} B S hS Y.1 Y.2} {P P' : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ M') (τ : (modulePullback B S hS g).obj M ⟶ P)
    (τ' : (modulePullback B S hS g).obj M' ⟶ P') (ψ : P ⟶ P')
    (hcomm : (modulePullback B S hS g).map φ ≫ τ' = τ ≫ ψ)
    (d : ChartDiagram B S hS X.1 Y.1 g.hom) (s : M.val.obj (op d.V)) :
    ψ.val.app (op d.U) (τ.val.app (op d.U) (modulePullbackChartSection B S hS g M d s)) =
      τ'.val.app (op d.U) (modulePullbackChartSection B S hS g M' d (φ.val.app (op d.V) s)) := by
  rw [← modulePullbackChartSection_map B S hS g M φ d s]
  exact (congrArg (fun m ↦ m.val.app (op d.U) (modulePullbackChartSection B S hS g M d s))
    hcomm).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-- **The sections of the formula of Stacks 06WT are the sections of `w_small^*𝒢` over the
identity chart of `h_T`.**  The value `Γ(T, w_small^*𝒢)` of the backward functor is the global
sections of the restriction of `w_small^*𝒢` to the Zariski site of the representing scheme, and
the global sections of a chart restriction are the sections over the chart
(`AlgebraicGeometry.Space.restrictToChartTopSectionsEquiv`); the chart here is the identity chart
of `h_T`, that being the chart `AlgebraicGeometry.Space.representedZariskiRestriction` restricts
along.

The identification is canonical and asks nothing of the module — in particular not
quasi-coherence, which every base change of the Zariski restriction needs.  It is at the level of
additive groups, which is what the `sections` field of
`AlgebraicGeometry.Stack.PrestackBackwardFunctor` asks for. -/
def prestackPointSectionsEquiv (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
    (w : G.objects.1.obj (op T)) :
    (prestackPointSections G M T w : Type u) ≃+
      ((prestackPointModule G M T w).val.obj (op (Space.selfChart C S hS T)) : Type u) :=
  Space.restrictToChartTopSectionsEquiv C S hS
    ⟨yoneda.obj T, isAlgebraicSpace_yoneda C S hS T⟩ (prestackPointModule G M T w)
    (Space.selfChart C S hS T)

/-- **The restriction map of the backward functor of Stacks 06WT, on sections over the identity
charts.**  For a morphism `(T', w') ⟶ (T, w)` of the pointwise quotient — by Stacks 02XV an arrow
`f : T' ⟶ T` of the site together with a `T'`-point `a` of the arrow space whose target is `w`
restricted along `f` — this carries a section of `w_small^*𝒢` over the identity chart of `h_T` to
a section of `w'_small^*𝒢` over the identity chart of `h_{T'}`.

It is the canonical pullback of a section along `f`
(`AlgebraicGeometry.Space.modulePullbackChartSection` at
`AlgebraicGeometry.Space.representedSelfChartDiagram`) followed by the action of the transition
`AlgebraicGeometry.Stack.prestackTransition` on sections over the identity chart of `h_{T'}`.
Neither step is a chosen witness, and no base change of the Zariski restriction appears. -/
def prestackChartTransition (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) {T' T : BigFppfOver C S hS} (f : T' ⟶ T)
    (w : G.objects.1.obj (op T)) (a : G.arrows.1.obj (op T'))
    (ha : G.target.hom.app (op T') a = G.objects.1.map f.op w)
    (s : (prestackPointModule G M T w).val.obj (op (Space.selfChart C S hS T))) :
    (prestackPointModule G M T' (G.source.hom.app (op T') a)).val.obj
      (op (Space.selfChart C S hS T')) :=
  (prestackTransition G M f w a ha).val.app (op (Space.selfChart C S hS T'))
    (Space.modulePullbackChartSection C S hS (Space.representedSpaceMap C S hS f)
      (prestackPointModule G M T w) (Space.representedSelfChartDiagram C S hS f) s)

/-- **The restriction map of the backward functor of Stacks 06WT, on the values of the source's
formula.**  `AlgebraicGeometry.Stack.prestackChartTransition` conjugated by the identification
`AlgebraicGeometry.Stack.prestackPointSectionsEquiv` of those values with the sections over the
identity charts.

This is the map the packaging of the backward functor into a presheaf of modules needs along a
morphism of `[U/_pR]` with a nontrivial arrow of the site; along a morphism over the identity of
the test object it is `AlgebraicGeometry.Stack.prestackArrowTransitionSections`. -/
def prestackTransitionSections (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) {T' T : BigFppfOver C S hS} (f : T' ⟶ T)
    (w : G.objects.1.obj (op T)) (a : G.arrows.1.obj (op T'))
    (ha : G.target.hom.app (op T') a = G.objects.1.map f.op w)
    (s : prestackPointSections G M T w) :
    prestackPointSections G M T' (G.source.hom.app (op T') a) :=
  (prestackPointSectionsEquiv G M T' (G.source.hom.app (op T') a)).symm
    (prestackChartTransition G M f w a ha (prestackPointSectionsEquiv G M T w s))

end AlgebraicGeometry.Stack

end
