module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# Gluing across a thickening: from schemes to algebraic spaces

Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism, let `Y' = Y ⨿_X X'`, and
let `V' = V ⨿_U U'` be the scheme glued from a triple `(V, U', φ)`, with `V' ⟶ Y'` the induced
morphism.  [Stacks Project, Tag 07RX] says that `V' ⟶ Y'` is locally of finite type, flat, flat
and locally of finite presentation, smooth or étale exactly when both `V ⟶ Y` and `U' ⟶ X'` are.
This file descends those five clauses to morphisms of *algebraic spaces* over `S`.

Each of the five properties of a morphism of algebraic spaces is, by definition, the
corresponding property of the morphism of schemes underlying every commuting square of étale
scheme charts, so a single commuting square of charts whose chart of the source is surjective
computes it ([Stacks Project, Tag 03MJ]).  Given such a square for each of the three morphisms
`V' ⟶ Y'`, `V ⟶ Y` and `U' ⟶ X'`, in which the three morphisms of charts carry the
scheme-level gluing situation of
`StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluingSquare`, the five clauses for
algebraic spaces follow from the five clauses for schemes.

## Main definitions

* `AlgebraicGeometry.Space.EtaleChartSquare`: a commuting square of étale scheme charts of a
  morphism of presheaves whose chart of the source is surjective — condition (2) of
  [Stacks Project, Tag 03MJ] without the property.
* `AlgebraicGeometry.Space.ThickeningAffineGluingChart`: three such squares for the three
  morphisms of [Stacks Project, Tag 07RX], together with the scheme-level gluing situation
  carried by the three morphisms of charts.

## Main results

* `AlgebraicGeometry.Space.EtaleChartSquare.holdsOnEveryEtaleChart_iff`: an étale-local property
  of a morphism of presheaves is the property of the morphism of charts of one such square.
* `AlgebraicGeometry.Space.ThickeningAffineGluingChart.isLocallyOfFiniteType_iff`,
  `isFlat_iff`, `isFlat_and_isLocallyOfFinitePresentation_iff`, `isSmooth_iff` and
  `isEtale_iff`: the five clauses for morphisms of algebraic spaces over `S`, given a chart
  presentation.

## What is not covered

[Stacks Project, Tag 07W3], the algebraic-space form of [Stacks Project, Tag 07RX], is **not**
registered here, and none of the statements below claims it.  Tag 07W3 is stated in the
situation of [Stacks Project, Tag 07W0], where `Y'` is the pushout of a thickening and an
affine morphism of *algebraic spaces* and `V'` is the pushout of the triple; the proof the
source gives reduces to the scheme case along the surjective étale chart of `Y'` produced by
the *construction* of that pushout in [Stacks Project, Tag 07VX], which exhibits `Y'` as the
quotient of an étale equivalence relation on a pushout of scheme charts.  That construction is
what a `AlgebraicGeometry.Space.ThickeningAffineGluingChart` records, and in this library it is
not available: `AlgebraicGeometry.Space.isPushout_quotient_of_thickeningAffineAtlas` produces it
only from a `AlgebraicGeometry.Space.ThickeningAffineAtlas`, and
`AlgebraicGeometry.Space.HasThickeningAffineAtlases` is undischarged.  The chart presentation of
the *triple* needs more still: the chart of `U'` has to restrict to the chart of `U` along the
thickening `U ⟶ U'`, which is [Stacks Project, Tag 05ZS], the lemma the source's proof of
Tag 07W0 cites for exactly this step.  That step is no longer the obstruction: Tag 05ZS is
available on the small étale sites of scheme charts at a thickening of *arbitrary* order, as
`AlgebraicGeometry.Space.smallEtalePullback_isEquivalence_of_isThickeningHom`, and in the
chart-lift form as
`AlgebraicGeometry.Space.exists_etaleChart_lift_of_isThickeningHom`, both granted only the two
inputs `h09YA` and `hFinitePresentation` that [Stacks Project, Tag 05ZR] carries.
What is still missing for `AlgebraicGeometry.Space.HasThickeningAffineAtlases` is set out under
`What is not covered` in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces`: the two scheme pushouts
as objects of the size-bounded site, that the pushed-out relation is an étale equivalence
relation, and a compatible choice of the three kernel pairs.  Neither presentation follows from
the universal property of the
two pushouts alone — that property speaks only about morphisms *out of* `Y'` and `V'`, while a
chart is a morphism *into* them — so the statements below take the presentation as data; they
are the descent step of Tag 07W3 and nothing more.

*What the landing of Tag 07VY changed, and what it did not.*  The paragraph above was written
when the gluing functor `G` did not exist for algebraic spaces, so that the final assertion of
Tag 07W3 could not even be *written* here.  It now exists:
`AlgebraicGeometry.Space.pushoutGluingFunctor`,
`AlgebraicGeometry.Space.pushoutBaseChangeFunctor` and
`AlgebraicGeometry.Space.pushoutGluingAdjunction`, in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesGluing`, carry Tag 07VY
granted `AlgebraicGeometry.Space.HasThickeningAffineAtlases` as `hatlas`, so the counit
`G(F(W')) ⟶ W'` is writable and the statement of Tag 07W3 is expressible at this level.  Its
counit clause is now **proved**, as
`AlgebraicGeometry.Space.isIso_pushoutGluingAdjunction_counit_of_isFlat` in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFlatPushout`, which carries
Tag 07W3 for that clause granted the same `hatlas`; see *What the assembly proves* at the end
of this section.  The paragraphs between here and there record the route and also price what
is still open.  Tag 07W3 is still not registered *in this module*,
and none of the statements below claims it.

`hatlas` is `Nonempty (AlgebraicGeometry.Space.ThickeningAffineAtlas …)`: it yields *some*
atlas of each thickening-and-affine span, with no control over which charts.  What the source's
proof of the counit assertion needs is an atlas of the span of the triple `F(W')` whose charts
of `W' ×_{Y'} Y` and `W' ×_{Y'} X'` are the base changes along `Y_1 ⟶ Y'_1` and `X'_1 ⟶ Y'_1`
of **one prescribed** chart `W'_1` of `Y'_1 ×_{Y'} W'`; only then is the pushout of those charts
identified with `W'_1` — by `Stacks.Pushout.gluingCounit_isIso_of_flat`, since `W'_1` is flat
over the scheme pushout `Y'_1` — and only then is the composite
`yoneda.obj W'_1 ⟶ G(F(W')) ⟶ W'` the chart of `W'`, which is what makes it étale and lets
[Stacks Project, Tag 03FS] conclude.  For an atlas with unrelated charts that composite is not
étale and the argument does not start.  `AlgebraicGeometry.Space.ThickeningAffineGluingChart`
is that prescribed presentation; it is the cube diagrams 81.6.5.1 and 81.6.5.2 of the *proof*
of Tag 07W0 — Stacks equation tags 07W1 and 07W2 — and not the assertion of Tag 07VX, which is
only that a pushout exists.  Note also that
`AlgebraicGeometry.Space.isPushout_quotient_of_thickeningAffineAtlas` asserts of its chart
squares only that they *commute* (`A.p' ≫ a.hom = yoneda.map A.a ≫ qm` and
`A.q ≫ b.hom = yoneda.map A.b ≫ qm`), whereas diagram 81.6.5.1 asserts them cartesian, which
is what `EtaleChartSquare` and the fields `isPullback_i`, `isPullback_f` below require.

*The one route that is circular, and must not be carried.*  Isomorphisms are local at the
target for the fppf precoverage, `AlgebraicGeometry.Space.isomorphisms_isLocalAtTarget_fppf`,
so it is tempting to descend the counit along a cover `T ⟶ W'`.  That reduction needs the base
change of the counit at `W'` along `T ⟶ W'` to be the counit at `T`, that is, it needs the
pushout of algebraic spaces to commute with étale base change.  No such lemma exists in this
tree at either level, and it is not a carriable input: for `T` étale over `Y'` the assertion
`T ≅ (T ×_{Y'} Y) ⨿_{T ×_{Y'} X} (T ×_{Y'} X')` *is* the counit of Tag 07VY being an
isomorphism at the flat object `T`, i.e. a case of Tag 07W3's own final assertion.

*What the route to the counit assertion costs, step by step.*  Every step has an available
input, so what is left is construction volume rather than a missing result.  (i) From the atlas
`A` that `hatlas` gives for `i, f`, prove the two chart squares of diagram 81.6.5.1 cartesian
with Tag 07S3, `AlgebraicGeometry.Space.isPullback_chart_of_isPullback_source`, whose one
missing input is cartesianness of the kernel-pair squares `IsPullback A.bR A.sY A.s A.b` and
`IsPullback A.aR A.s' A.s A.a`.  The first is the private
`isPullback_of_isThickening_of_etale` of
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces` (a commuting square of
two thickenings over two étale morphisms is cartesian), and it does not in fact have to be
restated: the Y-side chart square it yields is already derived in that module, as the step
`hbase : IsPullback (yoneda.map A.b) A.q qm b.hom` inside
`AlgebraicGeometry.Space.pushout_inr_isThickening`, where it is consumed and then discarded
rather than exported.

Two points about the second square matter for the route.  One might expect it to need a
scheme-level lemma derivable from
`Stacks.Pushout.gluingCounit_isIso_of_flat` on the shape of
`AlgebraicGeometry.pushoutMap_left_isPullback`.  First, `IsPullback A.aR A.s' A.s A.a` is not
derivable from an atlas *at all*, by any route: `AlgebraicGeometry.Space.ThickeningAffineAtlas`
never pins `R₀` down.  Its only fields mentioning `R₀` are `R₀`, `kR`, `gR`, `isThickening_kR`,
`isAffineHom_gR` and `isPushout_relation`; there is no `kernelPair_X` field and nothing
identifies `R₀` with `R' ×_{U'} U` or with `T ×_V U`, so the triple over the span `(k, g)` that
the scheme-level unit isomorphism of Tag 07RV would need is not even assembled.  Strengthening
the structure to pin it is not available either: `HasThickeningAffineAtlases` is the carried
hypothesis of the four Tag 07VY carriers in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesGluing`, and adding a
field weakens every one of them.  Second, the square that is actually wanted — the X'-side
chart square `IsPullback (yoneda.map A.a) A.p' qm a.hom` — does not need the kernel pairs, and
needs no new scheme-level lemma.  Both `yoneda.obj A.U'` along `A.p'` and the base change of
`yoneda.obj A.P` along `X' ⟶ E` are objects of the spaces-étale site of `X'`, the comparison of
the two restricts along `i` to an isomorphism (`A.isPullback_thickening` identifies the first
restriction with `U`, and `hbase` together with `A.isPullback_affine` identifies the second with
`U` as well, since `P ×_E X = (P ×_E Y) ×_Y X = V ×_Y X`), and
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickeningHom` — Tag 05ZH, whose
only hypothesis is the thickening, with no `h09YA` and no `hFinitePresentation` — is an
equivalence and so reflects that isomorphism.  So the lateral squares of the cube cost one
lemma, not a missing result.  (ii) Choose `W'_1`
surjective étale over `Y'_1 ×_{Y'} W'` and base change it to get the charts of the triple; the
three items recorded as missing for an atlas under `What is not covered` in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces` do **not** bite for this
atlas: its `P` is `W'_1` and its `Rel` is the
kernel pair `W'_1 ×_{W'} W'_1`.  That claim holds, with three details of
this account made precise in *The three absences in the flat case, checked* below.
(iii) `isPushout_quotient_of_thickeningAffineAtlas` on that atlas, with uniqueness of the
pushout against `AlgebraicGeometry.Space.pushoutGluingFunctor_obj_isPushout`, gives
`yoneda.obj W'_1 ⟶ G(F(W'))` surjective étale over the chart of `W'`.  (iv) The counit is then
étale by Tag 03FS condition (2),
`AlgebraicGeometry.Space.isEtale_iff_exists_source_chart`, and an isomorphism by Tag 05W5,
`AlgebraicGeometry.Space.isIso_of_isEtale_of_universallyInjective_of_isSurjective`, or by
`AlgebraicGeometry.Space.isIso_of_isEtale_of_isSurjective_baseChange_isIso` with the unit
isomorphism of Tag 07W0 supplying the base change.  Step (ii) is the one of the size of the
Tag 07VX module itself, which is why no carrier is registered here yet.

*The three absences in the flat case, checked.*  The claim of (ii) — that the three items
missing for a general atlas do not bite for the prescribed flat-case one — has been checked
against the tree, and it holds.  Three details of the account in (ii) are nevertheless wrong,
and the corrections change what step (ii) costs.

* **Size: escapes.**  `P := W'_1` is an object of the site because it is produced by
  `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas` from the algebraic space
  `Y'_1 ×_{Y'} W'`, which is one by `AlgebraicGeometry.Space.isAlgebraicSpace_pullback`; and
  `Rel := W'_1 ×_{W'} W'_1` is one by
  `AlgebraicGeometry.Space.exists_kernelPair_of_etale_atlas` applied to the chart
  `W'_1 ⟶ W'`, which is surjective étale as the composite of the chart of `Y'_1 ×_{Y'} W'`
  with the base change of `qm`.  Nothing has to be known about the size of a scheme pushout:
  the fields `isPushout_chart` and `isPushout_relation` are `IsPushout` properties of a
  *square*, invariant under isomorphism of the cocone point, so an isomorphism with the pushout
  is all they need.
* **Étale equivalence relation: escapes, but not by the route named in (ii).**
  `StacksDraft.AlgebraicGeometry.Groupoids.QuotientSheaf.SpacesDictionary` has no kernel-pair
  converse at all: every producer of `Stacks.Groupoids.IsEtaleEquivalenceRelation` there routes
  from a `Stacks.Groupoids.GroupoidScheme`.  The lemma that does it is
  `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_etaleImage`, which needs only the
  presheaf-étaleness of the chart and the kernel-pair square — not surjectivity, not
  `IsAlgebraicSpace` — and is applied with the two projections transposed, since
  `AlgebraicGeometry.Space.relation B S hS s t` is `prod.lift (map t) (map s)`.  Its
  equivalence-relation half alone is
  `AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback`, Stacks 0262 part (1).  So this
  absence is discharged by the dictionary between an algebraic space and the kernel pair of a
  chart of it, and *not* by anything about a pushed-out relation — which remains unproved and is
  not needed.
* **The three kernel pairs: escapes, more cheaply than (ii) says.**
  `AlgebraicGeometry.Space.ThickeningAffineAtlas` has no `kernelPair_X` field, so `R₀` may be
  taken to be whatever the counit application hands over and nothing has to identify it with a
  base change of `Rel` to `X`.  The item that *does* have content is the identification of `R'`
  and `T`, and it is priced in the next paragraph.

*Two corrections to the relation half of (ii).*  First, `Rel = W'_1 ×_{W'} W'_1` is **not**
flat over `Y'_1` in any usable sense: it carries two morphisms to `Y'_1`, one per projection,
and the counit at the span `(A.k, A.g)` — the span whose pushout is `Y'_1` — would exhibit it as
the pushout of its base changes to `A.U'`, `A.U` and `A.V`, which are not the kernel pairs that
`isPushout_relation` asks for.  The correct span is `(A.kR, A.gR)`, whose pushout is `A.Rel` by
the atlas field `isPushout_relation` and which is thickening-and-affine by `A.isThickening_kR`
and `A.isAffineHom_gR`; `Rel ⟶ A.Rel` exists because `A.Rel` is the kernel pair of the chart
`qm` of `Y'`, and it is flat because it factors as the surjective étale
`W'_1 ×_{W'} W'_1 ⟶ (yoneda.obj A.P ×_{Y'} W') ×_{W'} (yoneda.obj A.P ×_{Y'} W')`, which is
`yoneda.obj A.Rel ×_{Y'} W'`, followed by the base change of the flat `W' ⟶ Y'`.  So the route
applies the counit **twice, at two different spans**, not once at `W'_1` and once at its kernel
pair over the same pushout.

Second, `isPushout_relation` for the new atlas then needs `Rel ×_{A.Rel} A.R'` to be the kernel
pair of the chart `p'` of `W' ×_{Y'} X'`, and that holds only through a step (ii) did not price:
`A.R' ≅ A.Rel ×_{Y'} X'`, which follows from `A.kernelPair_X'`, from the X'-side cartesian chart
square and from `A.Rel` being the kernel pair of `qm` — and symmetrically `A.T ≅ A.Rel ×_{Y'} Y`
from `A.kernelPair_Y` and the Y-side square.  Those three inputs are now available together from
`AlgebraicGeometry.Space.exists_pushout_chart_of_thickeningAffineAtlas`, which exists for this
reason: `isPushout_quotient_of_thickeningAffineAtlas` asserts its chart squares only commute,
and the Tag 07W1 carrier asserts them cartesian but quantifies over the atlas and so discards
`A.Rel`.  That the canonically constructed `A.R' ⟶ A.Rel` is `A.aR` is forced by `A.aR_s` and
`A.aR_t`, a morphism into a kernel pair being determined by its two legs.

*The scheme-level engine.*  Step (ii) consumes the counit isomorphism as a *pushout
square*, not as an isomorphism of adjunction values.  The first form of that in the tree was
`Stacks.Pushout.isPushout_baseChange_of_flat`: a scheme flat over `Y' = Y ⨿_X X'` is the pushout
of its own two base changes along their common restriction to `X`.  It is unconditional, but it
is **not** the form step (ii) can consume, for two reasons.  Its two legs `v` and `u'` are
existentially quantified and constrained only by `v ≫ W'.hom = …` and `u' ≫ W'.hom = …`, so nothing
in that statement identifies either of them with the projection of a base change, and a square over
prescribed charts cannot be compared with it; and its span and cocone point are the *canonical*
`pushout i f` and canonical pullbacks, whereas `ThickeningAffineAtlas.isPushout_chart` and
`isPushout_relation` carry an arbitrary `CategoryTheory.IsPushout` square over objects of the site.
Both gaps are closed; see the account of step (ii) below.

*What the atlas needs that `isPushout_baseChange_of_flat` does not give directly, and where it
comes from.*  The two legs of the pushout square it produces are the pushout inclusions of the
glued scheme composed with the counit, and the atlas fields `isPushout_chart` and
`isPushout_relation` need the square over a span of *prescribed* charts instead.  Transporting it
requires identifying those legs with the canonical projections
`pullback.fst W'.hom (pushout.inl i f)` and `pullback.fst W'.hom (pushout.inr i f)`, and nothing
is exported about the counit beyond `Stacks.Pushout.gluingCounit_isAffine` and
`Stacks.Pushout.gluingCounit_isIso_of_flat`.  The identification is nevertheless available, and
it is `Stacks.Pushout.gluing_components_isPullback`: the two components of a triple *are* the base
changes of the glued scheme, with the two pushout inclusions as the projections.  It was private;
it is now public, for this use.

With it the transport is a bounded argument and needs no counit chase — and it needs
substantially less than the route this paragraph used to describe, which went through a
comparison morphism `χ : G(T₀) ⟶ W'_1` produced by the pushout property of
`Stacks.Pushout.gluingFunctor_obj_isPushout`, argued `F(χ)` to be an isomorphism, and invoked the
triangle identity with `Stacks.Pushout.gluingAdjunction_unit_app_isIso` together with naturality
of the counit.  **None of that is required.**  No triple has to be built, no comparison morphism
has to be produced, and the unit of the adjunction does not enter.  Compose
`gluing_components_isPullback` with the counit isomorphism of
`Stacks.Pushout.gluingCounit_isIso_of_flat` and the two *canonical* base changes of `W'_1` become
cartesian squares whose cocone point is `W'_1` itself; uniqueness of a pullback then yields the
comparison isomorphisms with the prescribed objects, and
`CategoryTheory.IsPushout.of_iso'` finishes.  The one step that is not automatic is that the
identification of the span apex read off the `Y`-side square agrees with the one read off the
`X'`-side square, and that is supplied by the single extra hypothesis `jY ≫ cY = jX' ≫ cX'`,
which holds by construction wherever the statement is applied.  A further economy the old
account missed: only the *commutativity* of the `X'`-side square is used, not its
cartesianness — the apex is pinned by the `Y`-side square alone.  The whole transport is about
forty lines, and it runs identically for the relation half at the span `(A.kR, A.gR)`.

So what remains for the prescribed atlas is construction volume — the two transports just
described, the three chart identifications, the forty-odd fields — and not a missing result.  No
part of it is carriable as another tag's hypothesis: it is Tag 07VX's own construction.

*What is proved for step (ii), and what is left.*  Five declarations of
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFlatPushout` discharge the named
inputs of step (ii).  All five are unconditional in the atlas and the chart data — none of them
assumes any part of Tag 07W3 — and all five are axiom-clean, depending only on `propext`,
`Classical.choice` and `Quot.sound`.

* `Stacks.Pushout.isPushout_of_flat_of_isPullback`: the engine in the only form that is
  consumable, namely over a *prescribed* span.  A scheme `W` flat over `Y' = Y ⨿_X X'` is the
  pushout of any prescribed pair of cartesian base changes along `Y ⟶ Y'` and `X' ⟶ Y'`, glued
  along any prescribed common restriction to `X`.
* `Stacks.Pushout.isPushout_of_flat_of_isPullback_of_isPushout`: the same over an arbitrary
  cocartesian square instead of the canonical `pushout k g`, which is what the two atlas
  fields carry.
* `AlgebraicGeometry.Space.exists_flat_chart_of_thickeningAffineAtlas`: the source's *choose a
  scheme `W'_1` and a surjective étale morphism `W'_1 → Y'_1 ×_{Y'} W'`*.  It produces the site
  object, a morphism `χ : W'_1 ⟶ A.P` of the site that is **flat** on schemes, and a surjective
  étale chart `W'_1 ⟶ W'`.  This is the one place where flatness of `W'` enters, and it is the
  hypothesis the engine needs.  The three *size* escapes recorded above are confirmed: `A.P` is
  already an object of the site and `A.P ×_E W'` is an algebraic space by Stacks 02X2, so no
  statement about the size of a scheme pushout is used anywhere.
* `AlgebraicGeometry.Space.exists_chart_pullback_of_isPullback`: one statement covering all
  three chart squares — for `χ` lying over `W'_1 ⟶ W'` and `z : Z ⟶ A.P` exhibiting `Z` as a
  base change `A.P ×_E D`, the fibre product `W'_1 ×_{A.P} Z` of the site is the base change
  `W'_1 ×_{W'} (W' ×_E D)`.  Instantiated at `A.a`, at `A.b` and at their common restriction it
  gives the three charts of the triple with their chart squares, and hence their surjectivity
  and étaleness by base change of `W'_1 ⟶ W'`.
* `AlgebraicGeometry.Space.isPullback_R'_of_thickeningAffineAtlas` and
  `AlgebraicGeometry.Space.isPullback_T_of_thickeningAffineAtlas`: the two identifications the
  paragraph *Two corrections to the relation half of (ii)* above says step (ii) did not price.
  `A.R'` is the base change `A.Rel ×_E X'` with `A.aR` as its projection, and `A.T` is
  `A.Rel ×_E Y` with `A.bR`.  They cost about fifteen lines each: they are pullback algebra in
  the atlas's own fields, since `A.Rel` is the kernel pair of `qm`, `A.R'` that of `A.p'` and
  `A.U'` is `A.P ×_E X'`, and `A.aR_s` with `A.aR_t` force the canonical projection to be
  `A.aR`.  So that paragraph's diagnosis was right and its pricing was high.

What is **not** formalized is the assembly: the forty-odd fields of the atlas of the triple itself,
and in particular the relation half.  Relative to the pieces above, what is left is
(a) the chart objects `W'_1 ×_{A.P} A.U'`, `W'_1 ×_{A.P} A.V`, `W'_1 ×_{A.P} A.U` with their
chart maps and the two fields `isPullback_affine` and `isPullback_thickening`, which are
instantiations of `exists_chart_pullback_of_isPullback` plus base change of `A.k` and `A.g`;
(b) the field `isPushout_chart`, an instantiation of
`isPushout_of_flat_of_isPullback_of_isPushout` at `A.isPushout_chart`;
(c) the relation half: the kernel pairs by
`AlgebraicGeometry.Space.exists_kernelPair_of_etale_atlas`, the morphism
`W'_1 ×_{W'} W'_1 ⟶ A.Rel` induced by `hqm` from `(fst ≫ χ, snd ≫ χ)`, **the flatness of that
morphism** — which the route above prices as a surjective étale map onto
`yoneda.obj A.Rel ×_E W'` followed by a base change of the flat `W' ⟶ E`, and which is the one
remaining step with content rather than volume — and then `isPushout_relation` by the engine at
the span `(A.kR, A.gR)` using the two identifications just established;
(d) `etaleRelation` from `isEtaleEquivalenceRelation_etaleImage` with the projections
transposed;
(e) the chain out: the atlas into `isPushout_quotient_of_thickeningAffineAtlas`, uniqueness of
the pushout against `pushoutGluingFunctor_obj_isPushout`, Tag 03FS condition (2) and Tag 05W5.
No step of (a)–(e) is blocked by a missing declaration; the blocker is volume.

*What the assembly proves, and the two places the pricing above is wrong.*  Steps (a)–(e) are
done, in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFlatPushout`:
`AlgebraicGeometry.Space.exists_thickeningAffineAtlas_of_isFlat` is (a)–(d), the prescribed
atlas of the span of the triple `F(W')` for `W'` flat over the pushout, together with the
surjective étale chart `pW` of `W'` on its pushout of charts and the assertion that the
relation of the atlas **is** the kernel pair of `pW`;
`AlgebraicGeometry.Space.isPushout_of_isFlat_of_thickeningAffineAtlas` is the first half of (e),
that `W'` is a pushout of that span; and
`AlgebraicGeometry.Space.isIso_pushoutGluingAdjunction_counit_of_isFlat` reads that off as the
counit assertion and carries Tag 07W3 for it.  All three are axiom-clean and assume no part of
Tag 07W3 — in particular no prescribed atlas is hypothesised, it is constructed.

Two corrections to the pricing above.  First, step (e) does **not** need Tag 03FS condition (2)
or Tag 05W5, which (iv) and (e) both price for it, and does not need the unit isomorphism of
Tag 07W0 either.  The comparison between `W'` and the pushout that
`AlgebraicGeometry.Space.isPushout_quotient_of_thickeningAffineAtlas` builds from the atlas is
an isomorphism for a reason that mentions neither étaleness nor universal injectivity of it:
the prescribed chart `pW` of `W'` and the chart `qm₂` of that pushout are surjective étale
charts of the *same* scheme with the *same* kernel pair, so each sheaf is the quotient of that
scheme by that relation and the two descents between them compose to the identity either way,
by the uniqueness half of
`AlgebraicGeometry.Space.existsUnique_desc_of_surjective_etale_atlas`.  That is why the atlas
built in (c) must take `Rel` to be the kernel pair of `pW` and nothing weaker.

Second, (c) understates the flatness step and (ii) names the wrong intermediate object for it.
Flatness of `Rel = W'_1 ×_{W'} W'_1 ⟶ A.Rel` is *not* obtained by factoring through
`yoneda.obj A.Rel ×_{Y'} W'`, which the account above describes: that object is a fibre product
of algebraic spaces and the morphism to it is not exhibited as a base change of anything the
chart data provides.  What works is the factorisation through the **scheme** `W'_1 ×_{A.P} A.Rel`
along `A.s`: its projection to `A.Rel` is the base change of the flat `χ`, and the morphism
`Rel ⟶ W'_1 ×_{A.P} A.Rel` is the base change of the chart `W'_1 ⟶ A.P ×_{Y'} W'` itself,
hence étale.  Exhibiting it as that base change needs the fibre product `A.P ×_{Y'} W'` and its
chart as *data*, which no output of
`AlgebraicGeometry.Space.exists_flat_chart_of_thickeningAffineAtlas` records — only the
composites `χ` and `W'_1 ⟶ W'` — so the chart theorem had to be restated as
`AlgebraicGeometry.Space.exists_flat_chart_pullback_of_isFlat`, from which the old one is now
deduced.  That is the one step of the assembly with mathematical content, and the record was
right to classify it as own-content for Tag 07VX's construction rather than carriable.

*What Tag 07W2 is, and why landing it would not discharge step (ii).*  Tag 07W2 is not a lemma.
It is the label of equation 81.6.5.2, `spaces-pushouts-equation-cube-over`, a displayed xymatrix
cube inside the *proof* of Lemma 81.6.5 — Tag 07W0 — in the chapter *Pushouts of Algebraic
Spaces*, Section 81.6, `Pushouts along thickenings and affine morphisms`; Tag 07W1 is the
previous equation 81.6.5.1 in the same proof.  The displayed cube has exactly eight vertices,
`U, U', V, G(V, U', φ)` at the back and `U_1, U_1', V_1, G_1(V_1, U_1', φ_1)` at the front, and
its assertion is: the front and back squares are pushouts, the other four faces are cartesian,
the four northeast arrows are surjective étale, and in particular `G_1 ⟶ G` is surjective étale.
It names none of `X_1, X_1', Y_1, Y_1'`.  The prescription that makes the cube *useful* — that
`V_1` is a chart of `Y_1 ×_Y V` and `U_1 = V_1 ×_Y X`, so that `G_1` comes with a map to `Y_1'`
— is in the prose of Tag 07W0's proof preceding the equation, not under the label.

So the faithful registration of Tag 07W2 is the form existentially quantified over charts, and
that form is formalized, as
`AlgebraicGeometry.Space.exists_etaleChartCube_gluingData_of_isThickening_of_isAffineHom` in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesGluing`: `hatlas` applies
to the span of a triple, exactly as
`AlgebraicGeometry.Space.pushoutGluingHasPushout` already applies it, so the whole cube is the
sibling equation 81.6.5.1 — Tag 07W1,
`AlgebraicGeometry.Space.exists_etaleChartCube_of_isThickening_of_isAffineHom` — instantiated
at that span, including the two lateral squares priced in (i), both of which are proved inside
that Tag 07W1 carrier.  But that form is *not* step (ii), and proving it does not discharge
it.  Step (ii) needs the charts prescribed, because the
argument identifies `G_1` with `W'_1` through `Stacks.Pushout.gluingCounit_isIso_of_flat` and
then uses `W'_1 ⟶ W'` surjective étale to make the composite étale by Tag 03FS; for an atlas
with unrelated charts `A.P ⟶ E` is surjective étale onto `G(F(W'))` and there is no surjective
étale `A.P ⟶ W'` at all, so Tag 03FS has no hypothesis to take.  The prescribed cube is a
strictly different statement, which is why it is an auxiliary statement of its own
rather than Tag 07W2; it depends on Tags 05ZS and 07W3, so it cannot be an input to Tag 07W3.

The prescribed cube is also not reachable by carrying more tags.  Its `G_1` is a scheme pushout
that has to enter the site and carry an étale equivalence relation, so all three items under
`What is not covered` in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces` bite for it, and `hatlas`
cannot supply them: being `Nonempty`, it hands over an atlas with charts one does not choose.
Those three are Tag 07VX's own construction, not another tag's results.  The one case in which
they do not bite is the flat one described in (ii) above, where `P` is `W'_1` and `Rel` is its
kernel pair; that case, and not Tag 07W2, is what would unblock the counit half of Tag 07W3.

## References

* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
* [Stacks Project, Tag 07W0](https://stacks.math.columbia.edu/tag/07W0)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07VY](https://stacks.math.columbia.edu/tag/07VY)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 07VW](https://stacks.math.columbia.edu/tag/07VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings

universe u

namespace AlgebraicGeometry

/-! ### Chart squares -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A commuting square of étale scheme charts of a morphism `f : F ⟶ G` of presheaves on the big
fppf site of `S` whose chart of the source is surjective.  This is the data of condition (2) of
[Stacks Project, Tag 03MJ], with the property of the morphism of charts omitted. -/
structure EtaleChartSquare {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) where
  /-- The chart of the source. -/
  src : BigFppfOver B S hS
  /-- The chart of the target. -/
  tgt : BigFppfOver B S hS
  /-- The morphism of charts. -/
  hom : src ⟶ tgt
  /-- The chart map of the source. -/
  chartSrc : yoneda.obj src ⟶ F
  /-- The chart map of the target. -/
  chartTgt : yoneda.obj tgt ⟶ G
  /-- The chart of the source is étale. -/
  etale_chartSrc : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf chartSrc
  /-- The chart of the source is surjective. -/
  surjective_chartSrc : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf chartSrc
  /-- The chart of the target is étale. -/
  etale_chartTgt : (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf chartTgt
  /-- The square commutes. -/
  comm : yoneda.map hom ≫ chartTgt = chartSrc ≫ f

namespace EtaleChartSquare

variable {B S hS} {P : MorphismProperty Scheme.{u}}
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}

/-- **[Stacks Project, Tag 03MJ] in the form in which it is used.**  A property of morphisms of
schemes which is étale local on the source and target holds on every commuting square of étale
charts of `f` exactly when it holds on the morphism of charts of one such square whose chart of
the source is surjective. -/
theorem holdsOnEveryEtaleChart_iff (hP : IsEtaleLocalOnSourceAndTarget P)
    (sq : EtaleChartSquare B S hS f) :
    HoldsOnEveryEtaleChart B S hS P f ↔ P ((BigFppfOver.toScheme B S hS).map sq.hom) :=
  ⟨fun hall ↦ hall _ _ _ _ _ sq.etale_chartSrc sq.etale_chartTgt sq.comm,
    fun hp ↦ holdsOnEveryEtaleChart_of_surjectiveChart B S hS P hP
      ⟨sq.src, sq.tgt, sq.chartSrc, sq.chartTgt, sq.hom, sq.etale_chartSrc, sq.etale_chartTgt,
        sq.surjective_chartSrc, sq.comm, hp⟩⟩

end EtaleChartSquare

/-! ### The five clauses for algebraic spaces, given a chart presentation -/

/-- A presentation by étale scheme charts of the three morphisms of [Stacks Project, Tag 07RX]
over a thickening-and-affine pushout square of algebraic spaces: a commuting square of étale
charts for each of `g : V' ⟶ Y'`, `v : V ⟶ Y` and `u' : U' ⟶ X'`, whose three morphisms of
charts carry the scheme-level situation of [Stacks Project, Tag 07RV] — two cocartesian squares
along a thickening and an affine morphism, and the two cartesian squares of the triple.

This is the content of the cube diagrams of the proof of [Stacks Project, Tag 07W0]; it is the
input the source's proof of [Stacks Project, Tag 07W3] obtains from the construction of the
pushout of algebraic spaces in [Stacks Project, Tag 07VX]. -/
structure ThickeningAffineGluingChart
    {Y' V' Y V X' U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : V' ⟶ Y') (v : V ⟶ Y) (u' : U' ⟶ X') where
  /-- The chart square of the glued morphism `V' ⟶ Y'`. -/
  sqGlued : EtaleChartSquare B S hS g
  /-- The chart square of `V ⟶ Y`. -/
  sqY : EtaleChartSquare B S hS v
  /-- The chart square of `U' ⟶ X'`. -/
  sqX' : EtaleChartSquare B S hS u'
  /-- The chart of `X`, the common restriction downstairs. -/
  chartX : BigFppfOver B S hS
  /-- The chart of `U`, the common restriction upstairs. -/
  chartU : BigFppfOver B S hS
  /-- The thickening of charts downstairs. -/
  i : chartX ⟶ sqX'.tgt
  /-- The affine morphism of charts downstairs. -/
  f : chartX ⟶ sqY.tgt
  /-- The left leg of the pushout of charts downstairs. -/
  inX' : sqX'.tgt ⟶ sqGlued.tgt
  /-- The right leg of the pushout of charts downstairs. -/
  inY : sqY.tgt ⟶ sqGlued.tgt
  /-- The thickening of charts upstairs. -/
  iT : chartU ⟶ sqX'.src
  /-- The affine morphism of charts upstairs. -/
  fT : chartU ⟶ sqY.src
  /-- The left leg of the pushout of charts upstairs. -/
  inU' : sqX'.src ⟶ sqGlued.src
  /-- The right leg of the pushout of charts upstairs. -/
  inV : sqY.src ⟶ sqGlued.src
  /-- The morphism of charts of `U ⟶ X`. -/
  toX : chartU ⟶ chartX
  /-- The morphism of charts downstairs is a thickening of schemes. -/
  isThickening_i : IsThickening ((BigFppfOver.toScheme B S hS).map i)
  /-- The morphism of charts downstairs is an affine morphism of schemes. -/
  isAffineHom_f : AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)
  /-- The chart of `Y'` is the pushout of the charts of `X'` and `Y`. -/
  isPushout_base : IsPushout ((BigFppfOver.toScheme B S hS).map i)
    ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map inX')
    ((BigFppfOver.toScheme B S hS).map inY)
  /-- The chart of `V'` is the pushout of the charts of `U'` and `V`. -/
  isPushout_glued : IsPushout ((BigFppfOver.toScheme B S hS).map iT)
    ((BigFppfOver.toScheme B S hS).map fT) ((BigFppfOver.toScheme B S hS).map inU')
    ((BigFppfOver.toScheme B S hS).map inV)
  /-- The chart of `U` is the fibre product of the charts of `U'` and `X`. -/
  isPullback_i : IsPullback ((BigFppfOver.toScheme B S hS).map iT)
    ((BigFppfOver.toScheme B S hS).map toX) ((BigFppfOver.toScheme B S hS).map sqX'.hom)
    ((BigFppfOver.toScheme B S hS).map i)
  /-- The chart of `U` is the fibre product of the charts of `V` and `X`. -/
  isPullback_f : IsPullback ((BigFppfOver.toScheme B S hS).map fT)
    ((BigFppfOver.toScheme B S hS).map toX) ((BigFppfOver.toScheme B S hS).map sqY.hom)
    ((BigFppfOver.toScheme B S hS).map f)
  /-- The morphism of charts of `V' ⟶ Y'` restricts on `U'` to that of `U' ⟶ X'`. -/
  inU'_comp_hom : inU' ≫ sqGlued.hom = sqX'.hom ≫ inX'
  /-- The morphism of charts of `V' ⟶ Y'` restricts on `V` to that of `V ⟶ Y`. -/
  inV_comp_hom : inV ≫ sqGlued.hom = sqY.hom ≫ inY

namespace ThickeningAffineGluingChart

variable {B S hS} {Y' V' Y V X' U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {g : V' ⟶ Y'} {v : V ⟶ Y} {u' : U' ⟶ X'}

/-- The morphism of charts of the glued morphism restricts on the chart of `U'` to the morphism
of charts of `U' ⟶ X'`, read on schemes. -/
theorem map_inU'_comp_hom (D : ThickeningAffineGluingChart B S hS g v u') :
    (BigFppfOver.toScheme B S hS).map D.inU' ≫ (BigFppfOver.toScheme B S hS).map D.sqGlued.hom =
      (BigFppfOver.toScheme B S hS).map D.sqX'.hom ≫
        (BigFppfOver.toScheme B S hS).map D.inX' := by
  rw [← Functor.map_comp, ← Functor.map_comp, D.inU'_comp_hom]

/-- The morphism of charts of the glued morphism restricts on the chart of `V` to the morphism
of charts of `V ⟶ Y`, read on schemes. -/
theorem map_inV_comp_hom (D : ThickeningAffineGluingChart B S hS g v u') :
    (BigFppfOver.toScheme B S hS).map D.inV ≫ (BigFppfOver.toScheme B S hS).map D.sqGlued.hom =
      (BigFppfOver.toScheme B S hS).map D.sqY.hom ≫
        (BigFppfOver.toScheme B S hS).map D.inY := by
  rw [← Functor.map_comp, ← Functor.map_comp, D.inV_comp_hom]

/-- The clause of [Stacks Project, Tag 07RX] belonging to an étale-local property, read on the
charts of a presentation. -/
theorem holdsOnEveryEtaleChart_iff (D : ThickeningAffineGluingChart B S hS g v u')
    {P : MorphismProperty Scheme.{u}} (hP : IsEtaleLocalOnSourceAndTarget P)
    (hscheme : P ((BigFppfOver.toScheme B S hS).map D.sqGlued.hom) ↔
      P ((BigFppfOver.toScheme B S hS).map D.sqY.hom) ∧
        P ((BigFppfOver.toScheme B S hS).map D.sqX'.hom)) :
    HoldsOnEveryEtaleChart B S hS P g ↔
      HoldsOnEveryEtaleChart B S hS P v ∧ HoldsOnEveryEtaleChart B S hS P u' := by
  rw [D.sqGlued.holdsOnEveryEtaleChart_iff hP, D.sqY.holdsOnEveryEtaleChart_iff hP,
    D.sqX'.holdsOnEveryEtaleChart_iff hP]
  exact hscheme

/-- **The algebraic-space form of [Stacks Project, Tag 07RX], clause (1), given a chart
presentation.**  The glued morphism is locally of finite type if and only if both `V ⟶ Y` and
`U' ⟶ X'` are. -/
theorem isLocallyOfFiniteType_iff (D : ThickeningAffineGluingChart B S hS g v u') :
    IsLocallyOfFiniteType B S hS g ↔
      IsLocallyOfFiniteType B S hS v ∧ IsLocallyOfFiniteType B S hS u' :=
  have := D.isAffineHom_f
  D.holdsOnEveryEtaleChart_iff isEtaleLocalOnSourceAndTarget_locallyOfFiniteType
    (ThickeningAffineGluing.locallyOfFiniteType_induced_iff_of_isPushout D.isThickening_i
      D.isPushout_base D.isPushout_glued D.isPullback_i D.isPullback_f
      D.map_inU'_comp_hom D.map_inV_comp_hom)

/-- **The algebraic-space form of [Stacks Project, Tag 07RX], clause (2), given a chart
presentation.**  The glued morphism is flat if and only if both `V ⟶ Y` and `U' ⟶ X'` are. -/
theorem isFlat_iff (D : ThickeningAffineGluingChart B S hS g v u') :
    IsFlat B S hS g ↔ IsFlat B S hS v ∧ IsFlat B S hS u' :=
  have := D.isAffineHom_f
  D.holdsOnEveryEtaleChart_iff Flat.isEtaleLocalOnSourceAndTarget
    (ThickeningAffineGluing.flat_induced_iff_of_isPushout D.isThickening_i
      D.isPushout_base D.isPushout_glued D.isPullback_i D.isPullback_f
      D.map_inU'_comp_hom D.map_inV_comp_hom)

/-- **The algebraic-space form of [Stacks Project, Tag 07RX], clause (3), given a chart
presentation.**  The glued morphism is flat and locally of finite presentation if and only if
both `V ⟶ Y` and `U' ⟶ X'` are. -/
theorem isFlat_and_isLocallyOfFinitePresentation_iff
    (D : ThickeningAffineGluingChart B S hS g v u') :
    (IsFlat B S hS g ∧ IsLocallyOfFinitePresentation B S hS g) ↔
      ((IsFlat B S hS v ∧ IsLocallyOfFinitePresentation B S hS v) ∧
        (IsFlat B S hS u' ∧ IsLocallyOfFinitePresentation B S hS u')) := by
  have := D.isAffineHom_f
  have hscheme :=
    ThickeningAffineGluing.flat_and_locallyOfFinitePresentation_induced_iff_of_isPushout
      D.isThickening_i D.isPushout_base D.isPushout_glued D.isPullback_i D.isPullback_f
      D.map_inU'_comp_hom D.map_inV_comp_hom
  have hflat := Flat.isEtaleLocalOnSourceAndTarget.{u}
  have hlfp := LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget.{u}
  simp only [IsFlat, IsLocallyOfFinitePresentation, D.sqGlued.holdsOnEveryEtaleChart_iff hflat,
    D.sqGlued.holdsOnEveryEtaleChart_iff hlfp, D.sqY.holdsOnEveryEtaleChart_iff hflat,
    D.sqY.holdsOnEveryEtaleChart_iff hlfp, D.sqX'.holdsOnEveryEtaleChart_iff hflat,
    D.sqX'.holdsOnEveryEtaleChart_iff hlfp]
  exact hscheme

/-- **The algebraic-space form of [Stacks Project, Tag 07RX], clause (4), given a chart
presentation.**  The glued morphism is smooth if and only if both `V ⟶ Y` and `U' ⟶ X'` are. -/
theorem isSmooth_iff (D : ThickeningAffineGluingChart B S hS g v u') :
    IsSmooth B S hS g ↔ IsSmooth B S hS v ∧ IsSmooth B S hS u' :=
  have := D.isAffineHom_f
  D.holdsOnEveryEtaleChart_iff Smooth.isEtaleLocalOnSourceAndTarget
    (ThickeningAffineGluing.smooth_induced_iff_of_isPushout D.isThickening_i
      D.isPushout_base D.isPushout_glued D.isPullback_i D.isPullback_f
      D.map_inU'_comp_hom D.map_inV_comp_hom)

/-- **The algebraic-space form of [Stacks Project, Tag 07RX], clause (5), given a chart
presentation.**  The glued morphism is étale if and only if both `V ⟶ Y` and `U' ⟶ X'` are. -/
theorem isEtale_iff (D : ThickeningAffineGluingChart B S hS g v u')
    (hV' : IsAlgebraicSpace B S hS V') (hY' : IsAlgebraicSpace B S hS Y')
    (hV : IsAlgebraicSpace B S hS V) (hY : IsAlgebraicSpace B S hS Y)
    (hU' : IsAlgebraicSpace B S hS U') (hX' : IsAlgebraicSpace B S hS X') :
    IsEtale B S hS g ↔ IsEtale B S hS v ∧ IsEtale B S hS u' := by
  have := D.isAffineHom_f
  rw [isEtale_iff_holdsOnEveryEtaleChart B S hS hV' hY' g,
    isEtale_iff_holdsOnEveryEtaleChart B S hS hV hY v,
    isEtale_iff_holdsOnEveryEtaleChart B S hS hU' hX' u']
  exact D.holdsOnEveryEtaleChart_iff etale_isEtaleLocalOnSourceAndTarget
    (ThickeningAffineGluing.etale_induced_iff_of_isPushout D.isThickening_i
      D.isPushout_base D.isPushout_glued D.isPullback_i D.isPullback_f
      D.map_inU'_comp_hom D.map_inV_comp_hom)

end ThickeningAffineGluingChart

end Space

end AlgebraicGeometry

end
