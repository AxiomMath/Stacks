module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.CompositeChartData
public import StacksFrontier.AlgebraicGeometry.Spaces.TestSchemePullbacks
public import StacksFrontier.CategoryTheory.Sites.SubsingletonPresheaf

/-!
# Descent and limit preservation for the flat-dimension functor of an algebraic space

In **Situation 0CWU** — a morphism `f : X ⟶ Y` of algebraic spaces over `S` which is locally of
finite type, a quasi-coherent `𝒪_X`-module `ℱ` of finite type, and a natural number `n` — the
functor `F_n` of equation 0CWV on the test schemes over `Y` is a sheaf for the fpqc topology,
and it is limit preserving as soon as `f` is quasi-compact and locally of finite presentation
and `ℱ` is of finite presentation.  This is **Stacks 0CWW**.

Clause (1) is proved here for every situation of the tag, from nothing but the data of
Situation 0CWU.  It does not go through the chart presentation of the source's proof: `F_n` is
subterminal, so its sheaf property is exactly fpqc locality of the condition of Stacks 0CWT on
the base change, and that locality is proved pointwise, on condition (3) of Stacks 0CWS, along
the jointly surjective flat family of test schemes which a covering sieve contains.  This is the
space-level form of the argument by which the scheme-level part (1) of Stacks 05MV is proved in
`StacksFrontier/AlgebraicGeometry/Flatness/FlatteningFunctor/FlatDimensionFpqcSheaf.lean`, and it
needs no chart.

Clause (2) is proved here for every situation of the tag as well, from the three hypotheses the
clause names.  It follows the source's argument: a commuting square of étale scheme charts
presents `F_n` as the scheme-level functor `F'_n` of Stacks 05MT, and the clause is read off
part (2) of **Stacks 05MV** for `F'_n`.  The square is taken over a *stage* of the tested inverse
system rather than over `Y`, which is what makes it constructible; see the section below.

## Main results

* `AlgebraicGeometry.Space.FlatDimensionSituation.isSheaf_flatDimensionFunctor_iff` and
  `AlgebraicGeometry.Space.FlatDimensionSituation.limitPreserving_flatDimensionFunctor_iff`:
  because `F_n` is subterminal, its sheaf property is fpqc locality of the condition of
  Stacks 0CWT, and its limit preservation is descent of that condition along cofiltered limits
  of affine test schemes.  Both are unconditional.
* `isFlatInDimensionsGEAfterBaseChange_of_mem_fpqcTopology`, in
  `AlgebraicGeometry.Space.FlatDimensionSituation`: the condition of Stacks 0CWT on the base
  change is fpqc local on the test scheme.
* `AlgebraicGeometry.Space.FlatDimensionSituation.flatDimensionFunctor_isSheaf_fpqc`:
  **Stacks 0CWW, clause (1)**, the fpqc sheaf property of `F_n`, for an arbitrary situation of
  Situation 0CWU.
* `AlgebraicGeometry.Space.FlatDimensionSituation.flatDimensionFunctor_limitPreserving`:
  **Stacks 0CWW, clause (2)**, limit preservation of `F_n`, for an arbitrary situation of
  Situation 0CWU in which `f` is quasi-compact and locally of finite presentation and `ℱ` is of
  finite presentation.
* `flatDimensionFunctor_limitPreserving_of_presentation`, in the same namespace: the step of the
  source's argument that applies part (2) of Stacks 05MV, taking a chart presentation as data.
  Clause (2) is read off it once the presentation is constructed.  Its special case for a
  presentation that is affine and limit preserving as a functor on all test schemes, which is
  the case of a chart affine over `Y`, is
  `flatDimensionFunctor_limitPreserving_of_affinePresentation` in the same namespace.

The fpqc topology on the test schemes, `AlgebraicGeometry.Space.fpqcTopology`, and the
underlying-scheme functor it is pulled back along are in
`StacksFrontier/AlgebraicGeometry/Spaces/TestSchemeFpqcSite.lean`.

## How clause (1) is proved

The three inputs are all in the tree and all unconditional.

A covering sieve of a test scheme `T` contains a family of arrows `T_i ⟶ T` which is an fpqc
covering of Stacks 03MQ of the algebraic space represented by `T` and is jointly surjective on
the points of Stacks 03BU; this is
`AlgebraicGeometry.Space.exists_isFpqcCovering_jointlySurjective_family_of_mem_fpqcTopology` of
`StacksFrontier/AlgebraicGeometry/Spaces/TestSchemePullbacks.lean`, and in particular every member
of the family is flat, hence flat at every point.

Condition (3) of Stacks 0CWS descends along such a family:
`AlgebraicGeometry.Space.hasTrdegLtAtNonflatPoints_of_jointlySurjective_flat_baseChange` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleInDimensionsGE.lean`.  Its two ingredients are
part (3) of Stacks 04NS,
`AlgebraicGeometry.Space.exists_point_preserving_fiberLocalRingDimension_and_trdeg`, which lifts
a point of `|X_T|` and a point of `|T_i|` above its image to a common point of `|X_{T_i}|` at
which the transcendence degree over the base is unchanged, and part (2) of Stacks 05VW read at a
point, `AlgebraicGeometry.Space.mem_flatLocus_of_mem_flatLocus_modulePullback`, which carries
flatness of the inverse image over `T_i` at that lift back to flatness of `ℱ_T` over `T` — the
hypothesis of flatness at the image point being supplied by flatness of `T_i ⟶ T`.

The passage between condition (3) and the definition of Stacks 0CWT is the equivalence of
conditions (2) and (3) of Stacks 0CWS,
`AlgebraicGeometry.Space.isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasTrdegLt`.  It
consumes local finite type of the base-changed morphism and quasi-coherence and finite type of
the base-changed module, on the small étale site and on charts: the first two observations of
Situation 0CWU, Stacks 03GA, and
`AlgebraicGeometry.Space.isQuasicoherentOnCharts_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.Space.isFiniteTypeOnCharts_of_isFiniteTypeOnSite`.  The module over `T_i` is
identified with the inverse image of the one over `T` by the composition comparison of
Stacks 03LU, across which the condition moves because it depends on the module only through its
isomorphism class.

## How clause (2) is proved

Limit preservation of `F_n` is, because `F_n` is subterminal, descent of the condition of
Stacks 0CWT along a cofiltered inverse system of affine test schemes with affine limit:
`limitPreserving_flatDimensionFunctor_iff`, which is unconditional.  So the system
`T = lim_{i ∈ I} T_i` may be fixed before anything is chosen, and the chart presentation may be
taken over one of its *stages* rather than over `Y`.  That is the one departure from the letter
of the source's proof, and it is what makes the presentation constructible.

Fix an index `i₀`.  The base change `X_{T_{i₀}}` is a quasi-compact algebraic space, because `f`
is quasi-compact in the sense of Stacks 03HE and `T_{i₀}` is affine, so it has a surjective étale
scheme chart `U` whose scheme is affine, by **Stacks 03H6**; this is
`AlgebraicGeometry.Space.exists_isAffine_isSurjective_chart_baseChangeSpace`.  Since `T_{i₀}` is
a scheme, the algebraic space it represents has the identity chart, so `U` and that identity
chart form a commuting square of étale scheme charts of `f_{T_{i₀}}`, and the chart morphism
`U ⟶ T_{i₀}` together with the restriction of `ℱ_{T_{i₀}}` to `U` is a situation `E` of
**Stacks 05MT**: `AlgebraicGeometry.Space.FlatDimensionSituation.stageSituation`.

This is the source's `U ⟶ V` with `V` the identity chart of a stage instead of a chart of `Y`,
and the simplification is exactly that the presentation is then the identity on test schemes:
`V ×_{T_{i₀}} T' = T'`.  The source, working over `Y`, has to send `T'` to `V ×_Y T'`, which is
étale over `T'` and not affine over it, and therefore has to choose, after the system is given,
an affine open of `V ×_Y T_{i₀}` surjecting onto `T_{i₀}` and pass to its inverse images.  Over a
stage none of that is needed: affine test schemes over `T_{i₀}` are already affine schemes over
the scheme underlying `T_{i₀}`.

The identification of the two conditions is the theorem
`isFlatInDimensionsGEAfterBaseChange_iff_stageSituation`, in the same namespace,
of `StacksFrontier/AlgebraicGeometry/Spaces/FlatDimensionStagePresentation.lean`: for every test
scheme `T'` over `T_{i₀}`, `ℱ_{T'}` is flat over `T'` in dimensions `≥ n` exactly when the base
change of `E` to `T'` is.  It is **the chart clause of Stacks 0CWS** — *not* the base-change
clause, which is a different statement, proved unconditionally as
`AlgebraicGeometry.Space.isFlatOverInDimensionsGE_modulePullback_of_isPullback`; that clause
compares the condition for `F` over `Y` with the condition for its inverse image over `Y'`
through condition (3), which mentions no chart, whereas this one compares the condition over a
test scheme with a scheme-level situation read on a chart, and so needs the chart restriction of
an inverse image.  Its two halves are the equivalence of conditions (1) and (2) of Stacks 0CWS,
`AlgebraicGeometry.Space.isFlatOverInDimensionsGEOnSomeChartDiagram_iff_onEveryChartDiagram`,
applied at the square whose source chart is the base change of `U` to `X_{T'}` and whose target
chart is the identity chart of `T'` — both surjective — and the module comparison
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean`: for a morphism
`a : X ⟶ Z` of algebraic spaces, a quasi-coherent `𝒪_Z`-module `G`, charts `V` of `Z` and `W` of
`X` and a morphism `g` of their schemes filling the square, it is an isomorphism
`(Scheme.Modules.pullback g)^* (G|_V) ≅ ((a^* G)|_W)`.  The square is not required to be
cartesian and only quasi-coherence of `G` is asked.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleInDimensionsGE.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleGeometricPointCriterion.lean`, which report that
comparison as unavailable, predate it; only invertibility of the *canonical* comparison
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` is still unproved, and it is
not needed, since the condition of Stacks 0CWT depends on the module only through its
isomorphism class
(`AlgebraicGeometry.Space.isFlatOverInDimensionsGEOnChartDiagram_iff_of_moduleIso`).

The inverse system of affine schemes over the scheme underlying `T_{i₀}` to which part (2) of
**Stacks 05MV** is applied is the given one restricted to the indices over `i₀`:
`CategoryTheory.Over.post` of the underlying-scheme diagram on `CategoryTheory.Over i₀`, with
`CategoryTheory.Limits.Cone.overPost` of the given limit cone.  That cone is limiting because
`CategoryTheory.Over.forget i₀` is initial for a cofiltered index category
(`CategoryTheory.Over.initial_forget`), and the slice is again cofiltered
(`CategoryTheory.IsCofiltered.over`).  Part (2) of Stacks 05MV itself is
`AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_limitPreserving` of
`StacksFrontier/AlgebraicGeometry/Flatness/FlatteningFunctor/FlatDimensionLimitPreserving.lean`,
which is applied and not assumed.

The three hypotheses of the clause on `f` and `ℱ` — quasi-compact, locally of finite
presentation, of finite presentation — enter in two places: quasi-compactness gives the affine
chart `U`, and all three are what part (2) of Stacks 05MV asks of `E`.  On `E` they are
`AlgebraicGeometry.Space.FlatDimensionSituation.quasiCompact_stageSituation_f` — both ends of the
presenting chart morphism are affine schemes, so it is affine and hence quasi-compact —
`AlgebraicGeometry.Space.FlatDimensionSituation.locallyOfFinitePresentation_stageSituation_f` and
`AlgebraicGeometry.Space.FlatDimensionSituation.isFinitePresentation_stageSituation_F`.

None of this is needed for clause (1), which is not proved through a presentation: the pointwise
descent above replaces both the chart identification and the source's step
"`{V ×_Y T_i ⟶ V ×_Y T}` is again an fpqc covering", because the covering is used on the test
schemes themselves rather than on their chart base changes.

## The presentation form of clause (2), and the functorial special case

`flatDimensionFunctor_limitPreserving_of_presentation` is the step of the source's argument that
applies part (2) of Stacks 05MV, with the presentation as data: a scheme-level situation `E` of
Stacks 05MT, a functor `Φ` on the test schemes, the identification `hcond` of the condition of
Stacks 0CWT for `ℱ_T` over `T` with the condition for `E` at `Φ T`, and a per-inverse-system
datum `hsys` — for each cofiltered system `G` of affine test schemes with limit `c`, a cofiltered
system `K` of affine schemes over `E.S` indexed over the given one by a functor `Ψ`, with an
affine limit `d`, a morphism `d.pt ⟶ Φ T`, and the implication from the condition for `E` at a
stage `K j` to the condition for `D` at the stage `G (Ψ j)`.  That shape is the source's own: it
is what a presentation over a chart `V` of `Y` delivers, where `Φ T = V ×_Y T` is étale over `T`
rather than affine over it and the system has to be cut down to affine opens.  Clause (2) above
does not go through it, taking the presentation over a stage instead.

`flatDimensionFunctor_limitPreserving_of_affinePresentation` records that the per-system datum is
implied by the functorial hypotheses that `Φ` carry affine test schemes to affine schemes and
cofiltered limit diagrams to cofiltered limit diagrams — the case of a chart `V` affine over `Y`
— with `J = I`, `Ψ = 𝟭 I` and `K = G ⋙ Φ`, so that the per-system form generalises the functorial
one.

## Implementation notes

`F_n` is `AlgebraicGeometry.Space.FlatDimensionSituation.flatDimensionFunctor`, which is
unconditional: its functoriality is the base-change clause of Stacks 0CWS, proved in this
development, so nothing about `F_n` is carried here.  Both clauses go through the fact that `F_n`
is subterminal: the sheaf condition and the colimit condition for a presheaf of subsingletons are
`CategoryTheory.Presheaf.isSheaf_iff_nonempty_of_subsingleton` and
`CategoryTheory.nonempty_isColimit_mapCocone_op_iff_of_subsingleton`.  Limit preservation is
`AlgebraicGeometry.LimitPreserving` of Stacks 049J, as for the loci of Stacks 083J in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapLociLimitPreserving.lean`.

Clause (1) is the same shape of proof as the four clauses of Stacks 083H in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapLociFpqcSheaf.lean`: a subterminal presheaf on
the same test schemes, a covering family extracted from the sieve, and a descent statement for
the condition the presheaf expresses.

## References

* [Stacks Project, Tag 0CWW](https://stacks.math.columbia.edu/tag/0CWW)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0CWU](https://stacks.math.columbia.edu/tag/0CWU)
* [Stacks Project, Tag 0CWV](https://stacks.math.columbia.edu/tag/0CWV)
* [Stacks Project, Tag 0CWS](https://stacks.math.columbia.edu/tag/0CWS)
* [Stacks Project, Tag 0CWT](https://stacks.math.columbia.edu/tag/0CWT)
* [Stacks Project, Tag 05MV](https://stacks.math.columbia.edu/tag/05MV)
* [Stacks Project, Tag 05MT](https://stacks.math.columbia.edu/tag/05MT)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w w'

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace FlatDimensionSituation

/-- The values of the scheme-level functor `F'_n` of Stacks 05MT are subsingletons: they are
`PLift` of a proposition. -/
private instance flatDimensionFunctor_obj_subsingleton'
    (E : _root_.AlgebraicGeometry.FlatDimensionSituation.{u}) (T : (Over E.S)ᵒᵖ) :
    Subsingleton (E.flatDimensionFunctor.obj T) :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The functor `F_n` is subterminal, so its sheaf property for the fpqc topology on the test
schemes is exactly fpqc locality of the condition of **Stacks 0CWT**: the base change of `ℱ` to
a test scheme is flat over it in dimensions `≥ n` as soon as this holds at every member of an
fpqc covering sieve of that test scheme. -/
theorem isSheaf_flatDimensionFunctor_iff (D : FlatDimensionSituation.{u} B S hS) (n : ℕ) :
    Presheaf.IsSheaf (fpqcTopology D.Y) (D.flatDimensionFunctor n) ↔
      ∀ (T : SchemesOver D.Y) (R : Sieve T), R ∈ fpqcTopology D.Y T →
        (∀ ⦃T' : SchemesOver D.Y⦄ (g : T' ⟶ T), R.arrows g →
            D.IsFlatInDimensionsGEAfterBaseChange T' n) →
          D.IsFlatInDimensionsGEAfterBaseChange T n := by
  have : ∀ T : (SchemesOver D.Y)ᵒᵖ, Subsingleton ((D.flatDimensionFunctor n).obj T) :=
    fun T => D.flatDimensionFunctor_obj_subsingleton n T.unop
  constructor
  · intro hsh T R hR hT
    refine (D.nonempty_flatDimensionFunctor_obj_iff n T).1
      ((Presheaf.isSheaf_iff_nonempty_of_subsingleton _ _).1 hsh T R hR fun T' g hg => ?_)
    exact (D.nonempty_flatDimensionFunctor_obj_iff n T').2 (hT g hg)
  · intro hloc
    refine (Presheaf.isSheaf_iff_nonempty_of_subsingleton _ _).2 fun T R hR hne => ?_
    refine (D.nonempty_flatDimensionFunctor_obj_iff n T).2 (hloc T R hR fun T' g hg => ?_)
    exact (D.nonempty_flatDimensionFunctor_obj_iff n T').1 (hne g hg)

/-- The functor `F_n` is subterminal, so its limit preservation in the sense of **Stacks 049J**
is exactly descent of the condition of **Stacks 0CWT** along cofiltered limits of affine test
schemes: whenever the base change of `ℱ` to the limit of such a diagram is flat over it in
dimensions `≥ n`, this already holds at some stage of the diagram. -/
theorem limitPreserving_flatDimensionFunctor_iff (D : FlatDimensionSituation.{u} B S hS)
    (n : ℕ) :
    LimitPreserving.{u, u, w, w'} (testSchemeFunctor D.Y) (D.flatDimensionFunctor n) ↔
      ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I] (G : I ⥤ SchemesOver D.Y)
        (c : Cone G), IsLimit ((testSchemeFunctor D.Y).mapCone c) →
          (∀ i, IsAffine ((testSchemeFunctor D.Y).obj (G.obj i))) →
          IsAffine ((testSchemeFunctor D.Y).obj c.pt) →
          D.IsFlatInDimensionsGEAfterBaseChange c.pt n →
            ∃ i, D.IsFlatInDimensionsGEAfterBaseChange (G.obj i) n := by
  have : ∀ T : (SchemesOver D.Y)ᵒᵖ, Subsingleton ((D.flatDimensionFunctor n).obj T) :=
    fun T => D.flatDimensionFunctor_obj_subsingleton n T.unop
  constructor
  · intro hlp I _ _ G c hc haff hpt hT
    obtain ⟨i, hi⟩ := (nonempty_isColimit_mapCocone_op_iff_of_subsingleton
      (D.flatDimensionFunctor n) G c).1 (hlp I G c hc haff hpt)
      ((D.nonempty_flatDimensionFunctor_obj_iff n c.pt).2 hT)
    exact ⟨i, (D.nonempty_flatDimensionFunctor_obj_iff n (G.obj i)).1 hi⟩
  · intro hdes I _ _ G c hc haff hpt
    refine (nonempty_isColimit_mapCocone_op_iff_of_subsingleton
      (D.flatDimensionFunctor n) G c).2 fun hne => ?_
    obtain ⟨i, hi⟩ := hdes I G c hc haff hpt
      ((D.nonempty_flatDimensionFunctor_obj_iff n c.pt).1 hne)
    exact ⟨i, (D.nonempty_flatDimensionFunctor_obj_iff n (G.obj i)).2 hi⟩

/-- Condition (2) of Stacks 0CWS is condition (3) for a quasi-coherent module of finite type on the
small étale site. -/
private theorem isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasTrdegLt_of_onSite
    {Xs Ys : AlgebraicSpaces B S hS} (f : Xs ⟶ Ys) (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (hqc : F.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) (n : ℕ) :
    IsFlatOverInDimensionsGEOnEveryChartDiagram B S hS Xs.2 f.hom F n ↔
      HasTrdegLtAtNonflatPoints B S hS Xs.2 f.hom F n :=
  isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasTrdegLt B S hS f F hf
    (isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS _ _ hqc)
    (isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS _ _ hqc hft) n

/-- **The condition of Stacks 0CWT on a base change is fpqc local on the test scheme.** If a
covering sieve of a test scheme `T` over `Y` for the fpqc topology on the test schemes has
`F_{T'}` flat over `T'` in dimensions `≥ n` at every one of its members `T' ⟶ T`, then `F_T` is
flat over `T` in dimensions `≥ n`.

A covering sieve contains a family of arrows `T_i ⟶ T` which is an fpqc covering of Stacks 03MQ
of the algebraic space represented by `T` and is jointly surjective on points
(`AlgebraicGeometry.Space.exists_isFpqcCovering_jointlySurjective_family_of_mem_fpqcTopology`);
in particular every member of it is flat, hence flat at every point.  The squares of the
base changes over those arrows are cartesian
(`AlgebraicGeometry.Space.isPullback_baseChangeMap`), so the condition descends along the family
by `AlgebraicGeometry.Space.hasTrdegLtAtNonflatPoints_of_jointlySurjective_flat_baseChange`, the
pointwise descent of condition (3) of Stacks 0CWS, read on both sides through the equivalence of
conditions (2) and (3) of that tag.  The module on the base change over `T_i` is identified with
the inverse image of the one over `T` by the composition comparison of Stacks 03LU, across which
the condition moves because it depends on the module only through its isomorphism class.

Quasi-coherence and finite type of the base-changed module, on the small étale site and on
charts, are the two observations of Situation 0CWU together with Stacks 03GA, and local finite
type of the base-changed morphism is the first of them, so nothing beyond Situation 0CWU is
needed. -/
theorem isFlatInDimensionsGEAfterBaseChange_of_mem_fpqcTopology
    (D : FlatDimensionSituation.{u} B S hS) (n : ℕ) {T : SchemesOver D.Y} {R : Sieve T}
    (hR : R ∈ fpqcTopology D.Y T)
    (hT : ∀ ⦃T' : SchemesOver D.Y⦄ (g : T' ⟶ T), R.arrows g →
      D.IsFlatInDimensionsGEAfterBaseChange T' n) :
    D.IsFlatInDimensionsGEAfterBaseChange T n := by
  have hqcT : (D.toFlatnessSituation.baseChangeModule T).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (baseChangeProjection D.f T) D.F D.quasicoherent
  obtain ⟨I, T', k, hk, hcov, hsurj⟩ :=
    exists_isFpqcCovering_jointlySurjective_family_of_mem_fpqcTopology hR
  refine (isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasTrdegLt_of_onSite
    (baseChangeInclusion D.f T) (D.toFlatnessSituation.baseChangeModule T)
    (D.isLocallyOfFiniteType_baseChangeInclusion T) hqcT
    (D.isFiniteTypeOnSite_baseChangeModule T) n).2 ?_
  refine hasTrdegLtAtNonflatPoints_of_jointlySurjective_flat_baseChange B S hS
    (baseChangeInclusion D.f T) (D.toFlatnessSituation.baseChangeModule T)
    (D.isLocallyOfFiniteType_baseChangeInclusion T)
    (p := fun i => baseChangeMap D.f (k i)) (q := fun i => baseChangeInclusion D.f (T' i))
    (r := fun i => (schemeSpaceFunctor B S hS).map (k i).left)
    (fun i => AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f (k i)))
    (fun i w => isFlatAt_of_isFlat B S hS _ (hcov.1 i) w)
    ((isJointlySurjective_iff B S hS _ _).1 hsurj) fun i => ?_
  have hqcTi : ((modulePullback B S hS (baseChangeMap D.f (k i))).obj
      (D.toFlatnessSituation.baseChangeModule T)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (baseChangeMap D.f (k i)) (D.toFlatnessSituation.baseChangeModule T) hqcT
  refine (isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasTrdegLt_of_onSite
    (baseChangeInclusion D.f (T' i)) _ (D.isLocallyOfFiniteType_baseChangeInclusion (T' i))
    hqcTi (isFiniteTypeOnSite_modulePullback B S hS (baseChangeMap D.f (k i)) _
      (D.isFiniteTypeOnSite_baseChangeModule T)) n).1 ?_
  exact (isFlatOverInDimensionsGEOnEveryChartDiagram_iff_of_moduleIso B S hS
    (baseChangeSpace D.f (T' i)).2 (baseChangeInclusion D.f (T' i)).hom
    ((modulePullbackTriangle B S hS (baseChangeMap_comp_projection D.f (k i))).app D.F)
    n).1 (hT (k i) (hk i))

/-- **Stacks 0CWW, clause (1).** In Situation 0CWU the functor `F_n` of equation 0CWV satisfies
the sheaf property for the fpqc topology on the test schemes over `Y`.

`F_n` is subterminal, so its sheaf property is exactly fpqc locality of the condition of
Stacks 0CWT on the base change, which is
`isFlatInDimensionsGEAfterBaseChange_of_mem_fpqcTopology` of this namespace. -/
@[stacks 0CWW "clause (1): in Situation 0CWU the functor F_n of equation 0CWV is a sheaf for \
the fpqc topology on the test schemes over Y. Proved for every situation of the tag, from \
nothing but the data of Situation 0CWU: the functor is subterminal, so its sheaf property is \
fpqc locality of the condition of Stacks 0CWT on the base change, and that locality is the \
pointwise descent of condition (3) of Stacks 0CWS along the jointly surjective flat family a \
covering sieve contains"]
theorem flatDimensionFunctor_isSheaf_fpqc (D : FlatDimensionSituation.{u} B S hS) (n : ℕ) :
    Presheaf.IsSheaf (fpqcTopology D.Y) (D.flatDimensionFunctor n) :=
  (D.isSheaf_flatDimensionFunctor_iff n).2 fun _ _ hR hT =>
    D.isFlatInDimensionsGEAfterBaseChange_of_mem_fpqcTopology n hR hT

section LimitPreservation

variable {B₁ : BigFppfSite.{max u w w'}} {S₁ : Scheme.{max u w w'}} {hS₁ : B₁.Contains S₁}

/-- **Limit preservation of `F_n` from a chart presentation**, the tool out of which
**Stacks 0CWW, clause (2)** is read off below once the presentation is constructed.

The chart presentation `Φ`
identifies `F_n` with the scheme-level functor `F'_n` of the situation `E` of Stacks 05MT, by
`hcond`.  A cofiltered system of affine test schemes over `Y` with limit `c` is *not* carried by
`Φ` to a cofiltered system of affine schemes — `Φ T = V ×_Y T` is étale over `T`, not affine
over it — so the source instead chooses, after the system is given, an affine open
`W_i ⊆ V ×_Y T_i` surjecting onto `T_i` and passes to its inverse images.  That choice is
`hsys`: a cofiltered system `K` of affine schemes over `E.S` whose stages sit over the stages of
`G` through `Ψ`, whose limit `d` is affine and maps to `Φ` of the limiting test scheme, and at
whose stages the condition for `E` implies the condition for `D` at the corresponding stage of
`G`.  Then `F'_n` is limit preserving by **part (2) of Stacks 05MV**, which is *not* assumed —
it is `AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_limitPreserving` of
`StacksFrontier/AlgebraicGeometry/Flatness/FlatteningFunctor/FlatDimensionLimitPreserving.lean`,
applied to `E` and to the system `K`.  The three hypotheses it asks of `E` — quasi-compact,
locally of finite presentation, of finite presentation — are the source's hypotheses on `f` and
`ℱ` read on the chart presentation, and are where they enter.

The schemes live in the maximum of the two index universes of the tested inverse system and a
third parameter.  That is the universe signature every limit-preservation statement in this
library carries: Stacks 05MY and part (2) of Stacks 05MV both have it, and it is the signature
at which the limit of a cofiltered system of affine schemes indexed by a category of those
universes exists in the first place.  It is also the signature of the statement of
Stacks 0CWW (limit preserving).

The presentation this statement takes as data is constructed, for an arbitrary situation of
Situation 0CWU, by `flatDimensionFunctor_limitPreserving` below, which is where clause (2) is
registered; this statement is only the step of the source's argument that applies part (2) of
Stacks 05MV. -/
theorem flatDimensionFunctor_limitPreserving_of_presentation
    (D : FlatDimensionSituation.{max u w w'} B₁ S₁ hS₁) (n : ℕ)
    (E : _root_.AlgebraicGeometry.FlatDimensionSituation.{max u w w'})
    [QuasiCompact E.f] [LocallyOfFinitePresentation E.f] [E.F.IsFinitePresentation]
    (Φ : SchemesOver D.Y ⥤ Over E.S)
    (hcond : ∀ T : SchemesOver D.Y, D.IsFlatInDimensionsGEAfterBaseChange T n ↔
      E.IsFlatInDimensionsGEAfterBaseChange (Φ.obj T))
    (hsys : ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I]
      (G : I ⥤ SchemesOver D.Y) (c : Cone G), IsLimit ((testSchemeFunctor D.Y).mapCone c) →
        (∀ i, IsAffine ((testSchemeFunctor D.Y).obj (G.obj i))) →
        IsAffine ((testSchemeFunctor D.Y).obj c.pt) →
        ∃ (J : Type (max w w')) (_ : Category.{w'} J) (_ : IsCofiltered J) (Ψ : J ⥤ I)
          (K : J ⥤ Over E.S) (d : Cone K) (_ : IsLimit ((Over.forget E.S).mapCone d))
          (_ : d.pt ⟶ Φ.obj c.pt),
          (∀ j, IsAffine ((Over.forget E.S).obj (K.obj j))) ∧
            IsAffine ((Over.forget E.S).obj d.pt) ∧
            ∀ j, E.IsFlatInDimensionsGEAfterBaseChange (K.obj j) →
              D.IsFlatInDimensionsGEAfterBaseChange (G.obj (Ψ.obj j)) n) :
    LimitPreserving.{max u w w', max u w w', w, w'}
      (testSchemeFunctor D.Y) (D.flatDimensionFunctor n) := by
  have hE : LimitPreserving.{max u w w', 0, w, w'} (Over.forget E.S) E.flatDimensionFunctor :=
    _root_.AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_limitPreserving.{u, w, w'}
      E
  refine (D.limitPreserving_flatDimensionFunctor_iff n).2 ?_
  intro I _ _ G c hc hstage hpt hT
  obtain ⟨J, _, _, Ψ, K, d, hd, ι, hKaff, hdaff, htrans⟩ := hsys I G c hc hstage hpt
  obtain ⟨j, hj⟩ := (nonempty_isColimit_mapCocone_op_iff_of_subsingleton
    E.flatDimensionFunctor K d).1 (hE J K d hd hKaff hdaff)
      ⟨⟨E.isFlatInDimensionsGEAfterBaseChange_of_hom ι ((hcond c.pt).1 hT)⟩⟩
  exact ⟨Ψ.obj j, htrans j hj.some.down⟩

/-- Limit preservation of `F_n` from a chart presentation that is affine and limit preserving as
a functor on all test schemes: the special case of
`flatDimensionFunctor_limitPreserving_of_presentation` of this namespace in which
the per-system choice of affine opens is not needed, because `Φ` already carries a cofiltered
limit diagram of affine test schemes to a cofiltered limit diagram of affine schemes.  Then
`J = I`, `Ψ = 𝟭 I`, the system is `G ⋙ Φ` and its limit is `Φ.mapCone c`, so the morphism into
`Φ` of the limiting test scheme is the identity and the transfer at a stage is `hcond` there.

For the presentation of the source's proof, where `Φ T = V ×_Y T`, the hypotheses `hlim` and
`haff` hold exactly when the chart `V` is affine over `Y`.  This statement records that the
per-system hypothesis of the presentation form is implied by them, so the per-system form
generalises the functorial one. -/
theorem flatDimensionFunctor_limitPreserving_of_affinePresentation
    (D : FlatDimensionSituation.{max u w w'} B₁ S₁ hS₁) (n : ℕ)
    (E : _root_.AlgebraicGeometry.FlatDimensionSituation.{max u w w'})
    [QuasiCompact E.f] [LocallyOfFinitePresentation E.f] [E.F.IsFinitePresentation]
    (Φ : SchemesOver D.Y ⥤ Over E.S)
    (hcond : ∀ T : SchemesOver D.Y, D.IsFlatInDimensionsGEAfterBaseChange T n ↔
      E.IsFlatInDimensionsGEAfterBaseChange (Φ.obj T))
    (hlim : ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I]
      (G : I ⥤ SchemesOver D.Y) (c : Cone G), IsLimit ((testSchemeFunctor D.Y).mapCone c) →
        (∀ i, IsAffine ((testSchemeFunctor D.Y).obj (G.obj i))) →
        IsAffine ((testSchemeFunctor D.Y).obj c.pt) →
        IsLimit ((Over.forget E.S).mapCone (Φ.mapCone c)))
    (haff : ∀ T : SchemesOver D.Y, IsAffine ((testSchemeFunctor D.Y).obj T) →
      IsAffine ((Over.forget E.S).obj (Φ.obj T))) :
    LimitPreserving.{max u w w', max u w w', w, w'}
      (testSchemeFunctor D.Y) (D.flatDimensionFunctor n) := by
  refine flatDimensionFunctor_limitPreserving_of_presentation.{u, w, w'} D n E Φ hcond
    fun I _ _ G c hc hstage hpt => ?_
  exact ⟨I, inferInstance, inferInstance, 𝟭 I, G ⋙ Φ, Φ.mapCone c, hlim I G c hc hstage hpt,
    𝟙 _, fun j => haff _ (hstage j), haff _ hpt, fun j hj => (hcond (G.obj j)).2 hj⟩

/-- **Stacks 0CWW, clause (2).** In Situation 0CWU, if `f` is quasi-compact and locally of
finite presentation and `ℱ` is of finite presentation, then the functor `F_n` of equation 0CWV
is limit preserving.

The proof is the source's, with the chart presentation constructed rather than assumed.  Since
`F_n` is subterminal, limit preservation is descent of the condition of Stacks 0CWT along a
cofiltered inverse system of affine test schemes with affine limit
(`limitPreserving_flatDimensionFunctor_iff`), so a system `T = lim T_i` of affine test schemes
may be fixed first.  The presentation is then taken at one of its stages: for an index `i₀`, the
base change `X_{T_{i₀}}` is quasi-compact over the affine scheme underlying `T_{i₀}`, hence has
a surjective étale scheme chart `U` with affine scheme
(`AlgebraicGeometry.Space.exists_isAffine_isSurjective_chart_baseChangeSpace`, Stacks 03H6), and
`U ⟶ T_{i₀}` together with the restriction of `F_{T_{i₀}}` to `U` is a scheme-level situation
`E` of Stacks 05MT (`AlgebraicGeometry.Space.FlatDimensionSituation.stageSituation`).  That is
the chart presentation of the source read over a stage instead of over `Y`: because `T_{i₀}` is
represented, the target chart of the presenting square is the identity chart, so no base change
of a chart of `Y` and no affine open of one is needed, and the value of the presentation at a
test scheme `T'` over `T_{i₀}` is `T'` itself.

The identification of the two conditions at every test scheme over `T_{i₀}` is the theorem
`isFlatInDimensionsGEAfterBaseChange_iff_stageSituation` of that same namespace,
the chart clause of Stacks 0CWS at the square whose source chart is the base change of `U` and
whose target chart is the identity chart.  The system `K` of affine schemes over the scheme
underlying `T_{i₀}` is the given system restricted to the indices over `i₀`,
`CategoryTheory.Over.post` of `T ↦ T` on `CategoryTheory.Over i₀`; its limit is the given one
because `CategoryTheory.Over.forget i₀` is initial for a cofiltered index category.  Limit
preservation of the scheme-level `F'_n` is part (2) of **Stacks 05MV**,
`AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_limitPreserving`, applied to `E`
and to `K`; the three hypotheses it asks of `E` are the hypotheses on `f` and `ℱ` read on the
presentation, and are where they enter.

The schemes live in the maximum of the two index universes of the tested inverse system and a
third parameter.  That is the universe signature every limit-preservation statement in this
library carries: Stacks 05MY and part (2) of Stacks 05MV both have it, and it is the signature
at which the limit of a cofiltered system of affine schemes indexed by a category of those
universes exists in the first place.  It is also the signature of the statement of
Stacks 0CWW (limit preserving). -/
@[stacks 0CWW "clause (2), limit preservation of F_n"]
theorem flatDimensionFunctor_limitPreserving
    (D : FlatDimensionSituation.{max u w w'} B₁ S₁ hS₁) (n : ℕ)
    (hqc : IsQuasiCompact B₁ S₁ hS₁ D.f.hom)
    (hlfp : IsLocallyOfFinitePresentation B₁ S₁ hS₁ D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F) :
    LimitPreserving.{max u w w', max u w w', w, w'}
      (testSchemeFunctor D.Y) (D.flatDimensionFunctor n) := by
  refine (D.limitPreserving_flatDimensionFunctor_iff n).2 ?_
  intro I _ _ G c hc hstage hpt hT
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have hTaff : IsAffine ((BigFppfOver.toScheme B₁ S₁ hS₁).obj (G.obj i₀).left) := hstage i₀
  obtain ⟨U, hUaff, hUsurj⟩ := exists_isAffine_isSurjective_chart_baseChangeSpace
    B₁ S₁ hS₁ D.f hqc (G.obj i₀) hTaff
  have hEqc : QuasiCompact (D.stageSituation B₁ S₁ hS₁ n (G.obj i₀) U).f :=
    D.quasiCompact_stageSituation_f B₁ S₁ hS₁ n (G.obj i₀) hTaff U hUaff
  have hElfp : LocallyOfFinitePresentation (D.stageSituation B₁ S₁ hS₁ n (G.obj i₀) U).f :=
    D.locallyOfFinitePresentation_stageSituation_f B₁ S₁ hS₁ n hlfp (G.obj i₀) U
  have hEfp : (D.stageSituation B₁ S₁ hS₁ n (G.obj i₀) U).F.IsFinitePresentation :=
    D.isFinitePresentation_stageSituation_F B₁ S₁ hS₁ n hF (G.obj i₀) U
  have hE : LimitPreserving.{max u w w', 0, w, w'}
      (Over.forget (D.stageSituation B₁ S₁ hS₁ n (G.obj i₀) U).S)
      (D.stageSituation B₁ S₁ hS₁ n (G.obj i₀) U).flatDimensionFunctor :=
    @_root_.AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_limitPreserving.{u, w, w'}
      (D.stageSituation B₁ S₁ hS₁ n (G.obj i₀) U) hEqc hElfp hEfp
  have hd : IsLimit ((Over.forget (D.stageSituation B₁ S₁ hS₁ n (G.obj i₀) U).S).mapCone
      (((testSchemeFunctor D.Y).mapCone c).overPost i₀)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀)
      ((testSchemeFunctor D.Y).mapCone c)).symm hc
  obtain ⟨k, hk⟩ := (nonempty_isColimit_mapCocone_op_iff_of_subsingleton
    (D.stageSituation B₁ S₁ hS₁ n (G.obj i₀) U).flatDimensionFunctor
    (Over.post (X := i₀) (G ⋙ testSchemeFunctor D.Y))
    (((testSchemeFunctor D.Y).mapCone c).overPost i₀)).1
      (hE (Over i₀) (Over.post (X := i₀) (G ⋙ testSchemeFunctor D.Y))
        (((testSchemeFunctor D.Y).mapCone c).overPost i₀) hd
        (fun j => hstage j.left) hpt)
      ⟨⟨(D.isFlatInDimensionsGEAfterBaseChange_iff_stageSituation B₁ S₁ hS₁ n
        (c.π.app i₀) U hUsurj).1 hT⟩⟩
  exact ⟨k.left, (D.isFlatInDimensionsGEAfterBaseChange_iff_stageSituation B₁ S₁ hS₁ n
    (G.map k.hom) U hUsurj).2 hk.some.down⟩

end LimitPreservation

end FlatDimensionSituation

end AlgebraicGeometry.Space

end
