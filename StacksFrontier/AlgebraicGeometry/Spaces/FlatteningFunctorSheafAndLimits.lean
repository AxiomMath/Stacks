module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.TestSchemePullbacks
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFlattening
public import StacksFrontier.CategoryTheory.Sites.SubsingletonPresheaf

/-!
# The flattening functor as a presheaf on the test schemes: sheaf property and limits

In Situation 0CWX — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` of a big fppf
site together with a quasi-coherent `𝒪_X`-module `F` — equation 0CWY attaches to every scheme
`T` over `Y` the one-point set `{*}` when the base change `F_T` is flat over `T` and the empty
set otherwise.  Stacks 0CWZ asserts two things about the resulting functor `F_flat`: that it
satisfies the sheaf property for the fpqc topology, and that it is limit preserving when `f` is
quasi-compact and locally of finite presentation and `F` is of finite presentation.

This file proves part (1) in full, and of part (2) the half that needs no hypothesis, for the
functor `F_flat` of `StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctor.lean`.  Both
assertions are about a *subterminal* presheaf: every value of `F_flat` has at most one element,
so the sheaf property splits into a separatedness half, which holds for formal reasons, and a
gluing half, which is fpqc descent of flatness of the base-changed module; and limit
preservation splits into a filtered-colimit bookkeeping half, which again holds for formal
reasons, and the assertion that flatness over a cofiltered limit of affine test schemes already
holds at a stage.  Both halves of part (1) are proved here.  The geometric half of part (2) is
isolated here as the right-hand side of an equivalence and discharged in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctorLimitPreserving.lean`, where part (2) is
proved in full.

## Main definitions

* `AlgebraicGeometry.Space.FlatnessSituation.testScheme`: the underlying scheme of a test
  scheme over `Y`, functorially.
* `AlgebraicGeometry.Space.FlatnessSituation.testFpqcPrecoverage`: the fpqc precoverage on the
  test schemes over `Y`, pulled back from `AlgebraicGeometry.Scheme.fpqcPrecoverage`.

## Main results

* `AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_isSheaf_fpqcTopology` and
  `AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_isSheafFor_fpqc`: **Stacks 0CWZ
  part (1)**, that `F_flat` satisfies the sheaf property for the fpqc topology on the test
  schemes over `Y`, in the covering-sieve and the covering-presieve form.
* `AlgebraicGeometry.Space.FlatnessSituation.isFlatAfterBaseChange_of_jointlySurjective`:
  **fpqc descent of flatness of the base-changed module**, which is the geometric content of
  part (1).
* `AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_isSeparatedFor_fpqc`: the separatedness
  half of the sheaf condition, which holds for an arbitrary presieve.
* `AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_isSheafFor_iff` and
  `AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_isSheaf_fpqc_iff`: the sheaf property
  of part (1) is equivalent to fpqc descent of flatness of the base-changed module.
* `AlgebraicGeometry.Space.FlatnessSituation.subsingleton_colimitType_flatFunctor`: **the
  injectivity half of part (2)**, which needs none of its hypotheses.
* `AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_limitPreserving_iff`: part (2) is
  equivalent to the assertion that flatness of the base-changed module over a cofiltered limit
  of affine test schemes already holds over one of the stages.  That assertion is discharged,
  and part (2) proved in full, by
  `AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_limitPreserving` of
  `StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctorLimitPreserving.lean`.

## Implementation notes

The test schemes over `Y` are `AlgebraicGeometry.Space.SchemesOver`, the costructured arrows
from `AlgebraicGeometry.schemeSpaceFunctor`; the flatness condition at a test scheme is
`AlgebraicGeometry.Space.FlatnessSituation.IsFlatAfterBaseChange` and the functor is
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor`, both of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctor.lean`, where the functor is
unconditional: its action on morphisms is the final assertion of Stacks 05VW.  An earlier
revision of this file defined the functor here instead, with that action carried as a
hypothesis; nothing is assumed about it now.  The functor takes values in a subtype of `PUnit`,
a one-point set where the condition holds and empty where it does not, which is the reading of
equation 0CWY; the same shape is used by
`AlgebraicGeometry.Space.FlatnessSituation.flatSubfunctor` of
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalFlattening.lean` for the companion packaging of
`F_flat` as a subfunctor of `Y`.

The sheaf property is stated twice: for the covering sieves of
`AlgebraicGeometry.Space.fpqcTopology`, the Grothendieck topology the pulled-back precoverage
generates, which is the form the sibling tag Stacks 083H is stated in; and for every covering
presieve of `AlgebraicGeometry.Space.FlatnessSituation.testFpqcPrecoverage`, which is the form
the source's own definition of a sheaf on a site uses.  The two are not identified here —
`CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange` would need
base-change stability of the pulled-back precoverage, which is not established — so the presieve
form is deduced from the sieve form directly: every arrow of the sieve a presieve generates
factors through a member of the presieve, and flatness of the base change is inherited along
that factorisation by the final assertion of Stacks 05VW.
`AlgebraicGeometry.isSheaf_fpqc_of_isSheafFor` of
`StacksFrontier/AlgebraicGeometry/Topologies/Fpqc/SheafCondition.lean` makes the same passage for
presheaves on the big fppf category itself.

Separatedness is proved for an arbitrary presieve and the fpqc hypothesis is carried only so
that the statement is the one the source makes; nothing about the fpqc topology is used, because
the values of a subterminal functor have at most one element.

## How the gluing half of part (1) is proved

The gluing half is fpqc descent of flatness: for a flat family `T_i ⟶ T` of test schemes which
is jointly surjective on points, flatness of every `F_{T_i}` over `T_i` implies flatness of
`F_T` over `T`.  This is the descent direction of Morphisms of Spaces, Stacks 05VW, which the
source's proof cites, and it is assembled here from four inputs.

* Flatness of a quasi-coherent module over the target is a condition on geometric points alone,
  `AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtGeometricPoint` of
  `StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleGeometricPointCriterion.lean`, which is
  Stacks 05VU; so it is enough to descend flatness at each geometric point of `X_T`.
* Part (2) of Stacks 05VW,
  `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_of_modulePullback` of
  `StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleBaseChange.lean`, descends flatness at one
  geometric point of `X_{T_i}` to its image in `X_T`, the comparison square of the two
  base-change spaces being cartesian — `AlgebraicGeometry.Space.isPullback_baseChangeMap`.
* The *geometric* points of `X_T` need not lift to `X_{T_i}`, and no such lift is used: only the
  points of Stacks 03BU lift, by surjectivity of the comparison map out of the points of a
  cartesian square — `AlgebraicGeometry.Space.exists_point_of_isPullback`, Stacks 03H4 — and
  every point of `X_{T_i}` is the image of a geometric point by
  `AlgebraicGeometry.Space.exists_geometricRepresentative`.  Flatness at a geometric point
  depends on it only through its point of `|X_T|`, again by Stacks 05VU, so a geometric point
  over the same point of `|X_T|` is as good as the given one.
* Flatness of the base morphism at the relevant point, which Stacks 05VW part (2) asks for, is
  `AlgebraicGeometry.Space.isFlat_iff_forall_isFlatAt`, Stacks 03MM.

The covering family itself is extracted from a covering sieve by
`AlgebraicGeometry.Space.exists_isFpqcCovering_jointlySurjective_family_of_mem_fpqcTopology` of
`StacksFrontier/AlgebraicGeometry/Spaces/TestSchemePullbacks.lean`, which is the same entry point
the sibling tag Stacks 083H uses in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapLociFpqcSheaf.lean`.  No hypothesis on `f` or on
`F` beyond quasi-coherence of `F`, which is part of the standing data of Stacks 0CWX, enters:
the source states part (1) without any, and so is it proved.

## How part (2) is proved

Part (2) is proved in full, at the source's own hypotheses and with nothing carried, but in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctorLimitPreserving.lean`, as
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_limitPreserving`.  What is proved here is
the part of it that needs no hypothesis at all: the injectivity half,
`subsingleton_colimitType_flatFunctor`, and the reduction
`flatFunctor_limitPreserving_iff` of the rest to the geometric input the source cites — the main
clause of Stacks 08K0, that for a cofiltered limit of affine test schemes flatness of the
base-changed *module* over the limit descends to a stage.

For a subterminal functor that clause *is* the conclusion of part (2), so it is never carried as
a hypothesis — a statement assuming it and concluding limit preservation would assume its own
conclusion.  It appears only as the right-hand side of the equivalence, and it is discharged
from the scheme-level descent theorem Stacks 05LY,
`AlgebraicGeometry.eventually_isFlatOver_modulePullback` of
`StacksFrontier/AlgebraicGeometry/Limits/RelativeApproximation/FlatDescent.lean`.  In particular the
gap that the companion tag Stacks 0CWW carries as the hypothesis `hcond` of
`AlgebraicGeometry.Space.FlatDimensionSituation.flatDimensionFunctor_limitPreserving` is not
carried here.

The passage from the condition at a test scheme to the statement Stacks 05LY tests is
`StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctorChartReduction.lean`: the condition is
read on one surjective étale scheme chart over the test scheme
(`AlgebraicGeometry.Space.FlatnessSituation.TestChart.isFlatAfterBaseChange_iff`), a chart base
changes along a morphism of test schemes
(`AlgebraicGeometry.Space.FlatnessSituation.TestChart.baseChange`), the chart restriction of
`F_{T'}` to the base-changed chart is the Zariski inverse image of the chart restriction of
`F_T` (`AlgebraicGeometry.Space.FlatnessSituation.TestChart.restrictToChartBaseChange`, which
rests on `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, the compatibility of
Stacks 03M0 with Stacks 03LW), and that reading is identified with the one Stacks 05LY tests —
the chart restriction lives on the scheme of the fibre product formed *in the site*, while
Stacks 05LY tests flatness over the second projection of the fibre product formed *in schemes*,
and the two differ by the comparison isomorphism of the pullback-preserving functor
`AlgebraicGeometry.BigFppfOver.toScheme`, across which flatness is invariant
(`AlgebraicGeometry.Space.FlatnessSituation.TestChart.isFlatAfterBaseChange_baseChange_iff`).

The one restriction is on the index universes.  The equivalence below is universe-polymorphic in
`u`, `w` and `w'` independently, whereas Stacks 05LY constrains its index category by
`CategoryTheory.EssentiallySmall.{u}`; so part (2) is proved at `w = w' = u`, which is an
instance of the equivalence below and not a weakening of it.  Unlike the scheme-level
Stacks 05MY, `AlgebraicGeometry.FlatnessSituation.flatFunctor_limitPreserving` of
`StacksFrontier/AlgebraicGeometry/Flatness/FlatteningFunctor/LimitPreserving.lean`, whose schemes
live in the maximum of the two index universes and so leave them free below it, the universe of
the schemes here is pinned by the big fppf site.

## References

* [Stacks Project, Tag 0CWZ](https://stacks.math.columbia.edu/tag/0CWZ)
* [Stacks Project, Tag 0CWX](https://stacks.math.columbia.edu/tag/0CWX)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 083H](https://stacks.math.columbia.edu/tag/083H)
* [Stacks Project, Tag 05MY](https://stacks.math.columbia.edu/tag/05MY)
* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
* [Stacks Project, Tag 0CWW](https://stacks.math.columbia.edu/tag/0CWW)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace AlgebraicGeometry.Space

namespace FlatnessSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The scheme of the big fppf site underlying a test scheme over `Y`, functorially. -/
abbrev testScheme (D : FlatnessSituation.{u} B S hS) : SchemesOver D.Y ⥤ Scheme.{u} :=
  CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙ BigFppfOver.toScheme B S hS

/-- The fpqc precoverage on the test schemes over `Y`: a presieve covers when the family of
underlying schemes is an fpqc covering. -/
abbrev testFpqcPrecoverage (D : FlatnessSituation.{u} B S hS) :
    Precoverage (SchemesOver D.Y) :=
  Scheme.fpqcPrecoverage.comap D.testScheme

/-- **Stacks 0CWZ, part (1), the separatedness half of the fpqc sheaf property.** Two sections
of `F_flat` over a test scheme which agree on the members of an fpqc covering presieve of that
test scheme are equal.

Every value of `F_flat` has at most one element, so this holds for an arbitrary presieve; the
fpqc hypothesis is carried only so that the statement is the one the source makes.  The
existence half of the sheaf condition is fpqc descent of flatness of the base-changed module; it
is proved separately, so that part (1) holds in full, as
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_isSheafFor_fpqc` and
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_isSheaf_fpqcTopology`. -/
@[stacks 0CWZ "part (1), separatedness half only; gluing half not proved"]
theorem flatFunctor_isSeparatedFor_fpqc (D : FlatnessSituation.{u} B S hS)
    {T : SchemesOver D.Y} (R : Presieve T)
    (_hR : R ∈ D.testFpqcPrecoverage T) :
    Presieve.IsSeparatedFor D.flatFunctor R := fun _ t₁ t₂ _ _ =>
  Subtype.ext (Subsingleton.elim t₁.val t₂.val)

/-- `F_flat` satisfies the sheaf condition for a presieve exactly when flatness of the
base-changed module descends along that presieve.  The separatedness half of the sheaf condition
is `flatFunctor_isSeparatedFor_fpqc`; what the right-hand side adds is the existence of an
amalgamation, which for a subterminal functor is precisely descent.

This is a reduction, not part (1): the right-hand side is the geometric input the source's proof
cites.  For an fpqc covering presieve that input is
`AlgebraicGeometry.Space.FlatnessSituation.isFlatAfterBaseChange_of_jointlySurjective`, so this
equivalence is what turns it into part (1). -/
theorem flatFunctor_isSheafFor_iff (D : FlatnessSituation.{u} B S hS)
    {T : SchemesOver D.Y} (R : Presieve T) :
    Presieve.IsSheafFor D.flatFunctor R ↔
      ((∀ ⦃T' : SchemesOver D.Y⦄ ⦃g : T' ⟶ T⦄, R g → D.IsFlatAfterBaseChange T') →
        D.IsFlatAfterBaseChange T) := by
  constructor
  · intro hs hall
    obtain ⟨t, -, -⟩ := hs (fun _ _ hg => ⟨PUnit.unit, hall hg⟩)
      (by
        intro _ _ _ _ _ _ _ _ _ _
        exact Subtype.ext rfl)
    exact t.2
  · intro hd x _
    refine ⟨⟨PUnit.unit, hd fun _ _ hg => (x _ hg).2⟩, ?_, ?_⟩
    · intro _ _ _
      exact Subtype.ext rfl
    · intro _ _
      exact Subtype.ext rfl

/-- The fpqc sheaf property of `F_flat`, in the form of the sheaf condition for every fpqc
covering presieve, is equivalent to fpqc descent of flatness of the base-changed module.

This is the full content of part (1) of Stacks 0CWZ reduced to the geometric input its proof
cites.  Both sides hold: the left-hand side is
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_isSheafFor_fpqc`, which carries the tag,
so this equivalence records the reduction and carries none. -/
theorem flatFunctor_isSheaf_fpqc_iff (D : FlatnessSituation.{u} B S hS) :
    (∀ (T : SchemesOver D.Y) (R : Presieve T), R ∈ D.testFpqcPrecoverage T →
        Presieve.IsSheafFor D.flatFunctor R) ↔
      (∀ (T : SchemesOver D.Y) (R : Presieve T), R ∈ D.testFpqcPrecoverage T →
        (∀ ⦃T' : SchemesOver D.Y⦄ ⦃g : T' ⟶ T⦄, R g → D.IsFlatAfterBaseChange T') →
          D.IsFlatAfterBaseChange T) :=
  ⟨fun H T R hR => (D.flatFunctor_isSheafFor_iff R).mp (H T R hR),
    fun H T R hR => (D.flatFunctor_isSheafFor_iff R).mpr (H T R hR)⟩

/-! ### Fpqc descent of flatness of the base-changed module -/

/-- **Flatness of the base-changed module at a geometric point coming from a flat test scheme
over `T`.**  Let `g : T' ⟶ T` be a morphism of test schemes which is flat on the algebraic
spaces they represent, and suppose `F_{T'}` is flat over `T'`.  Then `F_T` is flat over `T` at
every geometric point of `X_T` whose point of `|X_T|` is in the image of `|X_{T'}|`.

This is Stacks 05VW, part (2), read at that geometric point.  The comparison square of the two
base-change spaces over `g` is cartesian, so a geometric point of `X_{T'}` above the given point
of `|X_T|` carries flatness of `F_{T'}` at it down to flatness of `F_T` at its image.  That
image need not be the given geometric point, only a geometric point with the same point of
`|X_T|`; flatness at a geometric point depends on it through that point alone, by Stacks 05VU,
so the two are interchangeable. -/
private theorem isFlatOverAtGeometricPoint_baseChangeModule_of_mem_range
    (D : FlatnessSituation.{u} B S hS) {T T' : SchemesOver D.Y} (g : T' ⟶ T)
    (hg : IsFlat B S hS ((schemeSpaceFunctor B S hS).map g.left).hom)
    (hT' : D.IsFlatAfterBaseChange T')
    (x : GeometricPoint B S hS (baseChangeSpace D.f T).1)
    (hx : x.image ∈ Set.range
      (pointsMap B S hS (baseChangeSpace D.f T').1 (baseChangeMap D.f g).hom)) :
    IsFlatOverAtGeometricPoint B S hS (baseChangeInclusion D.f T) (D.baseChangeModule T) x := by
  have hqcT : (D.baseChangeModule T).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (baseChangeProjection D.f T) D.F D.quasicoherent
  have hqc' : ((modulePullback B S hS (baseChangeMap D.f g)).obj
      (D.baseChangeModule T)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (baseChangeMap D.f g) (D.baseChangeModule T) hqcT
  obtain ⟨q, hq⟩ := hx
  obtain ⟨x', hx'⟩ := exists_geometricRepresentative B S hS (baseChangeSpace D.f T').1 q
  have hpull : IsFlatOver B S hS (baseChangeSpace D.f T').2
      (baseChangeInclusion D.f T').hom
      ((modulePullback B S hS (baseChangeMap D.f g)).obj (D.baseChangeModule T)) :=
    IsFlatOver.of_iso B S hS (baseChangeSpace D.f T').2
      ((modulePullbackTriangle B S hS (baseChangeMap_comp_projection D.f g)).app D.F) hT'
  have hat := isFlatOverAtGeometricPoint_of_modulePullback B S hS
    (isPullback_baseChangeMap D.f g) (D.baseChangeModule T) x'
    ((isFlat_iff_forall_isFlatAt B S hS _).mp hg _)
    ((isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS (baseChangeInclusion D.f T')
      ((modulePullback B S hS (baseChangeMap D.f g)).obj (D.baseChangeModule T))).mp hpull x')
  have himage : (geometricPointMap (baseChangeMap D.f g).hom x').image = x.image := by
    rw [geometricPointMap_image, hx', hq]
  obtain ⟨d, u, hcp, hflat⟩ :=
    (isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint B S hS
      (baseChangeInclusion D.f T) (D.baseChangeModule T) _).mpr hat
  exact (isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint B S hS
    (baseChangeInclusion D.f T) (D.baseChangeModule T) x).mp ⟨d, u, himage ▸ hcp, hflat⟩

/-- **Fpqc descent of flatness of the base-changed module.**  If a family `T_i ⟶ T` of test
schemes over `Y` is flat and jointly surjective on the points of the algebraic spaces the test
schemes represent, and `F_{T_i}` is flat over `T_i` for every `i`, then `F_T` is flat over `T`.

Flatness of a quasi-coherent module over the target is a condition at every geometric point of
the source, by Stacks 05VU, and the base-change spaces `X_{T_i} ⟶ X_T` are jointly surjective on
points because the comparison squares are cartesian — Stacks 03H4.  So every geometric point of
`X_T` is covered by some `X_{T_i}`, where
`AlgebraicGeometry.Space.FlatnessSituation.isFlatOverAtGeometricPoint_baseChangeModule_of_mem_range`
applies. -/
theorem isFlatAfterBaseChange_of_jointlySurjective (D : FlatnessSituation.{u} B S hS)
    {I : Type v} {T : SchemesOver D.Y} (T' : I → SchemesOver D.Y) (k : ∀ i, T' i ⟶ T)
    (hflat : ∀ i, IsFlat B S hS ((schemeSpaceFunctor B S hS).map (k i).left).hom)
    (hjs : IsJointlySurjective B S hS (fun i ↦ (schemeSpace (T' i).left).1)
      fun i ↦ ((schemeSpaceFunctor B S hS).map (k i).left).hom)
    (hall : ∀ i, D.IsFlatAfterBaseChange (T' i)) :
    D.IsFlatAfterBaseChange T := by
  have hqcT : (D.baseChangeModule T).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (baseChangeProjection D.f T) D.F D.quasicoherent
  refine (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS
    (baseChangeInclusion D.f T) (D.baseChangeModule T)).mpr fun x ↦ ?_
  obtain ⟨i, t, ht⟩ := (isJointlySurjective_iff B S hS _ _).mp hjs
    (pointsMap B S hS (baseChangeSpace D.f T).1 (baseChangeInclusion D.f T).hom x.image)
  obtain ⟨w, -, hw⟩ := exists_point_of_isPullback B S hS
    (isPullback_baseChangeMap D.f (k i)).flip t x.image ht
  exact D.isFlatOverAtGeometricPoint_baseChangeModule_of_mem_range (k i) (hflat i) (hall i) x
    ⟨w, hw⟩

/-- **Stacks 0CWZ, part (1).**  The functor `F_flat` satisfies the sheaf property for the fpqc
topology on the test schemes over `Y`.

`F_flat` is subterminal, so the sheaf condition for a covering sieve is the implication from
flatness of the base-changed module at every member of the sieve to flatness at its target.  A
covering sieve of the fpqc topology contains a flat family which is jointly surjective on points
— `AlgebraicGeometry.Space.exists_isFpqcCovering_jointlySurjective_family_of_mem_fpqcTopology` —
and flatness of the base-changed module descends along such a family by
`AlgebraicGeometry.Space.FlatnessSituation.isFlatAfterBaseChange_of_jointlySurjective`. -/
@[stacks 0CWZ "part (1)"]
theorem flatFunctor_isSheaf_fpqcTopology (D : FlatnessSituation.{u} B S hS) :
    Presheaf.IsSheaf (fpqcTopology D.Y) D.flatFunctor := by
  rw [Presheaf.isSheaf_iff_nonempty_of_subsingleton]
  intro T R hR hne
  rw [D.nonempty_flatFunctor_obj_iff T]
  obtain ⟨I, T', k, hk, hcov, hjs⟩ :=
    exists_isFpqcCovering_jointlySurjective_family_of_mem_fpqcTopology hR
  exact D.isFlatAfterBaseChange_of_jointlySurjective T' k (fun i ↦ hcov.1 i) hjs
    fun i ↦ (D.nonempty_flatFunctor_obj_iff (T' i)).1 (hne (k i) (hk i))

/-- **Stacks 0CWZ, part (1)**, in the presieve form: `F_flat` satisfies the sheaf condition for
every fpqc covering presieve of a test scheme over `Y`.

The sieve a covering presieve generates is a covering sieve of the fpqc topology, and every
member of that sieve factors through a member of the presieve, along which flatness of the
base-changed module is inherited by the final assertion of Stacks 05VW. -/
@[stacks 0CWZ "part (1), the sheaf condition for a covering presieve"]
theorem flatFunctor_isSheafFor_fpqc (D : FlatnessSituation.{u} B S hS)
    {T : SchemesOver D.Y} (R : Presieve T) (hR : R ∈ D.testFpqcPrecoverage T) :
    Presieve.IsSheafFor D.flatFunctor R := by
  refine (D.flatFunctor_isSheafFor_iff R).mpr fun hall ↦ ?_
  refine (D.nonempty_flatFunctor_obj_iff T).1
    ((Presheaf.isSheaf_iff_nonempty_of_subsingleton _ _).1 D.flatFunctor_isSheaf_fpqcTopology
      T (Sieve.generate R) (Precoverage.generate_mem_toGrothendieck hR) ?_)
  rintro T'' h ⟨W, a, b, hb, rfl⟩
  exact (D.nonempty_flatFunctor_obj_iff T'').2 (D.isFlatAfterBaseChange_of_hom a (hall hb))

/-- The filtered colimit of a diagram of sets whose every value has at most one element has at
most one element. -/
private theorem subsingleton_colimitType {J : Type w} [Category.{w'} J] [IsFiltered J]
    {G : J ⥤ Type u} (hG : ∀ j, Subsingleton (G.obj j)) : Subsingleton G.ColimitType := by
  classical
  refine ⟨fun a b => ?_⟩
  obtain ⟨i, x, rfl⟩ := G.ιColimitType_jointly_surjective a
  obtain ⟨j, y, rfl⟩ := G.ιColimitType_jointly_surjective b
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists ({i, j} : Finset J)
  have : Subsingleton (G.obj k) := hG k
  exact G.ιColimitType_eq_of_map_eq_map x y
    (hk (Finset.mem_insert_self i {j})).some
    (hk (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))).some
    (Subsingleton.elim _ _)

/-- **Stacks 0CWZ, part (2), the uniqueness half of limit preservation.** Along a cofiltered
system of test schemes over `Y`, the filtered colimit of the values of `F_flat` has at most one
element.

Limit preservation asserts that the canonical map from that colimit to the value of `F_flat` at
the limit test scheme is a bijection.  This is its injectivity half: the target also has at most
one element (`flatFunctor_obj_subsingleton`), so no two classes in the colimit can be separated.
It needs none of the hypotheses of part (2) — not quasi-compactness or local finite presentation
of `f`, not finite presentation of `F` — and no restriction on the index universes.  The
surjectivity half does need them and is
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_limitPreserving` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctorLimitPreserving.lean`, which is part (2)
in full. -/
@[stacks 0CWZ "part (2), injectivity half only; surjectivity not proved"]
theorem subsingleton_colimitType_flatFunctor (D : FlatnessSituation.{u} B S hS)
    {I : Type w} [Category.{w'} I] [IsCofiltered I]
    (E : I ⥤ SchemesOver D.Y) :
    Subsingleton ((E.op ⋙ D.flatFunctor).ColimitType) :=
  subsingleton_colimitType fun j => flatFunctor_obj_subsingleton D (E.op.obj j)

/-- A cocone of sets over a filtered index category whose every value has at most one element is
a colimit cocone as soon as every element of its vertex comes from a stage. -/
private theorem nonempty_isColimit_of_subsingleton {J : Type w} [Category.{w'} J] [IsFiltered J]
    {G : J ⥤ Type u} (c : Cocone G) (hG : ∀ j, Subsingleton (G.obj j))
    (hcover : ∀ y : c.pt, ∃ (j : J) (x : G.obj j), c.ι.app j x = y) :
    Nonempty (IsColimit c) := by
  classical
  apply (Types.isColimit_iff_coconeTypesIsColimit c).2
  show (G.coconeTypesEquiv.symm c).IsColimit
  refine ⟨?_, ?_⟩
  · intro a b _
    exact (subsingleton_colimitType hG).elim a b
  · intro y
    obtain ⟨j, x, hx⟩ := hcover y
    refine ⟨G.ιColimitType j x, ?_⟩
    rw [G.descColimitType_ιColimitType_apply]
    exact hx

/-- Limit preservation of `F_flat` in the sense of Stacks 049J is equivalent to the assertion
that flatness of the base-changed module over a cofiltered limit of affine test schemes already
holds over one of the stages.

This is part (2) of Stacks 0CWZ reduced to the geometric input its proof cites — the main clause
of Stacks 08K0 for a quasi-coherent module.  Both sides hold at the source's hypotheses, the
left-hand side being
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_limitPreserving` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctorLimitPreserving.lean`, which carries the
tag, so this equivalence records the reduction and carries none.  The filtered-colimit
bookkeeping, which is what remains of part (2) once the right-hand side is granted, is
`nonempty_isColimit_of_subsingleton` together with
`CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`.

The source's hypotheses for part (2) — `f` quasi-compact and locally of finite presentation and
`F` of finite presentation — are the inputs of the right-hand side and are not needed for the
equivalence; the equivalence is also universe-polymorphic in `w` and `w'`, while the proof of
the right-hand side needs the index universes to be that of the schemes. -/
theorem flatFunctor_limitPreserving_iff (D : FlatnessSituation.{u} B S hS) :
    LimitPreserving.{u, u, w, w', u + 1, u} D.testScheme D.flatFunctor ↔
      ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I] (E : I ⥤ SchemesOver D.Y)
        (c : Cone E), IsLimit (D.testScheme.mapCone c) →
          (∀ i, IsAffine (D.testScheme.obj (E.obj i))) →
          IsAffine (D.testScheme.obj c.pt) →
          D.IsFlatAfterBaseChange c.pt → ∃ i, D.IsFlatAfterBaseChange (E.obj i) := by
  constructor
  · intro H I _ _ E c hlim haff hpt hflat
    obtain ⟨j, x, -⟩ := Types.jointly_surjective_of_isColimit
      (H I E c hlim haff hpt).some (⟨PUnit.unit, hflat⟩ : D.flatFunctor.obj (Opposite.op c.pt))
    exact ⟨j.unop, x.2⟩
  · intro H I _ _ E c hlim haff hpt
    refine nonempty_isColimit_of_subsingleton _ (fun j => ?_) (fun y => ?_)
    · exact flatFunctor_obj_subsingleton D (E.op.obj j)
    · obtain ⟨i, hi⟩ := H I E c hlim haff hpt y.2
      exact ⟨Opposite.op i, ⟨PUnit.unit, hi⟩, Subtype.ext rfl⟩

end FlatnessSituation

end AlgebraicGeometry.Space

end
