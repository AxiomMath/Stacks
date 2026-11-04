module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSliceKInjective
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedAlongEquivalence

/-!
# Derived sections over an étale chart cross the chart comparisons

Let `X` be an algebraic space over a scheme `S` and let `U` be an étale scheme chart of `X`.
The derived sections `RΓ(U, E)` of an object of `D(𝒪_X)` are read on three further ringed
sites in turn, and this file carries them across the first two steps:

* across the slice: `RΓ(U, E)` is the derived sections at the final object `Over.mk (𝟙 U)` of
  the localization `X_étale/U`, applied to the derived restriction of `E` to that slice;
* across the two reindexings of
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean`: derived sections at
  an object of the small étale site of the algebraic space represented by `U`, and at an object
  of the small étale site of the *scheme* underlying `U`, agree with derived sections at the
  corresponding object on the site one step back.

## Main results

* `AlgebraicGeometry.Space.derivedSectionsOverFunctorIso`: restriction to the slice at `U`
  followed by sections at the slice's final object derives to the composite of the two derived
  functors.
* `AlgebraicGeometry.Space.derivedSectionsOverFunctorObjIso`: the same read at an object, with
  `RΓ(U, -)` itself — `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections`,
  which is what `AlgebraicGeometry.Space.chartDerivedSections` is — on the left.
* `AlgebraicGeometry.Space.derivedSectionsChartLocalizationReindexIso`: derived sections cross
  the reindexing of Stacks 04M0.
* `AlgebraicGeometry.Space.derivedSectionsRepresentedSchemeReindexIso`: derived sections cross
  the comparison between a representable algebraic space and its scheme.

## The crossing of the slice, and the spelling it is forced into

The underived input is an *equality* of functors: for any sheaf of rings `R` on any site and any
object `U`,

`SheafOfModules.overFunctor R U ⋙ SheafOfModules.evaluation (R.over U) (op (Over.mk (𝟙 U)))`

is `SheafOfModules.evaluation R (op U)`, the final object of `Over U` being `Over.mk (𝟙 U)` and
the localized structure sheaf taking the value `R(U)` there by
`AlgebraicGeometry.RingedSite.over_O_obj_obj`.  That identity is proved, as
`AlgebraicGeometry.RingedSite.overEvaluationIso`, and it is an `Iso.refl`.

The derived statement is `Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes` at
`F = overFunctor`, `G = Γ(Over.mk (𝟙 U), -)`, whose hypothesis
`Stacks.Cohomology.LerayUnbounded.ComputesSecond` is proved as
`AlgebraicGeometry.Space.computesSecond_overFunctor_evaluation`.  Both inputs are therefore in
hand, and what remains is a question of spelling.

**`derivedCompIsoOfComputes` forces one target category on `G` and on `H`.**  Its three
categories are `A`, `B`, `C` with `G : B ⥤ C` and `H : A ⥤ C`, so writing the conclusion with
`H = SheafOfModules.evaluation 𝒪_X (op U)` asks for that functor at the codomain
`ModuleCat ((𝒪_X.over U)(Over.mk (𝟙 U)))` rather than at its own `ModuleCat (𝒪_X(U))`.  The two
rings are equal — `AlgebraicGeometry.RingedSite.over_O_obj_obj` is an `rfl` — but not
*reducibly* so, and `CategoryTheory.Functor.Additive` carries the `CategoryTheory.Preadditive`
instances of both categories as arguments, which instance search compares at reducible
transparency only.  So `(SheafOfModules.evaluation 𝒪_X (op U)).Additive` is not synthesizable at
that goal, and no local instance of that type repairs it: declaring one elaborates its own
statement with the `Preadditive` instances synthesized directly, whereas the goal's come from
the `CategoryTheory.Abelian` binders of `Stacks.DerivedFunctor.totalRightDerived`, and the two
do not match either.  Pinning `CategoryTheory.Abelian` at both spellings of the ring of sections
does not repair it either; all of this was compiled, not assumed.

What *does* go through is leaving `H` as the composite — `derivedCompIsoOfComputes` with
`e = Iso.refl`, which is `AlgebraicGeometry.RingedSite.overEvaluationIso` itself — so that one
spelling of the ring of sections is used throughout.  Nothing is lost: the object-level
`derivedSectionsOverFunctorObjIso` below does name `RΓ(U, -)` on the left, the two functors
being equal, and that is the form the assembly consumes.

The localized sheaf of rings is written `𝒪_X.ringSheaf.over U` and not
`((smallEtaleRingedSite …).over U).ringSheaf` in this section, for the reason recorded in the
module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean`: the first is the codomain
spelling of `SheafOfModules.overFunctor`, and at the second the instances of `ComputesSecond`
are not synthesizable.  The reindexing section below is at the other spelling, because that is
the domain spelling of `AlgebraicGeometry.Space.chartLocalizationReindex`; the two are
definitionally equal.

## The crossing of the two reindexings

Both reindexings are additive *equivalences* of module categories, so the tool is
`Stacks.Injectives.derivedPrecompIso` — the transport of an unbounded right derived functor
along an equivalence of its source — and these are its first consumers anywhere.  Its sibling
`Stacks.Injectives.totalRightDerivedPrecompIso` is the same statement for an arbitrary functor
`K(B) ⥤ H` out of the homotopy category, and it is `derivedPrecompIso` that fits here: the
functor being derived is an additive functor between abelian categories, namely evaluation.

The underived input is again an equality, by `rfl`:

`chartLocalizationReindex ⋙ Γ(W, -) = Γ(e.functor.obj W, -)`

for `e` the equivalence of Stacks 04M0, the reindexing being `SheafOfModules.pushforward` along
`e.functor` with the identity structure map.  The statements below are therefore written with
the composite on the left, which is that same functor at the spelling whose instances resolve.

## What the composite of the three statements costs

The three statements below do compose — at the identity chart
`AlgebraicGeometry.Space.idEtaleChart` for the first reindexing and at
`AlgebraicGeometry.SmallEtale.final` of the chart's scheme for the second — and the composite is
*true*: with the heartbeat ceiling raised it elaborates, with no unproved placeholder and no
missing input.
It does not fit the default ceiling, and the following numbers say where the cost is.  They are
`#count_heartbeats` on `leanprover/lean4:v4.34.0-rc2` at this commit, in a context with the
`local instance`s of this file, of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean` re-enabled.

* Each of the three statements *applied* costs nothing: 353, 393 and 359 heartbeats.
* `derivedSectionsOverFunctorObjIso ≪≫ (derivedSectionsChartLocalizationReindexIso … ).app _`
  costs **355,090**.
* that composite `≪≫ (derivedSectionsRepresentedSchemeReindexIso … ).app _` costs
  **4,664,592**.

**The cost is not the derived-category models, and pinning them does not touch it.**  Across the
second junction the identification of the two rings of sections,

`(chartRingedSite B S hS X U).ringSheaf.obj.obj (op (idEtaleChart …))
  = (representedSchemeRingedSite B S hS …).ringSheaf.obj.obj (op (SmallEtale.final …))`

is `rfl` at **816** heartbeats, and the same holds at the first junction, where

`((smallEtaleRingedSite B S hS F hF).ringSheaf.over U).obj.obj (op (Over.mk (𝟙 U)))
  = (chartRingedSite B S hS X U).ringSheaf.obj.obj (op (idEtaleChart …))`

is `rfl` inside the default ceiling.  What costs **6,707,816** heartbeats is the *underived*
equality of the second junction,

`representedSchemeReindex ⋙ Γ(SmallEtale.final …, -) = Γ(idEtaleChart …, -)`,

by `rfl` — the one the section above records as holding "on the nose".  It does hold; it is
expensive.  The reason is the shape of the two sides and not their content: their heads are
`CategoryTheory.Functor.comp` on the left and `SheafOfModules.evaluation` on the right, so the
unifier cannot use congruence and reduces both to structure literals, comparing the `obj` and
`map` fields through the concrete site terms — `AlgebraicGeometry.Space.smallEtaleRingedSite`,
`AlgebraicGeometry.Space.chartSpace`,
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` and the structure sheaves.  **At
opaque data the same equality is free**: for any site, any continuous `G` and any object `W`,

`SheafOfModules.pushforward (𝟙 ((G.sheafPushforwardContinuous RingCat J K).obj R)) ⋙
  SheafOfModules.evaluation _ (op W) = SheafOfModules.evaluation R (op (G.obj W))`

is `rfl` and costs nothing, and both reindexings here are that functor.  So the route for the
composite is to keep the two heads equal at every step — to reduce the spelling in equalities
whose two sides are both `Functor.comp`, or both `SheafOfModules.evaluation`, and never to let a
`CategoryTheory.Iso.trans` put a `Functor.comp` against an `evaluation`.  Stating the generic
equality and *instantiating* it against a stated concrete equality is not that route and does not
help: the instantiation performs the same unification, and exceeds the ceiling too.

Two further facts about the cost.

Splitting the composite into separate declarations does not help: the heartbeat counter is
per-declaration, but each junction on its own is already over the ceiling.

The typing of the chart is not the obstruction it looks like.  All three statements below accept
`U` at either `(smallEtaleRingedSite B S hS F hF).C` or `AlgebraicGeometry.Space.SmallEtale`, and
`AlgebraicGeometry.Space.derivedSectionsChartLocalizationReindexIso` applies at both.  What is not
writable is `CategoryTheory.Over U` in a position where its object universe is already fixed to
`u + 1`: `Over` carries the free universe of the `PUnit` of its `CategoryTheory.Comma`, so
`Category (Over U)` there asks instance search to solve `max (u + 1) ?w =?= u + 1`, which has no
solution.  Writing `((smallEtaleRingedSite B S hS F hF).over U).C` instead takes the instance from
`AlgebraicGeometry.RingedSite.category` and the question does not arise.  Independently, the
`local instance`s of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean` fire only when the
algebraic space is passed as a *variable* `X : AlgebraicGeometry.Space.AlgebraicSpaces B S hS`:
they are keyed on `X.1` and `X.2`, and against an anonymous constructor `⟨F, hF⟩` instance search
cannot invert the two projections.

## References

* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and
-- `Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck` are removed as instances for this
-- file, for the reason recorded in the implementation notes of
-- `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean`: they answer
-- `Abelian (SheafOfModules …)` and `IsGrothendieckAbelian (SheafOfModules …)` with the module
-- universe fixed to the join of the universes of the site and the rings, and a search reaching
-- one of them first ends in a universe constraint with no solution rather than in a recoverable
-- failure.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

/-! ### Derived sections across the slice at a chart -/

section Slice

attribute [local instance] smallEtaleRingedSite_essentiallySmall
  hasSheafifyAddCommGrp_smallEtaleRingedSite
  wEqualsLocallyBijectiveAddCommGrp_smallEtaleRingedSite
  isGrothendieckAbelian_modules hasRightDerivedFunctor_chartSections

-- The three derived-category models this section runs on are the `local instance`s of
-- `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean`, re-enabled here
-- rather than restated: they are `CategoryTheory.HasDerivedCategory.standard` at the
-- 𝒪_F-modules, at the 𝒪_F|_U-modules on the slice at `U`, and at the modules of sections
-- of the localized structure sheaf over the final object of the slice.  They are named there,
-- rather than synthesized, because instance search cannot produce
-- `CategoryTheory.HasDerivedCategory.standard` at a goal whose universe is already fixed to
-- `u + 1`: that would mean solving `max ?u_obj ?u_hom =?= u + 1` with both sides metavariables.
attribute [local instance] hasDerivedCategory_modules hasDerivedCategory_modules_over
  hasDerivedCategory_sections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (U : (smallEtaleRingedSite B S hS F hF).C)

/-- **Derived sections over an étale chart cross the slice at that chart.**  Restriction of
`𝒪_F`-modules to the slice over `U` followed by sections at the final object `Over.mk (𝟙 U)` of
the slice has, as its unbounded right derived functor, the composite of the two unbounded right
derived functors.

Both sides are right derived functors of one and the same functor on the unbounded homotopy
category: the comparison for `R(overFunctor)` is invertible on a K-injective complex with no
hypothesis, and the one for `RΓ(Over.mk (𝟙 U), -)` is invertible at the degreewise restriction
of a K-injective complex by `AlgebraicGeometry.Space.computesSecond_overFunctor_evaluation`,
which is Stacks 08FI at the slice together with Stacks 0D6G.  Uniqueness of right derived
functors identifies the two.

The left-hand side is `RΓ(U, -)` at the spelling the instances resolve at; see "The crossing of
the slice, and the spelling it is forced into" in the module documentation, and
`AlgebraicGeometry.Space.derivedSectionsOverFunctorObjIso` for the form naming `RΓ(U, -)`. -/
def derivedSectionsOverFunctorIso :
    Stacks.DerivedFunctor.totalRightDerived
        (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U ⋙
          SheafOfModules.evaluation.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U)
            (op (Over.mk (𝟙 U)))) ≅
      Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U) ⋙
        Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.evaluation.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U)
            (op (Over.mk (𝟙 U)))) :=
  (Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes _ _ _ (Iso.refl _)
    (computesSecond_overFunctor_evaluation B S hS F hF U)).symm

/-- **Derived sections over an étale chart cross the slice at that chart, at an object.**  For
an object `E` of `D(𝒪_F)`, the derived sections `RΓ(U, E)` are the derived sections at the final
object of the slice `X_étale/U` of the derived restriction of `E` to that slice.

This is `AlgebraicGeometry.Space.derivedSectionsOverFunctorIso` read at `E`, with the left-hand
side spelled through
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections` — the functor that
`AlgebraicGeometry.Space.chartDerivedSections` is built from.  The two functors on the left are
equal: derived sections over `U` derive `Γ(U, -)`, and `Γ(U, -)` is restriction to the slice
followed by sections at the slice's final object. -/
def derivedSectionsOverFunctorObjIso
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) :
    (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U).obj E ≅
      (Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.evaluation.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U)
            (op (Over.mk (𝟙 U))))).obj
        ((Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U)).obj
          E) :=
  (derivedSectionsOverFunctorIso B S hS F hF U).app E

end Slice

/-! ### Derived sections across the reindexing of Stacks 04M0 -/

section ChartLocalization

attribute [local instance] isGrothendieckAbelian_modules
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  hasSheafify_chartLocalization wEqualsLocallyBijective_chartLocalization
  abelian_chartLocalizationModules abelian_chartModules
  additive_chartLocalizationReindex

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)

/-- The `𝒪_X|_U`-modules on the localization of the small étale site at a chart form a
Grothendieck abelian category, at the `AlgebraicGeometry.RingedSite.ringSheaf` spelling of the
localized sheaf of rings and with the `CategoryTheory.Abelian` instance that
`AlgebraicGeometry.Space.abelian_chartLocalizationModules` supplies.

The content is `AlgebraicGeometry.Space.isGrothendieckAbelian_smallEtaleRingedSite_over`, which
is a global instance; it is restated because `CategoryTheory.IsGrothendieckAbelian` carries the
abelian structure as an argument, and the one baked into that instance is the one synthesized
generically, not the pinned one this section works with. -/
local instance isGrothendieckAbelian_chartLocalizationModules :
    IsGrothendieckAbelian.{u}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)) :=
  isGrothendieckAbelian_smallEtaleRingedSite_over B S hS X.1 X.2 U

/-- The standard derived category of the `𝒪_X|_U`-modules on the localization at a chart, named
for the reason recorded at `AlgebraicGeometry.Space.hasDerivedCategory_modules`. -/
local instance hasDerivedCategoryStandard_chartLocalizationModules :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)) :=
  HasDerivedCategory.standard _

/-- The standard derived category of the `𝒪`-modules on the small étale site of the algebraic
space represented by a chart, named for the reason recorded at
`AlgebraicGeometry.Space.hasDerivedCategory_modules`. -/
local instance hasDerivedCategoryStandard_chartModules :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O)) :=
  HasDerivedCategory.standard _

/-- The standard derived category of the modules of sections at an object of the small étale
site of the algebraic space represented by a chart, named for the reason recorded at
`AlgebraicGeometry.Space.hasDerivedCategory_modules`. -/
local instance hasDerivedCategoryStandard_chartSections
    (W : (chartRingedSite B S hS X U).C) :
    HasDerivedCategory.{u + 1}
      (ModuleCat.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O).obj.obj (op W))) :=
  HasDerivedCategory.standard _

/-- **Derived sections cross the reindexing of Stacks 04M0.**  Let `U` be an étale scheme chart
of an algebraic space `X` and let `W` be an object of the small étale site of the algebraic
space represented by `U`.  Then the unbounded right derived functor of sections at `W` of the
reindexing of an `𝒪_X|_U`-module is the derived reindexing followed by derived sections at `W`.

This is `Stacks.Injectives.derivedPrecompIso` at the equivalence of module categories of
Stacks 04M0, `AlgebraicGeometry.Space.chartLocalizationModulesEquivalence`, which is additive by
`AlgebraicGeometry.Space.additive_chartLocalizationReindex`.  The left-hand side is derived
sections at `e.functor.obj W` on the localization: the reindexing is
`SheafOfModules.pushforward` along `e.functor` with the identity structure map, so

`chartLocalizationReindex ⋙ Γ(W, -) = Γ(e.functor.obj W, -)`

on the nose.  It is written as the composite because that is the spelling of the ring of
sections at which the instances resolve. -/
def derivedSectionsChartLocalizationReindexIso (W : (chartRingedSite B S hS X U).C) :
    Stacks.DerivedFunctor.totalRightDerived
        (chartLocalizationReindex B S hS X U ⋙
          SheafOfModules.evaluation.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O) (op W)) ≅
      (chartLocalizationReindex B S hS X U).mapDerivedCategory ⋙
        Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.evaluation.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O) (op W)) :=
  Stacks.Injectives.derivedPrecompIso _ _

end ChartLocalization

/-! ### Derived sections across the comparison of a representable space with its scheme -/

section RepresentedScheme

attribute [local instance] isGrothendieckAbelian_modules
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  additive_representedSchemeReindex

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)

/-- The modules on the small étale site of the scheme underlying `V` form a Grothendieck abelian
category, at the `AlgebraicGeometry.Space.representedSchemeRingedSite` spelling of that site.

The content is `AlgebraicGeometry.smallEtaleRingedSite_isGrothendieckAbelian`, applied
explicitly: its sheaf of rings is constrained to live on the topology of
`AlgebraicGeometry.smallEtaleRingedSite`, which instance search does not recover from the
`AlgebraicGeometry.RingedSite.J` projection of the ringed site. -/
local instance isGrothendieckAbelian_representedSchemeModules :
    IsGrothendieckAbelian.{u}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O)) :=
  AlgebraicGeometry.smallEtaleRingedSite_isGrothendieckAbelian (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj V) V.left.property _

/-- The standard derived category of the `𝒪`-modules on the small étale site of a representable
algebraic space, named for the reason recorded at
`AlgebraicGeometry.Space.hasDerivedCategory_modules`. -/
local instance hasDerivedCategoryStandard_representedModules :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O)) :=
  HasDerivedCategory.standard _

/-- The standard derived category of the modules on the small étale site of the scheme
underlying `V`, named for the reason recorded at
`AlgebraicGeometry.Space.hasDerivedCategory_modules`. -/
local instance hasDerivedCategoryStandard_representedSchemeModules :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O)) :=
  HasDerivedCategory.standard _

/-- The standard derived category of the modules of sections at an object of the small étale
site of the scheme underlying `V`, named for the reason recorded at
`AlgebraicGeometry.Space.hasDerivedCategory_modules`. -/
local instance hasDerivedCategoryStandard_representedSchemeSections
    (Z : (representedSchemeRingedSite B S hS V).C) :
    HasDerivedCategory.{u + 1}
      (ModuleCat.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O).obj.obj
          (op Z))) :=
  HasDerivedCategory.standard _

/-- **Derived sections cross the comparison between a representable algebraic space and its
scheme.**  For an object `Z` of the small étale site of the scheme underlying `V`, the unbounded
right derived functor of sections at `Z` of the reindexing of an `𝒪`-module on the small étale
site of the algebraic space represented by `V` is the derived reindexing followed by derived
sections at `Z`.

This is `Stacks.Injectives.derivedPrecompIso` at
`AlgebraicGeometry.Space.representedSchemeModulesEquivalence`, whose inverse is the reindexing
and is additive by `AlgebraicGeometry.Space.additive_representedSchemeReindex`.  As for the
reindexing of Stacks 04M0 the underived input is an equality,

`representedSchemeReindex ⋙ Γ(Z, -) = Γ(e.inverse.obj Z, -)`

on the nose, the reindexing being `SheafOfModules.pushforward` along the inverse of the
comparison with the identity structure map; the left-hand side is written as the composite
because that is the spelling of the ring of sections at which the instances resolve. -/
def derivedSectionsRepresentedSchemeReindexIso (Z : (representedSchemeRingedSite B S hS V).C) :
    Stacks.DerivedFunctor.totalRightDerived
        (representedSchemeReindex B S hS V ⋙
          SheafOfModules.evaluation.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O)
            (op Z)) ≅
      (representedSchemeReindex B S hS V).mapDerivedCategory ⋙
        Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.evaluation.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O)
            (op Z)) :=
  Stacks.Injectives.derivedPrecompIso _ _

end RepresentedScheme

end AlgebraicGeometry.Space

end
