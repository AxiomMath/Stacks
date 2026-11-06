module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleZariskiDerivationEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeTransport
import StacksCore.Tactic.StacksAttribute

/-!
# A derivation on the small étale site of a represented algebraic space is a Zariski derivation

Let `α : U ⟶ V` be a morphism of schemes of the big fppf site over `S` and let `G` be an
`𝒪`-module on the small étale site of the represented algebraic space `yoneda.obj U`.  This file
proves that

> a `yoneda.obj V`-derivation of `𝒪_{yoneda.obj U}` with values in `G` is the same thing as an
> ordinary `V`-derivation of `𝒪_U` with values in the restriction of `G` to the small Zariski
> site of the scheme `U`,

`AlgebraicGeometry.Space.schemeZariskiDerivationEquiv`.  This is **Step 1** of the route by which
`AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction` — the last input Stacks 05ZC and
Stacks 05ZD needed, in the shape of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareDerivation.lean` — is
proved: it moves the question off the small étale site of an algebraic space and onto the small
Zariski site of a scheme, where Morphisms, Lemma 01V0 lives.  **That route is now complete**, in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareBijective.lean`
(`AlgebraicGeometry.Space.schemeSquareDerivationRestriction`), and both tags hold
unconditionally.

Nothing here is new mathematics.  The identification is built in two stages, and **both stages
describe their values**, which is the whole point of how they are built:

* **Across the identification of the two small étale sites** the derivation is the *same*
  derivation, only re-indexed: `AlgebraicGeometry.Space.etaleDerivationOfSpace` reads a
  `yoneda.obj V`-derivation on the scheme's site and
  `AlgebraicGeometry.Space.spaceDerivationOfEtale` reads it back, and
  `AlgebraicGeometry.Space.etaleDerivationOfSpace_d` says the value over an object `T` of the
  scheme's site is the value over the corresponding object of the space's site — by `rfl`.  Both
  readings are the transport of derivations of
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean` with the
  vanishing conditions discharged, generalizing
  `AlgebraicGeometry.Space.inverseEtaleDerivation` and the inner part of
  `AlgebraicGeometry.Space.transportedUniversalDerivation` from the universal derivation to an
  arbitrary one.  That they are mutually inverse is `AlgebraicGeometry.Space.derivation_d_map_unit`
  one way and `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_unit_app_inverse` the
  other.
* **From the scheme's small étale site down to its small Zariski site** it is the invertibility
  clause of Stacks 04CS, `AlgebraicGeometry.SmallEtale.etaleZariskiRestrictionEquiv`, which is
  literally restriction to the Zariski opens.

**The first stage is deliberately not assembled out of four universal properties** — the
universal property of Stacks 04CT,
`AlgebraicGeometry.Space.schemeDifferentialsIso`, the module equivalence and the universal property
of Stacks 04BN.  That compiles at once and makes the values unreachable: the inverse of an
`Equiv.ofBijective` is `Function.surjInv`, which is choice, so nothing reduces through it and every
computation of a value runs out of heartbeats. A bijection whose values are not described is a
black box that its next consumer has to unpack again; the transport-of-derivations construction
above is longer to set up and is the reusable one.

## Main definitions

* `AlgebraicGeometry.SmallEtale.etaleDifferentialsHomEquiv`: the universal property of
  `Ω_{X_étale/Y_étale}` read as a bijection.
* `AlgebraicGeometry.Space.etaleDerivationOfSpace` and
  `AlgebraicGeometry.Space.spaceDerivationOfEtale`: the two readings of a derivation across the
  identification of the two small étale sites, with
  `AlgebraicGeometry.Space.schemeEtaleDerivationEquiv` for their being mutually inverse.
* `AlgebraicGeometry.Space.schemeZariskiDerivationEquiv`: **a `yoneda.obj V`-derivation of
  `𝒪_{yoneda.obj U}` is a `V`-derivation of `𝒪_U`.**
* `AlgebraicGeometry.Space.schemeZariskiHomEquiv`: the same read as the morphisms
  `Ω_{U/V} ⟶ ε_*(G read on the scheme's site)`, which is the form in which the Zariski adjunction
  `k^* ⊣ k_*` is applied to it.

## Main results

* `AlgebraicGeometry.Space.etaleDerivationOfSpace_d`: **the identification changes no value.**
* `AlgebraicGeometry.Space.schemeZariskiDerivationEquiv_d`: **the bottom horizontal of the
  Stacks 05ZC/05ZD square describes its values** — over an open `W` of the scheme `U` the Zariski
  derivation takes the value the given derivation takes over the object of the small étale site
  of `yoneda.obj U` which `W` names.
* `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_unit_app_inverse`: the unit of the
  identification of the two sites is the identity at an object coming from the scheme's site.

## Implementation notes

The small étale site of the scheme underlying `U` has two spellings which are definitionally
equal but not at the reducible transparency `rw` and instance resolution use —
`(AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U` and `U.left.obj` — and the structure
sheaf of the small étale site of `yoneda.obj U` likewise; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackBaseChange.lean`.  Three proofs
below are in term mode rather than tactic mode for exactly that reason: `rw` reported its
rewritten goal "not type-correct under the `implicit` transparency level" each time, while `exact`
succeeds because it works up to defeq.  `AlgebraicGeometry.Space.presheaf_map_unit_inverse_apply`
is stated with its module written as `SheafOfModules.{u} (ringStructureSheaf …)` and not as
`AlgebraicGeometry.Space.Modules …`, for the same reason.

`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_unit_app_inverse` is proved by
faithfulness of the functor of the identification rather than from
`CategoryTheory.Equivalence.unit_app_inverse`: the counit is the identity, so
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_functor_map_unit` already gives the
equation after applying the functor, and faithfulness removes it.  Going through the counit
instead puts `𝟙 T` at the type `functor.obj (inverse.obj T) ⟶ T`, which is where the transparency
problem above bites.

No Stacks tag is registered: every step is attributed where it is proved.

## How `IsSchemeSquareDerivationRestriction` is proved, given this

For a cartesian square `k : U' ⟶ U`, `r : U ⟶ V`, `r' : U' ⟶ V'`, `l : V' ⟶ V` of schemes of the
site and an `𝒪`-module `C` on the small étale site of `yoneda.obj U'`, the square to be filled is

```
(Ω_{yU'/yV'} ⟶ C)  --(04CT, then schemeZariskiHomEquiv at r')-->  (Ω_{U'/V'} ⟶ ε_*Ψ_{U'}C)
      |  Space.restrictDerivation                                     |  restrictRelativeDerivation
      v                                                               v
Der_{yV}(𝒪_{yU}, k_*C)  --(schemeZariskiDerivationEquiv at r)-->  Der_V(𝒪_U, ε_*Ψ_U(k_*C))
```

**Both horizontals are bijections** (this file), **the right-hand vertical is a bijection** for a
cartesian square — Morphisms, Lemma 01V0 in derivation form,
`AlgebraicGeometry.Scheme.Hom.bijective_restrictRelativeDerivation_of_isPullback` — and **the
horizontals now describe their values**, `AlgebraicGeometry.Space.etaleDerivationOfSpace_d`
composed with `AlgebraicGeometry.SmallEtale.zariskiRestrictionData_d`.  So the left vertical is a
bijection, which is exactly `AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction`, as soon
as the square commutes — **and the square now commutes**,
`AlgebraicGeometry.Space.representedSquareDerivation_restrictRelativeDerivation`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareCommutes.lean`); see the
section "The square commutes" below for what that took.

The **matching of the two targets** that the commuting square needed — the right vertical
produces a derivation into `k_*(ε_*Ψ_{U'}C)`, the bottom horizontal one into `ε_*Ψ_U(k_*C)` — is
the comparison `Φ`, `AlgebraicGeometry.Space.representedSquareComparison`.  No adjoint-uniqueness
isomorphism occurs anywhere in that matching, which is what keeps this route clear of the
derivation compatibility of Stacks 03LC (1) that the invertibility form of the input needs.  The
**invertibility** of `Φ` and the composition of the four bijections are
`AlgebraicGeometry.Space.isIso_representedSquareComparison` and
`AlgebraicGeometry.Space.bijective_restrictDerivation_schemeSquare`; see the section
"The bijectivity" below.

**The step that makes the formula available is the action on sections of
`AlgebraicGeometry.Space.modulePushforwardChartIso`.**  That action is statable as the
component of the comparison on sections, and is
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_apply`, and the composite in which the
adjoint-uniqueness factor cancels is
`AlgebraicGeometry.Space.chartComparison_pushforwardUniversalDerivationHom`; the two together give
the formula the square needs,
`AlgebraicGeometry.Space.modulePushforwardChartIso_restrictDerivation_d`, which is literally
`AlgebraicGeometry.Scheme.Hom.restrictRelativeDerivation_d` read on the small étale site.  All
three are in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsChartPushforward.lean`.  Both lemmas
are needed and neither suffices alone; the difficulty there is heartbeats, not statability.

### What the matching still needs, precisely

Write `Ψ_U` for `AlgebraicGeometry.Space.representedModuleRestriction`, `F_U` for the functor of
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, `ε_*` for
`SheafOfModules.pushforward (AlgebraicGeometry.Space.representedSchemeStructureMapRing B S hS k)`
— which is `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing` of the underlying morphism of
schemes, the two being the same `abbrev` — and `sbc_*` for
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`.  The comparison to be built is

```
Φ : restrictModule_U (Ψ_U (k_*C)) ≅ (k_s)_* (restrictModule_{U'} (Ψ_{U'} C))
```

and it factors as three isomorphisms, all three of which are proved:

1. `restrictModule_U (Ψ_U (k_*C)) ≅ restrictModule_U (Ψ_U (sbc_*C))`, the functor
   `Ψ_U ⋙ restrictModule_U` applied to
   `(AlgebraicGeometry.Space.modulePushforwardChartIso B S hS k̂ hk̂).hom.app C`.  **Proved**, and
   it is the factor whose sections action
   `AlgebraicGeometry.Space.modulePushforwardChartIso_restrictDerivation_d` describes, in the
   `.hom` direction that lemma is stated for.
2. `Ψ_U (sbc_* C) ≅ ε_* (Ψ_{U'} C)`.  **Proved**, as
   `AlgebraicGeometry.Space.representedModulePushforwardInverseSquareIso`.  Both sides are
   composites of two *plain* direct images of modules — `Ψ_U ∘ sbc_*` reindexes along
   `(representedSmallEtaleEquivalence U).inverse ⋙ smallBaseChange k̂ hk̂` and `ε_* ∘ Ψ_{U'}`
   reindexes along `representedSchemeBaseChange k ⋙ (representedSmallEtaleEquivalence U').inverse`
   — so it is `SheafOfModules.pushforwardComp`, one `SheafOfModules.pushforwardCongr₂`, and
   `SheafOfModules.pushforwardComp` again, and the one equation `pushforwardCongr₂` asks for is
   `AlgebraicGeometry.Space.representedStructureMapRing_inverse_square`: the two routes round the
   square of small étale ringed sites carry the structure sheaf of the scheme `U` to the structure
   sheaf of the small étale site of `yoneda.obj U'` by the same map.  Everything is in
   `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePushforwardInverseSquare.lean`, whose
   implementation notes record what the heartbeat budget does and does not allow here.
3. `restrictModule_U (ε_* N) ≅ (k_s)_* (restrictModule_{U'} N)` at `N = Ψ_{U'} C`, which is
   `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso`.  **Proved**, with its sections
   action in both directions
   (`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_app_app` and
   `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_hom_app_app`).

**So all three factors of Φ are available.**  Step 2's one equation is proved, and three things
about how it is proved are worth recording, because the route a reader would reach for first
cannot be carried out:

* It is the `.hom`-direction equation that is provable, not the `.inv`-direction one.
  `SheafOfModules.pushforwardCongr₂` accepts either (take `.symm` of the isomorphism it returns),
  and the `.hom` direction consumes
  `functor_map_representedSmallEtaleBaseChangeInverseIso_hom` directly, with no cancellation
  lemma.
* The componentwise equation **cannot be reduced to explicit composites of components of the two
  structure maps**: the component of `representedSchemeStructureMapRing` has its target spelled
  through `k.left` rather than through `BigFppfOver.toScheme`, so composing that component with a
  restriction map of the scheme's structure sheaf does not elaborate at all.  The proof composes
  with the whole `SheafOfModules.comparisonComp` instead, whose type is written in the
  `represented…` spelling throughout.  In particular the step
  "`representedStructureMapInverse` is the identity, so the two `comparisonComp`s are
  `(inverse_U)_*` applied to …" is unaffordable.
* The counit is absorbed by `CategoryTheory.Functor.map_id` with **both** arguments given
  explicitly (`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso_hom_app_comp_counit`).
  With metavariables there it times out; that, and not `rw` versus `simp only`, is what decides
  whether it fires.

**Φ is now built and its three factors are read on sections**, in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareComparison.lean`:
`AlgebraicGeometry.Space.representedSquareComparison` is Φ,
`AlgebraicGeometry.Space.representedSquareOpensNat` is the composite restriction it amounts to
on sections over an open `W` of `U`, and the three factors' readings are
`AlgebraicGeometry.Space.representedSquareComparison_chart_restrict_apply`,
`AlgebraicGeometry.Space.representedSquareComparison_middle_app_apply` and
`AlgebraicGeometry.Space.restrictModuleBaseChange_representedModuleRestriction_app_apply`.

The middle factor's reading is
`AlgebraicGeometry.Space.representedSquareMiddle_app_val_app_apply`, and the measurement that
unlocks it is recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePushforwardInverseSquareSections.lean`.
In short: the target of `PresheafOfModules.map f` is a `ModuleCat.restrictScalars` along `f`, so
a reading of the form `M.val.map f x = …` with `f` a **concrete** component of one of these
comparisons forces the elaborator to weak-head-normalise that component — a conjugate of
Stacks 03G2 (4) by two tactic-built equivalences of sites — and a single such statement costs
about a third of the heartbeat budget.  **That cost, and not any mathematical obstruction, is
what makes such a reading look unstatable.**  The discipline that removes it: every statement
about such a reading keeps the morphism either a *variable* or a definition made `irreducible`
after the one statement that needs its value.

### The reading of Φ, and what it cost

The single statement that composes the three factor readings into the reading of Φ itself is
proved, as `AlgebraicGeometry.Space.representedSquareComparison_app_apply`:

```
Scheme.Modules.Hom.app (representedSquareComparison B S hS k hk C) W x =
  C.val.map (representedSquareOpensNat B S hS k hk W).op
    ((representedSquareChartComparison B S hS k hk C).val.app
      (op (inverse_U.obj (opensToSmallEtale W))) x)
```

`AlgebraicGeometry.Space.representedSquareChartComparison` is the chart comparison of
Stacks 03G2 (4) at `C`, named; `AlgebraicGeometry.Space.representedSquareChartComparison_eq`
identifies it with `(modulePushforwardChartIso …).hom.app C`, which is what a consumer needing
its value rewrites by.

Each half is cheap on its own, and the combination exceeds the heartbeat budget.  What
the budget goes on is **not** the one defeq between the `G.obj (F.obj C)` and `(F ⋙ G).obj C`
spellings of the iterated direct image, which is the natural suspect.  As
the elaborator's `diagnostics` option shows at a raised budget, the cost is the elaborator
*normalising
objects of the small étale site*: `Over.iteratedSliceEquiv` 87587 unfoldings,
`SmallEtale.opensToSmallEtale` 40197, `representedSmallEtaleEquivalence` 27219,
`Functor.relativelyRepresentable.pullback` 26912 with `Classical.choose` beneath it,
`yonedaCostructuredArrowOverEquiv` 19411, and `Functor.obj` 1915254 reducible unfoldings; the
whole proof wanted between 800000 and 4000000 heartbeats in one declaration.  Three moves bring
it inside 200000, all recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareComparison.lean`: naming
the chart comparison and making it `irreducible` after the one statement that needs its value;
reading the second and third factors together **at a variable section**
(`AlgebraicGeometry.Space.representedSquareComparison_middle_baseChange_app_apply`), so that
the reconciliation of `Γ(restrictModule.obj N, W)` with `C.val.obj (op T)` happens once rather
than once per factor; and making `representedSmallEtaleEquivalence`, `smallBaseChange` and
`SmallEtale.opensToSmallEtale` `local irreducible` for the rest of that file, since every
reading there needs their objects only symbolically.  With those three in place that file checks
with no elaborator options set anywhere.

Two further routes are dead ends:
restating the middle factor's reading at the `G.obj (F.obj C)` spelling moves the cost rather
than removing it, and making the first factor a `Functor.whiskerRight` natural transformation
with target `F ⋙ G` makes the composite's continuity instances arrive as
`(smallEtaleRingedSite …).J`, where instance search fails outright.

With that reading in hand, **the square commutes**, and the bijectivity follows.

### The square commutes

`AlgebraicGeometry.Space.representedSquareDerivation_restrictRelativeDerivation`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareCommutes.lean`), with
`AlgebraicGeometry.Space.representedSquareDerivation_restrictRelativeDerivation_schemeSpace` the
same statement at the `AlgebraicGeometry.schemeSpaceMap` spelling of the top edge, which is the
one `AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction` quantifies over.  It needed its
own module, `Morphisms/Differentials/BaseChangeDerivation.lean` not being in the import closure
of the comparison file.

Three elaboration facts about the proof, none of them mathematical:

* **`θ` is used only through its characterising equation and never computed**, which is what it
  has to be: `AlgebraicGeometry.Space.postcomp_schemeZariskiHomEquiv` is
  `Equiv.apply_symm_apply` for the `Equiv.ofBijective` of the universal property of `Ω_{U/V}`,
  and both of its sides are computable.  `Function.surjInv` is never reduced.
* **What remained was one identity about regular functions**, and it is
  `AlgebraicGeometry.Space.representedSquareOpensNat_chartPullback`.  It cost almost nothing:
  `AlgebraicGeometry.Space.chartPullback_chartBaseChangeArrow` turns the pullback along the
  cartesian projection into the scheme-level structure map restricted along the comparison of the
  two base changes of the chart, the two restrictions compose, and
  `AlgebraicGeometry.SmallEtale.map_structureSharp_opens_eq_pullbackSection` is the identity that
  is left.  The comparison of the two chart identifications —
  `AlgebraicGeometry.Space.functor_map_representedSquareOpensNat_comp` — needs **no computation at
  all**: both sides are morphisms into the base change of an *open*, whose structure morphism is a
  monomorphism, so `AlgebraicGeometry.SmallEtale.subsingleton_hom_baseChangeOpens` settles it.
  None of the machinery of `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeInverseIso`
  was needed.
* **Every difficulty was the heartbeat budget, and the budget is per declaration.**  Four
  arrangements of the same steps failed at `whnf` or `isDefEq` only because one declaration's
  statement plus three of its steps already accounted for most of 200000.  Two further rules came
  out of it and are recorded in that file's implementation notes: the two spellings
  `AlgebraicGeometry.Space.representedSpaceMap B S hS k` and `AlgebraicGeometry.schemeSpaceMap k`
  must never be unified underneath
  `AlgebraicGeometry.Space.modulePushforwardChartIso` (they are the same term up to two deltas,
  and that unification alone exhausts the budget — reconcile them in a declaration of their own,
  where it costs a second); and a morphism's action on sections must be written the way the lemma
  you compose with writes it, `ConcreteCategory.hom` against `ModuleCat.Hom.hom` being
  unaffordable to bridge at a concrete object of the site.

### The bijectivity

`AlgebraicGeometry.Space.bijective_restrictDerivation_schemeSquare` and, from it,
`AlgebraicGeometry.Space.schemeSquareDerivationRestriction`, in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareBijective.lean`.
`restrictDerivation` is `(schemeZariskiDerivationEquiv r (k_*C)).symm` after postcomposition with
`Φ.inv` after `Scheme.Hom.restrictRelativeDerivation` after `schemeZariskiHomEquiv r' C` — four
bijections, the third being Morphisms, Lemma 01V0 in derivation form
(`AlgebraicGeometry.Scheme.Hom.bijective_restrictRelativeDerivation_of_isPullback`), whose
cartesian square is the hypothesis of
`AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction` read through
`AlgebraicGeometry.SmallEtale.schemeHom` — the two spellings of the four edges being accepted for
one another by `exact`.  The commuting square above is what lets the four be composed.

`Φ` is a plain morphism, so its invertibility had to be supplied, and it is
`AlgebraicGeometry.Space.isIso_representedSquareComparison`: its three factors are isomorphisms
(`AlgebraicGeometry.Space.modulePushforwardChartIso`,
`AlgebraicGeometry.Space.representedModulePushforwardInverseSquareIso` and
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso`).  Two elaboration facts about that
step:

* the middle factor of `Φ` is **not** extracted from
  `AlgebraicGeometry.Space.representedModulePushforwardInverseSquareIso` — it is rebuilt as
  `SheafOfModules.pushforwardNatTrans` followed by `SheafOfModules.pushforwardCongr`, which is the
  only form whose sections action can be read — so its invertibility has to be re-derived.  It is,
  and cheaply: `SheafOfModules.pushforwardNatIso`'s `.hom` *is*
  `SheafOfModules.pushforwardNatTrans`, so
  `SheafOfModules.isIso_pushforwardNatTrans` is a one-liner with every site and structure map a
  variable;
* composing the three factors' invertibility exceeds the heartbeat budget at `whnf` even with
  each factor handed over as an explicit term of exactly the shape `Φ`'s body has, and
  `attribute [local irreducible] representedSmallEtaleEquivalence smallBaseChange
  SmallEtale.opensToSmallEtale` removes that cost outright — the same measurement as for the
  readings in
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareComparison.lean`, and
  the opposite of what that attribute does in
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareCommutes.lean`, where it
  stops the statements typechecking.

Three measurements, each worth not repeating:

* `AlgebraicGeometry.Space.representedModuleRestriction` after
  `AlgebraicGeometry.Space.representedModulePushforward` is **not** cheaply the identity functor.
  It is the identity on sections — the counit of the identification of the sites is the identity,
  so `functor.obj (inverse.obj T)` is `T` — but `rfl` between the two `SheafOfModules` objects
  exhausts the heartbeats, so the matching cannot be dodged by rewriting `Ψ_U(Φ_U M)` to `M`.
  For the same reason `AlgebraicGeometry.Space.representedModuleRestriction` is **not**
  definitionally `(representedSmallEtaleModuleEquivalence …).inverse`: the latter pushes forward
  along `Stacks.SheafOfModules.reindexBackSharp`, whose component is `R.map (𝟙 _)` and not `𝟙`.
  That is why step 2 above is built from `pushforwardComp` directly rather than by conjugating
  `AlgebraicGeometry.Space.representedModulePushforwardSquareIso` with the module equivalence.
* The sections of the direct image of **modules** of Stacks 03LU along a representable morphism
  are **not** definitionally the sections of the source over the base change: with
  `k` representable,
  `((modulePushforward B S hS (schemeSpaceMap k)).obj C).val.presheaf.obj (op W)` and
  `C.val.presheaf.obj (op ((smallBaseChange B S hS (schemeSpaceMap k) _).obj W))` are *different
  types*, not merely an expensive `rfl` — the comparison functor of Stacks 03G1 intervenes
  through `AlgebraicGeometry.Space.smallEtaleComparisonRestriction`.  (At the level of modules
  rather than abelian groups they differ already in the ring, the direct image having restricted
  scalars along `AlgebraicGeometry.Space.structureSharp`.)  This is what step 1 above goes
  through `AlgebraicGeometry.Space.modulePushforwardChartIso` to avoid.
* The sections are visible for the **other** direct image, the one along base change of charts:
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` is *definitionally*
  `SheafOfModules.pushforward` along `AlgebraicGeometry.Space.smallBaseChangeSharp`, and
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforward_obj_val_obj`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeAdjunction.lean`) gives
  `(f_*M)(V) = M(V ×_Y X)` by `rfl`, needing only representability.

And one measurement about tactics, which costs hours if rediscovered: on goals mentioning the
objects of these two small étale sites, **`rw` is unaffordable and `simp only` is not**.  A single
`rw [CategoryTheory.Functor.map_comp]` on the components of
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeInverseIso` exhausts the heartbeat budget,
while a `simp only` performing the same two rewrites costs a fraction of it; and
`CategoryTheory.Functor.map_id` cannot be made to fire on
`(representedSchemeBaseChange B S hS k).map (𝟙 T)` by either, the two sides sitting at
`(inverse ⋙ functor).obj T` and at `T`.  See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePushforwardInverseSquare.lean`.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 04BN](https://stacks.math.columbia.edu/tag/04BN)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0), what the Zariski side is
  for.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (F : SheafOfModules.{u} (structureSheaf B X.obj X.property))

/-- **The universal property of `Ω_{X_étale/Y_étale}` read as a bijection**: a morphism
`Ω_{X_étale/Y_étale} ⟶ 𝓕` of `𝒪_{X_étale}`-modules is the same thing as a `Y_étale`-derivation of
`𝒪_{X_étale}` with values in `𝓕`, the correspondence being composition with the universal
derivation. -/
public def etaleDifferentialsHomEquiv : (sheafOfDifferentials B f ⟶ F) ≃ EtaleDerivation B f F :=
  Equiv.ofBijective _ ((Function.bijective_iff_existsUnique _).2
    (universalDerivation_isUniversal B f F))

/-- `AlgebraicGeometry.SmallEtale.etaleDifferentialsHomEquiv` composes a morphism with the
universal derivation. -/
public theorem etaleDifferentialsHomEquiv_apply (g : sheafOfDifferentials B f ⟶ F) :
    etaleDifferentialsHomEquiv B f F g = (universalDerivation B f).postcomp g.val :=
  rfl

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V : BigFppfOver B S hS} (α : U ⟶ V)
  (G : Modules.{u, u} B S hS (yoneda.obj U) (schemeSpace U).property)

/-- **The unit of the identification of the two small étale sites is the identity at an object
coming from the scheme's site.**  The counit of that identification is the identity
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_counit_app`), and
`CategoryTheory.Equivalence.unit_app_inverse` expresses the unit there as the inverse functor
applied to the inverse of the counit. -/
theorem representedSmallEtaleEquivalence_unit_app_inverse
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :
    (representedSmallEtaleEquivalence B S hS U).unitIso.hom.app
        ((representedSmallEtaleEquivalence B S hS U).inverse.obj T) =
      𝟙 ((representedSmallEtaleEquivalence B S hS U).inverse.obj T) := by
  refine CategoryTheory.Functor.map_injective
    (representedSmallEtaleEquivalence B S hS U).functor ?_
  exact (representedSmallEtaleEquivalence_functor_map_unit B S hS U
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj T)).trans
    (CategoryTheory.Functor.map_id _ _).symm

/-- **Restriction along the unit of the identification, at an object coming from the scheme's
site, is the identity on sections.**  The unit is the identity there, by
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_unit_app_inverse`.

This is the counterpart of `AlgebraicGeometry.Space.presheaf_map_unit_apply`, which says the same
for a module on the small étale site of the scheme underlying `U`; here the module is on the small
étale site of `yoneda.obj U`. -/
public theorem presheaf_map_unit_inverse_apply
    (N : SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U)))
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (y : N.val.presheaf.obj (op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
      ((representedSmallEtaleEquivalence B S hS U).functor.obj
        ((representedSmallEtaleEquivalence B S hS U).inverse.obj T))))) :
    (N.val.presheaf.map ((representedSmallEtaleEquivalence B S hS U).unitIso.hom.app
        ((representedSmallEtaleEquivalence B S hS U).inverse.obj T)).op).hom y = y := by
  rw [representedSmallEtaleEquivalence_unit_app_inverse]
  show (N.val.presheaf.map
    (𝟙 (op ((representedSmallEtaleEquivalence B S hS U).inverse.obj T)))).hom y = y
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **A `yoneda.obj V`-derivation of `𝒪_{yoneda.obj U}`, read on the small étale site of the
scheme underlying `U`.**  The values are unchanged — only the indexing object moves across the
identification of the two sites, by
`AlgebraicGeometry.Space.transportDerivationInverse` — and what has to be checked is the
vanishing condition over `f_small^{-1}𝒪_{V_étale}`, which
`AlgebraicGeometry.Space.transportDerivationInverse_d_structureSharp_eq_zero` supplies from
`AlgebraicGeometry.Space.derivation_d_chartPullback_eq_zero`.

This generalizes `AlgebraicGeometry.Space.inverseEtaleDerivation`, which is the case of the
universal derivation, to an arbitrary derivation of an arbitrary module. -/
public noncomputable def etaleDerivationOfSpace
    (D : PresheafOfModulesOfCommRing.Derivation' G.val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom) :
    _root_.AlgebraicGeometry.SmallEtale.EtaleDerivation (associatedBigEtaleSite B) α.left
      ((representedModuleRestriction B S hS U).obj G) where
  d := (transportDerivationInverse B S hS U
    (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom D).d
  d_mul := (transportDerivationInverse B S hS U
    (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom D).d_mul
  d_map := (transportDerivationInverse B S hS U
    (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom D).d_map
  d_app := fun {W} s =>
    _root_.AlgebraicGeometry.SmallEtale.d_etaleStructureMap_eq_zero (associatedBigEtaleSite B)
      α.left
      (transportDerivationInverse B S hS U
        (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom D)
      (fun W' t => transportDerivationInverse_d_structureSharp_eq_zero B S hS α
        (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom D
        (fun V₁ j s => derivation_d_chartPullback_eq_zero B S hS (schemeSpaceMap α) D V₁ j s)
        ((representedSmallEtaleEquivalence B S hS V).inverse.obj W'.unop) t)
      W s

/-- **The identification changes no value**: over an object `T` of the small étale site of the
scheme underlying `U`, the derivation takes the value it took over the corresponding object of
the small étale site of `yoneda.obj U`. -/
@[simp]
public theorem etaleDerivationOfSpace_d
    (D : PresheafOfModulesOfCommRing.Derivation' G.val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom)
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (x : (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.obj (op T)) :
    (etaleDerivationOfSpace B S hS α G D).d (X := op T) x =
      D.d (X := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj T)) x :=
  rfl

/-- **A `V_étale`-derivation of `𝒪_{U_étale}`, read on the small étale site of `yoneda.obj U`.**
The transport of `AlgebraicGeometry.Space.transportDerivation`, whose values are those of the
given derivation at the image object, followed by the counit of the identification of the two
categories of modules, which restricts along the unit of the identification of the sites. -/
public noncomputable def spaceDerivationOfEtale
    (E : _root_.AlgebraicGeometry.SmallEtale.EtaleDerivation (associatedBigEtaleSite B) α.left
      ((representedModuleRestriction B S hS U).obj G)) :
    PresheafOfModulesOfCommRing.Derivation' G.val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom :=
  (Derivation'.ofChartPullback B S hS (schemeSpaceMap α)
    (transportDerivation B S hS U
      (_root_.AlgebraicGeometry.SmallEtale.etaleStructureMap (associatedBigEtaleSite B)
        α.left).hom E)
    (transportDerivation_d_chartPullback_eq_zero B S hS α E
      (fun W t => _root_.AlgebraicGeometry.SmallEtale.d_structureSharp_eq_zero
        (associatedBigEtaleSite B) α.left E
        (fun _ s => PresheafOfModulesOfCommRing.Derivation'.d_app E s) W t))).postcomp
    ((representedModuleEquivalence.{u, u} B S hS U).counit.app G).val

/-- Reading a `yoneda.obj V`-derivation on the scheme's site and back recovers it: the two
readings change no value, and the unit of the identification of the sites restricts a value at
the doubly shifted index back to the value at the index itself,
`AlgebraicGeometry.Space.derivation_d_map_unit`. -/
public theorem spaceDerivationOfEtale_etaleDerivationOfSpace
    (D : PresheafOfModulesOfCommRing.Derivation' G.val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom) :
    spaceDerivationOfEtale B S hS α G (etaleDerivationOfSpace B S hS α G D) = D :=
  PresheafOfModulesOfCommRing.Derivation.ext (funext fun W ↦ AddMonoidHom.ext fun x ↦
    derivation_d_map_unit B S hS U (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom D
      W x)

/-- Reading a `V_étale`-derivation on the space's site and back recovers it: the unit of the
identification of the sites is the identity at an object coming from the scheme's site, so the
counit of the identification of the modules does nothing to the value. -/
public theorem etaleDerivationOfSpace_spaceDerivationOfEtale
    (E : _root_.AlgebraicGeometry.SmallEtale.EtaleDerivation (associatedBigEtaleSite B) α.left
      ((representedModuleRestriction B S hS U).obj G)) :
    etaleDerivationOfSpace B S hS α G (spaceDerivationOfEtale B S hS α G E) = E := by
  refine PresheafOfModulesOfCommRing.Derivation.ext (funext fun T ↦ AddMonoidHom.ext fun x ↦ ?_)
  exact presheaf_map_unit_inverse_apply B S hS G T.unop (E.d (X := T) x)

/-- **A `yoneda.obj V`-derivation of `𝒪_{yoneda.obj U}` is a `V_étale`-derivation of
`𝒪_{U_étale}`.**  Steps 1 to 4 of the route, in one step: the two readings of a derivation across
the identification of the two small étale sites are mutually inverse.

Unlike a composite of the four universal properties, this identification is built from the
transport of derivations, so `AlgebraicGeometry.Space.etaleDerivationOfSpace_d` describes its
values and holds by `rfl`.  That description is what a consumer needs; an identification assembled
out of `Equiv.ofBijective`s cannot supply it, because the inverse of such an `Equiv` is
`Function.surjInv` and nothing reduces through it. -/
public def schemeEtaleDerivationEquiv :
    PresheafOfModulesOfCommRing.Derivation' G.val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom ≃
      _root_.AlgebraicGeometry.SmallEtale.EtaleDerivation (associatedBigEtaleSite B) α.left
        ((representedModuleRestriction B S hS U).obj G) where
  toFun := etaleDerivationOfSpace B S hS α G
  invFun := spaceDerivationOfEtale B S hS α G
  left_inv := spaceDerivationOfEtale_etaleDerivationOfSpace B S hS α G
  right_inv := etaleDerivationOfSpace_spaceDerivationOfEtale B S hS α G

/-- `AlgebraicGeometry.Space.schemeEtaleDerivationEquiv` only re-indexes: it changes no value. -/
public theorem schemeEtaleDerivationEquiv_apply
    (D : PresheafOfModulesOfCommRing.Derivation' G.val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom) :
    schemeEtaleDerivationEquiv B S hS α G D = etaleDerivationOfSpace B S hS α G D :=
  rfl

/-- **Step 1: a `yoneda.obj V`-derivation of `𝒪_{yoneda.obj U}` is an ordinary `V`-derivation of
`𝒪_U`.**  A derivation on the small étale site of the represented algebraic space `yoneda.obj U`
is the same thing as a derivation on the small Zariski site of the scheme `U`, with values in the
restriction of `G`.

This is `AlgebraicGeometry.Space.schemeEtaleDerivationEquiv` followed by
`AlgebraicGeometry.SmallEtale.etaleZariskiRestrictionEquiv`, the invertibility clause of
Stacks 04CS on the scheme side. -/
public def schemeZariskiDerivationEquiv :
    PresheafOfModulesOfCommRing.Derivation' G.val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom ≃
      SheafOfModules.SheafDerivation
        (inverseImageStructureMap
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) α.left))
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
          ((representedModuleRestriction B S hS U).obj G)) :=
  (schemeEtaleDerivationEquiv B S hS α G).trans
    (_root_.AlgebraicGeometry.SmallEtale.etaleZariskiRestrictionEquiv (associatedBigEtaleSite B)
      α.left ((representedModuleRestriction B S hS U).obj G))

/-- **The bottom horizontal of the Stacks 05ZC/05ZD square describes its values.**  Over an open
`W` of the scheme underlying `U`, the Zariski derivation attached to a `yoneda.obj V`-derivation
`D` of `𝒪_{yoneda.obj U}` takes the value `D` takes over the object of the small étale site of
`yoneda.obj U` that `W` names, on the global functions of the open subscheme `W`.

This is `AlgebraicGeometry.Space.etaleDerivationOfSpace_d` and
`AlgebraicGeometry.SmallEtale.zariskiRestrictionData_d` composed: the identification of the two
sites moves the indexing object and changes no value, and the passage to the small Zariski site
evaluates at the étale object an open names.  Both halves hold by `rfl`, and so does the
composite, because `AlgebraicGeometry.SmallEtale.etaleZariskiRestrictionEquiv` is an
`Equiv.ofBijective` of a derivation built by transport rather than by a universal property. -/
public theorem schemeZariskiDerivationEquiv_d
    (D : PresheafOfModulesOfCommRing.Derivation' G.val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom)
    {W : (((BigFppfOver.toScheme B S hS).obj U).Opens)ᵒᵖ}
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, W.unop)) :
    (schemeZariskiDerivationEquiv B S hS α G D).d a =
      D.d (X := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W.unop)))
        (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app W).hom a) :=
  rfl

/-- **Step 1, read as the morphisms out of `Ω_{U/V}`.**  A `yoneda.obj V`-derivation of
`𝒪_{yoneda.obj U}` with values in `G` is the same thing as a morphism of `𝒪_U`-modules
`Ω_{U/V} ⟶ ε_*(G read on the small étale site of the scheme `U`)`.

This is the form the Zariski adjunction `k^* ⊣ k_*` applies to, and it is
`AlgebraicGeometry.Space.schemeZariskiDerivationEquiv` followed by the universal property of
`Ω_{U/V}`, Stacks 08RM. -/
public def schemeZariskiHomEquiv :
    PresheafOfModulesOfCommRing.Derivation' G.val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom ≃
      (Scheme.Hom.relativeDifferentials
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) α.left) ⟶
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
          ((representedModuleRestriction B S hS U).obj G)) :=
  (schemeZariskiDerivationEquiv B S hS α G).trans
    (Equiv.ofBijective _
      (_root_.AlgebraicGeometry.SmallEtale.bijective_universalRelativeDerivation_postcomp
        (associatedBigEtaleSite B) α.left _)).symm

end AlgebraicGeometry.Space

end
