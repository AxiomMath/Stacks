module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponents
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedDerivationUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModulePullbackMate
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparisonMapDerivation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Zariski side of the naturality square of Stacks 04CS, on sections

`AlgebraicGeometry.Space.SchemeDifferentialsComparisonMapNaturality`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMap.lean`) is the
square which says that the identification of Stacks 04CS between the small Zariski and the small
étale relative differentials of a morphism of schemes of the site is compatible with the
comparison maps of a composable pair `ψ : U ⟶ V`, `χ : V ⟶ W`.  Both of its sides are morphisms
out of an inverse image of modules, so the square is attacked by transposing it across the two
composite adjunctions round the square of Stacks 03LC (1) — the ones
`AlgebraicGeometry.Space.representedAssociatedModulePullbackAdjunction` and
`AlgebraicGeometry.Space.representedAssociatedModuleSpacePullbackAdjunction` name — where both
sides are morphisms of Zariski modules on the scheme underlying `V` and are therefore readable on
sections over an open of that scheme.

This file reads the two transposed sides on sections, as far as each one goes without the
sections formula for the comparison of the two composite *right* adjoints.  For the Zariski side
that is all the way: its value on the universal differential `d_{V/W}(a)` is the canonical
derivation `d^a` of Stacks 04CS of `ψ ≫ χ` on the pullback `ψ♯ a`, read through the unit of the
equivalence of module categories of Stacks 03DX (2) over the open `ψ^{-1}O`.

## Main definitions

* `AlgebraicGeometry.Space.representedOpensObj`: an open of the scheme underlying `C`, read as an
  object of the small étale site of the represented algebraic space `yoneda.obj C` across the
  equivalence of the two sites.
* `AlgebraicGeometry.Space.representedRelativeDifferentialsZariski`: **the Zariski module that the
  chain of links of Stacks 04CS on sections is carried in**, which names the one spelling the five
  `zariskiChain_*` links below are stated in.

## Main results

* `AlgebraicGeometry.Space.zariskiChain_homEquiv_schemeChartDifferentialsMap`,
  `AlgebraicGeometry.Space.zariskiChain_representedAssociatedModuleAdjunction_unit`,
  `AlgebraicGeometry.Space.zariskiChain_associatedModuleAdjunction_unit_d`,
  `AlgebraicGeometry.Space.zariskiChain_representedModuleSiteEquivalence_unit` and
  `AlgebraicGeometry.Space.zariskiChain_representedUniversalDerivation`: **the five links of the
  Zariski side, each in its own declaration and all but the last in one chosen spelling**, so that
  the `Eq.trans` chain which consumes them is syntactic.  All but the first are stated at a
  general morphism `α : C ⟶ D` and a general open, so that the spaces side of the square, which
  needs the same four at `α = χ` and the open `O`, uses these and not copies of them.  See the
  implementation note on the spelling and on what the chain costs.
* `AlgebraicGeometry.Scheme.Hom.postcomp_universalRelativeDerivation_eq_of_app_d`: **a derivation
  identity of Stacks 01UV reduced to sections**, on variables, which is the shape the hypothesis
  of `AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_square_of_postcomp` is
  discharged in.
* `AlgebraicGeometry.Space.homEquiv_representedAssociatedModuleSpacePullback`: **the spaces side
  of the square, transposed across the composite adjunction, is the comparison map of
  Stacks 04CS followed by the transpose across the inverse image of Stacks 03LU alone.**  The
  right-hand side is what
  `Space.representedDifferentialsComparison_comp_homEquiv_representedUniversalDerivation`
  computes on the canonical derivations.
* `AlgebraicGeometry.Space.app_homEquiv_schemeChartDifferentialsMap`: **the Zariski side of the
  square, transposed, carries the universal differential `d_{V/W}(a)` to the associated-module
  unit at `ψ^{-1}O` of the universal differential `d_{U/W}(ψ♯ a)`.**  This is the characterizing
  property of Stacks 01UV, `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_d`, read
  through the direct image along the morphism of schemes.
* `AlgebraicGeometry.Space.app_representedAssociatedModuleAdjunction_unit`: the unit of the
  transported associated-module adjunction of a represented algebraic space, on sections over an
  open: it is the unit of the associated-module adjunction of Stacks 03DU (4) of the scheme,
  followed by the unit of the equivalence of module categories of Stacks 03DX (2).  Chained with
  `AlgebraicGeometry.SmallEtale.associatedModuleAdjunction_unit_app_universalRelativeDerivation_d`
  this turns the previous result into a statement about `d^a`.
* `CategoryTheory.Adjunction.comp_homEquiv_map_comp`: transposing, across a composite adjunction,
  a morphism which begins with the outer left adjoint applied to an arrow is transposing across
  the inner adjunction and composing with that arrow.
* `AlgebraicGeometry.Space.subsingleton_hom_smallBaseChange_representedOpensObj`: **there is at
  most one morphism of the small étale site of `yoneda.obj U` into the base change along `ψ̃` of
  the chart which a Zariski open of the scheme underlying `V` cuts out.**  This is what pins the
  arrow that
  `AlgebraicGeometry.Space.induced_representedRestrictModuleBaseChangeIso_inv_tail` only asserts
  to exist.  It rests on `AlgebraicGeometry.Space.mono_hom_representedOpensObj`, that the
  structure morphism of such a chart is a monomorphism — it is the image under `yoneda` of the
  open immersion of the open — and on
  `AlgebraicGeometry.Space.mono_hom_smallBaseChange`, that base change along a representable
  morphism preserves that.

## Implementation notes

**Why the sections are read in the `AlgebraicGeometry.Scheme.Modules.Hom.app` spelling.**  The
sections of a pushforward of sheaves of modules are the sections of the module at the reindexed
object *after a restriction of scalars*, so the two spellings of one group of sections are equal
only after unfolding `SheafOfModules.pushforward`.  Over a scheme that unfolding is already
packaged: `AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj` is a `rfl` lemma identifying
`Γ(f_* M, O)` with `Γ(M, f^{-1}O)`, and `Γ` is the abelian-group sections, where the restriction
of scalars is invisible.  Statements written with `Γ` and
`AlgebraicGeometry.Scheme.Modules.Hom.app` therefore typecheck, while the same statements written
with `.val.app` and `ModuleCat.Hom.hom` exhaust the heartbeat budget at `whnf` on the elaboration
of their own types.

**Why each step is its own declaration, and why they are not combined.**  A statement whose two
sides are separated by *two* pushforward unfoldings does not elaborate: the composite
of `AlgebraicGeometry.Space.app_homEquiv_schemeChartDifferentialsMap` with
`AlgebraicGeometry.Space.app_representedAssociatedModuleAdjunction_unit` cannot be *stated* —
its left-hand side lives in the sections of a direct image of a restriction of a transport and
its right-hand side in the sections of the module itself.  The chain is therefore assembled by
`Eq.trans` at the point of use, where the intermediate type is supplied by the previous step and
never has to be written down.

**What is still missing, and where.**  The square is equivalent, through the mate identity
`AlgebraicGeometry.Space.conjugateEquiv_representedAssociatedModulePullbackMateIso_hom` and
`CategoryTheory.homEquiv_comp_conjugateEquiv`, to the statement that the Zariski side transposed,
followed by the comparison
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso` of the two composite right
adjoints, is the spaces side transposed; that reduction is
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_square_of_postcomp`, whose one
hypothesis is the identity of Zariski derivations it leaves.  Both transposed sides are computed
here and in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMapDerivation.lean`, and
the value on sections of the comparison is read, in its `inv`
direction, by
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_chartFirst` together with
`AlgebraicGeometry.Space.induced_representedRestrictModuleBaseChangeIso_inv_tail`.

That it is the `inv` direction and not the `hom` direction is forced: by
`CategoryTheory.Iso.eq_comp_inv` the equation `(Zariski side) ≫ γ.hom.app X = (spaces side)` is
the equation `(Zariski side) = (spaces side) ≫ γ.inv.app X`, and `γ.inv` is the direction every
factor of `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso` computes in.  Its
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso` factor is assembled from
`CategoryTheory.SheafOfModules.pushforwardComp` and
`CategoryTheory.SheafOfModules.pushforwardCongr₂`, whose components in both directions are read
off by `CategoryTheory.SheafOfModules.pushforwardComp_hom_app_val_app` and the simp lemmas of
`CategoryTheory.SheafOfModules.pushforwardCongr`; its
`AlgebraicGeometry.Space.representedModulePushforwardSquareInverseIso` factor contributes the two
structure comparisons of the equivalences of module categories, again
`CategoryTheory.SheafOfModules.pushforwardNatTrans` and `pushforwardCongr` components, and — the
only non-formal factor — `AlgebraicGeometry.Space.modulePushforwardChartIso`, the comparison of
the direct image of Stacks 03LU with base change of étale scheme charts.  That one enters `γ.inv`
through its `hom`, which is exactly the direction
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_val_app` reads off, as the chart
projection `AlgebraicGeometry.Space.chartSetProj`.  So no new reading of a right Kan extension is
needed.

**The remaining identity of sections cannot be split.**  What is left is one
equation: the two transposed sides, evaluated over an open `O` of the scheme underlying `V` on the
universal differential `d_{V/W}(a)`, agree.  Its two sides are the components at `O` of two
morphisms with one source and one target, so the equation itself elaborates — but no *resting
place* inside it does.  Each of the following exhausts the heartbeat budget at `whnf`
**while elaborating its own statement**, before any proof is elaborated:

* the Zariski side's value written as the canonical derivation `d^a` of `ψ ≫ χ`, through
  `AlgebraicGeometry.Space.representedUniversalDerivation`, on a regular function;
* the same with the scheme-side `AlgebraicGeometry.Space.representedAssociatedDerivation` in place
  of it, so that only the restriction to the small Zariski site and the transport of
  Stacks 03DX (2) have to be crossed;
* and the two-factor bridge on its own — the unit of
  `AlgebraicGeometry.Space.app_representedAssociatedModuleAdjunction_unit` in the `Γ` spelling on
  one side, and the value that
  `AlgebraicGeometry.SmallEtale.associatedModuleAdjunction_unit_app_universalRelativeDerivation_d`
  gives it on the other, at one open and one regular function.

So the note above on why each step is its own declaration is not merely about convenience: there
is no intermediate statement between the two sides to stop at.  The links of the chain exist, and
each of them applies.  On the Zariski side:
`AlgebraicGeometry.Space.app_homEquiv_schemeChartDifferentialsMap`,
`AlgebraicGeometry.Space.app_representedAssociatedModuleAdjunction_unit`,
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction_unit_app_universalRelativeDerivation_d`,
`AlgebraicGeometry.Space.representedModuleSiteEquivalence_unit_app_val_app` and the `d_map` field
of `PresheafOfModules.Derivation`, which absorbs the restriction along the counit of the
equivalence of sites back into `d^a`; then
`AlgebraicGeometry.Space.representedUniversalDerivation_d`, a `rfl` lemma, names the result at
`AlgebraicGeometry.Space.representedOpensObj`.  On the spaces side:
`CategoryTheory.Adjunction.homEquiv_unit`,
`AlgebraicGeometry.Space.representedRestrictModule_map_val_app_hom_apply`,
`Space.representedDifferentialsComparison_comp_homEquiv_representedUniversalDerivation`,
the two readings of the comparison named above,
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_chartSetProj`,
`AlgebraicGeometry.Space.chartSetProj_naturality` — which carries the chart projection past the
direct image of the derivation in its sheaf-of-sets form — and
`AlgebraicGeometry.Space.structureSharp_comp_chartProjectionSharpDirectImage`, Stacks 03G8 (2),
which turns the chart projection of `ψ̃♯` into pullback of regular functions along the cartesian
projection `AlgebraicGeometry.Space.cartesianProjection`.

**What a single declaration cannot do.**  Chaining those links by
`Eq.trans` does *not* fit one declaration's heartbeat budget, whichever of the two spellings the
chain is carried in.  With no option override, the first two links of the Zariski side
alone, chained against a goal whose type is the `Γ` of a direct image, need about twice the
budget; carried instead with the shared type given explicitly as the `Γ` of the module itself over
`ψ^{-1}O`, those same two links cost a second.  Each `Eq.trans` re-checks the shared type of its
two arguments, and a check which crosses an unfolding of `SheafOfModules.pushforward` — or the
`Γ`-to-`.val.app` bridge `AlgebraicGeometry.Scheme.Modules.app_apply_eq_val_app` — is tens of
thousands of heartbeats on its own, so the chain pays once per link for a crossing it should pay
for once in total.  The consequence is not that a resting place between the two
sides exists — none does — but that each *link* has to be restated: its own equation, in its
own declaration with its own budget, with the type shared by its two sides written out in the one
spelling the chain is to be carried in.  Every `Eq.trans` of the chain which consumes them is then
syntactic, and each crossing is paid once.

**The spelling the Zariski links are stated in, and why.**  The links are restated, and the
spelling is the `Γ` of `AlgebraicGeometry.Space.representedRelativeDifferentialsZariski` over the
*preimage* open `ψ^{-1}O` of the scheme underlying `U` — not the `Γ` of the direct image over `O`,
and not the `.val.obj` spelling in which the last links naturally live.  Three things choose it.
It is on the far side of the single unfolding of `CategoryTheory.SheafOfModules.pushforward` the
chain has to cross, so that crossing is paid exactly once, in the ascription of
`AlgebraicGeometry.Space.zariskiChain_homEquiv_schemeChartDifferentialsMap`.  `Γ` hides the
restriction of scalars, which is what makes statements written with `.val.app` and
`ModuleCat.Hom.hom` exhaust the budget on their own types.  And it is one cheap crossing from the
spelling the consumer forces: the hypothesis of
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_square_of_postcomp`, reduced to
sections by `AlgebraicGeometry.Scheme.Hom.postcomp_universalRelativeDerivation_eq_of_app_d`, is an
equation in the `Γ` of a direct image over `O`.

**What the restated chain costs.**  Per link, as reported by `#count_heartbeats` with no option
override in the library: 28,289 / 37,850 / 110,039 / 68,798 / 30,275 heartbeats
for the five links in order.  Three facts about how they may be combined follow.

*The chain term does not assemble at the standard budget, and the heartbeat figures in this note
do not predict that it will.*  `#count_heartbeats` reports **100,468** heartbeats for
`l₁.trans (l₂.trans (l₃.trans (l₄.trans l₅)))`, and 81,222 for the last four at `α = χ` and
`P = O`; both are under the project's budget of 200,000, and yet neither term compiles there.
With no option override, each of these is a `(deterministic) timeout at whnf` at 200,000
heartbeats: a bare `have h := l₁.trans (l₂.trans (l₃.trans (l₄.trans l₅)))`; the same with every
`Eq.trans`'s `α` written out as the `Γ` of
`AlgebraicGeometry.Space.representedRelativeDifferentialsZariski` of `ψ ≫ χ` over `ψ^{-1}O`; the
last four alone at `α = χ` and `P = O` with their `α` written out; and
`refine Eq.trans (α := …) (the chain) ?_` against the sections identity of the square itself.
With `α` left to be inferred the same `refine` is a `whnf` timeout at **2,000,000** heartbeats, so
the note above that the inferred form "is not a substitute" understates it.  `#count_heartbeats`
runs at `maxHeartbeats 0`; what it reports here is a lower bound and not a budget check, and every
figure in this module's notes is to be read as one.

*Where the wall is.*  Applying the links one at a time, by successive
`refine Eq.trans (α := …) lᵢ ?_` against the sections identity, links one, two and three go
through — with or without the `γ^{-1}` half of the square already discharged, which does fit (see
the note in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMapSpacesSections.lean`).
Adding link four is the timeout.  It is the same wall at
`AlgebraicGeometry.Space.zariskiChain_unit_representedUniversalDerivation`, which joins links four
and five with neither side pinned to the chain's spelling precisely so that the crossing between
the two spellings is paid once instead of twice: that declaration is green, and the step to it
from link three's output at the concrete arguments `α = ψ ≫ χ`, `P = ψ^{-1}O` is not.  So the
crossing is affordable at the general `(C, α, P)` of a declaration's own statement — link four
pays it for 68,798 — and is not affordable at those concrete arguments inside a consumer.  That
single crossing is what the assembly of this square still needs, and no rearrangement of the
links tried so far avoids it.

*And it cannot be moved into a hypothesis.*  The obvious way round — a lemma stated on variables
which takes `(hw : (the chain's left-hand side : Γ(…Zariski α, P)) = w)` with `w` in the
`.val.obj` spelling, so that the crossing is paid once in that lemma's statement and the consumer
only instantiates it — does not elaborate: `hw` is a `(deterministic) timeout at isDefEq` at
200,000 heartbeats, both with the module concrete and with it a *variable*.  That is the same wall
the companion module records for a sections restatement of its bridge, now known to hold on
variables too, so the pair "pay the crossing in one declaration, consume it in another" is not
available for this chain.

*The chain cannot be given a name.*  Stating that composite as a theorem costs **1,268,302**
heartbeats with its type pinned to the chain's spelling and **1,252,878** without — six times the
budget either way.  The cost is in the *statement*, not the proof: its right-hand side is the
canonical derivation `d^a` at `AlgebraicGeometry.Space.representedOpensObj`, and checking that
against the chain's spelling crosses `restrictModule` and both pushforwards of the equivalence of
module categories at once.  This is what the note above means by there being no resting place: the
chain must be built where it is used, by `Eq.trans` on the five links, and its type must never be
written down.

*The links cannot be merged, and generality is not what makes them expensive.*  Folding the last
three into one declaration costs 315,551 heartbeats with the type pinned and 281,517 without;
folding the last *four* into one costs **2,441,223** heartbeats at the concrete arguments
`(V, χ, O)` and **2,445,884** at general `(C, α, P)`, so the merge is dear for its own sake and
not for its arguments.  Pinning the fifth link's left-hand side to the chain's spelling, on its
own, is a `whnf` timeout.  Hence the fifth link is stated in its own spelling and the crossing
sits in the fourth link's right-hand side, where it is affordable.

*The last four links are stated at a general `α : C ⟶ D` and a general open, and that is cheaper,
not dearer.*  Only the first link is specific to the square: links two to five say nothing about
`ψ` and `χ` beyond the morphism whose differentials they are, so each is stated at a general
`α : C ⟶ D` and a general open `P` of the scheme underlying `C`.  Each general link is
slightly *cheaper* than the concrete one it replaces (37,850 against 39,282; 110,039 against
131,933; 68,798 against 70,674; 30,275 against 30,798), the Zariski chain still assembles
syntactically from them at `α = ψ ≫ χ` and `P = ψ^{-1}O`, and one copy serves the spaces side
too: see the note below.

**The spaces side: where it must rest, and why it cannot rest here.**  The spaces side is *not* to
be carried in the Zariski spelling above.  Its links live, one and all, in the `.val.app (op …)`
spelling over objects of the small étale site of a represented algebraic space, and the Zariski
chain already ends in the one place the two sides can meet:
`AlgebraicGeometry.Space.representedUniversalDerivation` of `ψ ≫ χ` over
`AlgebraicGeometry.Space.representedOpensObj U (ψ^{-1}O)`.  So the spaces side should be restated
in the sections of `AlgebraicGeometry.Space.representedRelativeDifferentials` over that object,
and the single crossing between the two spellings is the one
`AlgebraicGeometry.Space.zariskiChain_representedModuleSiteEquivalence_unit` has already paid.

But it cannot be restated *in this module*, and the reason is structural rather than budgetary.
Of the links the spaces side needs, these are in this file's import closure and can be used here
as they stand: `CategoryTheory.Adjunction.homEquiv_unit`,
`AlgebraicGeometry.Space.representedRestrictModule_map_val_app_hom_apply`, the evaluation of the
transposed spaces side on the canonical derivations that the note on
`AlgebraicGeometry.Space.homEquiv_representedAssociatedModuleSpacePullback` above names,
`AlgebraicGeometry.Space.representedDifferentialsComparison_representedUniversalDerivation`,
`AlgebraicGeometry.Space.representedUniversalDerivationHom_hom_app`,
`Space.representedRestrictModuleBaseChangeIso_inv_app_smallEtaleModuleEquivalence`
and `Stacks.SectionsComponents.Induced.eq`.

These are **not** —
`AlgebraicGeometry.Space.induced_representedRestrictModuleBaseChangeIso_inv_tail`,
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_chartFirst`,
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_val_app`,
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_chartSetProj`,
`AlgebraicGeometry.Space.chartSetProj_naturality`,
`AlgebraicGeometry.Space.structureSharp_comp_chartProjectionSharpDirectImage`,
`AlgebraicGeometry.Space.chartSetProj`, `AlgebraicGeometry.Space.cartesianProjection` and
`AlgebraicGeometry.Space.cartesianProjectionSharp`.  Both readings of the comparison on sections
are among them, and so is Stacks 03G8 (2); the notes above cite all of them, so they are a
description of what the repository proves and not of what is available here.  Three of the four
modules that supply them —
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeChartUnit.lean`,
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeChartUnitTransport.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSchemeStructureSharp.lean` — are independent of
this one and may be imported beside it.  **The fourth cannot be:**
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleSiteEquivalenceInverse.lean` imports
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMapMate.lean`, which
imports *this* module, so adding it here is an import cycle and Lean says so at line 1.  It
carries both readings of the comparison of the two composite right adjoints, which is to say the
whole far end of the spaces side, so there is no arrangement of the other three that avoids it.

The spaces side therefore belongs in a module **downstream** of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleSiteEquivalenceInverse.lean`, which is a
leaf, and the three independent modules are imported there beside it.  From such a
module the closure is 4,560 modules against this one's 4,537, every one of the nine names above
resolves, and there is no universe constraint of the kind the note in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsRepresented.lean` records for
`ChartSpaceGlobalPresentation`.  That module can also import
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeDifferentialsShortExact.lean`, which is a sibling of
this whole chain and not an ancestor of it, so
`AlgebraicGeometry.Space.PullbackDifferentialsMapChartComparison` is statable there and
the `hchart` hypothesis of Stacks 06BI is dischargeable there and nowhere upstream of it.

**The link the map of the spaces side is missing.**  Between
`CategoryTheory.Adjunction.homEquiv_unit`, which splits the transpose into the unit followed by the
right adjoint of the arrow, and the evaluation of that arrow on the canonical derivations named in
the `## Main results` entry for
`AlgebraicGeometry.Space.homEquiv_representedAssociatedModuleSpacePullback` above,
whose left-hand side is that arrow evaluated on `d^a` of `χ`, there is a step: the unit of the
transported associated-module adjunction of `V`, over `O`, on the universal differential
`d_{V/W}(a)`, has to *be* `d^a` of `χ` at
`AlgebraicGeometry.Space.representedOpensObj V O`.  That is the same four-link chain as the
Zariski side's last four, at `α = χ` and `P = O` instead of `α = ψ ≫ χ` and `P = ψ^{-1}O`, which
is why those four are stated generally above.  `#count_heartbeats` reports **81,222** heartbeats
for the four at the `V`-side arguments against 100,468 at the `U`-side ones; both figures are
lower bounds and neither chain compiles at the standard budget, for which see the note below.

**The arrow of the tail, and what is still owed.**
`AlgebraicGeometry.Space.induced_representedRestrictModuleBaseChangeIso_inv_tail` is a
`Stacks.SectionsComponents.Induced`, so it gives restriction along *some* arrow
`representedOpensObj U (ψ^{-1}O) ⟶ (smallBaseChange …).obj (representedOpensObj V O)` of the small
étale site of `yoneda.obj U` and not along a named one.  That arrow is now pinned:
`AlgebraicGeometry.Space.subsingleton_hom_smallBaseChange_representedOpensObj` is the
`Subsingleton` instance for that hom-set, and `Stacks.SectionsComponents.Induced.eq` consumes it.
The scheme-site statement `AlgebraicGeometry.SmallEtale.subsingleton_hom_opensToSmallEtale` does
not generalize to it: that one is about the small étale site of a *scheme* and about a target in
the image of the small Zariski site, so neither its category nor its target covers a base-changed
chart of a represented algebraic space.  What does generalize is its *reason*, monicity of the
structure morphism of the target, and that is the route taken here —
`AlgebraicGeometry.Space.mono_hom_representedOpensObj` and
`AlgebraicGeometry.Space.mono_hom_smallBaseChange`, through
`CategoryTheory.CostructuredArrow.subsingleton_hom_of_mono`.

With the arrow pinned, the last step is the identification of the two regular functions the two
sides evaluate the canonical derivation `d^a` of `ψ ≫ χ` on: the Zariski pullback `ψ♯ a` on one
side, and on the other the pullback of `a` along that arrow followed by the cartesian projection.
Both are pullbacks of `a` along morphisms of schemes into `O`, and the open immersion of `O` is a
monomorphism — indeed `AlgebraicGeometry.BigEtaleOver.subsingleton_hom_opensObj` already says that
there is at most one morphism of the big étale site over the scheme underlying `U` into the object
cut out by an open, so the two morphisms into `O` agree as soon as both are written as such.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **A composite of morphisms of `𝒪_X`-modules, on a section.**  This is
`AlgebraicGeometry.Scheme.Modules.Hom.comp_app` with both sides applied to a section; the applied
form is what a chain of `Eq.trans` steps consumes, and unlike the unapplied form it needs no
motive. -/
theorem comp_app_apply {X : Scheme.{u}} {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P)
    (O : X.Opens) (y : Γ(M, O)) : (f ≫ g).app O y = g.app O (f.app O y) := rfl

/-- **The two spellings of the action of a morphism of `𝒪_X`-modules on a section agree**: the
abelian-group spelling `AlgebraicGeometry.Scheme.Modules.Hom.app`, in which the sections of a
direct image are the sections of the module over the preimage open on the nose, and the
module-category spelling through `ModuleCat.Hom.hom`, in which they are separated by a
restriction of scalars.  The first is the one whose statements elaborate; the second is the one
the characterizing property of Stacks 01UV is stated in. -/
theorem app_apply_eq_val_app {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (O : X.Opens) (y : Γ(M, O)) : f.app O y = (f.val.app (op O)).hom y := rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

/-- **A derivation identity of Stacks 01UV reduced to sections.**  Two morphisms out of the sheaf
of relative differentials of `f : X ⟶ Y` induce the same `Y`-derivation of `𝒪_X` as soon as they
agree, over every open `O` of `X` and every regular function `a` on `O`, on the universal
differential `d_{X/Y} a`.

This is the shape in which the hypothesis of
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_square_of_postcomp` is
discharged.  Both reductions it performs -- `PresheafOfModules.Derivation.postcomp_d_apply`, and
the two spellings of a section that `AlgebraicGeometry.Scheme.Modules.app_apply_eq_val_app`
identifies -- are crossings that cost tens of thousands of heartbeats at the small étale site of
a represented algebraic space.  Stated here on variables they cost nothing, and the consumer pays
for none of them. -/
theorem postcomp_universalRelativeDerivation_eq_of_app_d {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (u₁ u₂ : relativeDifferentials f ⟶ F)
    (h : ∀ (O : X.Opens) (a : Γ(X, O)),
      u₁.app O ((universalRelativeDerivation f).d a) =
        u₂.app O ((universalRelativeDerivation f).d a)) :
    (universalRelativeDerivation f).postcomp u₁.val =
      (universalRelativeDerivation f).postcomp u₂.val := by
  refine PresheafOfModules.Derivation.ext (funext fun O => AddMonoidHom.ext fun a => ?_)
  refine Eq.trans (PresheafOfModules.Derivation.postcomp_d_apply
    (universalRelativeDerivation f) u₁.val a) ?_
  refine Eq.trans ?_ (PresheafOfModules.Derivation.postcomp_d_apply
    (universalRelativeDerivation f) u₂.val a).symm
  refine Eq.trans (Scheme.Modules.app_apply_eq_val_app u₁ O.unop _).symm ?_
  exact (h O.unop a).trans (Scheme.Modules.app_apply_eq_val_app u₂ O.unop _)

end AlgebraicGeometry.Scheme.Hom

namespace CategoryTheory.Adjunction

/-- **Transposing a morphism which begins with the outer left adjoint applied to an arrow.**  For
adjunctions `adj : F ⊣ G` and `adj' : F' ⊣ G'`, the transpose across `adj.comp adj'` of
`F'.map j ≫ h` is the transpose of `h` across `adj'` alone, preceded by `j`, transposed across
`adj`.

This is `CategoryTheory.Adjunction.comp_homEquiv` followed by
`CategoryTheory.Adjunction.homEquiv_naturality_left`.  It is stated on variables because
rewriting with either of those on a concrete composite of module categories fails its motive
check: the two spellings of one category of modules on the small étale site of a represented
algebraic space are not type-correct against each other at the transparency `rw` uses. -/
@[ega "0 3.5.5" "more general"]
theorem comp_homEquiv_map_comp {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ C} {F' : D ⥤ E} {G' : E ⥤ D}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (c : C) {Z : D} {Y : E}
    (j : F.obj c ⟶ Z) (h : F'.obj Z ⟶ Y) :
    (adj.comp adj').homEquiv c Y (F'.map j ≫ h) =
      adj.homEquiv c (G'.obj Y) (j ≫ adj'.homEquiv Z Y h) := by
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left]

end CategoryTheory.Adjunction

namespace CategoryTheory.CostructuredArrow

/-- **There is at most one morphism into a costructured arrow whose structure morphism is a
monomorphism.**  Two of them have the same image under `F` after composition with that structure
morphism, by the triangle each of them commutes, so they have the same image under `F`, and `F` is
faithful.

This is the reason `AlgebraicGeometry.SmallEtale.subsingleton_hom_opensToSmallEtale` holds, taken
away from the small étale site of a scheme and from targets cut out by Zariski opens; the
statement itself is about neither, so it applies to a base-changed chart of a represented
algebraic space as well. -/
theorem subsingleton_hom_of_mono {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) [F.Faithful] {X : D} (Z T : CostructuredArrow F X) (hT : Mono T.hom) :
    Subsingleton (Z ⟶ T) :=
  have := hT
  ⟨fun f g => CostructuredArrow.hom_ext f g (F.map_injective
    ((cancel_mono T.hom).1 ((CostructuredArrow.w f).trans (CostructuredArrow.w g).symm)))⟩

end CategoryTheory.CostructuredArrow

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {U V W : BigFppfOver B S hS}

/-- **The spaces side of the naturality square of Stacks 04CS, transposed across the composite
adjunction round the square of Stacks 03LC (1).**  The comparison map `c_ψ̃` of Stacks 04CX
precomposed with the inverse image along `ψ̃` of the comparison map `(Ω_{V/W})^a ⟶ Ω_{χ̃}` of
Stacks 04CS, and followed by the identification `Ω_{ψ̃ ≫ χ̃} ≅ (Ω_{U/W})^a`, transposes to the
comparison map of Stacks 04CS followed by the transpose across the inverse image of Stacks 03LU
alone.

The composite adjunction is the adjunction of Stacks 03DU (4) for `V` followed by the adjunction
of Stacks 03LU for `ψ̃`, so its transpose is the two transposes in turn, and the outer one absorbs
the inverse image of the comparison map by naturality.  The point of the statement is that its
right-hand side is what
`representedDifferentialsComparison_comp_homEquiv_representedUniversalDerivation`
evaluates on the canonical derivation `d^a` of Stacks 04CS. -/
theorem homEquiv_representedAssociatedModuleSpacePullback (ψ : U ⟶ V) (χ : V ⟶ W) :
    (representedAssociatedModuleSpacePullbackAdjunction B S hS ψ).homEquiv
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))
        (representedRelativeDifferentials B S hS (ψ ≫ χ))
        ((modulePullback B S hS (schemeSpaceMap ψ)).map
            (representedDifferentialsComparison B S hS χ) ≫
          pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
            (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom) =
      (representedAssociatedModuleAdjunction B S hS V).homEquiv _ _
        (representedDifferentialsComparison B S hS χ ≫
          (modulePullbackAdjunction B S hS (schemeSpaceMap ψ)).homEquiv _ _
            (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
              (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom)) :=
  CategoryTheory.Adjunction.comp_homEquiv_map_comp
    (representedAssociatedModuleAdjunction B S hS V)
    (modulePullbackAdjunction B S hS (schemeSpaceMap ψ)) _
    (representedDifferentialsComparison B S hS χ) _

/-- **An open of the scheme underlying `C`, read as an object of the small étale site of the
represented algebraic space `yoneda.obj C`.**  It is the open as an object of the small étale site
of the scheme, carried across the inverse of the equivalence of the two sites of
Stacks 03DX (2); the sections over it are where a morphism out of a transported module is read
when the morphism is restricted to the small Zariski site of the scheme. -/
abbrev representedOpensObj (C : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj C).Opens) : SmallEtale B S hS (schemeSpace C).1 :=
  (representedSmallEtaleEquivalence B S hS C).inverse.obj
    (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj C) C.left.property O)

/-- **The structure morphism of the chart which a Zariski open cuts out is a monomorphism.**  It
is the image under `yoneda` of the morphism of the big fppf site over `S` whose underlying
morphism of schemes is the open immersion of the open; `yoneda` is fully faithful, the projection
of the big fppf site to its schemes is faithful, and so is the inclusion of the schemes of the
site into all schemes, so monicity is read off the open immersion. -/
theorem mono_hom_representedOpensObj (C : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj C).Opens) :
    Mono (representedOpensObj B S hS C O).1.hom :=
  have : Mono (((Over.iteratedSliceEquiv C).inverse.obj
      ((BigEtaleOver.IsEtaleOver (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj C) C.left.property).ι.obj
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property O))).hom) :=
    (CostructuredArrow.proj (𝟭 B.Schemes) (B.obj hS)).mono_of_mono_map
      (B.inclusion.mono_of_mono_map (inferInstanceAs (Mono O.ι)))
  yoneda.map_mono _

/-- **Base change along a representable morphism preserves monicity of the structure morphism of
an étale chart.**  The base-changed chart is the fibre product of the chart along the morphism,
`AlgebraicGeometry.Space.smallBaseChange_isPullback`, and monomorphisms are stable under base
change. -/
theorem mono_hom_smallBaseChange {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (T : SmallEtale B S hS Y.1)
    (hT : Mono T.1.hom) : Mono ((smallBaseChange B S hS f hf).obj T).1.hom :=
  (hf.isPullback T.1.hom).mono_fst_of_mono hT

/-- **There is at most one morphism of the small étale site of `yoneda.obj U` into the base change
along `ψ̃` of the chart which a Zariski open of the scheme underlying `V` cuts out.**  This pins
the arrow which
`AlgebraicGeometry.Space.induced_representedRestrictModuleBaseChangeIso_inv_tail` only asserts to
exist: that result is a `Stacks.SectionsComponents.Induced`, hence restriction along *some* arrow
with this source and target, and `Stacks.SectionsComponents.Induced.eq` turns a `Subsingleton` for
the hom-set into agreement with any named one.

The structure morphism of the target is a monomorphism, by
`AlgebraicGeometry.Space.mono_hom_representedOpensObj` and
`AlgebraicGeometry.Space.mono_hom_smallBaseChange`, so
`CategoryTheory.CostructuredArrow.subsingleton_hom_of_mono` applies. -/
instance subsingleton_hom_smallBaseChange_representedOpensObj (ψ : U ⟶ V)
    (Z : SmallEtale B S hS (schemeSpace U).1)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    Subsingleton (Z ⟶ (smallBaseChange B S hS (representedSpaceMap B S hS ψ)
      (relativelyRepresentable_yoneda_map B S hS ψ)).obj
      (representedOpensObj B S hS V O)) :=
  ⟨fun f g => ObjectProperty.hom_ext _ <|
    (CostructuredArrow.subsingleton_hom_of_mono yoneda Z.1 _
      (mono_hom_smallBaseChange B S hS (representedSpaceMap B S hS ψ)
        (relativelyRepresentable_yoneda_map B S hS ψ) (representedOpensObj B S hS V O)
        (mono_hom_representedOpensObj B S hS V O))).allEq f.hom g.hom⟩

/-- **Restriction to the small Zariski site of the scheme, on a section over an open.**  The
restriction of a morphism of sheaves of modules on the small étale site of the scheme underlying
`C` along the inclusion of the small Zariski site acts over an open `P` as the morphism itself
acts over the object of the small étale site that `P` is. -/
theorem restrictModule_map_app_apply (C : BigFppfOver B S hS)
    {G G' : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj C) C.left.property)}
    (k : G ⟶ G') (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (z : Γ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj G, P)) :
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj C) C.left.property).map k).app P z =
      (k.val.app (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))).hom z :=
  (Scheme.Modules.app_apply_eq_val_app _ P z).trans
    (Stacks.SectionsComponents.pushforward_map_val_app _ k (op P) z)

/-- **Restriction to the small Zariski site of the scheme through the equivalence of the two
small étale sites, on a section over an open.**  A morphism of `𝒪`-modules on the small étale
site of the represented algebraic space `yoneda.obj C`, transported to the small étale site of the
scheme and restricted to its small Zariski site, acts over an open `O` as the morphism itself
acts over `AlgebraicGeometry.Space.representedOpensObj`. -/
theorem representedRestrictModule_map_val_app_hom_apply (C : BigFppfOver B S hS)
    {G G' : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2} (k : G ⟶ G')
    (O : (((BigFppfOver.toScheme B S hS).obj C).Opens)ᵒᵖ)
    (z : (((representedModuleSiteEquivalence B S hS C).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj G).val.obj O) :
    ((((representedModuleSiteEquivalence B S hS C).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).map k).val.app O).hom z =
      (k.val.app (op (representedOpensObj B S hS C O.unop))).hom z :=
  (Stacks.SectionsComponents.pushforward_map_val_app
    (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj C) C.left.property)
    ((representedModuleSiteEquivalence B S hS C).inverse.map k) O z).trans
  (Stacks.SectionsComponents.pushforward_map_val_app
    (representedStructureMapInverse B S hS C) k _ z)

/-- **The unit of the equivalence of module categories of Stacks 03DX (2) is restriction along
the counit of the equivalence of sites.**  Over an object `T` of the small étale site of the
scheme underlying `C`, the unit `M ⟶ (M read on the space, read back on the scheme)` is
restriction of `M` along the counit component at `T`.

The equivalence of module categories is the pushforward-pushforward equivalence of the
equivalence of sites, whose unit `CategoryTheory.SheafOfModules.pushforwardPushforwardEquivalence`
computes on sections. -/
theorem representedModuleSiteEquivalence_unit_app_val_app (C : BigFppfOver B S hS)
    (M : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj C) C.left.property))
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj C) C.left.property) (y : M.val.obj (op T)) :
    (((representedModuleSiteEquivalence B S hS C).unit.app M).val.app (op T)).hom y =
      M.val.map ((representedSmallEtaleEquivalence B S hS C).counit.app T).op y :=
  SheafOfModules.pushforwardPushforwardEquivalence_unit_app_val_app
    (representedSmallEtaleEquivalence B S hS C) (representedStructureMap B S hS C)
    (representedStructureMapInverse B S hS C)
    (representedStructureMap_counit_coherence B S hS C)
    (representedStructureMap_unit_coherence B S hS C) M (op T) y

/-- **The unit of the transported associated-module adjunction of a represented algebraic space,
on a section over an open.**  The adjunction is the adjunction of Stacks 03DU (4) of the scheme
underlying `C` followed by the equivalence of module categories of Stacks 03DX (2), so its unit
over an open `P` is the unit of Stacks 03DU (4) over `P`, followed by the unit of the equivalence
over the object of the small étale site of the scheme that `P` is.

The two factors are the two computable ones: the first is carried to the canonical derivation
`d^a` of Stacks 04CS by
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction_unit_app_universalRelativeDerivation_d`,
and the second is restriction along the counit of the equivalence of sites by
`AlgebraicGeometry.Space.representedModuleSiteEquivalence_unit_app_val_app`. -/
theorem app_representedAssociatedModuleAdjunction_unit (C : BigFppfOver B S hS)
    (M : ((BigFppfOver.toScheme B S hS).obj C).Modules)
    (P : ((BigFppfOver.toScheme B S hS).obj C).Opens) (y : Γ(M, P)) :
    ((representedAssociatedModuleAdjunction B S hS C).unit.app M).app P y =
      (((representedModuleSiteEquivalence B S hS C).unit.app
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj M)).val.app
          (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))).hom
        ((((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
              (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj C)
              C.left.property).unit.app M).val.app (op P)).hom y) := by
  refine Eq.trans (congrArg (fun m : M ⟶
      ((representedModuleSiteEquivalence B S hS C).inverse ⋙
        _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
            ((representedAssociatedModule B S hS C (schemeSpace C).property).obj M) =>
    m.app P y) (CategoryTheory.Adjunction.comp_unit_app
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj C) C.left.property)
      (representedModuleSiteEquivalence B S hS C).toAdjunction M)) ?_
  refine Eq.trans (Scheme.Modules.comp_app_apply _ _ P y) ?_
  exact restrictModule_map_app_apply B S hS C _ P _

/-- **The Zariski side of the naturality square of Stacks 04CS, transposed, on the universal
differential.**  Over an open `O` of the scheme underlying `V` and a regular function `a` on `O`,
the transpose across the composite adjunction of the associated module of the Zariski comparison
map of Stacks 01UV carries the universal differential `d_{V/W}(a)` to the unit of the transported
associated-module adjunction of `U`, over the open `ψ^{-1}O`, applied to the universal
differential `d_{U/W}(ψ♯ a)` of the pullback of `a`.

The transpose splits as the transpose of the Zariski comparison map itself followed by that unit,
which is
`AlgebraicGeometry.Space.homEquiv_representedAssociatedModule_map_schemeChartDifferentialsMap`;
and the transpose of the Zariski comparison map on the universal derivation is the characterizing
property of Stacks 01UV,
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_d`.  The direct image along the
morphism of schemes contributes nothing on sections: it reindexes the open. -/
theorem app_homEquiv_schemeChartDifferentialsMap (ψ : U ⟶ V) (χ : V ⟶ W)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (a : Γ(((BigFppfOver.toScheme B S hS).obj V), O)) :
    (((representedAssociatedModulePullbackAdjunction B S hS ψ).homEquiv
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))
          (representedRelativeDifferentials B S hS (ψ ≫ χ)))
        ((representedAssociatedModule B S hS U (schemeSpace U).property).map
          (schemeChartDifferentialsMap B S hS ψ χ))).app O
        ((Scheme.Hom.universalRelativeDerivation
          ((BigFppfOver.toScheme B S hS).map χ)).d a) =
      ((representedAssociatedModuleAdjunction B S hS U).unit.app
          (Scheme.Hom.relativeDifferentials
            ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ)))).app
        ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)
        ((Scheme.Hom.universalRelativeDerivation
            ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ))).d
          ((((BigFppfOver.toScheme B S hS).map ψ).app O).hom a)) := by
  refine Eq.trans (congrArg (fun m : Scheme.Hom.relativeDifferentials
      ((BigFppfOver.toScheme B S hS).map χ) ⟶
        (((representedModuleSiteEquivalence B S hS U).inverse ⋙
            _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
          Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).obj
            (representedRelativeDifferentials B S hS (ψ ≫ χ)) =>
    m.app O ((Scheme.Hom.universalRelativeDerivation
      ((BigFppfOver.toScheme B S hS).map χ)).d a))
    (homEquiv_representedAssociatedModule_map_schemeChartDifferentialsMap B S hS ψ χ)) ?_
  refine Eq.trans (Scheme.Modules.comp_app_apply _ _ O _) ?_
  exact congrArg (((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).map
      ((representedAssociatedModuleAdjunction B S hS U).unit.app
        (Scheme.Hom.relativeDifferentials
          ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ))))).app O)
    ((Scheme.Modules.app_apply_eq_val_app _ O _).trans
      (Scheme.Hom.relativeDifferentialsMap_app_d (𝟙 _) (Category.comp_id _).symm O a))

/-- **The Zariski module that the chain of links of Stacks 04CS on sections is carried in.**  The
small-étale module `(Ω_{C/D})^a` of a morphism `α : C ⟶ D` of the big fppf site over `S`, read on
the small étale site of the scheme underlying `C` across the equivalence of Stacks 03DX (2), and
then restricted to the small Zariski site of that scheme.

Naming it fixes the one spelling the five links below are stated in; the implementation note on
the choice of spelling says why this is the one. -/
abbrev representedRelativeDifferentialsZariski {C D : BigFppfOver B S hS} (α : C ⟶ D) :
    ((BigFppfOver.toScheme B S hS).obj C).Modules :=
  ((representedModuleSiteEquivalence B S hS C).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
    (representedRelativeDifferentials B S hS α)

/-- **The Zariski side of the naturality square of Stacks 04CS, transposed, on the universal
differential, in the chain's spelling.**  This is
`AlgebraicGeometry.Space.app_homEquiv_schemeChartDifferentialsMap` with the type of its two sides
written out as the `Γ` of `AlgebraicGeometry.Space.representedRelativeDifferentialsZariski` over
the preimage open `ψ^{-1}O`.  The ascription is the one crossing of the unfolding of
`CategoryTheory.SheafOfModules.pushforward` the chain needs, and it is paid here and nowhere else.

Cost: 28,289 heartbeats. -/
theorem zariskiChain_homEquiv_schemeChartDifferentialsMap (ψ : U ⟶ V) (χ : V ⟶ W)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (a : Γ(((BigFppfOver.toScheme B S hS).obj V), O)) :
    ((((representedAssociatedModulePullbackAdjunction B S hS ψ).homEquiv
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))
              (representedRelativeDifferentials B S hS (ψ ≫ χ)))
            ((representedAssociatedModule B S hS U (schemeSpace U).property).map
              (schemeChartDifferentialsMap B S hS ψ χ))).app O
          ((Scheme.Hom.universalRelativeDerivation
            ((BigFppfOver.toScheme B S hS).map χ)).d a) :
        Γ(representedRelativeDifferentialsZariski B S hS (ψ ≫ χ),
          (BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)) =
      ((representedAssociatedModuleAdjunction B S hS U).unit.app
            (Scheme.Hom.relativeDifferentials
              ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ)))).app
          ((BigFppfOver.toScheme B S hS).map ψ ⁻¹ᵁ O)
          ((Scheme.Hom.universalRelativeDerivation
              ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ))).d
            ((((BigFppfOver.toScheme B S hS).map ψ).app O).hom a)) :=
  app_homEquiv_schemeChartDifferentialsMap B S hS ψ χ O a

/-- **The unit of the transported associated-module adjunction on the universal differential, in
the chain's spelling.**  `AlgebraicGeometry.Space.app_representedAssociatedModuleAdjunction_unit`
at an open `P` of the scheme underlying `C` and a regular function `a` on it, with the shared type
pinned, so that its left-hand side is *syntactically* the right-hand side of
`AlgebraicGeometry.Space.zariskiChain_homEquiv_schemeChartDifferentialsMap` when `α` is `ψ ≫ χ`,
`P` is `ψ^{-1}O` and `a` is the pullback `ψ♯ a`.

Stated at a general `α : C ⟶ D` and a general open, which is both cheaper and what the chain
needs: the spaces side of the square passes through this same link at `α = χ` and `P = O`, on
the scheme underlying `V`, and no second copy is needed for it.

Cost: 37,850 heartbeats. -/
theorem zariskiChain_representedAssociatedModuleAdjunction_unit {C D : BigFppfOver B S hS}
    (α : C ⟶ D) (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (a : Γ(((BigFppfOver.toScheme B S hS).obj C), P)) :
    (((representedAssociatedModuleAdjunction B S hS C).unit.app
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α))).app P
          ((Scheme.Hom.universalRelativeDerivation
            ((BigFppfOver.toScheme B S hS).map α)).d a) :
        Γ(representedRelativeDifferentialsZariski B S hS α, P)) =
      (((representedModuleSiteEquivalence B S hS C).unit.app
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
              (Scheme.Hom.relativeDifferentials
                ((BigFppfOver.toScheme B S hS).map α)))).val.app
          (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))).hom
        ((((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
                (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj C)
                C.left.property).unit.app
              (Scheme.Hom.relativeDifferentials
                ((BigFppfOver.toScheme B S hS).map α))).val.app (op P)).hom
          ((Scheme.Hom.universalRelativeDerivation
            ((BigFppfOver.toScheme B S hS).map α)).d a)) :=
  app_representedAssociatedModuleAdjunction_unit B S hS C
    (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α)) P _

/-- **The unit of the associated-module adjunction of the scheme carries `d_{C/D}(a)` to
`d^a(a)`, under the unit of the equivalence of module categories, in the chain's spelling.**
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction_unit_app_universalRelativeDerivation_d`
carried under the component at `P` of the unit of Stacks 03DX (2), with the shared type pinned.
This is the link that turns the two-factor bridge into the canonical derivation `d^a` of
Stacks 04CS.

Cost: 110,039 heartbeats -- the most expensive of the four, and most of the reason the links
cannot be combined. -/
theorem zariskiChain_associatedModuleAdjunction_unit_d {C D : BigFppfOver B S hS}
    (α : C ⟶ D) (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (a : Γ(((BigFppfOver.toScheme B S hS).obj C), P)) :
    ((((representedModuleSiteEquivalence B S hS C).unit.app
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
                (Scheme.Hom.relativeDifferentials
                  ((BigFppfOver.toScheme B S hS).map α)))).val.app
            (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))).hom
          ((((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
                  (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj C)
                  C.left.property).unit.app
                (Scheme.Hom.relativeDifferentials
                  ((BigFppfOver.toScheme B S hS).map α))).val.app (op P)).hom
            ((Scheme.Hom.universalRelativeDerivation
              ((BigFppfOver.toScheme B S hS).map α)).d a)) :
        Γ(representedRelativeDifferentialsZariski B S hS α, P)) =
      (((representedModuleSiteEquivalence B S hS C).unit.app
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
              (Scheme.Hom.relativeDifferentials
                ((BigFppfOver.toScheme B S hS).map α)))).val.app
          (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))).hom
        ((representedAssociatedDerivation B S hS α).d
            (X := op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property).hom.app (op P)).hom a)) :=
  congrArg (fun z => (((representedModuleSiteEquivalence B S hS C).unit.app
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
        (Scheme.Hom.relativeDifferentials
          ((BigFppfOver.toScheme B S hS).map α)))).val.app
      (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))).hom z)
    (AlgebraicGeometry.SmallEtale.associatedModuleAdjunction_unit_app_universalRelativeDerivation_d
      (associatedBigEtaleSite B) C.left.property
      ((BigFppfOver.toScheme B S hS).map α) P a)

/-- **The unit of the equivalence of module categories of Stacks 03DX (2) is restriction along
the counit of the equivalence of sites, in the chain's spelling.**
`AlgebraicGeometry.Space.representedModuleSiteEquivalence_unit_app_val_app` at the object of the
small étale site of the scheme that the open `P` is, with the shared type pinned.  Its right-hand
side is where the chain leaves that spelling: it is syntactically the left-hand side of
`AlgebraicGeometry.Space.zariskiChain_representedUniversalDerivation`, which is stated in its own.

Cost: 68,798 heartbeats. -/
theorem zariskiChain_representedModuleSiteEquivalence_unit {C D : BigFppfOver B S hS}
    (α : C ⟶ D) (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (a : Γ(((BigFppfOver.toScheme B S hS).obj C), P)) :
    ((((representedModuleSiteEquivalence B S hS C).unit.app
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
                (Scheme.Hom.relativeDifferentials
                  ((BigFppfOver.toScheme B S hS).map α)))).val.app
            (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))).hom
          ((representedAssociatedDerivation B S hS α).d
              (X := op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))
            (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj C) C.left.property).hom.app (op P)).hom a)) :
        Γ(representedRelativeDifferentialsZariski B S hS α, P)) =
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
          (Scheme.Hom.relativeDifferentials
            ((BigFppfOver.toScheme B S hS).map α))).val.map
        ((representedSmallEtaleEquivalence B S hS C).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property P)).op
        ((representedAssociatedDerivation B S hS α).d
            (X := op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property).hom.app (op P)).hom a)) :=
  representedModuleSiteEquivalence_unit_app_val_app B S hS C
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
      (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α)))
    (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj C) C.left.property P) _

/-- **The restriction of `d^a(a)` along the counit of the equivalence of sites is `d^a` of the
restricted function, read as the canonical `α`-derivation over
`AlgebraicGeometry.Space.representedOpensObj`.**  The `d_map` field of
`PresheafOfModules.Derivation` absorbs the restriction into the derivation, and
`AlgebraicGeometry.Space.representedUniversalDerivation_d`, a `rfl` lemma, names the result.

This last link is deliberately **not** pinned to the chain's spelling: ascribing its left-hand
side there exhausts the heartbeat budget at `whnf`, while in its own spelling the link is cheap.
The one crossing between the two spellings is paid instead by
`AlgebraicGeometry.Space.zariskiChain_representedModuleSiteEquivalence_unit`, whose right-hand
side is syntactically this one's left-hand side.

Its right-hand side is the one place the Zariski side and the spaces side of the square can meet:
the canonical derivation `d^a` evaluated at `AlgebraicGeometry.Space.representedOpensObj`.

Cost: 30,275 heartbeats. -/
theorem zariskiChain_representedUniversalDerivation {C D : BigFppfOver B S hS}
    (α : C ⟶ D) (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (a : Γ(((BigFppfOver.toScheme B S hS).obj C), P)) :
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
          (Scheme.Hom.relativeDifferentials
            ((BigFppfOver.toScheme B S hS).map α))).val.map
        ((representedSmallEtaleEquivalence B S hS C).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property P)).op
        ((representedAssociatedDerivation B S hS α).d
            (X := op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property).hom.app (op P)).hom a)) =
      (representedUniversalDerivation B S hS α).d
          (X := op (representedOpensObj B S hS C P))
        ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj.map
          ((representedSmallEtaleEquivalence B S hS C).counit.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property P)).op
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property).hom.app (op P)).hom a)) :=
  (((representedAssociatedDerivation B S hS α).d_map
        ((representedSmallEtaleEquivalence B S hS C).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property P)).op
        (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).hom.app (op P)).hom
          a)).symm.trans
    (representedUniversalDerivation_d B S hS α
        (op (representedOpensObj B S hS C P)) _).symm)

/-- **The last two links of the Zariski side, joined with no ascription to the chain's
spelling.**  The unit of the equivalence of module categories of Stacks 03DX (2), over the object
of the small étale site of the scheme underlying `C` that the open `P` is, applied to the
canonical derivation `d^a` of `α` on the regular function `a`, is `d^a` of `α` read over
`AlgebraicGeometry.Space.representedOpensObj` on the restriction of `a` along the counit of the
equivalence of sites.

This is `AlgebraicGeometry.Space.representedModuleSiteEquivalence_unit_app_val_app` followed by
`AlgebraicGeometry.Space.zariskiChain_representedUniversalDerivation`, and both of its sides are
in the `.val.app`/`.val.map` spelling of the small étale site: *nothing here is pinned to*
`AlgebraicGeometry.Space.representedRelativeDifferentialsZariski`.  That is the point of it.
`AlgebraicGeometry.Space.zariskiChain_representedModuleSiteEquivalence_unit` is the same first
step with the shared type pinned to the chain's spelling, which is where the chain's one crossing
between the two spellings is paid; a consumer which uses this instead pays that crossing once, at
the single `Eq.trans` which joins the output of
`AlgebraicGeometry.Space.zariskiChain_associatedModuleAdjunction_unit_d` to this result's
left-hand side, rather than twice.

This is the wall the chain meets: this declaration compiles at the project's
standard budget, and so is a consumer which applies links one to three of the chain by successive
`refine Eq.trans (α := ...) ... ?_` against the sections identity of the naturality square —
with or without the `γ⁻¹` half of that square already discharged.  Adding the step to *this*
result at the concrete arguments `α = ψ ≫ χ`, `P = ψ^{-1}O` is a `(deterministic) timeout at
whnf`, as is the step to
`AlgebraicGeometry.Space.zariskiChain_representedModuleSiteEquivalence_unit` there.  So the
crossing between the two spellings is affordable at the general `(C, α, P)` of a declaration's
own statement and is *not* affordable at those concrete arguments inside a consumer. -/
theorem zariskiChain_unit_representedUniversalDerivation {C D : BigFppfOver B S hS}
    (α : C ⟶ D) (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (a : Γ(((BigFppfOver.toScheme B S hS).obj C), P)) :
    (((representedModuleSiteEquivalence B S hS C).unit.app
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj
              (Scheme.Hom.relativeDifferentials
                ((BigFppfOver.toScheme B S hS).map α)))).val.app
          (op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))).hom
        ((representedAssociatedDerivation B S hS α).d
            (X := op (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property P))
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property).hom.app (op P)).hom a)) =
      (representedUniversalDerivation B S hS α).d
          (X := op (representedOpensObj B S hS C P))
        ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj.map
          ((representedSmallEtaleEquivalence B S hS C).counit.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property P)).op
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj C) C.left.property).hom.app (op P)).hom a)) :=
  (zariskiChain_representedModuleSiteEquivalence_unit B S hS α P a).trans
    (zariskiChain_representedUniversalDerivation B S hS α P a)

end AlgebraicGeometry.Space

end
