module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleSiteEquivalenceInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnitTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp

/-!
# The spaces side of the naturality square of Stacks 04CS, on sections

`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMapSections.lean` reads
the *Zariski* side of the naturality square of Stacks 04CS on sections, over an open `O` of the
scheme underlying `V` and on the universal differential `d_{V/W}(a)`, and it ends at the canonical
derivation `d^a` of Stacks 04CS of `ψ ≫ χ` evaluated over
`AlgebraicGeometry.Space.representedOpensObj U (ψ^{-1}O)`.  This file reads the *spaces* side,
which must end at the same place for the square to close.

## Why this is a separate module

The spaces side needs both readings of the comparison of the two composite right adjoints round
the square of Stacks 03LC (1), and those live in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleSiteEquivalenceInverse.lean`, which
imports
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMapMate.lean`,
which imports the Zariski-side module.  So the spaces side cannot be written beside the Zariski
side: that is an import cycle, and the implementation notes of the Zariski-side module record
it.  It has to be written downstream of the leaf instead, which is here.

## Main results

* `AlgebraicGeometry.Space.app_homEquiv_representedAssociatedModuleAdjunction`: **transposing a
  morphism `h` out of the transported associated module of `M` across the adjunction of
  Stacks 03DU (4) and reading the result over an open `P`, is the right adjoint of `h` over `P`
  applied to the unit over `P`.**  This is `CategoryTheory.Adjunction.homEquiv_unit`, the first
  link of the spaces side, on sections.
* `AlgebraicGeometry.Space.representedRestrictModule_map_app_apply`: **the right adjoint of `h`
  over `P` is `h` itself over `AlgebraicGeometry.Space.representedOpensObj C P`.**  This is the
  second link of the spaces side: the `Γ`-and-`app` form of
  `AlgebraicGeometry.Space.representedRestrictModule_map_val_app_hom_apply`, which is what lets
  it meet the first link.
* `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_proj_bridge`
  and
  `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_bridge_proj_chartFirst`:
  **the one spelling bridge and the three-way split of `γ⁻¹` at a module, each carried to an
  arbitrary projection**, which is what turns them into statements about sections without a
  sections restatement of either.
* `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_proj_chartFirst`: **their
  composite**, taking **one** projection rather than two.  This is the entry point for the `γ⁻¹`
  half, and the reason it exists is a cost: see the implementation note.

The first two cannot be one declaration: separately they cost 3,162 and
89,241 heartbeats, while the single declaration whose left-hand side is the transpose and whose
right-hand side is `h` at `AlgebraicGeometry.Space.representedOpensObj` exhausts the budget at
`isDefEq`.  It is the same phenomenon the Zariski-side module records for its own links -- each
`Eq.trans` re-checks the shared type of its two arguments, and a check which crosses an unfolding
of `CategoryTheory.SheafOfModules.pushforward` is tens of thousands of heartbeats -- so each link
gets its own declaration and its own budget, and the chain which consumes them is syntactic.

## Implementation notes

**The shape of the spaces side, and how far it is read here.**  The transposed spaces side is
`k ≫ γ⁻¹`, where `k` is the transpose across
`AlgebraicGeometry.Space.representedAssociatedModuleAdjunction` of `V` of the comparison map of
Stacks 04CS of `χ` followed by the transpose across the inverse image of Stacks 03LU, and `γ` is
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso`, the comparison of the two
composite right adjoints.  `AlgebraicGeometry.Scheme.Modules.comp_app_apply` splits the two over
an open `O`, and `k` over `O` is read all the way by the two links below followed by

* the four general links of the Zariski-side module at `α = χ` and the open `O`, which identify
  the unit on `d_{V/W}(a)` with the canonical derivation `d^a` of `χ` over
  `AlgebraicGeometry.Space.representedOpensObj V O` (they assemble for 81,222
  heartbeats), and then
* the evaluation of that arrow on the canonical derivations, which in this namespace is
  `representedDifferentialsComparison_comp_homEquiv_representedUniversalDerivation`.  It applies
  **as it stands**, with no restatement: it is already general in the object of the site and in
  the regular function, and the previous link leaves its left-hand side in exactly its spelling.

**What `γ⁻¹` over `O` still owes, and what it costs.**  `γ⁻¹` at a module splits three ways by
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_chartFirst`, reached
through the one spelling bridge, in this namespace
`representedRestrictModuleBaseChangeIso_inv_app_smallEtaleModuleEquivalence`;
the chart factor is read as `AlgebraicGeometry.Space.chartSetProj` by
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_chartSetProj`, carried past the direct
image of the derivation by `AlgebraicGeometry.Space.chartSetProj_naturality`, and turned into
pullback along the cartesian projection by Stacks 03G8 (2),
`AlgebraicGeometry.Space.structureSharp_comp_chartProjectionSharpDirectImage`; the tail is
`AlgebraicGeometry.Space.induced_representedRestrictModuleBaseChangeIso_inv_tail`, which is a
`Stacks.SectionsComponents.Induced` and so names no arrow, and the arrow is pinned by
`AlgebraicGeometry.Space.subsingleton_hom_smallBaseChange_representedOpensObj` through
`Stacks.SectionsComponents.Induced.eq`.

The two morphism-level links, 4 and 8, need **no** restatement in a sections spelling:
`Stacks.CategoryTheory.proj_congr` carries an equality of morphisms to an arbitrary projection of
it, so `proj_congr (bridge.trans chartFirst) (fun m => m.app O z)` has the sections form of link 4
with its right-hand side *inferred* rather than transcribed.  That term costs **250,675**
heartbeats, over the budget of one declaration, and the three results above are what replaces it.
The figures in the paragraphs that follow are `#count_heartbeats` counts, with the budget raised
only to let the failing variants finish; where a figure decides something, it holds at the
standard budget with no option override as well, which matters because `#count_heartbeats` runs
at `maxHeartbeats 0` and over-reports wherever a budget would cut a speculative `whnf` short.

**The one crossing, and why it must sit in a proof and not in a statement.**  `γ` is *declared*
with `AlgebraicGeometry.Space.representedModuleSiteEquivalence` and
`AlgebraicGeometry.Space.schemeSpaceMap`, and every factor beneath it with
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` and
`AlgebraicGeometry.Space.representedSpaceMap`; the bridge is where the two meet, and the chain
pays for that meeting exactly once.  The crossing is cheap as a defeq of *functors* — the two
inverses are `rfl` for 36,571 heartbeats and the two direct images for 150 — but at the sections of
a module it is some 150,000, and that is the whole cost of the `γ⁻¹` half.  Where it is paid is
therefore the only design decision here, and the measurements are one-sided:

* *In a statement it does not fit.*  The sections-level bridge, written out — `(γ.inv.app M).app O
  z` on the left and the bridged spelling on the right — reports 238,023 heartbeats with the
  section in `γ`'s own spelling and 385,126 with it in the factors', and at the standard budget it
  genuinely fails, `(deterministic) timeout at isDefEq` on the section in its right-hand side.  So
  no sections restatement of either link can be named, for the same reason the Zariski chain
  cannot: the cost is in the type.
* *In a proof it fits, if the projection is left general.*  Carried to an arbitrary projection
  whose domain is written in the factors' spelling, the bridge costs 180,520 and the split 60,062,
  and the sections instantiation `fun m => m.app O z` is then **4,157** heartbeats when `z` is
  presented in the factors' spelling.  The asymmetry is sharp and it chooses the spelling: the
  split carried to a projection in `γ`'s spelling instead costs **1,011,700**, because its
  right-hand side is a three-factor composite and every factor of it then crosses.

**Why the composite takes one projection and not two.**  A consumer reaches the `γ⁻¹` half holding
a section in `γ`'s spelling — that is what `AlgebraicGeometry.Scheme.Modules.comp_app_apply` hands
it when it splits the spaces side off the comparison — so the crossing is paid at the projection
it supplies.  Supplying it twice, once to each half, costs **303,997** heartbeats and does not fit
a declaration; supplying it once, to
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_proj_chartFirst`, costs
about half that.  That is why the composite is named even though it is one `Eq.trans` of its two
halves: it is not a convenience, it is the difference between fitting a budget and not.  Its own
statement costs 130,081 heartbeats — *less* than the bridge alone, because its right-hand side is
in the factors' spelling throughout while the bridge's names the bridged `CategoryTheory.Iso.inv`.

**Which projection the consumer must supply.**  The crossing is in the *section*, and in
nothing else — so what decides the cost is which module's sections the consumer's section lives
in, and the consumer has a choice.  At the entry point above:

* `fun m => m.app O z`, the section being one of `γ⁻¹`'s own source — **153,131** heartbeats.  The
  same at the unapplied `.app O` with the section supplied afterwards by `congrFun` is 153,243, so
  deferring the section does not move the cost; the unapplied `.app O` with no section at all is
  2,343, which locates all of it in the section.
* `fun m => (k ≫ m).app O y`, post-composing the `k` half first and reading a section of the
  source of the *whole* spaces side — **28,805** heartbeats.  Post-composition alone, with no
  section, is 28,499, so this route pays the crossing once at the level of morphisms and the
  sections reading on top of it is free.

The second is a fifth of the first, and the reason is worth stating because it is the opposite of
the obvious move: `AlgebraicGeometry.Scheme.Modules.comp_app_apply` should **not** be used to split
the spaces side off the comparison first.  Splitting puts the section into `γ⁻¹`'s source, which is
the one module here whose two spellings differ — the `k` half delivers `(F ⋙ G).obj (H.obj Ω)`
where `γ⁻¹` wants `((H ⋙ F) ⋙ G).obj Ω`, and the equivalence of module categories is spelled
differently on the two sides as well.  Keeping the composite whole and projecting through it puts
the section in `Γ(Ω_{V/W}, O)` instead, where there is nothing to cross.

**What this buys, and what it does not.**  The `γ^{-1}` half is affordable, and that is now
checked against the square itself and not only by `#count_heartbeats`: with the sections identity
of the naturality square of Stacks 04CS as the goal, the step
`refine Eq.trans (α := …) ?_ (Eq.symm (…))` — with `α` written out as the `Γ` of
`AlgebraicGeometry.Space.representedRelativeDifferentialsZariski` of `ψ ≫ χ` over `ψ^{-1}O`, and
the second argument the entry point above at the projection
`fun m => (k ≫ m).app O (d_{V/W} a)` — succeeds at the project's standard budget, leaving the
goal
`(the Zariski side) = (k ≫ chart ≫ tail).app O (d_{V/W} a)` with every factor of the right-hand
side in the factors' spelling.  So the entry point above, and the choice of projection, are right.

What is *not* affordable is the Zariski side.  The sum 81,222 + 28,805 does not show room: it
omits the `U`-side five-link chain, which has to sit in the same declaration, and
`#count_heartbeats` figures, taken at `maxHeartbeats 0`, are not budget checks.  At the standard
budget, the Zariski chain goes through its first three
links — before or after the `γ^{-1}` step above — and the fourth is a `(deterministic) timeout at
whnf`; the companion module's notes record the full set of positions tried and the one crossing
that is the wall.  So the assembly is **not** within budget as it stands: what it needs is a way
to pay the crossing between the chain's spelling and the `.val.obj` spelling of
`AlgebraicGeometry.Space.representedUniversalDerivation` at the concrete arguments `α = ψ ≫ χ`,
`P = ψ^{-1}O`, and neither a merged link nor a hypothesis on variables supplies one.

The identity of regular functions that closes the square is likewise not here: its two sides'
spellings of the pullback are determined *by* the assembly, and guessing them is what four
predecessors declined to do.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u t

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {U V W : BigFppfOver B S hS}

/-- **The first link of the spaces side: the transpose across the transported associated-module
adjunction of Stacks 03DU (4), read on sections over an open.**  A morphism `h` out of the
transported associated module of a Zariski module `M` on the scheme underlying `C`, transposed
across `AlgebraicGeometry.Space.representedAssociatedModuleAdjunction` and evaluated over an open
`P` on a section `y`, is the right adjoint of `h` over `P` applied to the unit of the adjunction
at `P` on `y`.

This is `CategoryTheory.Adjunction.homEquiv_unit` carried under the sections map by `congrArg`
and split by `AlgebraicGeometry.Scheme.Modules.comp_app_apply`.  The
motive of the `congrArg` is given explicitly: on variables the ascription is free, and the
inferred form is what the Zariski-side module records as dying at `whnf`.

Elaboration cost: 3,162 heartbeats. -/
theorem app_homEquiv_representedAssociatedModuleAdjunction (C : BigFppfOver B S hS)
    (M : ((BigFppfOver.toScheme B S hS).obj C).Modules)
    {N : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2}
    (h : (representedAssociatedModule B S hS C (schemeSpace C).property).obj M ⟶ N)
    (P : ((BigFppfOver.toScheme B S hS).obj C).Opens) (y : Γ(M, P)) :
    ((representedAssociatedModuleAdjunction B S hS C).homEquiv M N h).app P y =
      (((representedModuleSiteEquivalence B S hS C).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).map h).app P
        (((representedAssociatedModuleAdjunction B S hS C).unit.app M).app P y) :=
  (congrArg (fun m : M ⟶
      ((representedModuleSiteEquivalence B S hS C).inverse ⋙
        _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj N =>
    m.app P y) (CategoryTheory.Adjunction.homEquiv_unit
      (representedAssociatedModuleAdjunction B S hS C) M N h)).trans
    (Scheme.Modules.comp_app_apply _ _ P y)

/-- **The second link of the spaces side: the right adjoint of `h` over an open `P` is `h` itself
over `AlgebraicGeometry.Space.representedOpensObj C P`.**  The right adjoint is the transport of
Stacks 03DX (2) followed by restriction to the small Zariski site of the scheme underlying `C`,
and `AlgebraicGeometry.Space.representedRestrictModule_map_val_app_hom_apply` reads that composite
on sections.

This is that result in the `Γ`-and-`AlgebraicGeometry.Scheme.Modules.Hom.app` spelling, which is
the spelling the previous link leaves its right-hand side in; the bridge between the two is
`AlgebraicGeometry.Scheme.Modules.app_apply_eq_val_app`, and paying for it here is what makes the
`Eq.trans` against the previous link syntactic.

Elaboration cost: 89,241 heartbeats. -/
theorem representedRestrictModule_map_app_apply (C : BigFppfOver B S hS)
    {N N' : Modules.{u, u} B S hS (schemeSpace C).1 (schemeSpace C).2} (h : N ⟶ N')
    (P : ((BigFppfOver.toScheme B S hS).obj C).Opens)
    (z : Γ(((representedModuleSiteEquivalence B S hS C).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj C) C.left.property).obj N, P)) :
    (((representedModuleSiteEquivalence B S hS C).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj C) C.left.property).map h).app P z =
      (h.val.app (op (representedOpensObj B S hS C P))).hom z :=
  (Scheme.Modules.app_apply_eq_val_app _ P z).trans
    (representedRestrictModule_map_val_app_hom_apply B S hS C h (op P) z)

section GammaInverse

variable (ψ : U ⟶ V) (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))

/-- **The one bridge between the two spellings of the equivalence of module categories, carried
to an arbitrary projection.**  `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso`,
in its `inv` direction at a module, is the same morphism read with its two composite functors
spelled the way everything beneath it is spelled; this carries that equation to any projection of
it, in particular to its reading on sections over an open.

The projection's domain is written in the spelling of
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, the spelling of the factors —
*not* in the spelling the comparison is declared in.  That choice is what makes the pair of
readings usable; see the implementation note of this module.

Elaboration cost: 180,520 heartbeats. -/
theorem representedRestrictModuleBaseChangeIso_inv_app_proj_bridge
    {T : Sort t}
    (pr : ((modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
          ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
            _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property)).obj M ⟶
        (((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
              _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
            Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).obj M) → T) :
    pr ((representedRestrictModuleBaseChangeIso B S hS ψ).inv.app M) =
      pr ((Iso.inv
          (X := ((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
                _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
              Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ))
          (Y := modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
            ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
              _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
          (representedRestrictModuleBaseChangeIso B S hS ψ)).app M) :=
  Stacks.CategoryTheory.proj_congr
    (representedRestrictModuleBaseChangeIso_inv_app_smallEtaleModuleEquivalence B S hS ψ M) pr

/-- **The three-way split of `γ⁻¹` at a module, carried to an arbitrary projection.**  This is
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_chartFirst` — the chart
comparison of Stacks 03LU, taken inside `V`'s equivalence of module categories and then inside the
restriction to the small Zariski site, followed by the tail — read through any projection, in
particular on sections over an open.

Its left-hand side is the bridged spelling, so a consumer which starts from
`(representedRestrictModuleBaseChangeIso B S hS ψ).inv.app M` reaches it through the previous
result; `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso_inv_app_proj_chartFirst`
below is that composite.  Everything here is in one spelling, which is why it is the cheap half.

Elaboration cost: 60,062 heartbeats. -/
theorem representedRestrictModuleBaseChangeIso_inv_app_bridge_proj_chartFirst
    {T : Sort t}
    (pr : ((modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
          ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
            _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property)).obj M ⟶
        (((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
              _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
            Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).obj M) → T) :
    pr ((Iso.inv
          (X := ((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
                _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
              Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ))
          (Y := modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
            ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
              _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
          (representedRestrictModuleBaseChangeIso B S hS ψ)).app M) =
      pr ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
            ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS ψ)
              (relativelyRepresentable_yoneda_map B S hS ψ)).hom.app M)) ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
              ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
                  ((smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS ψ)
                          (relativelyRepresentable_yoneda_map B S hS ψ)).map
                        ((representedSmallEtaleModuleEquivalence B S hS U).counitInv.app M) ≫
                    (representedModulePushforwardSquareRestrictIso B S hS ψ
                          (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
                        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M)) ≫
                (representedModulePushforwardSquareInverseIsoUnit B S hS ψ).inv.app M) ≫
          (representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).inv.app M) :=
  Stacks.CategoryTheory.proj_congr
    (representedRestrictModuleBaseChangeIso_inv_app_chartFirst B S hS ψ M) pr

/-- **`γ⁻¹` at a module, under an arbitrary projection, is the chart comparison first.**  The
bridge and the three-way split of the two previous results, composed: this is the entry point a
consumer of the `γ⁻¹` half of the square of Stacks 04CS uses, and it takes **one** projection, not
two.  That is the point of it — see the implementation note of this module: a
consumer which applies the two halves separately pays the crossing between the two spellings of
the equivalence of module categories once per projection, and twice does not fit a declaration's
budget.

Elaboration cost: 130,081 heartbeats. -/
theorem representedRestrictModuleBaseChangeIso_inv_app_proj_chartFirst {T : Sort t}
    (pr : ((modulePushforward B S hS (representedSpaceMap B S hS ψ) ⋙
          ((representedSmallEtaleModuleEquivalence B S hS V).inverse ⋙
            _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property)).obj M ⟶
        (((representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
              _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
            Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).obj M) → T) :
    pr ((representedRestrictModuleBaseChangeIso B S hS ψ).inv.app M) =
      pr ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
            ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS ψ)
              (relativelyRepresentable_yoneda_map B S hS ψ)).hom.app M)) ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
              ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map
                  ((smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS ψ)
                          (relativelyRepresentable_yoneda_map B S hS ψ)).map
                        ((representedSmallEtaleModuleEquivalence B S hS U).counitInv.app M) ≫
                    (representedModulePushforwardSquareRestrictIso B S hS ψ
                          (relativelyRepresentable_yoneda_map B S hS ψ)).inv.app
                        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M)) ≫
                (representedModulePushforwardSquareInverseIsoUnit B S hS ψ).inv.app M) ≫
          (representedRestrictModuleBaseChangeIsoBaseChange B S hS ψ).inv.app M) :=
  (representedRestrictModuleBaseChangeIso_inv_app_proj_bridge
      B S hS ψ M pr).trans
    (representedRestrictModuleBaseChangeIso_inv_app_bridge_proj_chartFirst
      B S hS ψ M pr)

end GammaInverse

end AlgebraicGeometry.Space

end
