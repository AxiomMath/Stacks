module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingAtTopUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenNonVacuity

/-!
# Tag 0D6A: the sheaf condition is needed at two subsystems, not at every one

Let `(X, 𝒪_X)` be a ringed space and `S` a system of locally given derived objects on it, as in
Situation [Stacks, Tag 0D67].  After
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingAtTopUnconditional` the existence
half of [Stacks, Tag 0D6A] rests on one hypothesis,

```
∀ (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens), HasGluingForHomsOver (S.subcollection 𝒟 h𝒟)
```

the sheaf condition of [Stacks, Tag 0D66] part (2) for *every* subsystem.  That quantifier is
larger than the proof needs.  `Stacks.DerivedGlueing.nonempty_solutionOver_sup_of_glueing` — the
minimal interface of the two-open case — consumes the uniqueness clause of [Stacks, Tag 0D68] at
exactly two systems: the given one, and the subsystem carried by
`Stacks.DerivedGlueing.opensBelowPair S U V`, the members contained in `U` or in `V`.  This file
rewrites the chain so that only those two appear, and registers the resulting existence statement
against Tag 0D6A.

Both hypotheses sit in hypothesis position, so asking for less of them makes every statement below
**stronger**; `Stacks.DerivedGlueing.hasGluingForHomsOver_pairs_of_subcollections` records that
implication formally, so that the strengthening is machine-checked and not merely asserted.

## What the tag still owes, after this file

The sheaf condition at the pair subsystems,

```
∀ (U V : Opens X.carrier), U ∈ S.opens → V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
    U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
  HasGluingForHomsOver (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V))
```

together with `Stacks.DerivedGlueing.HasGluingForHomsOver S` itself.

## The narrowing is what makes the hypothesis witnessable

The `∀ 𝒟 ⊆ S.opens` form has **no inhabitant in this development, for any system whatever**.  The
only route to `Stacks.DerivedGlueing.HasGluingForHomsOver` is
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem`, which asks that every open which is
the union of the members contained in it be itself a member, and the empty subcollection defeats
that outright: `⊥` is the union of the members of `∅` contained in it, and `⊥ ∉ ∅`.  So the one
hypothesis of `Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_homs` is, as it stands,
unwitnessed, and the statement is not known to be non-vacuous.

The subcollections the proof actually reads are not arbitrary, and the hole closes.
`Stacks.DerivedGlueing.hasGluingForHomsOver_opensBelowPair_of_covered_mem` proves the narrowed
hypothesis for a saturated collection whose members below `U ∪ V` all lie below `U` or below `V`;
`Stacks.DerivedGlueing.hasGluingForHomsOver_opensBelowPair_locallyGivenOfTop` is that at the
system attached to a single global object on a space whose opens are totally ordered; and
`Stacks.DerivedGlueing.nonempty_solution_botTop_single` instantiates *every* binder of the
narrowed existence statement at once, at the collection `{⊥, ⊤}` and the system prescribed by an
arbitrary sheaf of modules placed in degree zero, with no hypothesis on the space at all.

The inhabitant is degenerate in the familiar way — `⊤` is a member, so the `n = 1` partner
`Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_top_mem` already proves the conclusion,
and the covering hypothesis forces `⊤` to be a finite union of members for any witness whatever.
But it is an inhabitant, which the `∀ 𝒟` form does not have.

## Relation to the glueing of morphisms at `⊤`

`Stacks.DerivedGlueing.HasGluingForHomsAt S ⊤` — the obligation of the *uniqueness* half, and the
subject of the reduction to a single equation that this chapter carries elsewhere — is **not**
this obligation.  By `Stacks.DerivedGlueing.hasGluingForHomsOver_iff_forall_hasGluingForHomsAt`
it is one instance of `HasGluingForHomsOver S`: the open `⊤`, and the whole collection.  What the
existence half needs is every open which is a union of members, for the pair subcollections as
well as for the collection itself.  So a discharge of `HasGluingForHomsAt S ⊤` closes none of the
hypotheses below, and neither of the two obligations implies the other: `HasGluingForHomsAt S ⊤`
says nothing about a proper open, and the pair hypothesis says nothing about a collection that is
not a pair subcollection — `Stacks.DerivedGlueing.hasGluingForHomsOver_pairs_of_subcollections`
goes one way only.

## Main results

* `Stacks.DerivedGlueing.gluesAlongTwoOpens_of_hasUniqueSolutionOverIso_pairs`: the two-open case
  of [Stacks, Tag 0D6A] from the uniqueness clause of [Stacks, Tag 0D68] at the system and at the
  pair subsystems only.
* `Stacks.DerivedGlueing.gluesAlongTwoOpens_of_hasGluingForHomsOver_pairs`: the same from the
  sheaf condition of [Stacks, Tag 0D66] part (2) at those two places.
* `Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_homs_pairs`: **[Stacks, Tag 0D6A],
  existence, from the sheaf condition at the system and at the pair subsystems alone.**
* `Stacks.DerivedGlueing.hasGluingForHomsOver_pairs_of_subcollections`: the narrowed hypothesis
  follows from the old one, which is what makes the statements above strengthenings.
* `Stacks.DerivedGlueing.hasGluingForHomsOver_opensBelowPair_of_covered_mem` and
  `Stacks.DerivedGlueing.hasGluingForHomsOver_opensBelowPair_locallyGivenOfTop`: an inhabitant of
  the narrowed hypothesis, which the `∀ 𝒟` form does not have.
* `Stacks.DerivedGlueing.nonempty_solution_botTop_single`: every binder of the existence
  statement instantiated at once, with nothing assumed.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### The two-open case from the two subsystems the argument uses -/

/-- **The two-open case of [Stacks, Tag 0D6A], from the uniqueness clause of [Stacks, Tag 0D68]
at the system and at the pair subsystems only.**

`Stacks.DerivedGlueing.gluesAlongTwoOpens_of_gluesObjectsAlongTwoOpens` grants that clause for
every subsystem; `Stacks.DerivedGlueing.nonempty_solutionOver_sup_of_glueing` shows that the
argument reads it at two systems only — the given one, over `U ∩ V`, and the subsystem carried by
the members contained in `U` or in `V`, over the members of the collection below `U ∪ V`.  The
hypothesis here asks for exactly those, and carries into the pair hypothesis all three side
conditions that `Stacks.DerivedGlueing.GluesAlongTwoOpens` makes available at the pair, so that it
asks for as little as possible. -/
theorem gluesAlongTwoOpens_of_hasUniqueSolutionOverIso_pairs (S : LocallyGiven X)
    (huniqS : HasUniqueSolutionOverIso S)
    (huniqP : ∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      HasUniqueSolutionOverIso
        (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V)))
    (hglue : GluesObjectsAlongTwoOpens S) :
    GluesAlongTwoOpens S :=
  fun U hU V hV hUV hinter hExt A B =>
    nonempty_solutionOver_sup_of_glueing S U V hU hV hUV hinter hExt huniqS
      (huniqP U V hU hV hUV) (hglue U V) A B

/-- **The two-open case of [Stacks, Tag 0D6A], from the sheaf condition of [Stacks, Tag 0D66]
part (2) at the system and at the pair subsystems only.**  This is
`Stacks.DerivedGlueing.gluesAlongTwoOpens_of_hasUniqueSolutionOverIso_pairs` with both inputs
produced by `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver`. -/
theorem gluesAlongTwoOpens_of_hasGluingForHomsOver_pairs (S : LocallyGiven X)
    (hhomS : HasGluingForHomsOver S)
    (hhomP : ∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      HasGluingForHomsOver
        (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V)))
    (hglue : GluesObjectsAlongTwoOpens S) :
    GluesAlongTwoOpens S :=
  gluesAlongTwoOpens_of_hasUniqueSolutionOverIso_pairs S
    (hasUniqueSolutionOverIso_of_hasGluingForHomsOver S hhomS)
    (fun U V hU hV hUV =>
      hasUniqueSolutionOverIso_of_hasGluingForHomsOver _ (hhomP U V hU hV hUV))
    hglue

/-! ### The narrowed hypothesis is weaker -/

/-- **The narrowed hypothesis follows from the sheaf condition for every subsystem.**  The pair
subsystem is a subsystem, and the system is its own subsystem by
`Stacks.DerivedGlueing.LocallyGiven.subcollection_self`; so every statement below that carries the
narrowed hypothesis is a strengthening of its partner carrying the old one. -/
theorem hasGluingForHomsOver_pairs_of_subcollections (S : LocallyGiven X)
    (hhom : ∀ (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens),
      HasGluingForHomsOver (S.subcollection 𝒟 h𝒟)) :
    HasGluingForHomsOver S ∧
      ∀ (U V : Opens X.carrier), U ∈ S.opens →
          V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
          U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
        HasGluingForHomsOver
          (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V)) :=
  ⟨LocallyGiven.subcollection_self S (fun _ hW => hW) ▸ hhom S.opens fun _ hW => hW,
    fun U V _ _ _ => hhom (opensBelowPair S U V) (opensBelowPair_subset S U V)⟩

/-! ### The narrowed hypothesis is inhabited -/

/-- **The sheaf condition at a pair subsystem, for a saturated collection on a pair that splits
the opens below its union.**

Let the collection be saturated — every open which is the union of the members contained in it is
a member, the hypothesis of `Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem` — and let
`U`, `V` be opens such that every open contained in `U ∪ V` is contained in `U` or in `V`.  Then
`Stacks.DerivedGlueing.opensBelowPair S U V` is itself saturated, and the member case applies.

Both inclusions of the saturation are needed.  An open `O` which is the union of the members of
`opensBelowPair S U V` contained in it is also the union of the members of the whole collection
contained in it — the larger family has the same supremum, being squeezed between the smaller one
and `O` — so `O` is a member; and `O` lies below `U ∪ V`, so `hsplit` puts it below one of the
two.  Without `hsplit` the conclusion is false: for incomparable members `U`, `V` the open
`U ∪ V` is the union of the members of the pair subcollection contained in it and does not belong
to it. -/
theorem hasGluingForHomsOver_opensBelowPair_of_covered_mem (S : LocallyGiven X)
    (hmem : ∀ O : Opens X.carrier, O = sSup {W | W ∈ S.opens ∧ W ≤ O} → O ∈ S.opens)
    (U V : Opens X.carrier)
    (hsplit : ∀ O ∈ S.opens, O ≤ U ⊔ V → O ≤ U ∨ O ≤ V) :
    HasGluingForHomsOver
      (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V)) := by
  refine hasGluingForHomsOver_of_covered_mem _ fun O hO => ?_
  have hsub : sSup {W | W ∈ opensBelowPair S U V ∧ W ≤ O} ≤
      sSup {W | W ∈ S.opens ∧ W ≤ O} :=
    sSup_le_sSup fun W hW => ⟨opensBelowPair_subset S U V hW.1, hW.2⟩
  have hbig : O = sSup {W | W ∈ S.opens ∧ W ≤ O} :=
    le_antisymm (hO.le.trans hsub) (sSup_le fun _ hW => hW.2)
  refine ⟨hmem O hbig, hsplit O (hmem O hbig) ?_⟩
  exact hO.le.trans (sSup_le fun _ hW => hW.1.2.elim (fun h => h.trans le_sup_left)
    fun h => h.trans le_sup_right)

/-- **An inhabitant of the narrowed hypothesis.**  For the system attached to a single global
object and the collection of *all* opens, `Stacks.DerivedGlueing.locallyGivenOfTop`, every open is
a member, so the collection is saturated; and on a space whose opens are totally ordered every
open contained in `U ∪ V` is contained in the larger of the two.  The `∀ 𝒟` form of the hypothesis
has no inhabitant at all, by the argument in the module documentation, so this is what the
narrowing buys. -/
theorem hasGluingForHomsOver_opensBelowPair_locallyGivenOfTop
    (hchain : ∀ U V : Opens X.carrier, U ≤ V ∨ V ≤ U) (K : OpenDerivedCategory X ⊤)
    (U V : Opens X.carrier) :
    HasGluingForHomsOver
      ((locallyGivenOfTop X K).subcollection
        (opensBelowPair (locallyGivenOfTop X K) U V)
        (opensBelowPair_subset (locallyGivenOfTop X K) U V)) :=
  hasGluingForHomsOver_opensBelowPair_of_covered_mem _ (fun O _ => Set.mem_univ O) U V
    fun _ _ hO => (hchain U V).elim
      (fun h => Or.inr (hO.trans (sup_le h le_rfl)))
      fun h => Or.inl (hO.trans (sup_le le_rfl h))

/-! ### The collection `{⊥, ⊤}`, which needs no hypothesis on the space -/

/-- **The collection `{⊥, ⊤}` is saturated.**  An open which is the union of the members
contained in it is `⊤` if `⊤` is one of them and `⊥` otherwise. -/
theorem mem_botTop_of_eq_sSup {O : Opens X.carrier}
    (hO : O = sSup {W | W ∈ ({⊥, ⊤} : Set (Opens X.carrier)) ∧ W ≤ O}) :
    O ∈ ({⊥, ⊤} : Set (Opens X.carrier)) := by
  rcases eq_or_ne O ⊤ with rfl | hne
  · simp
  · refine Set.mem_insert_iff.mpr (Or.inl (le_bot_iff.mp (hO.le.trans (sSup_le ?_))))
    rintro W ⟨hW, hWO⟩
    rcases Set.mem_insert_iff.mp hW with rfl | hW'
    · exact le_rfl
    · exact absurd (top_le_iff.mp (Set.mem_singleton_iff.mp hW' ▸ hWO)) hne

/-- **Two members of `{⊥, ⊤}` split the members below their union.**  A member below `⊥ ∪ ⊥` is
`⊥`, and if one of the two is `⊤` it already contains everything. -/
theorem botTop_le_sup_split {U V : Opens X.carrier}
    (hU : U ∈ ({⊥, ⊤} : Set (Opens X.carrier)))
    (hV : V ∈ ({⊥, ⊤} : Set (Opens X.carrier))) :
    ∀ O ∈ ({⊥, ⊤} : Set (Opens X.carrier)), O ≤ U ⊔ V → O ≤ U ∨ O ≤ V := by
  rintro O hO hOUV
  rcases hO with rfl | rfl
  · exact Or.inl bot_le
  · rcases hU with rfl | rfl <;> rcases hV with rfl | rfl
    · exact Or.inl (by simpa using hOUV)
    · exact Or.inr le_top
    all_goals exact Or.inl le_top

/-- **The members of `{⊥, ⊤}` meet in a member**, which is hypothesis (2) of [Stacks, Tag 0D6A]
for this collection. -/
theorem inter_eq_sSup_botTop (X : RingedSpace.{u, u}) :
    ∀ U ∈ ({⊥, ⊤} : Set (Opens X.carrier)), ∀ V ∈ ({⊥, ⊤} : Set (Opens X.carrier)),
      U ⊓ V = sSup {W | W ∈ ({⊥, ⊤} : Set (Opens X.carrier)) ∧ W ≤ U ⊓ V} := by
  rintro U hU V hV
  refine le_antisymm (le_sSup ⟨?_, le_rfl⟩) (sSup_le fun _ hW => hW.2)
  rcases hU with rfl | rfl <;> rcases hV with rfl | rfl <;> simp

/-- **The saturation of `{⊥, ⊤}`, read on a system whose collection is that set.**  Stated
through the equation `hopens` rather than at a particular system, so that no structure has to be
unfolded: asking the elaborator to see `{⊥, ⊤}` inside
`Stacks.DerivedGlueing.locallyGivenOfGlobal` directly exhausts the heartbeat budget at `whnf`. -/
theorem mem_opens_of_eq_sSup_of_opens_eq_botTop {S : LocallyGiven X}
    (hopens : S.opens = ({⊥, ⊤} : Set (Opens X.carrier)))
    (O : Opens X.carrier) (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O}) : O ∈ S.opens := by
  rw [hopens] at hO ⊢
  exact mem_botTop_of_eq_sSup hO

/-! ### Tag 0D6A, existence -/

/-- **Existence of a solution over a finite cover, from the sheaf condition of
[Stacks, Tag 0D66] part (2) at the system and at the pair subsystems.**

In Situation [Stacks, Tag 0D67], assume that `X = U_1 ∪ … ∪ U_n` with `U_i` in the collection,
that the intersection of two members of the collection is the union of the members contained in
it, that the prescribed objects have no negative self-Ext, and that the glueing of morphisms
holds for the system itself and for the subsystem on the members contained in `U` or in `V`, for
each pair `U`, `V` to which the two-open case is applied.  Then the system has a solution.  The
compatibility clause of the transport of [Stacks, Tag 08DG] is
`Stacks.DerivedGlueing.gluesObjectsAlongTwoOpens`. -/
theorem exists_solution_of_finite_cover_of_homs_pairs (S : LocallyGiven X)
    (hhomS : HasGluingForHomsOver S)
    (hhomP : ∀ (U V : Opens X.carrier), U ∈ S.opens →
        V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
        U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      HasGluingForHomsOver
        (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V)))
    (s : Finset (Opens X.carrier)) (hs : s.Nonempty) (hmem : ∀ U ∈ s, U ∈ S.opens)
    (hcover : s.sup id = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) :=
  exists_solution_of_finite_cover S
    (gluesAlongTwoOpens_of_hasGluingForHomsOver_pairs S hhomS hhomP
      (gluesObjectsAlongTwoOpens S))
    s hs hmem hcover hinter hExt

/-! ### Every binder of the existence statement, at once -/

/-- **The whole hypothesis bundle of the narrowed existence statement, for a system whose
collection is `{⊥, ⊤}`.**  The collection is saturated, so the sheaf condition holds at the system
and at every pair subsystem by `Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem` and
`Stacks.DerivedGlueing.hasGluingForHomsOver_opensBelowPair_of_covered_mem` — the second because
the side conditions of `Stacks.DerivedGlueing.GluesAlongTwoOpens` force both opens of the pair
into `{⊥, ⊤}`, where `Stacks.DerivedGlueing.botTop_le_sup_split` applies.  `{⊤}` is a one-member
cover by members, and the members meet in a member.  Only the negative self-Ext hypothesis is
left to supply. -/
theorem nonempty_solution_of_opens_eq_botTop (S : LocallyGiven X)
    (hopens : S.opens = ({⊥, ⊤} : Set (Opens X.carrier)))
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) := by
  have hmemS := mem_opens_of_eq_sSup_of_opens_eq_botTop hopens
  have hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens,
      U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} := by
    intro U hU V hV
    rw [hopens] at hU hV ⊢
    exact inter_eq_sSup_botTop X U hU V hV
  have hpair : ∀ (U V : Opens X.carrier), U ∈ S.opens →
      V = sSup {W | W ∈ S.opens ∧ W ≤ V} →
      U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V} →
      HasGluingForHomsOver
        (S.subcollection (opensBelowPair S U V) (opensBelowPair_subset S U V)) := by
    intro U V hU hV _
    refine hasGluingForHomsOver_opensBelowPair_of_covered_mem S hmemS U V fun O hO hOUV => ?_
    have hVmem : V ∈ S.opens := hmemS V hV
    rw [hopens] at hU hVmem hO
    exact botTop_le_sup_split hU hVmem O hO hOUV
  have htop : (⊤ : Opens X.carrier) ∈ S.opens := by rw [hopens]; simp
  exact exists_solution_of_finite_cover_of_homs_pairs S
    (hasGluingForHomsOver_of_covered_mem S hmemS) hpair
    {⊤} ⟨⊤, Finset.mem_singleton_self _⟩
    (fun U hU => (Finset.mem_singleton.mp hU) ▸ htop)
    (by simp) hinter hExt

/-- **Every binder of `Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_homs_pairs`
instantiated at once, with nothing assumed.**

Take the collection `{⊥, ⊤}` and the system prescribed on it by a sheaf of `𝒪_X`-modules `F`
placed in degree zero.  Everything except the negative self-Ext hypothesis is
`Stacks.DerivedGlueing.nonempty_solution_of_opens_eq_botTop`, and that hypothesis is
`Stacks.DerivedGlueing.subsingleton_shiftedHom_locallyGivenOfGlobal_single`.  `X` and `F` are
arbitrary.

So the hypothesis bundle of the narrowed existence statement is satisfiable — which the bundle of
`Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_homs` is not known to be.  It is
satisfiable only degenerately: `⊤` is a member, so
`Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_top_mem` already gives the conclusion
with nothing assumed, and the covering hypothesis forces `⊤` to be a finite union of members for
any witness whatever.  What is *not* degenerate is `F`, which is an arbitrary sheaf of modules and
not the zero object. -/
theorem nonempty_solution_botTop_single (X : RingedSpace.{u, u})
    (F : SheafOfModules.{u} (restrictedRingSheaf X ⊤)) :
    Nonempty (Solution (locallyGivenOfGlobal X {⊥, ⊤}
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (restrictedRingSheaf X ⊤)) 0).obj F))) :=
  nonempty_solution_of_opens_eq_botTop _ (locallyGivenOfGlobal_opens X _ _)
    (subsingleton_shiftedHom_locallyGivenOfGlobal_single X {⊥, ⊤} F)

end Stacks.DerivedGlueing

end
