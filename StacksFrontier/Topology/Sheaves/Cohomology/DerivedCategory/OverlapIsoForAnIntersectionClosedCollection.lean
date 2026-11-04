module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOverASaturatedCollection
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingInput

/-!
# The descent datum of Tag 0D69 for a collection closed under intersection

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67.  [Stacks, Tag 0D69] attaches to it, for `U, V ∈ ℬ`, a
*unique* isomorphism `ρ_{U,V} : K_U|_{U ∩ V} ⟶ K_V|_{U ∩ V}` compatible with the prescribed
transitions on the members of `ℬ` contained in `U ∩ V`, and shows that these isomorphisms satisfy
the cocycle condition over a triple intersection.

The source obtains both from the uniqueness clause of [Stacks, Tag 0D68], applied to the system
induced on the ringed space `U ∩ V`.  In this development that clause is the predicate
`Stacks.DerivedGlueing.HasUniqueSolutionOverIso`, which is *granted* in
`Stacks.DerivedGlueing.exists_unique_overlapIso` and
`Stacks.DerivedGlueing.restrictOverlapHom_cocycle`.

This file proves both statements of Tag 0D69 **granted nothing at all** under one extra
hypothesis on the collection: that it is closed under pairwise intersection.  Then the open at
which the uniqueness clause is applied — `U ∩ V` in the first statement, `U ∩ V ∩ W` in the
second — is itself a member of the collection, and over a member the clause is a theorem,
`Stacks.DerivedGlueing.exists_unique_solutionOverIso_of_mem_opens`: restriction from a member to
itself is the identity functor, so the identifications of two solutions over it compose to the
required isomorphism and determine it.

Two hypotheses of the general statements disappear with the granted clause, and both are
discharged rather than assumed:

* the covering condition on intersections of members, `hinter` — a member is the union of the
  members contained in it, itself among them;
* the vanishing of negative self-`Ext` of the prescribed objects — it enters only through the
  general case of the sheaf condition of [Stacks, Tag 0D66] part (2), and over a member there is
  nothing to glue.

So the statements below are the two statements of Tag 0D69 with *strictly fewer* hypotheses than
the general conditional forms, at the cost of the closure hypothesis on the collection.

## Main results

* `Stacks.DerivedGlueing.exists_unique_overlapIso_of_inf_mem`: the unique compatible isomorphism
  `ρ_{U,V}` over an overlap, for a collection closed under pairwise intersection.
* `Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_inf_mem`: the cocycle condition
  `ρ_{U,W} = ρ_{V,W} ∘ ρ_{U,V}` over a triple intersection, for such a collection.
* `Stacks.DerivedGlueing.inf_mem_opensLE`: the collection of all opens contained in a fixed open
  is closed under pairwise intersection.
* `Stacks.DerivedGlueing.exists_unique_overlapIso_opensLE`: the first statement with *every*
  binder discharged from closed terms, at a collection that contains `⊤` only in the degenerate
  case.

## Why the hypothesis is not a disguised saturation, and why these are not vacuous

`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_sSup_covered_mem` already proves the granted
clause outright for a *saturated* collection — one containing every open that is the union of the
members contained in it.  That hypothesis is much stronger than closure under intersection: it
forces `⊤` into the collection as soon as the collection covers `X`, and when `⊤ ∈ ℬ` the
conclusions of Tags 0D6A to 0D6C are already unconditional by
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem`.  Closure under intersection forces
nothing of the kind: the collection of all opens contained in a fixed open `P` is closed under
intersection and contains `⊤` only when `P = ⊤`, by
`Stacks.DerivedGlueing.top_mem_opensLE_iff`.

`Stacks.DerivedGlueing.exists_unique_overlapIso_opensLE` discharges every binder of the first
statement from closed terms at exactly that collection, with the prescribed objects those of
`Stacks.DerivedGlueing.locallyGivenOfGlobal` — so the closure hypothesis is satisfiable, and
satisfiable away from `⊤ ∈ ℬ`.  That certificate covers the cocycle statement too: its remaining
binders are three compatible isomorphisms over the three overlaps, and those are exactly what the
first statement produces, at the same collection.

## What is tagged here, and under which clause string

Both statements below are registered for [Stacks, Tag 0D69].  Each is a *restricted case* — the
collection is assumed closed under pairwise intersection, which the source does not assume — so
each clause string names that restriction in full, which is the condition under which this
repository registers a restricted case.  A bare registration on either would be wrong; a
registration whose clause string states the restriction is not.

`Stacks.DerivedGlueing.exists_unique_overlapIso_locallyGivenOfTop` is left untagged on a
different ground: its collection is *all* opens, so `⊤` is a member and the statement is
subsumed by the two below.

These are not the only registrations of Tag 0D69, and they are not meant to be: the tag is
registered once per clause it covers, across
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.OverlapRestrictedSystem` (the restricted
system over the overlap, and its two solutions),
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DescentDatumOfLocallyGivenObjects` and
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DescentDatumFromGlueingAtTheOverlap`
(the comparison isomorphism and the cocycle condition for an arbitrary collection, taking
`Stacks.DerivedGlueing.HasUniqueSolutionOverIso` and `Stacks.DerivedGlueing.HasGluingForHomsAt`
respectively as hypotheses),
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomVanishingOverASubcollection` (both
clauses for an arbitrary collection at the source's own hypotheses, nothing else assumed, which
is where the two hypotheses just named are discharged), and this file (both clauses for a
collection closed under intersection, granted nothing).

## References

* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### Tag 0D69 for a collection closed under pairwise intersection -/

/-- **The comparison isomorphism over an overlap, for a collection closed under pairwise
intersection.** In Situation 0D67, assume that the intersection of two members of the collection
is again a member.  Then for members `U` and `V` there is a unique isomorphism
`K_U|_{U ∩ V} ≅ K_V|_{U ∩ V}` compatible with the prescribed transitions on the members of the
collection contained in `U ∩ V`.

Both restrictions are solutions over `U ∩ V`, by
`Stacks.DerivedGlueing.SolutionOver.restrictOpen` applied to
`Stacks.DerivedGlueing.selfSolutionOver`, and `U ∩ V` is a member, so
`Stacks.DerivedGlueing.exists_unique_solutionOverIso_of_mem_opens` identifies them. -/
theorem exists_unique_overlapIso_of_inf_mem (S : LocallyGiven X)
    (hinf : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V ∈ S.opens)
    (U V : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) :
    ∃! φ : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
        (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV),
      IsOverlapHom S hU hV inf_le_left inf_le_right φ.hom := by
  obtain ⟨φ, hφ, hφuniq⟩ := exists_unique_solutionOverIso_of_mem_opens (hinf U hU V hV)
    ((selfSolutionOver S U hU).restrictOpen (U ⊓ V) inf_le_left)
    ((selfSolutionOver S V hV).restrictOpen (U ⊓ V) inf_le_right)
  exact ⟨φ, hφ, hφuniq⟩

/-- **The cocycle condition, for a collection closed under pairwise intersection.** Let `U`,
`V` and `W` be members of the collection and let `ρ_{U,V}`, `ρ_{V,W}` and `ρ_{U,W}` be compatible
isomorphisms between the restrictions of the prescribed objects to the corresponding overlaps.
Then over the triple intersection `ρ_{U,W} = ρ_{V,W} ∘ ρ_{U,V}`.

Both sides are morphisms of the solutions over `U ∩ V ∩ W` defined by the prescribed objects on
`U` and on `W`; that open is a member, being an intersection of members twice over, so
`Stacks.DerivedGlueing.exists_unique_solutionOverIso_of_mem_opens` identifies them. -/
theorem restrictOverlapHom_cocycle_of_inf_mem (S : LocallyGiven X)
    (hinf : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V ∈ S.opens)
    (U V W : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) (hW : W ∈ S.opens)
    (φUV : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV))
    (hφUV : IsOverlapHom S hU hV inf_le_left inf_le_right φUV.hom)
    (φVW : (S.restriction (V ⊓ W) V inf_le_left).obj (S.obj V hV) ≅
      (S.restriction (V ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφVW : IsOverlapHom S hV hW inf_le_left inf_le_right φVW.hom)
    (φUW : (S.restriction (U ⊓ W) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφUW : IsOverlapHom S hU hW inf_le_left inf_le_right φUW.hom) :
    restrictOverlapHom S hU hW inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U ⊓ V ⊓ W ≤ U ⊓ W) φUW.hom =
      restrictOverlapHom S hU hV inf_le_left inf_le_right
          (inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V) φUV.hom ≫
        restrictOverlapHom S hV hW inf_le_left inf_le_right
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U ⊓ V ⊓ W ≤ V ⊓ W) φVW.hom := by
  obtain ⟨φ, -, hφuniq⟩ := exists_unique_solutionOverIso_of_mem_opens
    (hinf (U ⊓ V) (hinf U hU V hV) W hW)
    ((selfSolutionOver S U hU).restrictOpen (U ⊓ V ⊓ W)
      (inf_le_left.trans inf_le_left))
    ((selfSolutionOver S W hW).restrictOpen (U ⊓ V ⊓ W) inf_le_right)
  have h₁ := hφuniq (restrictOverlapIso S hU hW inf_le_left inf_le_right
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) φUW)
    (hφUW.restrict _)
  have h₂ := hφuniq (restrictOverlapIso S hU hV inf_le_left inf_le_right inf_le_left φUV ≪≫
      restrictOverlapIso S hV hW inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) φVW)
    ((hφUV.restrict _).comp (hφVW.restrict _))
  rw [← restrictOverlapIso_hom, ← restrictOverlapIso_hom, ← restrictOverlapIso_hom, h₁, ← h₂]
  rfl

/-! ### A collection closed under intersection that does not contain `⊤` -/

/-- **The collection of all opens contained in a fixed open is closed under pairwise
intersection.** The intersection of two opens contained in `P` is contained in `P`.

Together with `Stacks.DerivedGlueing.top_mem_opensLE_iff`, which says that this collection
contains `⊤` exactly when `P = ⊤`, this is what makes the hypothesis of
`Stacks.DerivedGlueing.exists_unique_overlapIso_of_inf_mem` satisfiable away from the degenerate
case `⊤ ∈ ℬ`. -/
theorem inf_mem_opensLE (P : Opens X.carrier) :
    ∀ U ∈ {W : Opens X.carrier | W ≤ P}, ∀ V ∈ {W : Opens X.carrier | W ≤ P},
      U ⊓ V ∈ {W : Opens X.carrier | W ≤ P} := by
  intro _ hU _ _
  exact inf_le_left.trans (Set.mem_ofPred_eq ▸ hU)

/-- **[Stacks, Tag 0D69] over an overlap with every binder discharged from closed terms, at a
collection that does not contain `⊤`.** Take the collection of all opens contained in a fixed
open `P` and prescribe on each of them the restriction of a single global object, as in
`Stacks.DerivedGlueing.locallyGivenOfGlobal`.  Then the unique compatible isomorphism over the
overlap of any two members exists, with nothing assumed.

Nothing is assumed about `P`, `U`, `V` or the global object: `U` and `V` may be distinct,
incomparable and both proper, and `⊤` belongs to the collection only when `P = ⊤`
(`Stacks.DerivedGlueing.top_mem_opensLE_iff`).  This is the non-degeneracy certificate for
`Stacks.DerivedGlueing.exists_unique_overlapIso_of_inf_mem`. -/
theorem exists_unique_overlapIso_opensLE (X : RingedSpace.{u, u}) (P : Opens X.carrier)
    (K : OpenDerivedCategory X ⊤) (U V : Opens X.carrier) (hUP : U ≤ P) (hVP : V ≤ P) :
    ∃! φ : ((locallyGivenOfGlobal X {W : Opens X.carrier | W ≤ P} K).restriction (U ⊓ V) U
          inf_le_left).obj
          ((locallyGivenOfGlobal X {W : Opens X.carrier | W ≤ P} K).obj U hUP) ≅
        ((locallyGivenOfGlobal X {W : Opens X.carrier | W ≤ P} K).restriction (U ⊓ V) V
          inf_le_right).obj
          ((locallyGivenOfGlobal X {W : Opens X.carrier | W ≤ P} K).obj V hVP),
      IsOverlapHom (locallyGivenOfGlobal X {W : Opens X.carrier | W ≤ P} K) hUP hVP
        inf_le_left inf_le_right φ.hom :=
  exists_unique_overlapIso_of_inf_mem (locallyGivenOfGlobal X {W : Opens X.carrier | W ≤ P} K)
    (inf_mem_opensLE P) U V hUP hVP

end Stacks.DerivedGlueing

end
