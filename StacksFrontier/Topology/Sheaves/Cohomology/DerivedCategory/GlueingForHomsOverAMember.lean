module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenOfGlobalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOverACover

/-!
# The glueing of morphisms over a member of the collection

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67.  The predicate
`Stacks.DerivedGlueing.HasGluingForHomsOver` — the sheaf condition of [Stacks, Tag 0D66] part (2)
for the rule `W ↦ Hom(K|_W, L|_W)` — is *granted* throughout
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOverACover`, and it is the one
hypothesis on which the uniqueness halves of Tags 0D68, 0D69, 0D6A and 0D6C in this development
still rest.

This file proves the case of that condition in which the open subset `O` carrying the two objects
is **itself a member of the collection**.  There the sheaf condition is not a sheaf condition at
all: the family already has a member over `O`, restriction from `O` to `O` is the identity
functor, and the glued morphism is the family's own value at `O` read through that
identification.  It needs no hypothesis — in particular none of the negative-`Ext` vanishing that
the general case needs.

Two consequences are recorded.  First, a system whose collection contains every open that is a
union of its members satisfies the glueing condition outright,
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem`.  Second, applying that to the system
of all opens attached to a single global object,
`Stacks.DerivedGlueing.hasGluingForHomsOver_locallyGivenOfTop`, exhibits an inhabitant of
`Stacks.DerivedGlueing.HasGluingForHomsOver`.  That matters because the uniqueness halves of
Tags 0D6A and 0D6C are stated *conditionally* on it: without an inhabitant those statements would
be vacuously true, and nothing else in the development rules that out.

## Relation to the saturated-collection file

`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOverASaturatedCollection` runs
the same argument one level down, on *solutions* rather than on morphisms:
`Stacks.DerivedGlueing.exists_unique_solutionOverIso_of_mem_opens` is the member case there, and
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_sSup_covered_mem` and
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_locallyGivenOfTop` are its two consequences.  The
results here are strictly stronger, and both of those consequences follow from them in one line
through `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver`:

```
hasUniqueSolutionOverIso_of_hasGluingForHomsOver S (hasGluingForHomsOver_of_covered_mem S hmem)
hasUniqueSolutionOverIso_of_hasGluingForHomsOver _ (hasGluingForHomsOver_locallyGivenOfTop K)
```

What that file carries and this one does not is the witness for the *solution*-level granted
hypothesis of Tag 0D69; what this one carries and that one does not is the witness for
`Stacks.DerivedGlueing.HasGluingForHomsOver`, which is the granted hypothesis of the uniqueness
halves of Tags 0D6A and 0D6C and is not addressed there.  The two member-case lemmas are parallel
proofs of one argument at two levels; unifying them needs a form of
`hasUniqueSolutionOverIso_of_hasGluingForHomsOver` that consumes the glueing condition at a single
open rather than at all of them, which does not exist yet.

## The inhabitant is degenerate, and what a non-degenerate one would be

`Stacks.DerivedGlueing.hasGluingForHomsOver_locallyGivenOfTop` settles that the hypothesis is
satisfiable, but it satisfies it for the degenerate reason: the open at which the condition is
applied is itself a member, so nothing is glued.  Worse, every inhabitant obtainable from
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem` forces `⊤` into the collection, and
when `⊤` is a member the conclusion of
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_finite_cover` and of
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers` is already proved with *no* granted
hypothesis, by `Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem`.  So at the only
inhabitant this repository has, those two conditional statements say nothing their unconditional
`n = 1` partner does not already say.  They are honest and not vacuous; their content beyond
`n = 1` is simply not witnessed.

A non-degenerate inhabitant is one for a collection that does *not* contain `⊤`.  The least that
would do is an instance of the target itself,

```
theorem hasGluingForHomsOver_of_covers (S : LocallyGiven X) :
    HasGluingForHomsOver S
```

at a single concrete `S` — for instance the two-element cover of a space by two proper opens,
with `Stacks.DerivedGlueing.locallyGivenOfGlobal` supplying the system.  That statement is
carried, at *every* system and with no hypothesis at all, by
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covers` in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomVanishingOverASubcollection`, so the
non-degenerate inhabitant is available there and the paragraph above is a record of the state
before it was.

## Main results

* `Stacks.DerivedGlueing.exists_unique_hom_of_mem`: a compatible family of morphisms between the
  restrictions of two objects over `O` to the members of the collection contained in `O` comes
  from a unique morphism over `O`, when `O` is itself a member.
* `Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem`: the glueing condition for a
  collection containing every open that is a union of its members.
* `Stacks.DerivedGlueing.hasGluingForHomsOver_locallyGivenOfTop`: an inhabitant of the glueing
  condition, so the conditional uniqueness statements of Tags 0D6A and 0D6C are not vacuous.

## What is *not* proved here, and its type

The general case is untouched *here*.  Nothing in this file is a step towards it: the member case
is exactly the case the sheaf condition says nothing about.  What this file does not prove is
`Stacks.DerivedGlueing.HasGluingForHomsOver S` for an arbitrary system, that is

```
theorem hasGluingForHomsOver_of_covers (S : LocallyGiven X) :
    HasGluingForHomsOver S
```

and that is proved, with no hypothesis at all, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomVanishingOverASubcollection`.

The section *What is granted, and why* of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolution` lists what that
needs, and reduces it to the restriction compatibility of the value identification of
[Stacks, Tag 0D66] part (2).

*That reduction is discharged.*  All three of the layers it rested on are carried —
`Stacks.Cohomology.UnboundedHigherDirectImage.preimageCohomologyEvaluationIso_restrict` for
layer 3, and
`Stacks.Cohomology.UnboundedHigherDirectImage.preimageSectionsHomologyEquivShiftedHom_zero_restrict`
for layers 1 and 2 joined — and their junction is
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv_map`, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HomPresheafValueRestrictionSquare`.
So the glueing of morphisms is unconditional in all three of the shapes this development states
it in: `Stacks.Cohomology.UnboundedHigherDirectImage.exists_unique_restrictDerivedHom_on_isBasis`
over a basis, and `Stacks.DerivedGlueing.exists_unique_restrictDerivedHom_on_sSup_covered` and
`Stacks.DerivedGlueing.existsUnique_hom_restrict_of_sSup_covered` off a basis, all three in
the module `GlueingForHomsFromTheCoverUnconditional` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory`.

*So the only obligation left is the one that list did not mention.*  The sheaf condition of
[Stacks, Tag 0D66] part (2)
is stated for objects of the derived category of the whole of `X`, restricted to the opens of the
collection — that is how `Stacks.DerivedGlueing.subsingleton_shiftedHom_restrict_of_sSup_covered`
reaches an arbitrary open `O`, and how
`Stacks.DerivedGlueing.Solution.subsingleton_shiftedHom_self` consumes it at `⊤`, through
`Stacks.DerivedGlueing.faithful_jShriekTop_mapDerivedCategory` and
`Stacks.DerivedGlueing.sliceToSubspace`.  But `Stacks.DerivedGlueing.HasGluingForHomsOver`
quantifies over `K L : OpenDerivedCategory X O`, objects given *only* over `O`, and those are not
restrictions of global ones.  So the deduction needs the whole argument run on the ringed space
`X` restricted to `O`, together with the identification of `S.restriction W O` for `W ≤ O` with
restriction on that subspace — the generalisation from `⊤` to `O` of
`Stacks.DerivedGlueing.openModuleRestriction_top_eq`.  Nothing in the library provides it; the
vanishing clause escaped it only because there the objects are global.  The groundwork for it is
`Stacks.DerivedGlueing.sliceRestrictOverIso` and its neighbours in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverACover`;
what is missing is the identification of `Stacks.DerivedGlueing.restrictHomBelow` with
`AlgebraicGeometry.RingedSite.restrictDerivedHom` through it.

*Which consumers need a general open at all.*  Not all of them.
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_finite_cover` and
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers` reach
`Stacks.DerivedGlueing.HasUniqueSolutionOverIso` only at `⊤`, through
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_hasUniqueSolutionOverIso`, so for those two
the instance of the glueing condition at `⊤` would suffice — and at `⊤` the mismatch of the
previous paragraph is already bridged, by
`Stacks.DerivedGlueing.faithful_jShriekTop_mapDerivedCategory`, exactly as
`Stacks.DerivedGlueing.Solution.subsingleton_shiftedHom_self` uses it.  It is
`Stacks.DerivedGlueing.exists_unique_overlapIso` and
`Stacks.DerivedGlueing.restrictOverlapHom_cocycle` of Tag 0D69 that consume the clause at `U ⊓ V`
instead, and the two-open case `Stacks.DerivedGlueing.GluesAlongTwoOpens` that consumes it at a
member; those are what need the relativization.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **The glueing of morphisms over an open which is itself a member of the collection.** Let `O`
be a member of the collection and let `K` and `L` be objects over `O`.  A family of morphisms
`K|_W ⟶ L|_W`, indexed by the members `W` of the collection contained in `O` and compatible with
restriction between members, comes from a unique morphism `K ⟶ L`.

This is the instance of `Stacks.DerivedGlueing.HasGluingForHomsOver` at a member, and it is
granted nothing: the glued morphism is the family's value at `O` itself, read through the
identification `Stacks.DerivedGlueing.restrictionSelfIso` of restriction from `O` to `O` with the
identity functor, and its restriction to a smaller member is the family's value there by the
compatibility of the family.  Uniqueness is the faithfulness of restriction from `O` to `O`,
`Stacks.DerivedGlueing.restrictionSelf_map_injective`.

No negative-`Ext` hypothesis appears: the vanishing of negative self-`Ext` enters the general
case of the sheaf condition of [Stacks, Tag 0D66] part (2), and over a member there is nothing to
glue. -/
theorem exists_unique_hom_of_mem (S : LocallyGiven X) {O : Opens X.carrier} (hO : O ∈ S.opens)
    (K L : OpenDerivedCategory X O)
    (φ : ∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ O,
      (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L)
    (hφ : ∀ (W T : Opens X.carrier) (hW : W ∈ S.opens) (hT : T ∈ S.opens) (hTW : T ≤ W)
      (hWO : W ≤ O), restrictHomBelow S hTW hWO (φ W hW hWO) = φ T hT (hTW.trans hWO)) :
    ∃! ψ : K ⟶ L, ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
      (S.restriction W O hWO).map ψ = φ W hW hWO := by
  obtain ⟨ψ₀, h₀⟩ : ∃ ψ : K ⟶ L, (S.restriction O O le_rfl).map ψ = φ O hO le_rfl := by
    refine ⟨((restrictionSelfIso S O le_rfl).app K).inv ≫ φ O hO le_rfl ≫
      ((restrictionSelfIso S O le_rfl).app L).hom, ?_⟩
    rw [← cancel_mono (((restrictionSelfIso S O le_rfl).app L).hom)]
    exact (restrictionSelfIso_naturality S O le_rfl _).trans (Iso.hom_inv_id_assoc _ _)
  refine ⟨ψ₀, fun W hW hWO => ?_, fun ψ hψ => ?_⟩
  · have h2 := restrictHomBelow_map S hWO le_rfl ψ₀
    rw [h₀] at h2
    exact h2.symm.trans (hφ O W hO hW hWO le_rfl)
  · refine restrictionSelf_map_injective S O le_rfl ?_
    rw [hψ O hO le_rfl, h₀]

/-- **The glueing condition for a collection containing every open it covers.** If every open
subset which is the union of the members of the collection contained in it is itself a member,
then the sheaf condition of [Stacks, Tag 0D66] part (2) holds for the system, by
`Stacks.DerivedGlueing.exists_unique_hom_of_mem` at each such open.

The hypothesis is strictly stronger than the covering hypothesis of the general case and this is
therefore not a step towards it; it is what makes
`Stacks.DerivedGlueing.hasGluingForHomsOver_locallyGivenOfTop` available. -/
theorem hasGluingForHomsOver_of_covered_mem (S : LocallyGiven X)
    (hmem : ∀ O : Opens X.carrier, O = sSup {W | W ∈ S.opens ∧ W ≤ O} → O ∈ S.opens) :
    HasGluingForHomsOver S :=
  fun O hO _ K L _ φ hφ => exists_unique_hom_of_mem S (hmem O hO) K L φ hφ

/-- **The glueing condition is inhabited.** For the system of locally given derived objects
attached to a single global object and the collection of *all* open subsets,
`Stacks.DerivedGlueing.locallyGivenOfTop`, the sheaf condition of [Stacks, Tag 0D66] part (2)
holds: every open is a member.

This is the witness that the hypothesis `HasGluingForHomsOver` carried by
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_finite_cover` and
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers` is satisfiable, so that those two
statements are not vacuously true. -/
theorem hasGluingForHomsOver_locallyGivenOfTop (K : OpenDerivedCategory X ⊤) :
    HasGluingForHomsOver (locallyGivenOfTop X K) :=
  hasGluingForHomsOver_of_covered_mem _ fun O _ => Set.mem_univ O

end Stacks.DerivedGlueing

end
