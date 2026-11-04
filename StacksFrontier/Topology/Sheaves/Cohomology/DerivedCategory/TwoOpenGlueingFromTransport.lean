module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsAtOneOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingFromUniqueness
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingObjectTransport

/-!
# Tag 0D6A with the two-open stand-in eliminated

Let `(X, 𝒪_X)` be a ringed space and `(ℬ, K_U, ρ^U_V)` a system of locally given derived objects
on it, as in Situation 0D67.  The existence half of [Stacks, Tag 0D6A],
`Stacks.DerivedGlueing.exists_solution_of_finite_cover`, is granted
`Stacks.DerivedGlueing.GluesAlongTwoOpens` — the case of a cover by two opens, carried as a
`Prop`-valued definition that nothing proves.  Three reductions now stand between that definition
and the inputs this development actually owes, and this file composes them.

* `Stacks.DerivedGlueing.gluesAlongTwoOpens_of_hasGluingForHomsOver_subcollections` reduces the
  two-open case to the sheaf condition of [Stacks, Tag 0D66] part (2) for every subsystem,
  together with `Stacks.DerivedGlueing.GluesObjectsAlongTwoOpens` — the glueing lemma
  [Stacks, Tag 08DG] in the vocabulary of Situation 0D67.
* `Stacks.DerivedGlueing.exists_glueing_two_opens_of_top` reduces that glueing lemma, at every
  pair of opens at once, to its instance `Stacks.DerivedGlueing.TwoOpenGlueingOver S U V ⊤` over
  the *ambient* open — where the object part is already proved with nothing assumed, by
  `Stacks.DerivedGlueing.exists_glueing_two_opens_objects`, so that what is left of it is the
  compatibility equation alone.

Composing them replaces the `GluesAlongTwoOpens` stand-in by two inputs, neither of which is a
definition of this development's own invention: the sheaf condition of another tag, and one
equation of the 08DG transport.  That is
`Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_glueingAtTop`, registered against
[Stacks, Tag 0D6A] below with the two granted inputs named in its clause string.

For the uniqueness half the corresponding statement is already formalized as
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_hasGluingForHomsAtTop`, which is registered
against [Stacks, Tag 0D6C] and carries no covering hypothesis at all; having none, it is equally
the uniqueness half of Tag 0D6A, and it is registered as such here by `add_to_stacks` rather than
restated — the two tags' uniqueness clauses are the same statement, and proving it twice would be
a duplicate.

## What the tag still owes, after this file

Exactly one thing, and it is not a definition peculiar to this development.

The compatibility clause of the 08DG transport,
`∀ (U V : Opens X.carrier), TwoOpenGlueingOver S U V ⊤ le_top le_top`, is **no longer owed**: it
is `Stacks.DerivedGlueing.twoOpenGlueingOver_top` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingOverTop`, proved with
nothing assumed.  What was open there — the identification of
`Stacks.Cohomology.GlueingComplexes.Glueing.compatible`, stated against
`Stacks.Cohomology.GlueingComplexes.overlapIso`, with the equation of `TwoOpenGlueingOver`,
stated against `Stacks.DerivedGlueing.LocallyGiven.restrictionComp` — is settled by the
`W ≤ U ≤ O` dictionary coherence of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DerivedRestrictionDictionaryCoherence`.

What remains owed is:

* `∀ 𝒟 (h𝒟 : 𝒟 ⊆ S.opens), HasGluingForHomsOver (S.subcollection 𝒟 h𝒟)` for existence, and
   `HasGluingForHomsAt S ⊤` for uniqueness — in both cases the sheaf condition of
   [Stacks, Tag 0D66] part (2), which this development carries in the vocabulary of a morphism of
   ringed spaces and a basis of the target and which is owed only its restriction compatibility.

## Main results

* `Stacks.DerivedGlueing.gluesObjectsAlongTwoOpens_of_top`: the glueing lemma in the vocabulary of
  Situation 0D67, from its instance over the ambient open.
* `Stacks.DerivedGlueing.gluesAlongTwoOpens_of_twoOpenGlueingOver_top`: the two-open case, from
  that instance and the sheaf condition for every subsystem.
* `Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_glueingAtTop`:
  **[Stacks, Tag 0D6A]**, existence, with `GluesAlongTwoOpens` eliminated.

## References

* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **The glueing lemma of [Stacks, Tag 08DG] in the vocabulary of Situation 0D67, from its
instance over the ambient open.** A glueing over `⊤` of two objects given over `U` and over `V`
descends to a glueing over `U ∪ V`, by
`Stacks.DerivedGlueing.exists_glueing_two_opens_of_top`; so the predicate
`Stacks.DerivedGlueing.GluesObjectsAlongTwoOpens`, which asks for a glueing over `U ∪ V` for every
pair, follows from the instance of `Stacks.DerivedGlueing.TwoOpenGlueingOver` over `⊤`. -/
theorem gluesObjectsAlongTwoOpens_of_top (S : LocallyGiven X)
    (hTop : ∀ U V : Opens X.carrier, TwoOpenGlueingOver S U V ⊤ le_top le_top) :
    GluesObjectsAlongTwoOpens S :=
  fun U V A B c => exists_glueing_two_opens_of_top S U V (hTop U V) A B c

/-- **The two-open case of [Stacks, Tag 0D6A], from the sheaf condition for every subsystem and
the glueing lemma over the ambient open.** This is
`Stacks.DerivedGlueing.gluesAlongTwoOpens_of_hasGluingForHomsOver_subcollections` with its second
input replaced by what remains of the transport of [Stacks, Tag 08DG]. -/
theorem gluesAlongTwoOpens_of_twoOpenGlueingOver_top (S : LocallyGiven X)
    (hhom : ∀ (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens),
      HasGluingForHomsOver (S.subcollection 𝒟 h𝒟))
    (hTop : ∀ U V : Opens X.carrier, TwoOpenGlueingOver S U V ⊤ le_top le_top) :
    GluesAlongTwoOpens S :=
  gluesAlongTwoOpens_of_hasGluingForHomsOver_subcollections S hhom
    (gluesObjectsAlongTwoOpens_of_top S hTop)

/-- **Existence of a solution over a finite cover, from the glueing of morphisms for every
subsystem and the transport of [Stacks, Tag 08DG] over the ambient open.** In Situation 0D67,
assume that `X = U_1 ∪ … ∪ U_n` with `U_i` in the collection, that the intersection of two members
of the collection is the union of the members contained in it, and that the prescribed objects
have no negative self-Ext.  Given `hhom`, the sheaf condition of [Stacks, Tag 0D66] part (2) for
every subsystem of the collection, and `hTop`, the compatibility clause of the transport of
[Stacks, Tag 08DG] into Situation 0D67 read over the ambient open, the system has a solution. -/
theorem exists_solution_of_finite_cover_of_glueingAtTop (S : LocallyGiven X)
    (hhom : ∀ (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens),
      HasGluingForHomsOver (S.subcollection 𝒟 h𝒟))
    (hTop : ∀ U V : Opens X.carrier, TwoOpenGlueingOver S U V ⊤ le_top le_top)
    (s : Finset (Opens X.carrier)) (hs : s.Nonempty) (hmem : ∀ U ∈ s, U ∈ S.opens)
    (hcover : s.sup id = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) :=
  exists_solution_of_finite_cover S (gluesAlongTwoOpens_of_twoOpenGlueingOver_top S hhom hTop)
    s hs hmem hcover hinter hExt

end Stacks.DerivedGlueing

end
