module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.OverlapIsoForAnIntersectionClosedCollection

/-!
# The system induced on an overlap, and the two solutions of it

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67, and let `U` and `V` be members of `ℬ`.

[Stacks, Tag 0D69] opens by forming the subcollection `ℬ'` of the members of `ℬ` contained in
`U ∩ V`, observing that `(K_{U'}, ρ^{U'}_{V'})_{U' ∈ ℬ'}` is a system on the ringed space
`U ∩ V` which satisfies the hypotheses of [Stacks, Tag 0D68], and observing that the two
restrictions `K_U|_{U ∩ V}` and `K_V|_{U ∩ V}` both solve it.  Only then does it invoke the
uniqueness clause of Tag 0D68 to produce `ρ_{U,V}`.

Those opening clauses are what this file states.  In the development the passage to the ringed
space `U ∩ V` is not needed — solutions are relativized to an open subset by
`Stacks.DerivedGlueing.SolutionOver`, and the subsystem on a subcollection is
`Stacks.DerivedGlueing.LocallyGiven.subcollection` — so the clauses read as statements about
that subsystem and about `U ∩ V`.

Nothing is granted.  The two hypotheses used are the source's own: hypothesis (1) of
Tag 0D68, that the intersection of two members is the union of the members contained in it, and
its hypothesis (2), the vanishing of negative self-`Ext`.  Each is used only where Tag 0D68 uses
it, and the `Ext` clause needs no hypothesis at all beyond (2) itself.

## Main definitions

* `Stacks.DerivedGlueing.restrictedSystemOverInf`: the subsystem on the members of the
  collection contained in an overlap — the system `(K_{U'}, ρ^{U'}_{V'})_{U' ∈ ℬ'}` of the
  source.

## Main results

* `Stacks.DerivedGlueing.restrictedSystemOverInf_covers`,
  `Stacks.DerivedGlueing.restrictedSystemOverInf_intersections_covered` and
  `Stacks.DerivedGlueing.restrictedSystemOverInf_ext`: the restricted system satisfies the
  hypotheses of [Stacks, Tag 0D68] over the overlap.
* `Stacks.DerivedGlueing.exists_solutionOver_inf`: both restrictions solve it.

## References

* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### The subsystem on the members contained in an overlap -/

/-- The members of the collection contained in an overlap are members of the collection. -/
theorem opensBelow_subset (S : LocallyGiven X) (O : Opens X.carrier) :
    {W : Opens X.carrier | W ∈ S.opens ∧ W ≤ O} ⊆ S.opens := fun _ hW => hW.1

/-- **The system induced on an overlap**, namely the subsystem carried by the members of the
collection contained in `U ⊓ V`.  This is the collection `ℬ'` of [Stacks, Tag 0D69] together
with the prescribed objects and transitions read on it. -/
def restrictedSystemOverInf (S : LocallyGiven X) (U V : Opens X.carrier) : LocallyGiven X :=
  S.subcollection {W : Opens X.carrier | W ∈ S.opens ∧ W ≤ U ⊓ V} (opensBelow_subset S (U ⊓ V))

/-- The members of the system induced on `U ⊓ V` are the members of the collection contained in
`U ⊓ V`. -/
@[simp]
theorem restrictedSystemOverInf_opens (S : LocallyGiven X) (U V : Opens X.carrier) :
    (restrictedSystemOverInf S U V).opens = {W : Opens X.carrier | W ∈ S.opens ∧ W ≤ U ⊓ V} :=
  rfl

/-! ### The restricted system satisfies the hypotheses of Tag 0D68 -/

/-- The members of the restricted collection below an open contained in `U ⊓ V` are the members
of the whole collection below it. -/
private theorem restrictedSystemOverInf_opens_below (S : LocallyGiven X) (U V : Opens X.carrier)
    (P : Opens X.carrier) (hP : P ≤ U ⊓ V) :
    {W : Opens X.carrier | W ∈ (restrictedSystemOverInf S U V).opens ∧ W ≤ P} =
      {W : Opens X.carrier | W ∈ S.opens ∧ W ≤ P} := by
  ext W
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hP⟩, h.2⟩⟩

/-- **[Stacks, Tag 0D69], the restricted system covers the overlap.** The overlap of two members
is the union of the members of the restricted collection contained in it — which is condition
(1) of [Stacks, Tag 0D68] for the restricted system, read at `U ⊓ V`.  It is the condition that
intersections of members are unions of members, read at the pair `U, V`. -/
@[stacks 0D69 "the restricted system covers the overlap: condition (1) of 0D68 for the
  subsystem on the members contained in `U ⊓ V`, from the condition that the intersection of two
  members is the union of the members contained in it"]
theorem restrictedSystemOverInf_covers (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (U V : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) :
    U ⊓ V = sSup {W | W ∈ (restrictedSystemOverInf S U V).opens ∧ W ≤ U ⊓ V} := by
  rw [restrictedSystemOverInf_opens_below S U V _ le_rfl, ← hinter U hU V hV]

/-- **[Stacks, Tag 0D69], the restricted system's intersection condition.** The intersection of
two members of the restricted collection is the union of the members of the restricted
collection contained in it — condition (1) of [Stacks, Tag 0D68] for the restricted system, at
an arbitrary pair of its members.

The members of the restricted collection contained in `A ⊓ B` are exactly the members of the
whole collection contained in it, because `A ⊓ B ≤ A ≤ U ⊓ V`. -/
@[stacks 0D69 "the restricted system's intersection condition: condition (1) of 0D68 for the
  subsystem on the members contained in `U ⊓ V`, at an arbitrary pair of its members"]
theorem restrictedSystemOverInf_intersections_covered (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (U V : Opens X.carrier) :
    ∀ A ∈ (restrictedSystemOverInf S U V).opens, ∀ B ∈ (restrictedSystemOverInf S U V).opens,
      A ⊓ B = sSup {W | W ∈ (restrictedSystemOverInf S U V).opens ∧ W ≤ A ⊓ B} := by
  intro A hA B hB
  rw [restrictedSystemOverInf_opens_below S U V _ (inf_le_left.trans hA.2),
    ← hinter A hA.1 B hB.1]

/-- **[Stacks, Tag 0D69], the restricted system's `Ext` condition.** The prescribed objects of
the restricted system have no negative self-`Ext`, since they are prescribed objects of the
whole system — condition (2) of [Stacks, Tag 0D68] for the restricted system. -/
@[stacks 0D69 "the restricted system's `Ext` condition: condition (2) of 0D68 for the
  subsystem on the members contained in `U ⊓ V`, from the vanishing of negative self-`Ext` of
  the prescribed objects"]
theorem restrictedSystemOverInf_ext (S : LocallyGiven X)
    (hExt : ∀ (W : Opens X.carrier) (hW : W ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj W hW) (S.obj W hW) i))
    (U V : Opens X.carrier) :
    ∀ (W : Opens X.carrier) (hW : W ∈ (restrictedSystemOverInf S U V).opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((restrictedSystemOverInf S U V).obj W hW)
        ((restrictedSystemOverInf S U V).obj W hW) i) :=
  fun W hW i hi => hExt W hW.1 i hi

/-! ### The two restrictions are solutions over the overlap -/

/-- **[Stacks, Tag 0D69], both restrictions are solutions over the overlap.** The prescribed
object on a member is a solution over that member,
`Stacks.DerivedGlueing.selfSolutionOver`, and a solution over an open restricts to a solution
over a smaller one, `Stacks.DerivedGlueing.SolutionOver.restrictOpen`.  So `K_U|_{U ∩ V}` and
`K_V|_{U ∩ V}` are each a solution for the system over `U ∩ V`, and these are the two solutions
the source feeds to the uniqueness clause of [Stacks, Tag 0D68].  This holds for all
`U, V ∈ ℬ`. -/
@[stacks 0D69 "the two restricted objects are solutions over the overlap: `K_U|_{U ∩ V}` and
  `K_V|_{U ∩ V}` are each a solution for the system over `U ∩ V`, for every `U, V ∈ ℬ`"]
theorem exists_solutionOver_inf (S : LocallyGiven X) (U V : Opens X.carrier)
    (hU : U ∈ S.opens) (hV : V ∈ S.opens) :
    (∃ A : SolutionOver S (U ⊓ V),
        A.obj = (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU)) ∧
      ∃ B : SolutionOver S (U ⊓ V),
        B.obj = (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV) :=
  ⟨⟨(selfSolutionOver S U hU).restrictOpen (U ⊓ V) inf_le_left, rfl⟩,
    ⟨(selfSolutionOver S V hV).restrictOpen (U ⊓ V) inf_le_right, rfl⟩⟩

end Stacks.DerivedGlueing

end
