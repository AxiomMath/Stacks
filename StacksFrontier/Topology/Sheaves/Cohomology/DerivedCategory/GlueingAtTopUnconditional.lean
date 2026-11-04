module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingOverTop
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingFromTransport

/-!
# Tag 0D6A with the compatibility clause of the 08DG transport discharged

Let `(X, 𝒪_X)` be a ringed space and `S` a system of locally given derived objects on it, as in
Situation 0D67. `Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_glueingAtTop` proves
the existence half of [Stacks, Tag 0D6A] granted two inputs: the sheaf condition of
[Stacks, Tag 0D66] part (2) for every subsystem, and the compatibility clause of the transport of
[Stacks, Tag 08DG] into Situation 0D67 over the ambient open. The second is the theorem
`Stacks.DerivedGlueing.twoOpenGlueingOver_top`, so this file removes it from the hypotheses; the
sheaf condition remains a hypothesis.

## Main results

* `Stacks.DerivedGlueing.gluesObjectsAlongTwoOpens`: the glueing lemma [Stacks, Tag 08DG] in the
  vocabulary of Situation 0D67, with nothing assumed.
* `Stacks.DerivedGlueing.gluesAlongTwoOpens_of_hasGluingForHomsOver`: the two-open case of
  [Stacks, Tag 0D6A], from the sheaf condition for every subsystem alone.
* `Stacks.DerivedGlueing.exists_solution_of_finite_cover_of_homs`: **[Stacks, Tag 0D6A],
  existence, from the sheaf condition for every subsystem alone.**

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **The glueing lemma of [Stacks, Tag 08DG] in the vocabulary of Situation 0D67, with nothing
assumed.** -/
theorem gluesObjectsAlongTwoOpens (S : LocallyGiven X) : GluesObjectsAlongTwoOpens S :=
  gluesObjectsAlongTwoOpens_of_top S (twoOpenGlueingOver_top S)

/-- **The two-open case of [Stacks, Tag 0D6A], from the sheaf condition for every subsystem
alone.** -/
theorem gluesAlongTwoOpens_of_hasGluingForHomsOver (S : LocallyGiven X)
    (hhom : ∀ (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens),
      HasGluingForHomsOver (S.subcollection 𝒟 h𝒟)) :
    GluesAlongTwoOpens S :=
  gluesAlongTwoOpens_of_twoOpenGlueingOver_top S hhom (twoOpenGlueingOver_top S)

/-- **Existence of a solution over a finite cover, from the glueing of morphisms for every
subsystem.** In Situation 0D67, assume that `X = U_1 ∪ … ∪ U_n` with `U_i` in the collection,
that the intersection of two members of the collection is the union of the members contained in
it, that the prescribed objects have no negative self-Ext, and that every subsystem satisfies the
sheaf condition of [Stacks, Tag 0D66] part (2). Then the system has a solution. -/
theorem exists_solution_of_finite_cover_of_homs (S : LocallyGiven X)
    (hhom : ∀ (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens),
      HasGluingForHomsOver (S.subcollection 𝒟 h𝒟))
    (s : Finset (Opens X.carrier)) (hs : s.Nonempty) (hmem : ∀ U ∈ s, U ∈ S.opens)
    (hcover : s.sup id = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) :=
  exists_solution_of_finite_cover_of_glueingAtTop S hhom (twoOpenGlueingOver_top S) s hs hmem
    hcover hinter hExt

end Stacks.DerivedGlueing

end
