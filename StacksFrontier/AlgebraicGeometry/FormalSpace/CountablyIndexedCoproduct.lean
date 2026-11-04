module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproductRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrumRefined

/-!
# A finite coproduct of countably indexed fppf sheaves is countably indexed

Let `S` be a scheme contained in a big fppf site `B`. An fppf sheaf over `S` is *countably
indexed* (**Stacks 0AIJ**) when it is the colimit of a sequence of affine schemes over `S`
along thickenings. This file proves that a coproduct of finitely many countably indexed
sheaves is countably indexed, and in particular that a coproduct of finitely many countably
indexed affine formal algebraic spaces over `S` is a countably indexed affine formal
algebraic space over `S`.

The presentation of the coproduct is the combined presentation of
`AlgebraicGeometry.FormalSpace.exists_piOrder_presentation_sigma`: its index is the product
`∏ᵢ Idx i` of the index preorders of the given presentations. Taking each `Idx i` countable —
which **Stacks 0AII** allows, a sequential presentation being the same as one indexed by a
countable nonempty directed preorder — the product over a *finite* index type is countable
again, nonempty and directed, so Stacks 0AII converts the combined presentation back into a
sequential one. That is the whole argument: the only work is the reindexing, since the
presentation itself is already built.

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_sigma`: a coproduct of finitely many
  countably indexed fppf sheaves over `S` is countably indexed.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexedAffine_sigma`: a coproduct of finitely many
  countably indexed affine formal algebraic spaces over `S` is one again.

## Implementation notes

Neither statement carries a `@[stacks]` registration. The Stacks project has no lemma to this
effect: countable indexing of a finite coproduct is used inside proofs — alongside the
untagged assertion that a finite union of formal affine algebraic spaces is a formal affine
algebraic space, which is `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sigma` —
and never stated on its own.

Nothing beyond countable indexing is asked of the summands in
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_sigma`: the colimit clause of **Stacks 0AIJ**
already supplies the presentations that are combined, and neither the set-theoretic condition
of **Stacks 0AIS** nor affineness of the formal space is used. The affine formal statement is
the conjunction of that with `isAffineFormalAlgebraicSpace_sigma`.

## References

* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0AII](https://stacks.math.columbia.edu/tag/0AII)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A coproduct of finitely many countably indexed fppf sheaves over `S` is countably
indexed.**

Each summand's sequential presentation is replaced by one over a countable nonempty directed
preorder (**Stacks 0AII**), the presentations are combined over the product of those index
preorders by `AlgebraicGeometry.FormalSpace.exists_piOrder_presentation_sigma`, and that
product is countable because the index type of the coproduct is finite; Stacks 0AII turns the
combined presentation back into a sequential one. -/
theorem isCountablyIndexed_sigma {I : Type (u + 1)} [Finite I] (Z : I → FppfSheaf B S hS)
    (hZ : ∀ i, IsCountablyIndexed B S hS (Z i)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsCountablyIndexed B S hS (∐ Z) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  show IsCountablyIndexed B S hS (∐ Z)
  choose Idx pre hne hdir hcnt D hthick hiso using fun i ↦
    (isCountablyIndexed_iff_exists_countable_presentation B S hS (Z i)).mp (hZ i)
  let : ∀ i, Preorder (Idx i) := pre
  let : ∀ i, Nonempty (Idx i) := hne
  let : ∀ i, IsDirectedOrder (Idx i) := hdir
  let : ∀ i, Countable (Idx i) := hcnt
  obtain ⟨E, hthickE, hE⟩ := exists_piOrder_presentation_sigma B S hS Z D hthick hiso
  exact (isCountablyIndexed_iff_exists_countable_presentation B S hS (∐ Z)).mpr
    ⟨PiOrder Idx, inferInstance, inferInstance, inferInstance, inferInstance, E, hthickE, hE⟩

/-- **A coproduct of finitely many countably indexed affine formal algebraic spaces over `S`
is a countably indexed affine formal algebraic space over `S`.**

The two halves are `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sigma` and
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_sigma`. -/
theorem isCountablyIndexedAffine_sigma {I : Type (u + 1)} [Finite I] (Z : I → FppfSheaf B S hS)
    (hZ : ∀ i, IsCountablyIndexedAffine B S hS (Z i)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsCountablyIndexedAffine B S hS (∐ Z) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  show IsCountablyIndexedAffine B S hS (∐ Z)
  exact ⟨isAffineFormalAlgebraicSpace_sigma B S hS Z fun i ↦ (hZ i).1,
    isCountablyIndexed_sigma B S hS Z fun i ↦ (hZ i).2⟩

end AlgebraicGeometry.FormalSpace

end
