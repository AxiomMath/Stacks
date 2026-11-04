module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.Topology.Noetherian.IrreducibleComponents

/-!
# Irreducible components of a closed subset of a locally Noetherian algebraic space

The space of points of a locally Noetherian algebraic space over `S` is a locally Noetherian
topological space (Stacks 04ZF), so the irreducible components of a closed subset of it are
locally finite: every point of the space of points has a neighbourhood meeting only finitely
many of them.

## Main results

* `AlgebraicGeometry.Space.locallyFinite_irreducibleComponents_of_isClosed`: the irreducible
  components of a closed subset of the space of points form a locally finite collection.

## Implementation notes

The components are those of the subspace on the closed subset, and the collection is the family
of their images under the inclusion of that subset, which is a closed embedding. Local
finiteness is Mathlib's `LocallyFinite`, which is Stacks 0BDS.
`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance and is
made a local instance here.

## References

* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The irreducible components of a closed subset of the space of points of a locally Noetherian
algebraic space over `S` form a locally finite collection. -/
@[stacks 0EE5]
theorem locallyFinite_irreducibleComponents_of_isClosed (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (hN : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} ↦ IsLocallyNoetherian X))
    (T : Set (points B S hS F)) (hT : IsClosed T) :
    LocallyFinite fun C : irreducibleComponents T ↦ Subtype.val '' (C : Set T) :=
  (isLocallyNoetherianSpace_of_isLocallyNoetherian B S hS F hF
    hN).locallyFinite_image_irreducibleComponents hT.isClosedEmbedding_subtypeVal

end AlgebraicGeometry.Space

end
