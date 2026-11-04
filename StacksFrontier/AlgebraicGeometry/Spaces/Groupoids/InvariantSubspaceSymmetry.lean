module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSubspaces

/-!
# Invariance is symmetric in the source and the target map

Let `G` be a groupoid in algebraic spaces over an algebraic space `B` over a scheme `S` of a big
fppf site, in the sense of Stacks 043W, and let `W` be a subspace of its space of objects. Stacks
044F states invariance of an *open* subspace as the one-sided condition that an arrow whose source
lies in `W` has its target in `W`, and invariance of a *locally closed* subspace as the two-sided
condition that the inverse images of `W` under the source and the target map agree. The results
here show that the one-sided condition already implies the two-sided one, for an arbitrary
subfunctor of the object space: the arrow witnessing the failure of the reverse inclusion is
inverted in the groupoid obtained by evaluating `G` at a test scheme, and its inverse exchanges the
roles of the source and the target.

This is the step the source takes for granted when it writes `R_Z = s^{-1}(Z) = t^{-1}(Z)` — the
discussion following Stacks 044F, invoked at the start of the proof of Stacks 04YN to see that the
two morphisms `R_Z ⟶ Z` are base changes of the source and the target map of `G`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.preimage_target_le_preimage_source`: the reverse of
  the one-sided invariance condition holds as soon as the condition itself does.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.preimage_source_eq_preimage_target`: hence the
  inverse images of an invariant subfunctor under the source and the target map are equal.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isInvariantOpen_iff_isOpenSubspace_and_preimage_eq`:
  part (1) of Stacks 044F may equivalently be stated with the two-sided condition that part (2)
  uses.

## Implementation notes

No openness and no local closedness is used: the statements are about an arbitrary
`CategoryTheory.Subfunctor` of the object space, which is the generality the argument has, and the
hypothesis is the bare inverse-image inequality rather than either predicate of Stacks 044F. The
predicate forms follow by projection, and are recorded only where they do not duplicate the general
statement.

Invariance is a condition on subfunctors, hence pointwise over the test schemes, and the inverse of
an arrow is available pointwise: the last field of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces` provides, at each test scheme `T`, a
`Deformation.PointwiseGroupoid` whose `arrowEquiv` identifies the morphisms of a groupoid structure
on the points of the object space with the points of the arrow space having prescribed endpoints.
Inverting there and reading the result back through `arrowEquiv` produces an arrow whose source is
the given arrow's target and whose target is the given arrow's source, which is all the argument
needs; no composition law and no identity arrow is used.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {B : AlgebraicSpaces site S hS}

/-- If every arrow of a groupoid in algebraic spaces whose source lies in a subspace `W` of the
object space has its target in `W`, then every arrow whose target lies in `W` has its source in
`W`: apply the hypothesis to the inverse of the arrow in the groupoid of points over a test
scheme. -/
theorem preimage_target_le_preimage_source
    (G : GroupoidInAlgebraicSpaces site S hS B) (W : Subfunctor G.objects.obj)
    (hW : W.preimage G.source.hom ≤ W.preimage G.target.hom) :
    W.preimage G.target.hom ≤ W.preimage G.source.hom := by
  intro T a ha
  obtain ⟨P⟩ := G.pointwiseGroupoid T
  let _ : Groupoid (G.objects.obj.obj T) := P.groupoid
  have hmem : G.target.hom.app T a ∈ W.obj T := ha
  let f : G.source.hom.app T a ⟶ G.target.hom.app T a :=
    (P.arrowEquiv _ _).symm ⟨a, rfl, rfl⟩
  let b := P.arrowEquiv (G.target.hom.app T a) (G.source.hom.app T a) (Groupoid.inv f)
  have hb := b.2
  have := hW T (show (b : G.arrows.obj.obj T) ∈ (W.preimage G.source.hom).obj T by
    simpa [hb.1] using hmem)
  simpa [hb.2] using this

/-- The inverse images of an invariant subspace of the object space of a groupoid in algebraic
spaces under the source and the target map coincide. The hypothesis is the one-sided condition of
Stacks 044F, part (1); the conclusion is the two-sided condition of part (2). -/
theorem preimage_source_eq_preimage_target
    (G : GroupoidInAlgebraicSpaces site S hS B) (W : Subfunctor G.objects.obj)
    (hW : W.preimage G.source.hom ≤ W.preimage G.target.hom) :
    W.preimage G.source.hom = W.preimage G.target.hom :=
  le_antisymm hW (preimage_target_le_preimage_source G W hW)

/-- For an invariant open subspace in the sense of Stacks 044F, part (1), the inverse images under
the source and the target map coincide. -/
theorem preimage_source_eq_preimage_target_of_isInvariantOpen
    (G : GroupoidInAlgebraicSpaces site S hS B) {W : Subfunctor G.objects.obj}
    (hW : IsInvariantOpen G W) :
    W.preimage G.source.hom = W.preimage G.target.hom :=
  preimage_source_eq_preimage_target G W hW.2

/-- Part (1) of Stacks 044F stated with the two-sided inverse-image condition that part (2) uses:
for an open subspace of the object space the one-sided and the two-sided conditions agree. -/
theorem isInvariantOpen_iff_isOpenSubspace_and_preimage_eq
    (G : GroupoidInAlgebraicSpaces site S hS B) (W : Subfunctor G.objects.obj) :
    IsInvariantOpen G W ↔
      Space.IsOpenSubspace site S hS W ∧
        W.preimage G.target.hom = W.preimage G.source.hom :=
  ⟨fun hW => ⟨hW.1, (preimage_source_eq_preimage_target_of_isInvariantOpen G hW).symm⟩,
    fun hW => ⟨hW.1, hW.2.ge⟩⟩

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
