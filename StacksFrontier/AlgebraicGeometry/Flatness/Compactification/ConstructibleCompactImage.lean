module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.Topology.Constructible.MeetConstructible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible subsets of a quasi-compact open are quasi-compact

A constructible subset of a topological space is retrocompact
(`Topology.IsRetrocompact_of_IsConstructible`), so on a compact space it is compact: intersecting
with the whole space is the identity. No separation or basis hypothesis is needed.

The geometric consequence recorded here is the step by which a pair of disjoint constructible
closed subsets of a quasi-compact open `U ⊆ X` produces a pair of quasi-compact opens of `X`:
the complement of such a subset inside `U` is again constructible, hence compact, hence its
image in `X` is compact, and that image is open because `U ⟶ X` is an open immersion. The
quasi-compact opens so obtained are what gets cut out by a finite type quasi-coherent ideal
sheaf when one wants to replace a set-theoretic condition on `U` by a closed subscheme of `X`.

## Main results

* `Topology.IsConstructible.isCompact`: a constructible subset of a compact space is compact.
* `AlgebraicGeometry.isCompact_image_compl_of_isConstructible`: for a quasi-compact open `U` of
  a scheme `X` and a constructible subset `T` of `U`, the image in `X` of the complement of `T`
  is quasi-compact.

## Implementation notes

`AlgebraicGeometry.ConnectedComponentSection.isCompact_of_isConstructible` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ConnectedComponentSection/DescentTopology.lean`
states the same conclusion as `Topology.IsConstructible.isCompact` for a space that is
additionally prespectral and quasi-separated, and proves it by induction over a basis of
quasi-compact opens. Those two hypotheses are not needed, and the statement is not about schemes;
the form below is the one to use, and the narrower one should be retired in a repository-wide
pass that can also update its one call site.

## References

* [Stacks Project, Tag 09YH](https://stacks.math.columbia.edu/tag/09YH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Topology

/-- **A constructible subset of a compact space is compact.** A constructible set is
retrocompact ([Stacks, Tag 09YH]), that is its intersection with every quasi-compact open is
quasi-compact; taking the whole space for that open gives the claim. -/
@[ega "0 9.1.4" "partial", ega "IV 1.8.1" "partial"]
theorem IsConstructible.isCompact {X : Type*} [TopologicalSpace X] [CompactSpace X] {E : Set X}
    (hE : IsConstructible E) : IsCompact E := by
  simpa using IsRetrocompact_of_IsConstructible hE isCompact_univ isOpen_univ

end Topology

namespace AlgebraicGeometry

/-- **The image of the complement of a constructible subset of a quasi-compact open is
quasi-compact.** Let `U` be a quasi-compact open subscheme of a scheme `X` and let `T` be a
constructible subset of `U`. Then the image of `Tᶜ` under the open immersion `U ⟶ X` is
quasi-compact.

Only quasi-compactness of `U` is used; the ambient scheme need be neither quasi-compact nor
quasi-separated. -/
@[ega "IV 1.8.1" "partial"]
theorem isCompact_image_compl_of_isConstructible {X : Scheme.{u}} (U : X.Opens)
    (hU : IsCompact (U : Set X)) {T : Set U.toScheme} (hT : Topology.IsConstructible T) :
    IsCompact (U.ι.base '' Tᶜ) :=
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  (hT.compl.isCompact).image U.ι.isOpenEmbedding.continuous

end AlgebraicGeometry

end
