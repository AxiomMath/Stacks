module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank

/-!
# Finite locally free of rank one means isomorphism

A morphism of schemes that is finite locally free of rank `1` is an isomorphism. Together with
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_one_of_isIso`, which is the converse, this
identifies the degree-`1` finite locally free morphisms with the isomorphisms.

## Main results

* `Stacks.Morphisms.isIso_of_isFiniteLocallyFreeOfRank_one`: a morphism of schemes that is
  finite locally free of rank `1` is an isomorphism.

## Implementation notes

The two halves of the statement are already available and only have to be composed. A finite
locally free morphism is finite, flat and locally of finite presentation by
`Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation`, which
supplies the `AlgebraicGeometry.IsFinite` and `AlgebraicGeometry.Flat` instances that the rank
function of a morphism needs. For a finite flat morphism,
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq` turns being finite locally
free of rank `r` into the rank function `AlgebraicGeometry.Scheme.Hom.finrank` being constantly
`r`, and `AlgebraicGeometry.Scheme.Hom.isIso_iff_finrank_eq` recognises the morphisms whose rank
function is constantly `1` as the isomorphisms.

So no reduction to an affine open of the target, and no ring-level argument that a free algebra
of rank one over its base is that base, is carried out here: both are already contained in the
two rank-function statements being composed. The only friction is that Mathlib states its
criterion as an equality of functions `T → ℕ` while this development states its own pointwise,
so the two are bridged by `funext` together with `Pi.one_apply`.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Morphisms

/-- **A finite locally free morphism of rank `1` is an isomorphism.** It is finite and flat, so
it has a rank function, and being finite locally free of rank `1` says exactly that this rank
function is constantly `1`, which characterises the isomorphisms among the finite flat
morphisms. This is the converse of
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_one_of_isIso`. -/
theorem isIso_of_isFiniteLocallyFreeOfRank_one {Z T : Scheme.{u}} (g : Z ⟶ T)
    (h : IsFiniteLocallyFreeOfRank g 1) : IsIso g := by
  obtain ⟨hfin, hflat, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree g 1)
  let : IsFinite g := hfin
  let : Flat g := hflat
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  refine funext fun t => ?_
  rw [Pi.one_apply]
  exact (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq g 1).mp h t

end Stacks.Morphisms

end
