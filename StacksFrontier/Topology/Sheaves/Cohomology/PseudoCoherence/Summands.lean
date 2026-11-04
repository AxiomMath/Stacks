module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentSummand

/-!
# Pseudo-coherence of the summands of a pseudo-coherent biproduct on a ringed space

Let `(X, O_X)` be a ringed space. If `K ⊞ L` is pseudo-coherent in `D(O_X)`, then so are `K` and
`L`. Together with the fixed-degree statement
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_biprod`, this is Stacks 08CE.

## Main results

* `Stacks.PseudoCoherence.Summands.isPseudoCoherent_of_biprod`: **Stacks 08CE** without a fixed
  degree.

## Implementation notes

Pseudo-coherence asks for a *single* complex representing the object which is `m`-pseudo-coherent
for every `m` at once, so it is not the conjunction over `m` of the fixed-degree conditions on the
nose; that it is equivalent to that conjunction is Stacks 08CC part (2), packaged as
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall`. With that, the degree-free statement
is the fixed-degree one applied in every degree, and nothing further is proved here.

The fixed-degree statement itself is `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_biprod`
(`StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentSummand`), which is Stacks 064X
run on an open subspace and already proves both of the fixed-degree conclusions of Stacks 08CE at
once; the tag for those two sits there, so this file carries only the remaining two.

Both conclusions of the degree-free statement are proved in one declaration, as in the
fixed-degree case, because the proof produces both at the same time.

The space, ring and module universes all coincide, as they already must for the predicates of
Tag 08CB on a ringed space, and the derived-category hom universes of `X` and of its open
subspaces stay independent.

## References

* [Stacks Project, Tag 08CE](https://stacks.math.columbia.edu/tag/08CE)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Tag 064X](https://stacks.math.columbia.edu/tag/064X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace StrictlyPerfect

namespace Stacks.PseudoCoherence.Summands

universe u d d'

/-- **Stacks 08CE.** Both summands of a pseudo-coherent binary biproduct in `D(O_X)` are
pseudo-coherent.

Pseudo-coherence is `m`-pseudo-coherence in every degree, by
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall`, and in each degree the two summands
are `m`-pseudo-coherent by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_biprod`. -/
@[stacks 08CE "pseudo-coherent, both summands"]
theorem isPseudoCoherent_of_biprod {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    [∀ V : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict V.isOpenEmbedding))]
    (A B : DerivedCategory (OXMod.{u, u} X))
    (h : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (A ⊞ B)) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent A ∧
      AlgebraicGeometry.RingedSpace.IsPseudoCoherent B :=
  by
  have key := fun m => AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_biprod m
    ((AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall (A ⊞ B)).1 h m)
  rw [AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall A,
    AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall B]
  exact forall_and.1 key

end Stacks.PseudoCoherence.Summands

end
