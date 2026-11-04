module

public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries

/-!
# `dim_k H⁰(X, 𝒪_X) = 1` on a scheme whose global functions are the constants

For a scheme `X` over a field `k` whose structure morphism induces an isomorphism of `k` with
the ring of global functions, the degree-zero cohomology of the structure sheaf is a line.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_unit_zero_eq_one`.

## Implementation notes

This is the public form of a lemma that is `private` in
`StacksFrontier/AlgebraicGeometry/Curves/LinearSeries.lean`; it is stated separately because
`AlgebraicGeometry.CohenMacaulayCurveSituation` carries exactly its hypothesis as an instance
and the private copy cannot be cited. The proof is the one there, with the private isomorphism
`H⁰(X, ℱ) ≅ Γ(ℱ, ⊤)` of that file replaced by the public
`AlgebraicGeometry.cohomologyOverFieldZeroLinearIso`, which is the same functor applied to the
same natural isomorphism.

**It lives in a module of its own** so that the consumers in
`Curves/VanishingResults/` can reach it without the import closure of the Euler characteristic.
It was separated when that closure still declared `AlgebraicGeometry.supp_subset_of_mono` a
second time, which blocked the import; that duplicate has since been collapsed onto
`StacksFrontier/AlgebraicGeometry/TwistedSheaf/EmbeddedPointStep.lean`, so the separation is now
only a matter of keeping the closure small.

## References

* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

end AlgebraicGeometry

end
