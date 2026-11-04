module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.DegreeSeparable
public import StacksFrontier.AlgebraicGeometry.Curves.NormalizationClosedFibre
public import StacksFrontier.RingTheory.Nagata.Defs

/-!
# The normalization of a node has one or two maximal ideals

Let `A` be a nodal Nagata local algebra over a field `k`, and let
`A' = integralClosure A (FractionRing A)` be its normalization inside its total ring of
fractions. Then `A'` has exactly one or two maximal ideals.

The proof composes two facts and needs no case distinction between a split and a non-split node.
Because `A'` is integral over the local ring `A`, every maximal ideal of `A'` contains `𝔪_A A'`,
so the maximal ideals of `A'` are those of the closed fibre
`Stacks.Curves.quadraticAlgebra A = A' ⧸ 𝔪_A A'`; and that fibre is two-dimensional over the
residue field of `A` (`Stacks.Curves.finrank_quadraticAlgebra_of_isNodalAlgebra`, Stacks Tag
0CBT), so it has at most two maximal ideals by the Chinese remainder theorem and at least one
because it is nonzero. The two cases of the source correspond to whether the quadratic
polynomial of the node is irreducible over the residue field or splits, but neither the
statement nor the proof mentions them.

## Main definitions

There are no definitions.

## Main results

* `Stacks.Curves.encard_maximalSpectrum_integralClosure_fractionRing_eq_one_or_two` — the
  normalization of a nodal Nagata local algebra has one or two maximal ideals.

## Implementation notes

The Nagata hypothesis is used only for the Noetherian property it carries, which is what the
quadratic-relation description of the closed fibre needs; it is kept because it is the
hypothesis of the source.

No `@[stacks]` tag is carried here.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-- **The normalization of a nodal Nagata local algebra in its total ring of fractions has one
or two maximal ideals.** -/
@[stacks 0C4A "number of maximal ideals"]
public theorem encard_maximalSpectrum_integralClosure_fractionRing_eq_one_or_two
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hA : IsNagataRing A) (hNodal : IsNodalAlgebra k A) :
    Set.encard (Set.univ : Set (MaximalSpectrum ↥(integralClosure A (FractionRing A)))) = 1 ∨
      Set.encard
        (Set.univ : Set (MaximalSpectrum ↥(integralClosure A (FractionRing A)))) = 2 := by
  have : IsNoetherianRing A := hA.isNoetherianRing
  have hrank := finrank_quadraticAlgebra_of_isNodalAlgebra k A hNodal
  have : Module.Finite (ResidueField A) (quadraticAlgebra A) :=
    finite_quadraticAlgebra_of_isNodalAlgebra k A hNodal
  exact encard_maximalSpectrum_eq_one_or_two_of_finrank_closedFibre_eq_two (A := A)
    (ResidueField A)
    (Ideal.Quotient.mk
      ((maximalIdeal A).map (algebraMap A ↥(integralClosure A (FractionRing A)))))
    Ideal.Quotient.mk_surjective Ideal.mk_ker hrank

end Stacks.Curves

end
