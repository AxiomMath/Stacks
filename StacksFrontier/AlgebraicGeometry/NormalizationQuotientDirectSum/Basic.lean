module

public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.StalkVanishing
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotientDirectSum.Decomposition
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotientDirectSum.RegularLocusOpen

/-!
# The normalization quotient of a one-dimensional Nagata scheme is a sum of skyscrapers

For a reduced Nagata scheme `X` of dimension one, the quotient of the pushforward of the
structure sheaf of the normalization by the structure sheaf of `X` is the direct sum of the
skyscraper modules of its own stalks at the singular points of `X`.  This is assertion (2) of
[Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R).

## Main results

* `normalizationQuotientIsoCoproductSkyscraper`: the normalization quotient of a reduced
  one-dimensional Nagata scheme is isomorphic to the direct sum of the skyscraper modules of its
  stalks at the singular points.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum

open Stacks.AlgebraicGeometry.NormalizationQuotient

/-- For a reduced Nagata scheme `X` of dimension one, the normalization quotient of `X` is
isomorphic to the direct sum, over the singular points `x` of `X`, of the skyscraper modules at
`x` of its stalks. -/
@[stacks 0C1R "quotient_sheaf"]
public theorem normalizationQuotientIsoCoproductSkyscraper (X : Scheme.{u}) [IsReduced X]
    (hX : IsNagataScheme X) (hdim : topologicalKrullDim X = 1) :
    Nonempty
      (normalizationQuotient X
          (Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme
            X hX) ≅
        ∐ fun x : singularLocus X =>
          skyscraperModule X x.1
            (normalizationQuotientStalk X
              (Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme
                X hX) x.1)) := by
  have : DiscreteTopology (singularLocus X) := discreteTopology_singularLocus X hX hdim
  exact sheaf_iso_coproduct_skyscraper_of_closed_discrete_support _ (singularLocus X)
    (isOpen_regularLocus X hX hdim).isClosed_compl fun y hy =>
      (isZero_normalizationQuotientStalk_iff_regular X hX hdim y).mpr (Classical.not_not.mp hy)

end Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum

end
