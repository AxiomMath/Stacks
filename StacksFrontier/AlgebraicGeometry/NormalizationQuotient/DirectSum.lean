module

public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.DimensionOne
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.SkyscraperDecomposition
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.StalkVanishing

/-!
# The normalization quotient of a curve is a sum of skyscrapers

Let `X` be a reduced Nagata scheme of dimension one with normalization `ν : X^ν ⟶ X`.  The
structure sheaf injects into `ν_* 𝒪_{X^ν}`, and the quotient `ν_* 𝒪_{X^ν} / 𝒪_X` is the direct
sum, over the singular points of `X`, of the skyscraper sheaves of its stalks there.  That is
part (2) of [Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R).

The three assertions of that part are proved in three different places, and this file is where
the tag is attached to all of them: the injectivity is
`Stacks.AlgebraicGeometry.Normalization.mono_toRingCatSheafHom_normalization`, which needs only
reducedness; the pointwise nonvanishing criterion is
`normalizationQuotientStalk_nonzero_iff_mem_singularLocus`; and the global decomposition is
proved here, by feeding the two geometric facts about the singular locus of a one-dimensional
reduced Nagata scheme — that it is closed and discrete — into the sheaf-theoretic
`sheaf_iso_coproduct_skyscraper_of_closed_discrete_support`.

## Main results

* `normalizationQuotient_iso_coproduct_skyscraperModule`.

## Implementation notes

The decomposition is stated as `Nonempty (… ≅ ∐ …)`: the isomorphism is assembled from a
sheafification and is not canonical.  Its index type is the singular locus as a subtype, so no
finiteness of the singular locus is asserted — and none is available, a one-dimensional scheme
being allowed infinitely many singular points, finitely many on each affine open.

The dimension hypothesis is `topologicalKrullDim X = 1`, as in the source, even though the
inputs are proved for `≤ 1`: the statement is the source's.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotient

open Stacks.AlgebraicGeometry.Normalization (finite_irreducibleComponents_of_isNagataScheme)

/-- **Stacks Project, Tag 0C1R(2).** For a reduced Nagata scheme of dimension one the quotient
`ν_* 𝒪_{X^ν} / 𝒪_X` is the direct sum of the skyscraper sheaves of its stalks at the singular
points: the quotient's stalk vanishes at every regular point, and the singular locus is closed
and discrete. -/
@[stacks 0C1R "quotient_sheaf"]
public theorem normalizationQuotient_iso_coproduct_skyscraperModule (X : Scheme.{u})
    [IsReduced X] (hX : IsNagataScheme X) (hdim : topologicalKrullDim X = 1) :
    Nonempty
      (normalizationQuotient X (finite_irreducibleComponents_of_isNagataScheme X hX) ≅
        ∐ fun z : singularLocus X =>
          skyscraperModule X z.1
            (normalizationQuotientStalk X
              (finite_irreducibleComponents_of_isNagataScheme X hX) z.1)) := by
  let _ : DiscreteTopology (singularLocus X) :=
    discreteTopology_singularLocus_of_isNagataScheme X hX hdim.le
  exact sheaf_iso_coproduct_skyscraper_of_closed_discrete_support _ (singularLocus X)
    (isOpen_regularLocus_of_isNagataScheme X hX hdim.le).isClosed_compl
    fun y hy => (isZero_normalizationQuotientStalk_iff_regular X hX hdim y).mpr
      (Classical.not_not.mp hy)

end Stacks.AlgebraicGeometry.NormalizationQuotient

add_to_stacks 0C1R "quotient_sheaf"
  Stacks.AlgebraicGeometry.Normalization.mono_toRingCatSheafHom_normalization
open Stacks.AlgebraicGeometry.NormalizationQuotient in
add_to_stacks 0C1R "quotient_sheaf" normalizationQuotientStalk_nonzero_iff_mem_singularLocus

end
