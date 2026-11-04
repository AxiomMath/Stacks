module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.InvertsQuasiIsomorphisms
public import StacksFrontier.CategoryTheory.Localization.FractionCriterion

/-!
# The equivalence `S⁻¹K^b(A) = D_perf(O_X)`, reduced to three statements about `K^b(A)`

Tag 0F8I is `CategoryTheory.Functor.IsLocalization` for the canonical functor
`K^b(A) ⥤ D_perf(O_X)`. Its first field, that the functor inverts `S`, is
`Stacks.Perfect.BoundedLocallyFreeComplexes.quasiIsomorphisms_isInvertedBy_perfectComplexFunctor`
and holds with no hypothesis on `X`; its second field is that the induced functor
`S⁻¹K^b(A) ⥤ D_perf(O_X)` is an equivalence.

The whole predicate follows from exactly three statements about the canonical functor, one for
each way a functor can fail to be an equivalence, by the general criterion
`CategoryTheory.Localization.isLocalization_of_rightFractions`.  The three are the
content of Tags 0F8F, 0F8G and 0F8H read on the two categories rather than on complexes:

* `hess`, essential surjectivity — every perfect object of `D(O_X)` is isomorphic to the image
  of an object of `K^b(A)`, which is [Stacks, Tag 0F8F];
* `hfull`, that every morphism of `D_perf(O_X)` between images is the image of a right fraction
  of `K^b(A)`, which is the roof of [Stacks, Tag 0F8G];
* `hfaithful`, that two morphisms of `K^b(A)` with the same image are equalized by
  precomposition with a quasi-isomorphism, which is [Stacks, Tag 0F8H].

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.quasiIsomorphisms_hasRightCalculusOfFractions`: the
  system `S` has a right calculus of fractions, being saturated.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectComplexFunctor_isLocalization`: the three
  statements above give the localization predicate.

## Implementation notes

The three hypotheses are deliberately stated at the level of the two categories and not at the
level of complexes.  For complexes, Tags 0F8F, 0F8G and 0F8H are
`exists_boundedFiniteLocallyFree_iso_of_affineDiagonal`,
`exists_boundedFiniteLocallyFree_roof_of_affineDiagonal` and
`exists_boundedFiniteLocallyFree_homotopy_of_affineDiagonal`, each on a quasi-compact
quasi-separated scheme with the resolution property and affine diagonal — and the passage from a
bounded complex of finite locally free modules to an object of `K^b(A)`, and from a map of such
complexes to a morphism of `K^b(A)`, is a separate step: it has to read
`CategoryTheory.ObjectProperty.strictMap` to recover a complex from an object, and transport
`DerivedCategory.Q` to `DerivedCategory.Qh` along `DerivedCategory.quotientCompQhIso`.  Keeping
that step out of this file is what makes this file independent of [Stacks, Tag 0F8C], and so of
the converse of Tag 0F8B, which the scheme-level forms of those three tags go through.

## References

* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 0F8G](https://stacks.math.columbia.edu/tag/0F8G)
* [Stacks Project, Tag 0F8H](https://stacks.math.columbia.edu/tag/0F8H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace StrictlyPerfect
  Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

section Scheme

attribute [local instance] HasDerivedCategory.standard

/-- **The system `S` of quasi-isomorphisms of `K^b(A)` has a right calculus of fractions.**  A
saturated multiplicative system has both calculi of fractions, and `S` is saturated by
`Stacks.Perfect.BoundedLocallyFreeComplexes.quasiIsomorphisms_isSaturated`. -/
instance quasiIsomorphisms_hasRightCalculusOfFractions (X : Scheme.{u}) :
    (quasiIsomorphisms X).HasRightCalculusOfFractions :=
  (quasiIsomorphisms_isSaturated X).hasRightCalculusOfFractions

/-- **The canonical functor presents `D_perf(O_X)` as `S⁻¹K^b(A)` as soon as it is essentially
surjective, computes every morphism as a right fraction, and is faithful up to precomposition
with a quasi-isomorphism.**  The three hypotheses are Tags 0F8F, 0F8G and 0F8H read on `K^b(A)`
and `D_perf(O_X)`; the deduction is
`CategoryTheory.Localization.isLocalization_of_rightFractions`, `S` having a right calculus of
fractions because it is saturated. -/
theorem perfectComplexFunctor_isLocalization (X : Scheme.{u})
    (hess : (perfectComplexFunctor X).EssSurj)
    (hfull : ∀ (a b : BoundedFiniteLocallyFreeHomotopyCategory X)
      (g : (perfectComplexFunctor X).obj a ⟶ (perfectComplexFunctor X).obj b),
      ∃ (c : BoundedFiniteLocallyFreeHomotopyCategory X) (s : c ⟶ a)
        (hs : quasiIsomorphisms X s) (f : c ⟶ b),
        g = (MorphismProperty.RightFraction.mk s hs f).map (perfectComplexFunctor X)
          (quasiIsomorphisms_isInvertedBy_perfectComplexFunctor X))
    (hfaithful : ∀ ⦃a b : BoundedFiniteLocallyFreeHomotopyCategory X⦄ (u v : a ⟶ b),
      (perfectComplexFunctor X).map u = (perfectComplexFunctor X).map v →
        ∃ (c : BoundedFiniteLocallyFreeHomotopyCategory X) (t : c ⟶ a),
          quasiIsomorphisms X t ∧ t ≫ u = t ≫ v) :
    (perfectComplexFunctor X).IsLocalization (quasiIsomorphisms X) :=
  haveI := hess
  CategoryTheory.Localization.isLocalization_of_rightFractions _ _
    (quasiIsomorphisms_isInvertedBy_perfectComplexFunctor X) hfull hfaithful

end Scheme

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
