module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.NormalizationReductionData
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSiteChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Reduction

/-!
# Tag 0BB3: the normalization of an algebraic space and of its reduction

Let `X` be an algebraic space over a scheme `S` satisfying the equivalent conditions of
Tag 0BB1, let `ν_X : X^ν ⟶ X` be its normalization, the morphism
`AlgebraicGeometry.Space.normalization` of Tag 0BB2, and let `X_red` be its reduction, the
subspace `AlgebraicGeometry.Space.reduction` of Tag 047X. Tag 0BB3 says that `ν_X` factors
through `X_red ⟶ X` and that the factorization `X^ν ⟶ X_red` is the normalization of `X_red`.

Both are stated here for the *constructed* objects: the normalization of `X` and the
normalization of `X_red` are the morphisms Tag 0BB2 names, and the reduction is the one
Tag 047X names. No normalization datum is supplied by the caller. That `X_red` again satisfies
the conditions of Tag 0BB1, so that its normalization is defined at all, is proved here too.

## Main definitions

* `AlgebraicGeometry.Space.normalizationToReduction`: the factorization `X^ν ⟶ X_red` of the
  normalization morphism through the reduction.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_reduction` and
  `AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_reduction`: the reduction is an
  algebraic space, and it satisfies the conditions of Tag 0BB1 whenever `X` does.
* `AlgebraicGeometry.Space.existsUnique_comp_ι_reduction_eq_normalization`: **Tag 0BB3, first
  assertion** — the normalization morphism factors, uniquely, through the reduction.
* `AlgebraicGeometry.Space.existsUnique_iso_normalization_reduction`: **Tag 0BB3, second
  assertion** — the factorization is the normalization of the reduction: it is carried to the
  normalization morphism `ν_{X_red}` of Tag 0BB2 by a unique isomorphism over `X_red`.
* `AlgebraicGeometry.Space.normalizationDataOfReduction` and
  `AlgebraicGeometry.Space.normalizationDataOfReduction_hom`: the second assertion in the form of
  the defining property of a normalization, normalization data for `X_red` whose normalization
  morphism is the factorization.

## Implementation notes

The mathematics is in `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization`, where it
is proved for an arbitrary normalization datum of `X` and an arbitrary closed subspace carrying
every point of `X`: the factorization is
`AlgebraicGeometry.Space.NormalizationData.existsUnique_lift_hom_reduction`, the chart condition
making the factorization normalization data of the subspace is
`AlgebraicGeometry.Space.NormalizationData.onReduction`, and the comparison with any normalization
datum of the subspace is
`AlgebraicGeometry.Space.NormalizationData.existsUnique_iso_of_hom_reduction`. This file
instantiates them at the data Tag 0BB2 constructs for `X` and for `X_red`, and at the reduction
of Tag 047X, which is a closed subspace carrying every point by
`AlgebraicGeometry.Space.isAlgebraicSpaceStructure_reduction`. The proof of Tag 0BB3 in the
source reduces étale locally to the scheme case, Tag 035O; the proof here goes instead through
the universal property of the normalization, Tag 0BB4 part (4), as explained in that file.

## References

* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 0BB2](https://stacks.math.columbia.edu/tag/0BB2)
* [Stacks Project, Tag 0BB3](https://stacks.math.columbia.edu/tag/0BB3)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The reduction of an algebraic space is an algebraic space. -/
theorem isAlgebraicSpace_reduction {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    IsAlgebraicSpace B S hS (reduction B S hS X hX).toFunctor :=
  (isAlgebraicSpaceStructure_reduction B S hS X hX).1.1

/-- **The reduction of an algebraic space satisfying the conditions of Tag 0BB1 satisfies them
again.** The reduction is a closed subspace carrying every point, and such a subspace has charts
homeomorphic to those of the space, by
`AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_range_pointsMap_eq_univ`. -/
theorem hasLocallyFiniteIrreducibleComponents_reduction
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X) :
    HasLocallyFiniteIrreducibleComponents B S hS (reduction B S hS X hX).toFunctor :=
  hasLocallyFiniteIrreducibleComponents_of_range_pointsMap_eq_univ B S hS hX hfin _
    (isAlgebraicSpaceStructure_reduction B S hS X hX).1
    (range_pointsMap_ι_reduction B S hS X hX)

/-- **Stacks 0BB3, the factorization.** Let `X` be an algebraic space over `S` satisfying the
equivalent conditions of Tag 0BB1. The normalization morphism `ν_X : X^ν ⟶ X` of Tag 0BB2
factors through the reduction `X_red ⟶ X` of Tag 047X, and the factorization is unique.

This is `AlgebraicGeometry.Space.NormalizationData.existsUnique_lift_hom_reduction` at the
normalization datum Tag 0BB2 constructs and at the reduction. -/
@[stacks 0BB3 "the normalization morphism ν_X of Tag 0BB2 factors uniquely through the \
reduction X_red ⟶ X"]
theorem existsUnique_comp_ι_reduction_eq_normalization
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X) :
    ∃! g : normalizationPresheaf B S hS hX hfin ⟶ (reduction B S hS X hX).toFunctor,
      g ≫ (reduction B S hS X hX).ι = normalization B S hS hX hfin :=
  (normalizationData B S hS hX hfin).existsUnique_lift_hom_reduction hX _
    (isAlgebraicSpaceStructure_reduction B S hS X hX).1
    (range_pointsMap_ι_reduction B S hS X hX)

/-- **The factorization `X^ν ⟶ X_red` of the normalization morphism through the reduction**, the
unique morphism of `AlgebraicGeometry.Space.existsUnique_comp_ι_reduction_eq_normalization`. -/
def normalizationToReduction {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hfin : HasLocallyFiniteIrreducibleComponents B S hS X) :
    normalizationPresheaf B S hS hX hfin ⟶ (reduction B S hS X hX).toFunctor :=
  (existsUnique_comp_ι_reduction_eq_normalization B S hS hX hfin).choose

/-- The factorization of the normalization morphism through the reduction is a factorization. -/
@[reassoc (attr := simp)]
theorem normalizationToReduction_ι {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hfin : HasLocallyFiniteIrreducibleComponents B S hS X) :
    normalizationToReduction B S hS hX hfin ≫ (reduction B S hS X hX).ι =
      normalization B S hS hX hfin :=
  (existsUnique_comp_ι_reduction_eq_normalization B S hS hX hfin).choose_spec.1

/-- A morphism from the normalization to the reduction which factors the normalization morphism
is `AlgebraicGeometry.Space.normalizationToReduction`. -/
theorem eq_normalizationToReduction {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (g : normalizationPresheaf B S hS hX hfin ⟶ (reduction B S hS X hX).toFunctor)
    (hg : g ≫ (reduction B S hS X hX).ι = normalization B S hS hX hfin) :
    g = normalizationToReduction B S hS hX hfin :=
  (existsUnique_comp_ι_reduction_eq_normalization B S hS hX hfin).choose_spec.2 g hg

/-- **Stacks 0BB3, the factorization is the normalization of the reduction.** Let `X` be an
algebraic space over `S` satisfying the equivalent conditions of Tag 0BB1, so that its reduction
`X_red` satisfies them too
(`AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_reduction`). Then the
factorization `X^ν ⟶ X_red` of the normalization morphism through the reduction is the
normalization `ν_{X_red} : X_red^ν ⟶ X_red` of Tag 0BB2: there is a unique isomorphism
`X^ν ≅ X_red^ν` over `X_red`.

Nothing is assumed about the normalization of `X_red`: it is the one Tag 0BB2 constructs. The
statement is `AlgebraicGeometry.Space.NormalizationData.existsUnique_iso_of_hom_reduction` at the
two normalization data Tag 0BB2 constructs, for `X` and for `X_red`. -/
@[stacks 0BB3 "the factorization X^ν ⟶ X_red is the normalization ν_{X_red} of Tag 0BB2: they \
are isomorphic over X_red by a unique isomorphism"]
theorem existsUnique_iso_normalization_reduction {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hfin : HasLocallyFiniteIrreducibleComponents B S hS X) :
    ∃! e : normalizationPresheaf B S hS hX hfin ≅
        normalizationPresheaf B S hS (isAlgebraicSpace_reduction B S hS hX)
          (hasLocallyFiniteIrreducibleComponents_reduction B S hS hX hfin),
      e.hom ≫ normalization B S hS (isAlgebraicSpace_reduction B S hS hX)
          (hasLocallyFiniteIrreducibleComponents_reduction B S hS hX hfin) =
        normalizationToReduction B S hS hX hfin :=
  (normalizationData B S hS hX hfin).existsUnique_iso_of_hom_reduction hX _
    (isAlgebraicSpaceStructure_reduction B S hS X hX).1
    (range_pointsMap_ι_reduction B S hS X hX) _ _ (normalizationToReduction_ι B S hS hX hfin)

/-- **The factorization `X^ν ⟶ X_red` as normalization data of the reduction.** This is the
second assertion of Tag 0BB3 in the form of the defining property of a normalization: the
normalization `X^ν` of `X`, with the factorization of `ν_X` through the reduction, is a
normalization datum for `X_red` — its base change along every étale scheme chart of `X_red` is
the normalization of that chart. It is
`AlgebraicGeometry.Space.NormalizationData.onReduction` at the datum Tag 0BB2 constructs. -/
def normalizationDataOfReduction {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hfin : HasLocallyFiniteIrreducibleComponents B S hS X) :
    NormalizationData B S hS (reduction B S hS X hX).toFunctor :=
  (normalizationData B S hS hX hfin).onReduction hX _
    (isAlgebraicSpaceStructure_reduction B S hS X hX).1
    (range_pointsMap_ι_reduction B S hS X hX)

/-- The normalization datum of the reduction carried by `X^ν` has `X^ν` as its space. -/
theorem normalizationDataOfReduction_space {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hfin : HasLocallyFiniteIrreducibleComponents B S hS X) :
    (normalizationDataOfReduction B S hS hX hfin).space = normalizationPresheaf B S hS hX hfin :=
  rfl

/-- The normalization morphism of the normalization datum of the reduction carried by `X^ν` is
the factorization `X^ν ⟶ X_red`. -/
theorem normalizationDataOfReduction_hom {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hfin : HasLocallyFiniteIrreducibleComponents B S hS X) :
    (normalizationDataOfReduction B S hS hX hfin).hom = normalizationToReduction B S hS hX hfin :=
  eq_normalizationToReduction B S hS hX hfin _
    ((normalizationData B S hS hX hfin).onReduction_hom_comp_ι hX _
      (isAlgebraicSpaceStructure_reduction B S hS X hX).1
      (range_pointsMap_ι_reduction B S hS X hX))

end AlgebraicGeometry.Space

end
