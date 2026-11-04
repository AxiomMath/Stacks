module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperDirectImageComparisonOfBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperEtaleComparisonSituation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.HSitePrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopologyEtaleComparisonProperBaseChange

/-!
# The h topology and the étale topology form a comparison situation

Let `B` be a chosen big h site. Its underlying category carries the h topology and, through
`AlgebraicGeometry.hAssociatedBigEtaleSite`, the étale topology. With the proper morphisms as
distinguished class and the sheaves `π_X⁻¹F` pulled back from torsion abelian sheaves on the
small étale sites as the classes `𝒜'_X`, the pair (h, étale) satisfies the assumptions of the
comparison situation of Stacks 0EZ3; this is the content of Stacks 0F0J.

The étale-side part of the situation is `AlgebraicGeometry.properEtaleCohomologyComparison`.
The three h-specific inputs are proved:

* étale coverings are h coverings, `AlgebraicGeometry.BigHSite.etalePrecoverage_le_precoverage`;
* the h sheaf condition for `π_X⁻¹F` (property 0EZ6), Stacks 0EW8,
  `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_h_and_isIso_unit`;
* the refinement of an h covering by an étale covering, a single proper surjection over each
  member and an étale covering of its source (property 0EZ8),
  `AlgebraicGeometry.BigHSite.exists_properRefinement`;

and the comparison of higher direct images along proper morphisms (property 0EZ7, from Stacks
0DDJ (2)) is supplied by the proper base change theorem, Stacks 095T,
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`, through
`AlgebraicGeometry.properDirectImageComparison_of_cohomologyCommutesWithBaseChange`.

## Main definitions

* `AlgebraicGeometry.BigHSite.properDirectImageComparison` — property 0EZ7 for the h site, from
  Stacks 095T.
* `AlgebraicGeometry.hEtaleCohomologyComparison` — the comparison situation of Stacks 0EZ3 for
  the h and étale topologies of a big h site.

## Implementation notes

The registration of Stacks 0F0J belongs to the declaration that states its clauses; the
structure value here is what the comparison results for the h site are instances of.

## References

* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0EW8](https://stacks.math.columbia.edu/tag/0EW8)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 0F0J](https://stacks.math.columbia.edu/tag/0F0J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Property 0EZ7 for a big h site.** Along a proper morphism `f : X ⟶ Y` of the associated big
étale site, `R^i f_{big,*}(π_X⁻¹F) ≅ π_Y⁻¹(R^i f_{small,*}F)` for every torsion abelian sheaf `F`
on `X_étale` and every `i`, by the proper base change theorem, Stacks 095T. -/
public theorem BigHSite.properDirectImageComparison (B : BigHSite.{u}) :
    ProperDirectImageComparison (hAssociatedBigEtaleSite B) :=
  properDirectImageComparison_of_cohomologyCommutesWithBaseChange _
    fun f _ => Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f

/-- **The comparison situation for the h and étale topologies.** For a big h site `B`, the
comparison of the h topology with the étale topology on its underlying category, with the proper
morphisms as distinguished class `𝒫` and, over every object `X`, the class `𝒜'_X` of abelian
sheaves `π_X⁻¹F` on `(Sch/X)_étale` with `F` a torsion abelian sheaf on `X_étale`, satisfies the
assumptions (0EZ4)–(0EZ8) of the comparison situation of Stacks 0EZ3, and `𝒜'_X` is a weak Serre
subcategory. -/
public def hEtaleCohomologyComparison (B : BigHSite.{u}) :
    Stacks.ComparingTopologies.CohomologyComparison (hAssociatedBigEtaleSite B).Scheme :=
  properEtaleCohomologyComparison (hAssociatedBigEtaleSite B) B.precoverage
    (BigHSite.etalePrecoverage_le_precoverage B)
    (fun X F => (smallEtaleInverseImage_isSheaf_h_and_isIso_unit B X.1 X.2 F).1)
    (BigHSite.properDirectImageComparison B)
    (BigHSite.exists_properRefinement B)

section Fields

variable (B : BigHSite.{u})

/-- The finer topology of `hEtaleCohomologyComparison` is the h topology of `B`. -/
@[simp]
public theorem hEtaleCohomologyComparison_fineCoverage :
    (hEtaleCohomologyComparison B).fineCoverage = B.precoverage := rfl

/-- The coarser topology of `hEtaleCohomologyComparison` is the étale topology of `B`. -/
@[simp]
public theorem hEtaleCohomologyComparison_coarseCoverage :
    (hEtaleCohomologyComparison B).coarseCoverage = (hAssociatedBigEtaleSite B).precoverage := rfl

/-- The distinguished class of `hEtaleCohomologyComparison` is the class of proper morphisms. -/
@[simp]
public theorem hEtaleCohomologyComparison_morphismProperty :
    (hEtaleCohomologyComparison B).morphismProperty =
      fun _ _ f => IsProper ((hAssociatedBigEtaleSite B).inclusion.map f) := rfl

/-- The class `𝒜'_X` of `hEtaleCohomologyComparison` consists of the sheaves `π_X⁻¹F` with `F` a
torsion abelian sheaf on `X_étale`. -/
@[simp]
public theorem hEtaleCohomologyComparison_weakSerre (X : (hAssociatedBigEtaleSite B).Scheme) :
    (hEtaleCohomologyComparison B).weakSerre X =
      smallEtaleTorsionPullbackClass (hAssociatedBigEtaleSite B) X
        ((hAssociatedBigEtaleSite B).topology.over X) := rfl

end Fields

end AlgebraicGeometry

end
