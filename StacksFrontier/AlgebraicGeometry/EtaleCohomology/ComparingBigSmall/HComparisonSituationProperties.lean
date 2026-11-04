module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.HComparisonSituation
import StacksCore.Tactic.StacksAttribute

/-!
# The h and étale topologies satisfy the properties of the comparison situation

Let `B` be a big h site, so that its underlying category carries the h topology and, through
`AlgebraicGeometry.hAssociatedBigEtaleSite`, the étale topology. Take the proper morphisms as
the class `𝒫`, and over every object `X` the class `𝒜'_X` of abelian sheaves on `(Sch/X)_étale`
of the form `π_X⁻¹F` with `F` a torsion abelian sheaf on `X_étale`. This file records Stacks
0F0J: `𝒜'_X` is a weak Serre subcategory, and properties (0EZ4)–(0EZ8) of the comparison
situation of Stacks 0EZ3 hold for the comparison of the h topology with the étale topology.

## Main results

* `AlgebraicGeometry.BigHSite.exists_hEtaleCohomologyComparison` — **Stacks 0F0J**: there is a
  comparison situation `Stacks.ComparingTopologies.CohomologyComparison` whose finer topology is
  the h topology of `B`, whose coarser topology is the étale topology, whose distinguished class
  is the class of proper morphisms and whose classes `𝒜'_X` are the sheaves `π_X⁻¹F` with `F`
  torsion.

## Implementation notes

A value of `Stacks.ComparingTopologies.CohomologyComparison` consists of the two topologies,
the class `𝒫` and the classes `𝒜'_X`, together with proofs of the site axioms, of the weak Serre
property of every `𝒜'_X` and of properties (0EZ4)–(0EZ8). Once these four data are fixed to be
the ones of the statement, the existence of such a value is exactly the assertion of the lemma.
The value is `AlgebraicGeometry.hEtaleCohomologyComparison`, built from

* the weak Serre property, property (0EZ4) and property (0EZ5), proved for every topology finer
  than the étale topology in `AlgebraicGeometry.properEtaleCohomologyComparison`;
* étale coverings are h coverings, `AlgebraicGeometry.BigHSite.etalePrecoverage_le_precoverage`;
* property (0EZ6), from Stacks 0EW8,
  `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_h_and_isIso_unit`;
* property (0EZ7), from Stacks 0DDJ (2) and the proper base change theorem Stacks 095T,
  `AlgebraicGeometry.BigHSite.properDirectImageComparison`;
* property (0EZ8), from Stacks 0ETU and 0ETW, `AlgebraicGeometry.BigHSite.exists_properRefinement`.

The classes `𝒜'_X` live on the localization of the coarser topology of the situation, so their
identification with `AlgebraicGeometry.smallEtaleTorsionPullbackClass` is stated as a
heterogeneous equality, the two ambient categories being equal by the identification of the
coarser topology.

## References

* [Stacks Project, Tag 0F0J](https://stacks.math.columbia.edu/tag/0F0J)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigHSite

/-- **Stacks 0F0J.** Consider the comparison of the h topology of a big h site `B` with the étale
topology on the same category of schemes. Let `𝒫` be the class of proper morphisms, and for `X`
in the site let `𝒜'_X ⊂ Ab((Sch/X)_étale)` be the full subcategory of sheaves of the form
`π_X⁻¹F` with `F` a torsion abelian sheaf on `X_étale`. Then `𝒜'_X` is a weak Serre subcategory
and properties (0EZ4)–(0EZ8) of the comparison situation of Stacks 0EZ3 hold: there is a
comparison situation with the h topology as finer topology, the étale topology as coarser
topology, `𝒫` as distinguished class and the `𝒜'_X` as weak Serre classes. -/
@[stacks 0F0J]
public theorem exists_hEtaleCohomologyComparison (B : BigHSite.{u}) :
    ∃ S : Stacks.ComparingTopologies.CohomologyComparison (hAssociatedBigEtaleSite B).Scheme,
      S.fineCoverage = B.precoverage ∧
      S.coarseCoverage = (hAssociatedBigEtaleSite B).precoverage ∧
      S.morphismProperty = (fun _ _ f => IsProper ((hAssociatedBigEtaleSite B).inclusion.map f)) ∧
      ∀ X : (hAssociatedBigEtaleSite B).Scheme,
        HEq (S.weakSerre X)
          (smallEtaleTorsionPullbackClass (hAssociatedBigEtaleSite B) X
            ((hAssociatedBigEtaleSite B).topology.over X)) :=
  ⟨hEtaleCohomologyComparison B, rfl, rfl, rfl, fun _ => HEq.rfl⟩

end BigHSite

end AlgebraicGeometry

end
