module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenCoarserSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteAffineRefinement

/-!
# Finite affine refinements on the big étale site carried by a big fppf site

Let `B` be a chosen big fppf site and let `AlgebraicGeometry.etaleCovering B` be its étale
subcollection of **Stacks 03FF**: the families selected by `B` which are étale coverings. This
file proves that every covering sieve of an object of `B` whose underlying scheme is affine
contains a selected étale covering family which is **finite** and whose members are again affine.

That is **Stacks 0218** — an étale covering of an affine scheme has a finite refinement by
affines — for the étale subcollection of a big fppf site, and it is the base-level input from
which condition (2) of **Stacks 0GN4** for the étale site of **Stacks 06TP** is read off in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyEtaleAffineRefinement.lean`, exactly as
`AlgebraicGeometry.exists_standardFppf_refinement` (Stacks 021P) is its fppf counterpart.

## Main results

* `AlgebraicGeometry.exists_finite_affine_etaleCovering_le_of_mem_etaleTopology`: a covering sieve
  of `AlgebraicGeometry.etaleTopology B` at an object with affine underlying scheme contains a
  finite selected étale covering family by objects with affine underlying scheme.

## Implementation notes

The geometric content is not reproved. `AlgebraicGeometry.BigFppfSite.toBigEtaleSite` presents the
étale subcollection as a big étale site on the *same* size-bounded category of schemes — same
cutoff, same covering bound — and
`AlgebraicGeometry.BigFppfSite.toBigEtaleSite_isCovering_iff` identifies its covering families
with `AlgebraicGeometry.etaleCovering B`. So
`AlgebraicGeometry.BigEtaleSite.exists_finite_affine_refinement`, which is the refinement step for
a big étale site, applies verbatim; passing through it rather than through the scheme-level
`AlgebraicGeometry.finite_affine_refinement_etaleCover` is what keeps the refinement *selected*,
the cardinality bound of the chosen system included.

What remains is to turn the refinement relation into containment in the sieve: a member of the
refinement factors through a member of the family one started with, which lies in the sieve, so
`CategoryTheory.Sieve.downward_closed` applies.

## References

* [Stacks Project, Tag 0218](https://stacks.math.columbia.edu/tag/0218)
* [Stacks Project, Tag 021P](https://stacks.math.columbia.edu/tag/021P)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks 0218 for the étale subcollection of a big fppf site.** A covering sieve of the big
étale topology `AlgebraicGeometry.etaleTopology B` at an object `X` whose underlying scheme is
affine contains a selected étale covering family of `X` which is finite and whose members again
have affine underlying scheme.

This is the étale analogue of `AlgebraicGeometry.exists_standardFppf_refinement` (Stacks 021P) on
the same category, and it is proved by reading the étale subcollection as the big étale site
`AlgebraicGeometry.BigFppfSite.toBigEtaleSite` and applying
`AlgebraicGeometry.BigEtaleSite.exists_finite_affine_refinement` there; see the module
documentation. -/
@[stacks 0218 "for the étale subcollection of a big fppf site, inside a covering sieve"]
theorem exists_finite_affine_etaleCovering_le_of_mem_etaleTopology (B : BigFppfSite.{u})
    {X : B.Schemes} (hX : IsAffine (B.inclusion.obj X))
    {R : Sieve X} (hR : R ∈ etaleTopology B X) :
    ∃ E : PreZeroHypercover.{u + 1} X, etaleCovering B ⟨X, E⟩ ∧ Finite E.I₀ ∧
      (∀ i, IsAffine (B.inclusion.obj (E.X i))) ∧ E.presieve₀ ≤ R.arrows := by
  obtain ⟨E, hE, hle⟩ := exists_etaleCovering_le_of_mem_etaleTopology B hR
  have hE' : B.toBigEtaleSite.IsCovering ⟨X, E⟩ :=
    (BigFppfSite.toBigEtaleSite_isCovering_iff B ⟨X, E⟩).mpr hE
  let _ : IsAffine (B.toBigEtaleSite.inclusion.obj X) := hX
  obtain ⟨F, hF, hfin, haff, hrefine, -⟩ :=
    BigEtaleSite.exists_finite_affine_refinement B.toBigEtaleSite X E hE'
  refine ⟨F, (BigFppfSite.toBigEtaleSite_isCovering_iff B ⟨X, F⟩).mp hF, hfin, haff, ?_⟩
  rw [Presieve.ofArrows_le_iff]
  intro i
  obtain ⟨j, g, hg⟩ := hrefine i
  exact hg ▸ R.downward_closed (hle _ _ ⟨j⟩) g

end AlgebraicGeometry

end
