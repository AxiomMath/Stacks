module

public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CommonBigSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

/-!
# A big étale site on the schemes of a chosen big fppf site

Every big fppf site carries a big étale site on the same size-bounded category of schemes:
the cutoff and its cardinal properties are reused verbatim, and the bounded class of étale
covering families is produced by the set-sized-covering construction of Stacks 000X applied to
the étale coverings of that category.

## Main definitions

* `AlgebraicGeometry.bigEtaleSiteOfFppfSite` is the big étale site obtained from a big fppf
  site in this way. Its cutoff is that of the given fppf site, so it contains exactly the same
  schemes.

## Implementation notes

The étale covering families of the schemes below a cutoff satisfy the site axioms by
`AlgebraicGeometry.isSite_etaleCutoff`, and `exists_covBounded_isSite` then supplies a cardinal
bound on their index types for which the bounded families still form a site and still represent
every étale covering up to combinatorial equivalence. No initial schemes or initial coverings
are selected, which is why the corresponding fields are empty.

This is a *choice* of big étale site, made so that the comparison of Stacks 04KF can be applied
to a chart of an algebraic space over a big fppf site; by
`AlgebraicGeometry.Space.commonInclusion_initial` the comparison does not depend on it.
-/

@[expose] public section

open Cardinal CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The big étale site on the schemes of a chosen big fppf site: the same size cutoff, with a
bounded class of étale covering families chosen by Stacks 000X. -/
noncomputable def bigEtaleSiteOfFppfSite (B : BigFppfSite.{u}) : BigEtaleSite.{u} := by
  classical
  have hsmall : Small.{u + 1} (∅ : Set (Covering (SchemeBelow B.cutoff))) := inferInstance
  let hBounded := exists_covBounded_isSite (IsEtaleCovering (κ := B.cutoff))
    (isSite_etaleCutoff B.cutoff) (∅ : Set (Covering (SchemeBelow B.cutoff)))
    (by intro 𝒰 h𝒰; cases h𝒰)
  let κ := Classical.choose hBounded
  let hBounded' := Classical.choose_spec hBounded
  let α := Classical.choose hBounded'
  have hParts := Classical.choose_spec hBounded'
  exact
    { S₀ := ∅
      small_S₀ := inferInstance
      cutoff := B.cutoff
      aleph0_lt_cutoff := B.aleph0_lt_cutoff
      cutoff_isStrongPrelimit := B.cutoff_isStrongPrelimit
      aleph0_lt_cutoff_cof := B.aleph0_lt_cutoff_cof
      mem_cutoff_of_mem := by simp
      initialCoverings := ∅
      small_initialCoverings := inferInstance
      initial_objects_mem := by simp
      initialCoverings_etale := by simp
      coveringBound := κ
      coveringOrdinal := α
      coveringOrdinal_isSuccLimit := hParts.1
      initialCoverings_bounded := by simp
      coverings_isSite := hParts.2.2.1
      exists_covering_rep := hParts.2.2.2 }

/-- The big étale site attached to a big fppf site has the same size cutoff, so it contains
every scheme the fppf site contains. -/
theorem bigEtaleSiteOfFppfSite_cutoff (B : BigFppfSite.{u}) :
    (bigEtaleSiteOfFppfSite B).cutoff = B.cutoff := rfl

end AlgebraicGeometry

end
