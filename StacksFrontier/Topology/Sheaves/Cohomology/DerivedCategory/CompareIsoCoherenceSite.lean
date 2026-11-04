module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsIsoOpenNaturalityDerived

/-!
# The restriction comparison of a ringed site, against the canonical factorizations

Let `X` be a ringed site and `g : W ⟶ V` an arrow of it.  The comparison
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso` identifies restriction to the
slice over `W` with restriction to the slice over `V` followed by restriction along `g`, on
unbounded derived categories.  This file records how that comparison interacts with the canonical
factorizations `CategoryTheory.Functor.mapDerivedCategoryFactors` of the three functors involved:
read at the class of a complex, the comparison turns the factorization of restriction in two
steps into the factorization of restriction in one.

## Implementation notes

The two spellings of the restriction of a complex in two steps —
`((SheafOfModules.overMap X.ringSheaf g).mapHomologicalComplex _).obj (restrictComplex X M V)`
and `restrictComplex X M W` — are the same complex, and `restrictComplex_overMap` says so.  It is
*not* economical to let the statement below identify them: that definitional identification costs
about 187000 heartbeats at the level of functors and about 196000 at the level of complexes,
against a per-declaration ceiling of 200000, so an equation whose two sides end at the two
spellings cannot be stated at all, however its proof is split.  The identification is therefore
**carried**, as the `CategoryTheory.eqToHom` of that one proof, and the statement below has
no definitional crossing in it; this is the same discipline the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsIsoOpenNaturality` record for the
rest of this cone.

## References

* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)

Tags covered: none.  This is a step of a proof, not a clause of a tag statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] hasSheafifyOver wEqualsLocallyBijectiveOver additiveOverMap
  preservesFiniteLimitsOverMap preservesFiniteColimitsOverMap

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **The restriction comparison of a ringed site turns the factorization of restriction in two
steps into the factorization of restriction in one.**  At the class of a complex `M` of
`O`-modules, the inverse of
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso`, followed by the canonical
factorization of restriction to the slice over `V` and then that of restriction along `g`, is the
canonical factorization of restriction to the slice over `W`, up to the transport of the two
spellings of the restriction in two steps.

That transport is the `CategoryTheory.eqToHom` of
`AlgebraicGeometry.RingedSite.restrictComplex_overMap` and is carried rather than discharged; see
the implementation notes of this file for why.  The proof is the value
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso_inv_app_Q` of the comparison,
whose last two legs are exactly the inverses of the two factorizations post-composed here. -/
theorem overMapDerivedCategoryRestrictIso_inv_app_Q_comp {V W : X.C} (g : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (overMapDerivedCategoryRestrictIso X g).inv.app (DerivedCategory.Q.obj M) ≫
        (SheafOfModules.overMap.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategory.map
            ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.hom.app M) ≫
          (SheafOfModules.overMap.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategoryFactors.hom.app
            (restrictComplex X M V) =
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map (eqToHom (restrictComplex_overMap M g)) := by
  rw [overMapDerivedCategoryRestrictIso_inv_app_Q]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

end AlgebraicGeometry.RingedSite

end
