module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductAlgebraicityFull
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductUniformAtlasCutoff

/-!
# Stacks 0ADK for an index type bounded by a regular cutoff

`AlgebraicGeometry.Space.Descent.familyCoproductEquivalenceOfAdmitsCoproductIndex` states the
equivalence of Stacks 0ADK for an index type admissible for the site, that is, of cardinality
below the *cofinality* of the size cutoff. This file records the one hypothesis under which that
bound is implied by the bound both sides of the statement need anyway, namely `#I < B.cutoff`:
regularity of the cutoff.

The exchange is exact. Under `AlgebraicGeometry.BigFppfSite.IsRegular` of the cutoff the
equivalence is available for every index type of cardinality below the cutoff, which is the
weakest hypothesis under which the sheaf coproduct of the sources can be formed at all. But a
regular cutoff is an inaccessible cardinal, by
`AlgebraicGeometry.BigFppfSite.isInaccessible_cutoff_of_isRegular`, so this is not a
simplification of the construction: it is a large-cardinal hypothesis on the site, which
`AlgebraicGeometry.BigFppfSite.exists_containing` does not provide and cannot.

Without it the cofinality bound is not removable, and not merely for want of a better proof:
`AlgebraicGeometry.exists_family_lt_cutoff_not_nonempty_algebraicSheafCoproduct` exhibits a site
and a family indexed below its cutoff whose coproduct in sheaves is not an algebraic space over
the base, so that the right-hand category of the equivalence does not exist.

## Main results

* `AlgebraicGeometry.Space.Descent.nonempty_algebraicSheafCoproduct_of_isRegular_cutoff`
* `AlgebraicGeometry.Space.Descent.nonempty_fullFamilyCoproductEquivalence_of_isRegular_cutoff`

## References

* [Stacks Project, Tag 0ADK](https://stacks.math.columbia.edu/tag/0ADK)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v w

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type v} [Small.{u} I]
  {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (f : ∀ i, X i ⟶ T) (hT : IsAlgebraicSpace B S hS T)
  (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

/-- **A family indexed below a regular cutoff has a sheaf coproduct that is an algebraic
space.** This is `AlgebraicGeometry.Space.Descent.nonempty_algebraicSheafCoproduct` with its
cofinality hypothesis discharged by
`AlgebraicGeometry.BigFppfSite.admitsCoproductIndex_of_isRegular_cutoff`: a regular cardinal
equals its own cofinality.

Regularity is not discharged here and is not dischargeable from the axioms of a big fppf site:
see `AlgebraicGeometry.BigFppfSite.isInaccessible_cutoff_of_isRegular` and
`AlgebraicGeometry.exists_cutoff_isSingular`. -/
public theorem nonempty_algebraicSheafCoproduct_of_isRegular_cutoff
    (hreg : B.cutoff.IsRegular) (hI : #(Shrink.{u} I) < B.cutoff) :
    Nonempty (AlgebraicSheafCoproduct X hX) :=
  let : B.AdmitsCoproductIndex I := B.admitsCoproductIndex_of_isRegular_cutoff hreg I hI
  nonempty_algebraicSheafCoproduct X hX

/-- **Stacks 0ADK for an index type bounded by a regular cutoff.** For a family of algebraic
spaces over `S` with fixed target `T`, indexed by a `u`-small type of cardinality below the size
cutoff of the site, the whole category of descent data for the family is canonically equivalent
to the category of descent data relative to the sheaf coproduct of the sources — provided the
cutoff is a regular cardinal.

This is `AlgebraicGeometry.Space.Descent.familyCoproductEquivalenceOfAdmitsCoproductIndex` with
its hypothesis derived from regularity of the cutoff rather than assumed; the derived instance
appears in the statement because the category of descent data relative to the coproduct, and
hence the type of the equivalence, is formed from it. -/
public theorem nonempty_fullFamilyCoproductEquivalence_of_isRegular_cutoff
    (hreg : B.cutoff.IsRegular) (hI : #(Shrink.{u} I) < B.cutoff) :
    letI : B.AdmitsCoproductIndex I := B.admitsCoproductIndex_of_isRegular_cutoff hreg I hI
    Nonempty (FullFamilyCoproductEquivalence.{u, v, w} f hT hX
      (sigmaAlgebraicSheafCoproduct X hX)) :=
  let : B.AdmitsCoproductIndex I := B.admitsCoproductIndex_of_isRegular_cutoff hreg I hI
  ⟨familyCoproductEquivalenceOfAdmitsCoproductIndex.{u, v, w} f hT hX⟩

end AlgebraicGeometry.Space.Descent

end
