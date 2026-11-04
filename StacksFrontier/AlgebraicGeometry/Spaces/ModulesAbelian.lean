module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite

/-!
# Sheafification on the small étale ringed site of an algebraic space

Presheaves of abelian groups on the small étale ringed site of an algebraic space have
sheafifications, and the local equivalences among them are exactly the locally bijective
morphisms.

## Main results

* `AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify`: presheaves of abelian groups on
  the small étale ringed site have sheafifications.
* `AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective`: on the small étale
  ringed site, the local equivalences of presheaves of abelian groups are the locally bijective
  morphisms.

## References

* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Presheaves of abelian groups on the small étale ringed site of the algebraic space `F`
have sheafifications. -/
instance smallEtaleRingedSite_hasSheafify (hF : IsAlgebraicSpace B S hS F) :
    HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{u})

/-- On the small étale ringed site of the algebraic space `F`, the local equivalences of
presheaves of abelian groups are exactly the locally bijective morphisms. -/
instance smallEtaleRingedSite_wEqualsLocallyBijective (hF : IsAlgebraicSpace B S hS F) :
    ((smallEtaleRingedSite B S hS F hF).J).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((SmallEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{u})

end AlgebraicGeometry.Space

end
