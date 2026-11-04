module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiRingedTopos

/-!
# Sheafification on the slices of the total Zariski site

`AlgebraicGeometry.SimplicialScheme.zariski_hasSheafify` and
`AlgebraicGeometry.SimplicialScheme.zariski_wEqualsLocallyBijective` record abelian
sheafification on the total Zariski site of a simplicial scheme, obtained from essential
smallness of the site. Every statement about *local* presentations of a sheaf of modules — a
global presentation on each member of a covering family, which is what quasi-coherence records —
is stated over the slices of the site as well, and so asks for the same two facts there:
`[∀ U, HasWeakSheafify (J.over U) AddCommGrpCat]` and
`[∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat]`.

This file supplies them, and the essential smallness of the slices that they are deduced from.
The argument is the one of the site itself: an object of `Over U` is an object of the site
together with an arrow, so `Over U` has a type of objects in the universe of the schemes and all
its morphism types are small, hence it is essentially small there, and
`CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` apply verbatim.

## Main results

* `AlgebraicGeometry.SimplicialScheme.essentiallySmall_over_zariskiOpen`: every slice of the
  total Zariski site is essentially small in the universe of the schemes.
* `AlgebraicGeometry.SimplicialScheme.zariskiOver_hasSheafify` and
  `.zariskiOver_wEqualsLocallyBijective`: abelian sheafification on every slice of the total
  Zariski site, and the identification of the morphisms it inverts.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SimplicialScheme

/-- Every slice of the total Zariski site of a simplicial scheme is essentially small in the
universe of the schemes: an object of `Over U` is an object of the site together with an arrow
into `U`, so the type of objects lies in that universe and all morphism types are small. -/
public instance essentiallySmall_over_zariskiOpen (X : SimplicialObject Scheme.{u})
    (U : ZariskiOpen X) : EssentiallySmall.{u} (Over U) :=
  essentiallySmall_of_small_of_locallySmall (Over U)

/-- Abelian sheafification exists on every slice of the total Zariski site, because every slice
is essentially small. -/
public instance zariskiOver_hasSheafify (X : SimplicialObject Scheme.{u}) (U : ZariskiOpen X) :
    HasSheafify ((zariskiTopology X).over U) AddCommGrpCat.{u} := by
  let : CategoryTheory.Limits.PreservesLimits (forget AddCommGrpCat.{u}) :=
    AddCommGrpCat.forget_preservesLimits
  exact hasSheafifyEssentiallySmallSite ((zariskiTopology X).over U) AddCommGrpCat.{u}

/-- Abelian sheafification on a slice of the total Zariski site inverts exactly the locally
bijective morphisms. -/
public instance zariskiOver_wEqualsLocallyBijective (X : SimplicialObject Scheme.{u})
    (U : ZariskiOpen X) :
    ((zariskiTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  let : CategoryTheory.Limits.PreservesLimits (forget AddCommGrpCat.{u}) :=
    AddCommGrpCat.forget_preservesLimits
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    (A := AddCommGrpCat.{u}) ((zariskiTopology X).over U)

end AlgebraicGeometry.SimplicialScheme

end
