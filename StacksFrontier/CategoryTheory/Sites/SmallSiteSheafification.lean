module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Sheafification of abelian presheaves on a small site

On a small site, abelian presheaves admit a sheafification and the maps it inverts are exactly
the locally bijective ones: `AddCommGrpCat` in the universe of the site satisfies AB5 and is a
concrete category with the exactness properties the two statements need, so both are instances.

## Main results

* `CategoryTheory.smallSiteHasSheafify`: abelian presheaves on a small site admit sheafification.
* `CategoryTheory.smallSiteWEqualsLocallyBijective`: sheafification of abelian presheaves on a
  small site inverts exactly the locally bijective maps.
-/

@[expose] public section

namespace CategoryTheory

universe w

/-- Sheafification of abelian presheaves exists on a small site. -/
theorem smallSiteHasSheafify {D : Type w} [SmallCategory D] (K : GrothendieckTopology D) :
    HasSheafify K AddCommGrpCat.{w} := inferInstance

/-- On a small site, the maps of abelian presheaves inverted by sheafification are exactly the
locally bijective ones. -/
theorem smallSiteWEqualsLocallyBijective {D : Type w} [SmallCategory D]
    (K : GrothendieckTopology D) : K.WEqualsLocallyBijective AddCommGrpCat.{w} := inferInstance

end CategoryTheory

end
