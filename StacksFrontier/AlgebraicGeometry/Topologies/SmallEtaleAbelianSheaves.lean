module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Abelian sheaves on the small étale site at the morphism universe of the site

Let `S : Scheme.{u}`. The small étale site `AlgebraicGeometry.Scheme.Etale` has its objects in
`Type (u + 1)` and its morphisms in `Type u`. Abelian sheaves on it with coefficients in
`AddCommGrpCat.{u}` have enough injectives, and their `Ext` groups live in `Type (u + 1)`.

## Main results

* `AlgebraicGeometry.enoughInjectives_sheaf_smallEtaleTopology`: abelian sheaves on the small
  étale site, with coefficients at the morphism universe of the site, have enough injectives.
* `AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology`: their `Ext` groups live in the universe
  of the objects of the site.

## References

* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Abelian sheaves on the small étale site of `S : Scheme.{u}`, with coefficients at the
morphism universe `u` of the site, have enough injectives. -/
public instance enoughInjectives_sheaf_smallEtaleTopology (S : Scheme.{u}) :
    EnoughInjectives (Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u}) := by
  have : IsGrothendieckAbelian.{u}
      (Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u}) := inferInstance
  infer_instance

/-- The `Ext` groups of abelian sheaves on the small étale site of `S : Scheme.{u}`, with
coefficients at the morphism universe `u` of the site, live in the universe `u + 1` of the
objects of the site. -/
public instance hasExt_sheaf_smallEtaleTopology (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u}) :=
  HasExt.standard _

end AlgebraicGeometry
