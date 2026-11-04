module

public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites

/-!
# Fibre products and final objects in the Zariski sites of a scheme

Let `B` be a big Zariski site containing a scheme `S`. The underlying cutoff category of `B` has
fibre products, and the big Zariski category of `S` is a slice of it, so it has them for formal
reasons. Fibre products for the cutoff category and for the three full subcategories of that
slice — the small Zariski category of schemes open over `S`, and the big and small affine
Zariski categories — together with the preservation statements for the canonical functors to
schemes, and `S / S` as a final object of the small Zariski category, are all in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits`, which this module re-exports.

What is added here is the preservation of fibre products by the inclusions of the two *affine*
categories into their ambient ones.

## Main results

* `AlgebraicGeometry.preservesPullbacks_bigAffineZariskiInclusion` and
  `AlgebraicGeometry.preservesPullbacks_smallAffineZariskiInclusion`: the inclusions of the big
  and the small affine Zariski categories of `S` into the big, respectively the small, Zariski
  category of `S` preserve fibre products.

## Implementation notes

The two affine categories are cut out of their ambient ones by a property of objects, and their
inclusions *create* fibre products, a fibre product of affine schemes over an affine base being
affine. That argument is `AlgebraicGeometry.ProEtale.affineCreatesPullbacks`, stated there for an
arbitrary category equipped with a pullback-preserving functor to schemes and used here
unchanged; only its location is pro-étale.

## References

* [Stacks Project, Tag 020T](https://stacks.math.columbia.edu/tag/020T)
* [Stacks Project, Tag 020V](https://stacks.math.columbia.edu/tag/020V)
* [Stacks Project, Tag 020Z](https://stacks.math.columbia.edu/tag/020Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of the big affine Zariski category of `S` into its big Zariski category
creates fibre products. -/
private noncomputable instance createsPullbacks_bigAffineZariski :
    CreatesLimitsOfShape WalkingCospan (BigAffineZariski.inclusion B S hS) :=
  ProEtale.affineCreatesPullbacks (BigZariskiOver.toScheme B S hS)

/-- The inclusion of the big affine Zariski category of `S` into its big Zariski category
preserves fibre products. -/
public instance preservesPullbacks_bigAffineZariskiInclusion :
    PreservesLimitsOfShape WalkingCospan (BigAffineZariski.inclusion B S hS) := by
  infer_instance

/-- The inclusion of the small affine Zariski category of `S` into its small Zariski category
creates fibre products. -/
private noncomputable instance createsPullbacks_smallAffineZariski :
    CreatesLimitsOfShape WalkingCospan (SmallAffineZariski.inclusion B S hS) :=
  ProEtale.affineCreatesPullbacks (SmallZariski.toScheme B S hS)

/-- The inclusion of the small affine Zariski category of `S` into its small Zariski category
preserves fibre products. -/
public instance preservesPullbacks_smallAffineZariskiInclusion :
    PreservesLimitsOfShape WalkingCospan (SmallAffineZariski.inclusion B S hS) := by
  infer_instance

end AlgebraicGeometry
