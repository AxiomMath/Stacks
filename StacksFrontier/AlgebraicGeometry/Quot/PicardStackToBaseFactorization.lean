module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToBase

/-!
# The structure morphism of the Picard stack factors through the stack of coherent sheaves

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is flat, of finite presentation
and proper. The structure morphism `Picardstack_{X/B} ⟶ 𝒮_B` of Section 0DM9, which forgets the
invertible module, is the natural map `Picardstack_{X/B} ⟶ Cohstack_{X/B}` of Stacks 0D03 followed
by the projection `Cohstack_{X/B} ⟶ 𝒮_B` of Stacks 08LP, which forgets the coherent module.

This is the shape in which the proofs of Stacks 0DMA and 0DMB use that `Picardstack_{X/B}` is an
open substack of `Cohstack_{X/B}`: the diagonal of `Picardstack_{X/B}` over `B` is the relative
diagonal of the composite, and the natural map is fully faithful.

## Main definitions

* `AlgebraicGeometry.Space.coherentToBaseCFG`: the projection `Cohstack_{X/B} ⟶ 𝒮_B` of
  Stacks 08LP as a 1-morphism of categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.Space.picardToCoherent_comp_coherentToBaseCFG`: the structure morphism of
  `Picardstack_{X/B}` is the natural map of Stacks 0D03 followed by the projection of
  `Cohstack_{X/B}`.

## References

* [Stacks Project, Section 0DM9](https://stacks.math.columbia.edu/tag/0DM9)
* [Stacks Project, Tag 0D03](https://stacks.math.columbia.edu/tag/0D03)
* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The projection `Cohstack_{X/B} ⟶ 𝒮_B` of Stacks 08LP**, `(T, g, ℱ) ↦ (T, g)`, as a
1-morphism of categories fibred in groupoids over the big fppf site of `S`. -/
def coherentToBaseCFG (D : CoherentSituation B S hS) : coherentCFG D ⟶ baseCFG D.Y :=
  Bicategory.InducedBicategory.mkHom (coherentToBase D.categoryData)

/-- The projection of `Cohstack_{X/B}` as a 1-morphism has the based functor of Stacks 08LP as its
underlying based functor. -/
@[simp]
theorem coherentToBaseCFG_hom (D : CoherentSituation B S hS) :
    (coherentToBaseCFG D).hom = coherentToBase D.categoryData :=
  rfl

/-- **The structure morphism of `Picardstack_{X/B}` factors through `Cohstack_{X/B}`.** For `f`
flat and proper (and of finite presentation, part of the standing data `D`), the structure
morphism `Picardstack_{X/B} ⟶ 𝒮_B`, `(U, b, L) ↦ (U, b)`, is the natural map
`Picardstack_{X/B} ⟶ Cohstack_{X/B}` of Stacks 0D03 followed by the projection
`Cohstack_{X/B} ⟶ 𝒮_B` of Stacks 08LP: both forget the module and keep the base map. -/
theorem picardToCoherent_comp_coherentToBaseCFG (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom) :
    picardToCoherent D hflat hproper ≫ coherentToBaseCFG D =
      picardToBase (modulePushforwardCoherence B S hS) D.toPicardSituation :=
  rfl

end AlgebraicGeometry.Space

end
