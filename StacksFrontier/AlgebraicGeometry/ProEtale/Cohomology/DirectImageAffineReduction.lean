module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.DirectImageEmbedding
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineCoversTop
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduction of the small pro-étale direct image to the affine case

Let `f : T ⟶ S` be a morphism of a chosen big pro-étale site. Full faithfulness of the direct
image along `f` on small pro-étale sheaves of sets, and invertibility of the counit of its
adjunction, both hold as soon as the counit is invertible after base change to every affine object
of the small pro-étale site of `S`. Both results take that affine counit statement as a
hypothesis.

## Main results

* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_affineCounit`: the counit of
  the direct-image adjunction along `f` is invertible if it is so after base change to every affine
  object.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_pushforward_fullyFaithful_of_affineCounit`: the
  direct image along `f` is fully faithful under the same hypothesis.

## References

* [Stacks Project, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- The counit of the direct-image adjunction along `f` on small pro-étale sheaves of sets is
invertible as soon as it is invertible after base change to every object of the small pro-étale
site of `S` whose underlying scheme is affine. -/
theorem smallProetaleMorphism_counit_isIso_of_affineCounit
    (hcounit : ∀ Y : SmallProetale B S.obj S.property,
      IsAffine ((SmallProetale.toScheme B S.obj S.property).obj Y) →
        IsIso (smallProetaleMorphism B ((smallProetaleBaseChange B T S f).obj Y).obj.left
          Y.obj.left (pullback.fst Y.obj.hom f)).adj.counit) :
    IsIso (smallProetaleMorphism B T S f).adj.counit :=
  smallProetaleMorphism_counit_isIso_of_coversTop_of_counit B T S f
    (SmallProetale.coversTop_affine B S) fun Y => hcounit Y.1 Y.2

/-- The direct image along `f` on small pro-étale sheaves of sets is fully faithful as soon as the
direct-image counit is invertible after base change to every object of the small pro-étale site of
`S` whose underlying scheme is affine. -/
theorem smallProetaleMorphism_pushforward_fullyFaithful_of_affineCounit
    (hcounit : ∀ Y : SmallProetale B S.obj S.property,
      IsAffine ((SmallProetale.toScheme B S.obj S.property).obj Y) →
        IsIso (smallProetaleMorphism B ((smallProetaleBaseChange B T S f).obj Y).obj.left
          Y.obj.left (pullback.fst Y.obj.hom f)).adj.counit) :
    Nonempty (smallProetaleMorphism B T S f).pushforward.FullyFaithful :=
  (smallProetaleMorphism_counit_isIso_iff_pushforward_fullyFaithful B T S f).mp
    (smallProetaleMorphism_counit_isIso_of_affineCounit B T S f hcounit)

end AlgebraicGeometry.ProEtale

end
