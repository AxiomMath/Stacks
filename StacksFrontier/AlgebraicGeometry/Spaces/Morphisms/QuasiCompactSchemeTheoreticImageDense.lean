module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageDense

/-!
# The support of the scheme-theoretic image of a quasi-compact morphism

Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`, and let `Z` be its scheme-theoretic image. The set of points of `Z` is exactly
the closure of the image of the point map of `f`; equivalently, the image of `f` is dense in `Z`.
This is part (4) of **Stacks 082Z**.

The inclusion of the closure in `|Z|` holds for every morphism, `Z` being a closed subspace
through which `f` factors. The reverse inclusion is
`AlgebraicGeometry.Space.range_pointsMap_ι_schemeTheoreticImage_eq_closure`, which asks for
compatibility of the scheme-theoretic image with étale base change of the target; for a
quasi-compact morphism that is part (3) of Stacks 082Z,
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact`,
so the two combine into an unconditional statement here.

## Main results

* `AlgebraicGeometry.Space.range_pointsMap_ι_schemeTheoreticImage_eq_closure_of_isQuasiCompact`
  is **part (4) of Stacks 082Z**: the set of points of the scheme-theoretic image of a
  quasi-compact morphism is the closure of the image of its point map.
* `AlgebraicGeometry.Space.denseRange_pointsMap_toSchemeTheoreticImage_of_isQuasiCompact` is the
  same statement read inside the scheme-theoretic image: the morphism to the scheme-theoretic
  image has dense image on points.

## References

* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 082Z, part (4).** The set of points of the scheme-theoretic image of a quasi-compact
morphism of algebraic spaces is the closure of the image of its point map. -/
@[stacks 082Z "part (4): the image is dense in the scheme-theoretic image"]
theorem range_pointsMap_ι_schemeTheoreticImage_eq_closure_of_isQuasiCompact (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsQuasiCompact B S hS f) :
    Set.range (pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor
        (schemeTheoreticImageSubfunctor B S hS f).ι) =
      closure (Set.range (pointsMap B S hS X f)) :=
  range_pointsMap_ι_schemeTheoreticImage_eq_closure B S hS f hX hY
    fun _ g hV hg =>
      schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS f g hX hY
        hV hf hg

/-- **Stacks 082Z, part (4)**, read inside the scheme-theoretic image: a quasi-compact morphism of
algebraic spaces has dense image on the points of its scheme-theoretic image. -/
@[stacks 082Z "part (4): density of the image on points"]
theorem denseRange_pointsMap_toSchemeTheoreticImage_of_isQuasiCompact (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsQuasiCompact B S hS f) :
    DenseRange (pointsMap B S hS X (toSchemeTheoreticImage B S hS f)) :=
  denseRange_pointsMap_toSchemeTheoreticImage B S hS f hX hY
    fun _ g hV hg =>
      schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS f g hX hY
        hV hf hg

end AlgebraicGeometry.Space

end
