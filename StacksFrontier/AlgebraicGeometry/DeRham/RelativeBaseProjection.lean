module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeInverseImageComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequence

/-!
# The two spellings of the relative base morphism agree

For a ringed space `(S, 𝒪_S)` and continuous maps `i : Z ⟶ W`, `j : W ⟶ S` the canonical
morphism of ringed spaces `(Z, (i ∘ j)^{-1}𝒪_S) ⟶ (W, j^{-1}𝒪_S)` over `i` was written down
twice: once as `AlgebraicGeometry.RingedSpace.inverseImageMap`, the morphism along which the
relative de Rham complex is pushed forward in the spectral sequence of a smooth morphism, and
once as `AlgebraicGeometry.RingedSpace.inverseImageCompProjection`, the morphism along which the
comparison `p^{-1}𝓕 ⟶ p^*𝓕` of modules over the inverse images of `𝒪_S` is formed. Both are the
transpose along `j^{-1} ⊣ j_*` of the unit of `(i ∘ j)^{-1} ⊣ (i ∘ j)_*` at `𝒪_S`, so they are
equal, and this file records that: it is what lets the filtration of `Ω^•_{X/S}` and the
comparison of inverse image with pullback be read against one another.

## Main results

* `AlgebraicGeometry.RingedSpace.inverseImageMap_eq_inverseImageCompProjection`: the two generic
  constructions agree.
* `Stacks.DeRhamSmooth.relativeBase_eq_relativeInverseImageProjection`: **the two morphisms of
  ringed spaces `(X, (f ∘ g)^{-1}𝒪_S) ⟶ (Y, g^{-1}𝒪_S)` agree**, so the pullback and pushforward
  functors they induce agree too, and so does the triangle over `S`.

## Implementation notes

The equality holds by `rfl`: both structure maps are literally the transpose along
`pullbackPushforwardAdjunction j` of `(pullbackPushforwardAdjunction (i ≫ j)).unit.app 𝒪_S`,
and both underlying continuous maps are `i`. The two definitions were written in different files
with their arguments in opposite orders, which is the only reason the agreement was not visible.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 008C](https://stacks.math.columbia.edu/tag/008C)
* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace

/-- **The two spellings of the canonical morphism agree.** For continuous maps `i : Z ⟶ W` and
`j : W ⟶ S` into (the space of) a ringed space `(S, 𝒪_S)`, the morphism
`(Z, (i ∘ j)^{-1}𝒪_S) ⟶ (W, j^{-1}𝒪_S)` of `inverseImageMap` is the one of
`inverseImageCompProjection`. -/
theorem inverseImageMap_eq_inverseImageCompProjection (S : RingedSpace.{u, u}) {Z W : TopCat.{u}}
    (i : Z ⟶ W) (j : W ⟶ S.carrier) :
    inverseImageMap S i j = inverseImageCompProjection S j i :=
  rfl

end AlgebraicGeometry.RingedSpace

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The relative base morphism is the relative inverse-image projection.** The morphism of
ringed spaces `(X, (f ∘ g)^{-1}𝒪_S) ⟶ (Y, g^{-1}𝒪_S)` along which `Ω^•_{X/S}` is pushed forward
is the one along which the comparison `f^{-1}𝓕 ⟶ f^*𝓕` of modules over the inverse images of
`𝒪_S` is formed. -/
theorem relativeBase_eq_relativeInverseImageProjection :
    relativeBase f g = relativeInverseImageProjection f g :=
  rfl

/-- The inverse image of modules along `relativeBase` is the one along
`relativeInverseImageProjection`, i.e. `relativeInverseImage`. -/
theorem pullback_relativeBase_eq :
    _root_.pullback (relativeBase f g) = relativeInverseImage f g :=
  rfl

/-- The direct image of modules along `relativeBase` is the one along
`relativeInverseImageProjection`, i.e. `relativeInverseImagePushforward`. -/
theorem pushforward_relativeBase_eq :
    _root_.pushforward (relativeBase f g) = relativeInverseImagePushforward f g :=
  rfl

/-- **The triangle over `S`** for `relativeBase`: pushing forward to `(Y, g^{-1}𝒪_S)` and then
projecting to `S` is projecting to `S`. This is the characterising property of `relativeBase`,
now available at that spelling. -/
theorem relativeBase_comp_inverseImageBaseProjection :
    relativeBase f g ≫ inverseImageBaseProjection g = inverseImageBaseProjection (f ≫ g) :=
  relativeInverseImageProjection_comp f g

/-! The square comparing the two factorizations of `f` — `toInverseImageBase (f ≫ g) ≫
relativeBase f g = f.toLRSHom.toShHom ≫ toInverseImageBase g` — is not restated here: it is
`Stacks.DeRhamPullback.toInverseImageBase_relativeBase` of
`StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplex`.  With `relativeBase_eq_relativeInverseImageProjection` above it is
also the `relativeInverseImageProjection` spelling of that square. -/

end Stacks.DeRhamSmooth

end
