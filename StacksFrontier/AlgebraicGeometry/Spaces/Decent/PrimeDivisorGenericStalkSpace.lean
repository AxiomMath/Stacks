module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The spectrum of the local ring of a chart at the generic point of a prime divisor

Let `X` be a locally Noetherian integral algebraic space over a scheme `S`, let `Z ⊂ X` be a
prime divisor and let `ξ ∈ |Z|` be its generic point. The chosen affine elementary étale
neighbourhood `(U, u)` of `ξ` has a local ring `A = 𝒪_{U, u}`, and `Spec A` is again an object
of the big fppf site. This file builds the canonical morphism

`j : Spec(𝒪_{U, u}) ⟶ X`

of algebraic spaces, and records that it is flat, so that pullbacks of meromorphic functions
are defined along it by Stacks 0EN9, part (2).

The point of the construction is that `Spec(𝒪_{U, u})` is the spectrum of a *local* ring, on
which an invertible module is trivial, while `A → 𝒪^h_{X, ξ}` carries nonzerodivisors to
nonzerodivisors; so a generator of an invertible `𝒪_X`-module can be read at `ξ` through `j`
without leaving the universe of the site, which the spectrum of `𝒪^h_{X, ξ}` does.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericStalkRing` is `A = 𝒪_{U, u}`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericStalkSpec` is `Spec A` as an object of the site,
  `AlgebraicGeometry.Space.PrimeDivisor.genericStalkSpace` the algebraic space it represents,
  and `AlgebraicGeometry.Space.PrimeDivisor.genericStalkMorphism` the morphism `j` to `X`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.isFlat_genericStalkMorphism`: `j` is flat.
* `AlgebraicGeometry.Space.PrimeDivisor.pullbacksMeromorphicSections_genericStalkMorphism`:
  pullbacks of meromorphic functions are defined along `j`.

## References

* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 0EN9](https://stacks.math.columbia.edu/tag/0EN9)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-- The local ring `𝒪_{U, u}` of the chosen affine elementary étale neighbourhood of the
generic point of a prime divisor at its distinguished point. -/
abbrev PrimeDivisor.genericStalkRing : CommRingCat.{u} :=
  ((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme).presheaf.stalk
    (Z.genericChart B S hS hX hdec).point

/-- **The spectrum of the local ring of the chart at the generic point of a prime divisor**, as
an object of the big fppf site over `S`. -/
def PrimeDivisor.genericStalkSpec : BigFppfOver B S hS :=
  Over.mk ((B.inclusion.preimage
      (((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme).fromSpecStalk
        (Z.genericChart B S hS hX hdec).point) :
      B.obj (CodimensionZeroPresentation.contains_Spec_stalk B S hS
        (Z.genericChart B S hS hX hdec).scheme (Z.genericChart B S hS hX hdec).point) ⟶
        (Z.genericChart B S hS hX hdec).scheme.left) ≫
    (Z.genericChart B S hS hX hdec).scheme.hom)

/-- The canonical morphism from the spectrum of the local ring of the chart at the generic
point of a prime divisor to the chart. -/
def PrimeDivisor.genericStalkSpecToChart :
    Z.genericStalkSpec B S hS hX hdec ⟶ (Z.genericChart B S hS hX hdec).scheme :=
  Over.homMk (B.inclusion.preimage
    (((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme).fromSpecStalk
      (Z.genericChart B S hS hX hdec).point)) rfl

/-- The underlying morphism of schemes of
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkSpecToChart` is
`AlgebraicGeometry.Scheme.fromSpecStalk`. -/
theorem PrimeDivisor.toScheme_map_genericStalkSpecToChart :
    (BigFppfOver.toScheme B S hS).map (Z.genericStalkSpecToChart B S hS hX hdec) =
      ((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme).fromSpecStalk
        (Z.genericChart B S hS hX hdec).point :=
  B.inclusion.map_preimage _

/-- `Spec(𝒪_{U, u})` as an algebraic space over `S`. -/
def PrimeDivisor.genericStalkSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (Z.genericStalkSpec B S hS hX hdec),
    isAlgebraicSpace_yoneda B S hS (Z.genericStalkSpec B S hS hX hdec)⟩

/-- **The canonical morphism `j : Spec(𝒪_{U, u}) ⟶ X`**, the spectrum of the local ring of the
chart at the generic point of a prime divisor mapping to the chart and on to `X`. -/
def PrimeDivisor.genericStalkMorphism :
    Z.genericStalkSpace B S hS hX hdec ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (yoneda.map (Z.genericStalkSpecToChart B S hS hX hdec) ≫
    (Z.genericChart B S hS hX hdec).toSpace)

/-- **The canonical morphism `j : Spec(𝒪_{U, u}) ⟶ X` is flat**: it is the composite of the
morphism from the spectrum of a local ring to its scheme, which is flat, with an étale chart of
`X`, which is flat. -/
theorem PrimeDivisor.isFlat_genericStalkMorphism :
    IsFlat B S hS (Z.genericStalkMorphism B S hS hX hdec).hom :=
  isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS (Z.genericStalkSpec B S hS hX hdec))
    (isAlgebraicSpace_yoneda B S hS (Z.genericChart B S hS hX hdec).scheme) hX _ _
    (isFlat_yoneda_map B S hS (Z.genericStalkSpecToChart B S hS hX hdec)
      (by
        rw [Z.toScheme_map_genericStalkSpecToChart B S hS hX hdec]
        exact flat_fromSpecStalk _ _))
    (isFlat_of_isEtale B S hS (Z.genericChart B S hS hX hdec).etale_toSpace)

/-- **Stacks 0EN9, part (2) at `j`.** Pullbacks of meromorphic functions are defined along the
canonical morphism `j : Spec(𝒪_{U, u}) ⟶ X`, which is flat. -/
theorem PrimeDivisor.pullbacksMeromorphicSections_genericStalkMorphism :
    PullbacksMeromorphicSections B S hS (Z.genericStalkMorphism B S hS hX hdec).hom :=
  pullbacksMeromorphicSections_of_flat B S hS _ (Z.isFlat_genericStalkMorphism B S hS hX hdec)

end AlgebraicGeometry.Space

end
