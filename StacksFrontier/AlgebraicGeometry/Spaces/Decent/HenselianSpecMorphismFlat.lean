module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorHenselianSpecMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullback

/-!
# The canonical morphism from the spectrum of the henselian local ring is flat

Let `X` be an algebraic space over `S`, let `x ∈ |X|` and let `(W, w) → (X, x)` be an elementary
étale neighborhood.  The canonical morphism

`c_x : Spec(𝒪^h_{X, x}) ⟶ X`

of `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.toSpaceHom` is flat: it is the spectrum
of `𝒪_{W, w} → 𝒪^h_{X, x}` followed by `Spec(𝒪_{W, w}) → W → X`, and all three are flat — a
henselization is flat over its base ring, the morphism from the spectrum of a local ring of a
scheme is flat, and an étale chart of an algebraic space is flat.

Flatness is what Section 72.7 of the source uses: "Since `c_ξ` is flat, pullbacks of meromorphic
functions and (regular) sections are defined for `c_ξ`".  By Stacks 0EN9, part (2) that is
exactly `AlgebraicGeometry.Space.PullbacksMeromorphicSections` for `c_x`, so a meromorphic
section of an `𝒪_X`-module `ℒ` may be pulled back to a meromorphic section of
`ℒ_ξ = c_ξ^*ℒ` on `Spec(𝒪^h_{X, ξ})`, which is where the ratio `s / s_ξ` of Stacks 0EPR is
read.

## Main results

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.flat_specToScheme`: the morphism of
  schemes `Spec(𝒪^h_{X, x}) ⟶ W` is flat.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.isFlat_toSpaceHom`: `c_x` is flat.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.pullbacksMeromorphicSections_toSpaceHom`:
  pullbacks of meromorphic functions and sections are defined for `c_x`.
* `AlgebraicGeometry.Space.PrimeDivisor.isFlat_genericHenselianMorphism` and
  `AlgebraicGeometry.Space.PrimeDivisor.pullbacksMeromorphicSections_genericHenselianMorphism`:
  the same at the generic point of a prime divisor, which is the clause of the construction
  preceding Stacks 0EPR.

## Implementation notes

As in `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.toSpaceHom`, the henselian local ring
is carried as an abstract henselization `R` in `Type u` of the Zariski local ring of the
neighborhood at its distinguished point, together with its containment in the chosen big site.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENV](https://stacks.math.columbia.edu/tag/0ENV)
* [Stacks Project, Tag 0EN9](https://stacks.math.columbia.edu/tag/0EN9)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

namespace ElementaryEtaleNeighborhood

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  {x : points B S hS F} (U : ElementaryEtaleNeighborhood B S hS F hF x)

section Henselian

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra (U.scheme.left.1.presheaf.stalk U.point) R]
  [IsLocalRing.IsHenselization (U.scheme.left.1.presheaf.stalk U.point)
    (IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point)) R]
  (hR : B.Contains (Spec (.of R)))

/-- **The morphism of schemes `Spec(𝒪^h_{X, x}) ⟶ W` is flat.**  It is the spectrum of the
structure map of the henselization followed by `Spec(𝒪_{W, w}) ⟶ W`; a henselization is flat
over its base ring and the morphism from the spectrum of a local ring of a scheme is flat. -/
theorem flat_specToScheme : Flat (U.specToScheme R) := by
  have hmod : Module.Flat (U.scheme.left.1.presheaf.stalk U.point) R :=
    IsLocalRing.IsHenselization.flat
      (L := IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point))
  have h1 : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap (U.scheme.left.1.presheaf.stalk U.point) R))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hmod)
  have h2 : Flat (U.scheme.left.1.fromSpecStalk U.point) :=
    _root_.AlgebraicGeometry.flat_fromSpecStalk _ _
  exact MorphismProperty.comp_mem @Flat _ _ h1 h2

/-- **The canonical morphism `c_x : Spec(𝒪^h_{X, x}) ⟶ X` is flat.**  It factors as the
morphism of the site `Spec(𝒪^h_{X, x}) ⟶ W`, whose underlying morphism of schemes is flat by
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.flat_specToScheme`, followed by the étale
chart `W ⟶ X`, which is flat because étale morphisms of schemes are. -/
theorem isFlat_toSpaceHom : IsFlat B S hS (U.toSpaceHom R hR).hom := by
  rw [U.toSpaceHom_hom R hR]
  exact isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS (U.henselianObj R hR))
    (isAlgebraicSpace_yoneda B S hS U.scheme) hF _ _
    (isFlat_yoneda_map B S hS (U.toSchemeHom R hR)
      (by rw [U.toScheme_map_toSchemeHom R hR]; exact U.flat_specToScheme R))
    (isFlat_atlas B S hS hF U.etale_toSpace)

/-- **Pullbacks of meromorphic functions and sections are defined for
`c_x : Spec(𝒪^h_{X, x}) ⟶ X`**, by Stacks 0EN9, part (2), `c_x` being flat.

This is what lets a meromorphic section of an `𝒪_X`-module be pulled back to
`Spec(𝒪^h_{X, x})`. -/
theorem pullbacksMeromorphicSections_toSpaceHom :
    PullbacksMeromorphicSections B S hS (U.toSpaceHom R hR).hom :=
  pullbacksMeromorphicSections_of_flat B S hS _ (U.isFlat_toSpaceHom R hR)

end Henselian

end ElementaryEtaleNeighborhood

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

section Generic

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R]
  (hR : B.Contains (Spec (.of R)))

/-- **The canonical morphism `c_ξ : Spec(𝒪^h_{X, ξ}) ⟶ X` at the generic point of a prime
divisor is flat.** -/
theorem PrimeDivisor.isFlat_genericHenselianMorphism :
    IsFlat B S hS (Z.genericHenselianMorphism B S hS hX hdec R hR).hom :=
  (Z.genericChart B S hS hX hdec).isFlat_toSpaceHom R hR

/-- **Pullbacks of meromorphic functions and sections are defined for
`c_ξ : Spec(𝒪^h_{X, ξ}) ⟶ X`.**

This is the clause of the construction of Section 72.7 of the source preceding Definition
72.7.1: "Since `c_ξ` is flat, pullbacks of meromorphic functions and (regular) sections are
defined for `c_ξ`".  It is what carries a regular meromorphic section `s` of `ℒ` to a
meromorphic section of `ℒ_ξ = c_ξ^*ℒ` on `Spec(𝒪^h_{X, ξ})`, against which the ratio `s / s_ξ`
is taken. -/
@[stacks 0EPR "the clause of the construction preceding the definition: c_ξ is flat, so \
  pullbacks of meromorphic functions and (regular) sections are defined for c_ξ"]
theorem PrimeDivisor.pullbacksMeromorphicSections_genericHenselianMorphism :
    PullbacksMeromorphicSections B S hS
      (Z.genericHenselianMorphism B S hS hX hdec R hR).hom :=
  (Z.genericChart B S hS hX hdec).pullbacksMeromorphicSections_toSpaceHom R hR

end Generic

end AlgebraicGeometry.Space

end
