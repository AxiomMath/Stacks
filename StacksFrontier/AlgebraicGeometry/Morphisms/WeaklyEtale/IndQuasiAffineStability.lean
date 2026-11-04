module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IndQuasiAffine.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffine

/-!
# Stability properties of ind-quasi-affine morphisms

Ind-quasi-affineness of a scheme is invariant under isomorphism, and
ind-quasi-affineness of a morphism of schemes is invariant under isomorphism of the
source and of the target, stable under restriction of the target to an open subscheme,
automatic when the source is ind-quasi-affine, and implied by quasi-affineness and by
immersions.

## Main results

* `AlgebraicGeometry.Scheme.IsQuasiAffine.of_iso` and
  `AlgebraicGeometry.IsIndQuasiAffine.of_iso` transport quasi-affineness and
  ind-quasi-affineness of a scheme along an isomorphism.
* `AlgebraicGeometry.isQuasiAffine_of_isQuasiAffineHom_of_isAffine` extracts
  quasi-affineness of the source of a quasi-affine morphism with affine target.
* `AlgebraicGeometry.isIndQuasiAffineHom_of_isIndQuasiAffine_source`: a morphism out of
  an ind-quasi-affine scheme is ind-quasi-affine.
* `AlgebraicGeometry.isIndQuasiAffineHom_respectsIso` records ind-quasi-affineness of
  morphisms as a property respecting isomorphisms.
* `AlgebraicGeometry.isIndQuasiAffineHom_restrict`: the restriction of an
  ind-quasi-affine morphism over an open subscheme of its target is ind-quasi-affine.

## Implementation notes

An open subscheme is represented by `Scheme.Opens` and its associated scheme by
`Scheme.Opens.toScheme`. Quasi-compactness of an open is expressed as compactness of
its underlying subset, matching `AlgebraicGeometry.IsIndQuasiAffine`. The transport
lemmas are stated for an isomorphism of schemes rather than for a general property
respecting isomorphisms, because they are consumed on concrete comparison
isomorphisms between open subschemes.

## References

* [Stacks Project, Tag 0F1W](https://stacks.math.columbia.edu/tag/0F1W)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Quasi-affineness of a scheme is invariant under isomorphism. -/
theorem Scheme.IsQuasiAffine.of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    [Scheme.IsQuasiAffine Y] : Scheme.IsQuasiAffine X := by
  have : CompactSpace X := (TopCat.homeoOfIso (asIso e.inv.base)).compactSpace
  exact Scheme.IsQuasiAffine.of_isImmersion e.hom

/-- Ind-quasi-affineness of a scheme is invariant under isomorphism. -/
theorem IsIndQuasiAffine.of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    [IsIndQuasiAffine X] : IsIndQuasiAffine Y := by
  constructor
  intro U hU
  let U' : X.Opens := e.hom ⁻¹ᵁ U
  let eU := e.hom.preimageIso U
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have hU' : IsCompact (U' : Set X) := isCompact_iff_compactSpace.mpr
    (TopCat.homeoOfIso (asIso eU.inv.base)).compactSpace
  have : Scheme.IsQuasiAffine U'.toScheme := IsIndQuasiAffine.isQuasiAffine U' hU'
  exact Scheme.IsQuasiAffine.of_iso eU.symm

/-- The source of a quasi-affine morphism with affine target is quasi-affine. -/
theorem isQuasiAffine_of_isQuasiAffineHom_of_isAffine {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsQuasiAffineHom f] : Scheme.IsQuasiAffine X := by
  have htop : Scheme.IsQuasiAffine (⊤ : X.Opens).toScheme := by
    simpa using IsQuasiAffineHom.isQuasiAffine_preimage (f := f) ⊤ (isAffineOpen_top Y)
  exact Scheme.IsQuasiAffine.of_iso X.topIso.symm

/-- A morphism out of an ind-quasi-affine scheme is ind-quasi-affine. -/
theorem isIndQuasiAffineHom_of_isIndQuasiAffine_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIndQuasiAffine X] : IsIndQuasiAffineHom f := by
  constructor
  intro U _
  constructor
  intro W hW
  let V : X.Opens := (f ⁻¹ᵁ U).ι ''ᵁ W
  have hV : IsCompact (V : Set X) := hW.image (f ⁻¹ᵁ U).ι.continuous
  have : Scheme.IsQuasiAffine V.toScheme := IsIndQuasiAffine.isQuasiAffine V hV
  exact Scheme.IsQuasiAffine.of_iso ((f ⁻¹ᵁ U).ι.isoImage W)

/-- Ind-quasi-affineness of a morphism of schemes respects isomorphisms of the source
and of the target. -/
theorem isIndQuasiAffineHom_respectsIso :
    MorphismProperty.RespectsIso (@IsIndQuasiAffineHom : MorphismProperty Scheme.{u}) := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    constructor
    intro V hV
    have : IsIndQuasiAffine (f ⁻¹ᵁ V).toScheme := hf.isIndQuasiAffine_preimage V hV
    change IsIndQuasiAffine ((e.hom ≫ f) ⁻¹ᵁ V).toScheme
    rw [Scheme.Hom.comp_preimage]
    exact IsIndQuasiAffine.of_iso (e.hom.preimageIso (f ⁻¹ᵁ V)).symm
  · intro X Y Z e f hf
    constructor
    intro V hV
    rw [Scheme.Hom.comp_preimage]
    exact hf.isIndQuasiAffine_preimage (e.hom ⁻¹ᵁ V) (hV.preimage_of_isIso e.hom)

/-- The restriction of an ind-quasi-affine morphism over an open subscheme of its target
is ind-quasi-affine. -/
theorem isIndQuasiAffineHom_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsIndQuasiAffineHom f) (V : Y.Opens) : IsIndQuasiAffineHom (f ∣_ V) := by
  constructor
  intro W hW
  have : IsIndQuasiAffine (f ⁻¹ᵁ (V.ι ''ᵁ W)).toScheme :=
    hf.isIndQuasiAffine_preimage _ (hW.image_of_isOpenImmersion V.ι)
  exact IsIndQuasiAffine.of_iso
    ((f ⁻¹ᵁ V).ι.isoImage ((f ∣_ V) ⁻¹ᵁ W) ≪≫
      X.isoOfEq (image_morphismRestrict_preimage f V W)).symm

end AlgebraicGeometry
