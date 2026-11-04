module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffine

/-!
# Quasi-affine morphisms and immersions are ind-quasi-affine

A quasi-affine morphism of schemes is ind-quasi-affine, because a quasi-compact open subscheme
of a quasi-affine scheme is quasi-affine. An immersion is ind-quasi-affine, because above an
affine open of the target a quasi-compact open of the source is a quasi-compact locally closed
subscheme of an affine scheme.

## Main results

* `AlgebraicGeometry.isIndQuasiAffineHom_of_isQuasiAffineHom`: a quasi-affine morphism of
  schemes is ind-quasi-affine.
* `AlgebraicGeometry.isIndQuasiAffineHom_of_isImmersion`: an immersion of schemes is
  ind-quasi-affine.

## References

* [Stacks Project, Tag 0F1W](https://stacks.math.columbia.edu/tag/0F1W)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A quasi-affine morphism of schemes is ind-quasi-affine. -/
@[stacks 0F1W "quasi-affine morphisms"]
instance isIndQuasiAffineHom_of_isQuasiAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsQuasiAffineHom f] : IsIndQuasiAffineHom f := by
  refine ⟨fun U hU => ⟨fun W hW => ?_⟩⟩
  have : (f ⁻¹ᵁ U).toScheme.IsQuasiAffine := IsQuasiAffineHom.isQuasiAffine_preimage U hU
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  exact Scheme.IsQuasiAffine.of_isImmersion W.ι

/-- An immersion of schemes is ind-quasi-affine. -/
@[stacks 0F1W "immersions"]
instance isIndQuasiAffineHom_of_isImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] : IsIndQuasiAffineHom f := by
  refine ⟨fun U hU => ⟨fun W hW => ?_⟩⟩
  have : IsAffine U.toScheme := hU
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  exact Scheme.IsQuasiAffine.of_isImmersion (W.ι ≫ f ∣_ U)

end AlgebraicGeometry

end
