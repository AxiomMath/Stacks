module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IndQuasiAffine.Comp
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IndQuasiAffine.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite

/-!
# Base change of ind-quasi-affine morphisms

An arbitrary base change of an ind-quasi-affine morphism of schemes is ind-quasi-affine.

## Main results

* `AlgebraicGeometry.isIndQuasiAffineHom_isStableUnderBaseChange`: ind-quasi-affine morphisms of
  schemes are stable under arbitrary base change.

## Implementation notes

The statement is Mathlib's `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`, so it
applies to every pullback square rather than to a chosen pullback. Since ind-quasi-affineness is
Zariski local on the base, it is enough to treat a base change of affine schemes; there the
second projection is affine, hence quasi-affine and ind-quasi-affine, so the composite
`pullback.fst f g ≫ f` is ind-quasi-affine and the first projection is ind-quasi-affine because
a factor of an ind-quasi-affine composite is ind-quasi-affine.

## References

* [Stacks Project, Tag 0AP7](https://stacks.math.columbia.edu/tag/0AP7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Ind-quasi-affine morphisms of schemes are stable under arbitrary base change. -/
@[stacks 0AP7]
instance isIndQuasiAffineHom_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@IsIndQuasiAffineHom : MorphismProperty Scheme.{u}) := by
  have hri : (AffineTargetMorphismProperty.of
      (@IsIndQuasiAffineHom : MorphismProperty Scheme.{u})).toProperty.RespectsIso :=
    AffineTargetMorphismProperty.respectsIso_of _
  have := HasAffineProperty.of_isZariskiLocalAtTarget
    (@IsIndQuasiAffineHom : MorphismProperty Scheme.{u})
  refine HasAffineProperty.isStableUnderBaseChange
    (AffineTargetMorphismProperty.IsStableUnderBaseChange.mk _ ?_)
  intro X Y S _ _ f g hg
  have hgP : IsIndQuasiAffineHom g := hg
  have : IsAffineHom (pullback.snd f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g)
      inferInstance
  have : IsQuasiAffineHom (pullback.snd f g) := isQuasiAffineHom_of_isAffineHom _
  have : IsIndQuasiAffineHom (pullback.fst f g ≫ f) := by
    rw [pullback.condition]
    exact MorphismProperty.comp_mem _ _ _ inferInstance hgP
  exact isIndQuasiAffineHom_of_comp (pullback.fst f g) f

end AlgebraicGeometry

end
