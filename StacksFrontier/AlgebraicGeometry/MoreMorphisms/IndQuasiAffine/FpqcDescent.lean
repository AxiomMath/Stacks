module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiAffine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IndQuasiAffine.BaseChange

/-!
# Ind-quasi-affineness is fpqc local on the base

Being an ind-quasi-affine morphism of schemes is preserved by base change and descends along
fpqc coverings of the target.

## Main results

* `AlgebraicGeometry.isIndQuasiAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact`:
  if the base change of a morphism along a surjective flat quasi-compact morphism is
  ind-quasi-affine, then so is the morphism itself.
* `AlgebraicGeometry.isIndQuasiAffineHom_isLocalAtTarget_fpqc`: ind-quasi-affineness of a
  morphism of schemes is fpqc local on the base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Ind-quasi-affine morphisms of schemes satisfy fpqc descent: if the base change of `g` along a
surjective flat quasi-compact morphism is ind-quasi-affine, then so is `g`. -/
instance isIndQuasiAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@IsIndQuasiAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have hbc : MorphismProperty.IsStableUnderBaseChange (C := Scheme.{u})
      (@Surjective ⊓ @Flat) := .inf
  have hcomp : MorphismProperty.IsStableUnderComposition (C := Scheme.{u})
      (@Surjective ⊓ @Flat) :=
    have := instIsMultiplicativeSchemeSurjective.{u}.toIsStableUnderComposition
    .inf
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact @IsIndQuasiAffineHom
    (@Surjective ⊓ @Flat) Stacks.Descent.isLocalIso_inf_surjective_le_surjective_inf_flat ?_
  intro R S Y φ g hφ hfst
  obtain ⟨_, _⟩ := hφ
  rw [isIndQuasiAffineHom_iff_isIndQuasiAffine] at hfst ⊢
  refine ⟨fun W hW => ?_⟩
  have hqa : Scheme.IsQuasiAffine ((pullback.snd (Spec.map φ) g) ⁻¹ᵁ W).toScheme :=
    hfst.isQuasiAffine _ ((pullback.snd (Spec.map φ) g).isCompact_preimage hW)
  exact Stacks.Descent.isQuasiAffine_of_isPullback_of_flat
    (((isPullback_morphismRestrict (pullback.snd (Spec.map φ) g) W).flip.paste_horiz
      (IsPullback.of_hasPullback (Spec.map φ) g)).flip) hqa

/-- Being an ind-quasi-affine morphism of schemes is fpqc local on the base. -/
@[stacks 0AP8]
instance isIndQuasiAffineHom_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@IsIndQuasiAffineHom : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@IsIndQuasiAffineHom : MorphismProperty Scheme.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

end AlgebraicGeometry

end
