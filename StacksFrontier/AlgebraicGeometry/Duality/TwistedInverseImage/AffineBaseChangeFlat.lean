module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonFlat
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChange

/-!
# Base change of the twisted inverse image over an affine base: the flat case

For a cartesian square of quasi-compact and quasi-separated schemes with `g : Y' ⟶ Y` a morphism
of affine schemes, `f` proper, flat and of finite presentation and `f`, `g` Tor independent, the
base change map `L(g')^* a(K) ⟶ a'(Lg^*K)` of [Stacks, Tag 0AA6] is invertible for every
`K ∈ D_QCoh(𝒪_Y)`: part (1) of [Stacks, Tag 0AA8].
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Duality

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- In a cartesian square of quasi-compact and quasi-separated schemes, let `g : Y' ⟶ Y` be a
morphism of affine schemes, `f : X ⟶ Y` proper, and `f`, `g` Tor independent. If `f` is flat and
of finite presentation, the base change map `L(g')^* a(K) ⟶ a'(Lg^*K)` of [Stacks, Tag 0AA6] is an
isomorphism for every `K ∈ D_QCoh(𝒪_Y)`. -/
@[stacks 0AA8 "(1)"]
theorem isIso_twistedInverseImageBaseChangeMap_app_of_flat (sq : IsPullback g' f' f g)
    [IsAffine Y] [IsAffine Y'] [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hTor : TorIndependent f g) (K : quasiCoherentDerivedCategory Y) :
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
    IsIso ((twistedInverseImageBaseChangeMap g' f' f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      sq).app K) := by
  refine isIso_twistedInverseImageBaseChangeMap_app_of_isIso_compareWithPullbackTensor sq
    hTor K ?_
  rw [compareWithPullbackTensor_eq_comparisonMap f _ _ (fun _ _ => rfl)]
  have := isIso_comparisonMap_of_isAffine_of_flat f
    ((quasiCoherentDerivedPushforward g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
      (𝟙_ (quasiCoherentDerivedCategory Y'))) K
  infer_instance

end Stacks.Duality
