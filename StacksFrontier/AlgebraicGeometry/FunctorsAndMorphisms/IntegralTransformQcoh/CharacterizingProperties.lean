module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ExactKernels

/-!
# Properties of an integral transform with quasi-compact source of affine diagonal

Let `R` be a commutative ring and let `X` and `Y` be schemes over `R`, with `X` quasi-compact
of affine diagonal.  A quasi-coherent module `K` on `X ×_R Y` has an integral transform
`AlgebraicGeometry.quasicoherentIntegralTransform`, and this file proves that it is right exact
after direct image along a morphism with affine source, in particular along the inclusion of an
affine open.  This is property (2) of [Stacks Project, Tag 0GPB]; the characterization of the
integral transforms by the three properties of that tag is
`AlgebraicGeometry.nonempty_iso_quasicoherentIntegralTransform_iff`, in
`StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Characterization`.

## Main results

* `AlgebraicGeometry.preservesFiniteColimits_quasicoherentPushforward_comp_integralTransform`
  and `AlgebraicGeometry.preservesFiniteColimits_affineOpenPushforward_comp_integralTransform`:
  the integral transform composed with the direct image along a morphism with affine source,
  respectively along the inclusion of an affine open, is right exact.

## Implementation notes

The direct image along a morphism `f` with affine source and target of affine diagonal is
affine, by Tag 01SG as recorded in `AlgebraicGeometry.isAffineHom_left_of_isAffine_left`; the
integral transform of `K` precomposed with it is the integral transform of `(f × id_Y)^*K` on the
affine source, which is right exact by Tag 0FZD.  The content of that identification is the
isomorphism of pullback--tensor--pushforward formulae
`AlgebraicGeometry.integralTransformFormulaSourceChangeIso`, which assumes only affineness of
`f`; what has to be redone is only its transport to quasi-coherent modules, since the form of
it carrying Tag 0FZF assumes in addition that `X` itself is affine, which is exactly the
hypothesis this file does without.

## References

* [Stacks Project, Tag 0GPB](https://stacks.math.columbia.edu/tag/0GPB)
* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 01SG](https://stacks.math.columbia.edu/tag/01SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (X X' Y : Over (Spec (.of R)))

/-- Affine change of source for the integral transform of a quasi-coherent kernel, with the
source quasi-compact and quasi-separated rather than affine.  The underlying isomorphism of
pullback--tensor--pushforward formulae is `integralTransformFormulaSourceChangeIso`, which
needs only affineness of `f`; this transports it to quasi-coherent modules, which is the one
step of `quasicoherentIntegralTransformSourceChangeIso` that uses affineness of `X`. -/
def quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace X'.left] [QuasiSeparatedSpace X'.left]
    (f : X' ⟶ X) [IsAffineHom f.left]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    quasicoherentPushforward f.left ⋙ quasicoherentIntegralTransform R X Y K ≅
      quasicoherentIntegralTransform R X' Y (sourceChangeKernel R X X' Y f K) :=
  ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
      _).preimageIso
    (Functor.isoWhiskerLeft (quasicoherentPushforward f.left)
        (quasicoherentIntegralTransformData R X Y K).comparison ≪≫
      integralTransformFormulaSourceChangeIso R X X' Y f K ≪≫
      (quasicoherentIntegralTransformData R X' Y
        (sourceChangeKernel R X X' Y f K)).comparison.symm)

/-- **The integral transform is right exact after direct image from an affine source.**  Let `X`
be quasi-compact of affine diagonal and let `f : X' ⟶ X` be a morphism of schemes over `R` whose
source is affine.  The integral transform of a quasi-coherent kernel on `X ×_R Y`, precomposed
with the direct image along `f`, is right exact. -/
theorem preservesFiniteColimits_quasicoherentPushforward_comp_integralTransform
    [CompactSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    [IsAffine X'.left] (f : X' ⟶ X)
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
    PreservesFiniteColimits
      (quasicoherentPushforward f.left ⋙ quasicoherentIntegralTransform R X Y K) := by
  let : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
  let e := quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f K
  refine ⟨fun J _ _ => ?_⟩
  let : PreservesColimitsOfShape J
      (quasicoherentIntegralTransform R X' Y (sourceChangeKernel R X X' Y f K)) :=
    (preservesFiniteColimits_quasicoherentIntegralTransform R X' Y
      (sourceChangeKernel R X X' Y f K)).preservesFiniteColimits J
  exact preservesColimitsOfShape_of_natIso e.symm

/-- **The integral transform is right exact after direct image from an affine open**, property
(2) of Tag 0GPB.  Let `X` be quasi-compact of affine diagonal and let `U` be an affine open of
`X`.  The integral transform of a quasi-coherent kernel on `X ×_R Y`, precomposed with the
direct image along the inclusion of `U`, is right exact. -/
theorem preservesFiniteColimits_affineOpenPushforward_comp_integralTransform
    [CompactSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    {U : X.left.Opens} (hU : IsAffineOpen U)
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    letI : IsAffine (sourceOver R X U.ι).left := hU
    letI : IsAffineHom U.ι :=
      isAffineHom_left_of_isAffine_left R X (sourceOverHom R X U.ι)
    PreservesFiniteColimits
      (quasicoherentPushforward U.ι ⋙ quasicoherentIntegralTransform R X Y K) := by
  let : IsAffine (sourceOver R X U.ι).left := hU
  exact preservesFiniteColimits_quasicoherentPushforward_comp_integralTransform R X
    (sourceOver R X U.ι) Y (sourceOverHom R X U.ι) K

end AlgebraicGeometry

end
