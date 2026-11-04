module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineOpenKernelGlue
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.CharacterizingProperties

/-!
# The glued kernel of Tag 0GPA, compared on the affine opens of `X`

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` with `X` quasi-compact of
affine diagonal, and let `F : QCoh(O_X) ⥤ QCoh(O_Y)` be `R`-linear, right exact and commuting
with arbitrary direct sums.  `AlgebraicGeometry.gluedKernel` is the quasi-coherent module `K` on
`X ×_R Y` of construction (1) of [Stacks, Tag 0GPA].  This file identifies, for every affine
open `U` of `X`, the functor `F_K ∘ j_{U,*}` with `F ∘ j_{U,*}`.

Three identifications are composed.  `AlgebraicGeometry.affineSourceKernelIso` of Tag 0FZF
identifies `F ∘ j_{U,*}` with the integral transform on `U ×_R Y` of the kernel
`AlgebraicGeometry.openKernel` attached to `U`;
`AlgebraicGeometry.gluedKernelSourceChangeIso` identifies that kernel with the inverse image of
`K` along the chart `U ×_R Y ⟶ X ×_R Y`, which is the glueing's defining property read through
the comparison of restriction with inverse image; and
`AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated` of Tag 0GPB
identifies the integral transform of that inverse image with `F_K ∘ j_{U,*}` -- it needs only
that `X` be quasi-compact and quasi-separated, which the affine diagonal supplies, so no second
gluing is involved.

## Main definitions

* `AlgebraicGeometry.gluedKernelSourceChangeIso`: **the inverse image of the glued kernel along
  the chart of an affine open `U` of `X` is the kernel attached to `U`.**
* `AlgebraicGeometry.affineOpenGluedComparison`: **`F ∘ j_{U,*} ≅ F_K ∘ j_{U,*}` for every affine
  open `U` of `X`.**

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 0GPB](https://stacks.math.columbia.edu/tag/0GPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section Comparison

attribute [local instance] isOpenImmersion_openSubOverHom_left

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)

/-- The kernel attached to an affine open is the kernel attached to its inclusion. -/
theorem openKernel_eq_affineSourceKernel {U : X.left.Opens} (hU : IsAffineOpen U) :
    letI : IsAffine (openSubOver R X U).left := hU
    openKernel R X Y F hF hU = affineSourceKernel R X Y F hF (openSubOverHom R X U) := rfl

/-- **The inverse image of the glued kernel along the chart of an affine open `U` of `X` is the
kernel attached to `U`.**  This is `AlgebraicGeometry.gluedKernelChartIso` -- the defining
property of the glueing -- read through the comparison of restriction along an open immersion
with inverse image. -/
def gluedKernelSourceChangeIso {U : X.left.Opens} (hU : IsAffineOpen U) :
    sourceChangeKernel R X (openSubOver R X U) Y (openSubOverHom R X U)
        (gluedKernel R X Y F hF) ≅ openKernel R X Y F hF hU :=
  ObjectProperty.isoMk _
    (((Scheme.Modules.restrictFunctorIsoPullback
          (baseChangeOpenTargetMap R X Y U)).app (gluedKernel R X Y F hF).obj).symm ≪≫
      gluedKernelChartIso R X Y F hF ⟨U, hU⟩)

/-- **`F ∘ j_{U,*} ≅ F_K ∘ j_{U,*}` for every affine open `U` of `X`**, where `K` is the glued
kernel of construction (1) of [Stacks, Tag 0GPA]. -/
def affineOpenGluedComparison [CompactSpace X.left] {U : X.left.Opens} (hU : IsAffineOpen U) :
    letI : IsAffine (openSubOver R X U).left := hU
    quasicoherentPushforward (openSubOverHom R X U).left ⋙ F ≅
      quasicoherentPushforward (openSubOverHom R X U).left ⋙
        quasicoherentIntegralTransform R X Y (gluedKernel R X Y F hF) :=
  let : IsAffine (openSubOver R X U).left := hU
  let : IsAffineHom (openSubOverHom R X U).left :=
    isAffineHom_left_of_isAffine_left R X (openSubOverHom R X U)
  affineSourceKernelIso R X Y F hF (openSubOverHom R X U) ≪≫
    (integralTransformQcohFunctor R (openSubOver R X U) Y).mapIso
        (gluedKernelSourceChangeIso R X Y F hF hU).symm ≪≫
      (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X (openSubOver R X U) Y
        (openSubOverHom R X U) (gluedKernel R X Y F hF)).symm

end Comparison

end AlgebraicGeometry

end
