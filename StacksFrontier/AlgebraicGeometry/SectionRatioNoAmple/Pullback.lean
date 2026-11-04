module

public import StacksFrontier.AlgebraicGeometry.SectionRatioNoAmple.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtensionNoAmple.Pullback
public import StacksFrontier.AlgebraicGeometry.HProjective.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveChartRoute.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of an ample invertible module along a quasi-affine morphism

Let `f : X ⟶ S` be a quasi-affine morphism and `M` an ample invertible module on `S`. Then `X` is
quasi-compact and quasi-separated, the pullback `f^* M` satisfies the surjectivity half of
[Stacks, Tag 01PW], and `f^* M` is ample. Consequently a quasi-affine morphism locally of finite
type to a base carrying an ample invertible module is H-quasi-projective, given
[Stacks, Tag 01VS] in either of the forms
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` or
`Stacks.QuasiProjectiveChartRoute.ChartImmersionUniform`.

## Main results

* `Stacks.SectionRatioNoAmple.compactSpace_and_quasiSeparatedSpace_of_isQuasiAffineHom`: the
  source of a quasi-affine morphism to a base with an ample invertible module is quasi-compact and
  quasi-separated.
* `Stacks.SectionRatioNoAmple.isSectionRatio_pullbackModule_of_isAmple`: the surjectivity half of
  [Stacks, Tag 01PW] holds for `f^* M`.
* `Stacks.SectionRatioNoAmple.basicOpenIsPow_pullbackModule_of_isAmple`: every basic open of a
  nonvanishing open of a power of `f^* M` is the nonvanishing open of a global section of a power
  of `f^* M`.
* `Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom`: the pullback of an
  ample invertible module along a quasi-affine morphism is ample.
* `Stacks.SectionRatioNoAmple.isHQuasiProjective_of_isAmple_base_of_isQuasiAffineHom` and
  `Stacks.SectionRatioNoAmple.isHQuasiProjective_of_isQuasiProjective_of_isQuasiAffineHom`: over a
  base with an ample invertible module, a quasi-affine morphism locally of finite type, or
  quasi-projective, is H-quasi-projective, given
  `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`.
* `Stacks.SectionRatioNoAmple.isHQuasiProjective_chartRoute_of_isQuasiAffineHom`: the same for a
  quasi-affine morphism locally of finite type, given
  `Stacks.QuasiProjectiveChartRoute.ChartImmersionUniform`.

## References

* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01SL](https://stacks.math.columbia.edu/tag/01SL)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory
open Stacks.SectionExtensionNoAmple (hasPointwiseNonvanishing_pullbackModule_of_isAmple)

universe u

namespace Stacks.SectionRatioNoAmple

section Pullback

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules) [IsInvertibleModule S M]

/-- If `f : X ⟶ S` is quasi-affine and `S` carries an ample invertible module, then `X` is
quasi-compact and quasi-separated. -/
theorem compactSpace_and_quasiSeparatedSpace_of_isQuasiAffineHom [IsQuasiAffineHom f]
    (hM : IsAmple S M) : CompactSpace X ∧ QuasiSeparatedSpace X := by
  have : CompactSpace S := Stacks.Ample.IsAmple.compactSpace S M hM
  have : QuasiSeparatedSpace S := Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple M hM
  exact ⟨QuasiCompact.compactSpace_of_compactSpace f, quasiSeparatedSpace_of_quasiSeparated f⟩

/-- The surjectivity half of [Stacks, Tag 01PW] for the pullback of an ample invertible module
along a quasi-affine morphism: every function on a nonvanishing open `X_s` of a power of `f^* M` is
a ratio of two global sections of a power of `f^* M`. -/
theorem isSectionRatio_pullbackModule_of_isAmple [IsQuasiAffineHom f] (hM : IsAmple S M) :
    Stacks.SectionExtension.IsSectionRatio X (Stacks.AmpleLocallyClosed.pullbackModule f M) := by
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_isQuasiAffineHom f M hM
  exact isSectionRatio_of_hasPointwiseNonvanishing _
    (hasPointwiseNonvanishing_pullbackModule_of_isAmple f M hM)

/-- For a quasi-affine morphism `f` and an ample invertible module `M`, every basic open of a
nonvanishing open of a power of `f^* M` is the nonvanishing open of a global section of a power of
`f^* M`. -/
theorem basicOpenIsPow_pullbackModule_of_isAmple [IsQuasiAffineHom f] (hM : IsAmple S M) :
    Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow X
      (Stacks.AmpleLocallyClosed.pullbackModule f M) := by
  exact Stacks.SectionExtension.basicOpenIsPow_of_isSectionRatio X _
    (isSectionRatio_pullbackModule_of_isAmple f M hM)

/-- The pullback of an ample invertible module along a quasi-affine morphism is ample. -/
@[stacks 0892 "part (2)", ega "II 5.1.12" "absolute case"]
theorem isAmple_modulePullback_of_isQuasiAffineHom [IsQuasiAffineHom f] (hM : IsAmple S M) :
    IsAmple X ((modulePullback f.toLRSHom.toShHom).obj M) :=
  Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isQuasiAffineHom f M
    (basicOpenIsPow_pullbackModule_of_isAmple f M hM) hM

end Pullback

/-! ### H-quasi-projectivity of quasi-affine morphisms -/

section HQuasiProjective

/-- A quasi-affine morphism locally of finite type to a base carrying an ample invertible module
is H-quasi-projective, given [Stacks, Tag 01VS] in the form
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`. -/
theorem isHQuasiProjective_of_isAmple_base_of_isQuasiAffineHom
    (hgap : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u})
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsQuasiAffineHom f] [LocallyOfFiniteType f] (M : S.Modules)
    [IsInvertibleModule S M] (hM : IsAmple S M) :
    Stacks.HProjective.IsHQuasiProjective f :=
  Stacks.QuasiProjectiveCompactification.isHQuasiProjective_of_isAmple f _
    (isAmple_modulePullback_of_isQuasiAffineHom f M hM) inferInstance
    ((Stacks.PowerFamilyBridge.immersionTwistGap_iff f _).mpr (hgap X S f _))

/-- Over a base carrying an ample invertible module, a quasi-projective quasi-affine morphism is
H-quasi-projective, given [Stacks, Tag 01VS] in the form
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`. -/
theorem isHQuasiProjective_of_isQuasiProjective_of_isQuasiAffineHom
    (hgap : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u})
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsQuasiAffineHom f] (M : S.Modules) [IsInvertibleModule S M] (hM : IsAmple S M)
    (hf : Stacks.HProjective.IsQuasiProjective f) : Stacks.HProjective.IsHQuasiProjective f := by
  have := hf.locallyOfFiniteType
  exact isHQuasiProjective_of_isAmple_base_of_isQuasiAffineHom hgap f M hM

/-- A quasi-affine morphism locally of finite type to a base carrying an ample invertible module
is H-quasi-projective, given [Stacks, Tag 01VS] in the form
`Stacks.QuasiProjectiveChartRoute.ChartImmersionUniform`. -/
theorem isHQuasiProjective_chartRoute_of_isQuasiAffineHom
    (hch : Stacks.QuasiProjectiveChartRoute.ChartImmersionUniform.{u})
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsQuasiAffineHom f] [LocallyOfFiniteType f] (M : S.Modules)
    [IsInvertibleModule S M] (hM : IsAmple S M) :
    Stacks.HProjective.IsHQuasiProjective f :=
  Stacks.QuasiProjectiveChartRoute.isHQuasiProjective_of_chartImmersion f _
    (isAmple_modulePullback_of_isQuasiAffineHom f M hM) inferInstance (hch X S f _)

end HQuasiProjective

end Stacks.SectionRatioNoAmple

end
