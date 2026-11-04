module

public import StacksFrontier.AlgebraicGeometry.AmpleQuasiAffinePullback.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.AffineBase

/-!
# H-quasi-projectivity of affine morphisms over a base with an ample sheaf

Let `S` be a scheme carrying an ample invertible module `M`, and let `f : X ⟶ S` be an affine
morphism locally of finite type. Then the pullback `f^* M` is ample on `X`, and, given the
immersion statement `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` (Stacks Tag
01VS), `f` is H-quasi-projective. In particular a quasi-projective affine morphism to `S` is
H-quasi-projective, which is part (2) of Stacks Tag 087S under the extra hypothesis that `f` is
affine.

## Main results

* `Stacks.HProjective.isHQuasiProjective_of_isAmple_base_of_isAffineHom`: an affine morphism
  locally of finite type to a base carrying an ample invertible module is H-quasi-projective,
  given `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`.
* `Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffineHom`: a quasi-projective
  affine morphism to a base carrying an ample invertible module is H-quasi-projective, given
  `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`.

## Implementation notes

An affine morphism is quasi-compact, so only the `LocallyOfFiniteType` half of finite type is
assumed in `Stacks.HProjective.isHQuasiProjective_of_isAmple_base_of_isAffineHom`. No relatively
ample module on `X` is needed: the ample module on `X` is the pullback of `M`.

## References

* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.HProjective

/-- An affine morphism `f : X ⟶ S` locally of finite type to a scheme `S` carrying an ample
invertible module `M` is H-quasi-projective, given
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`. -/
theorem isHQuasiProjective_of_isAmple_base_of_isAffineHom
    (hgap : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u}) {X S : Scheme.{u}}
      (f : X ⟶ S)
    [IsAffineHom f] [LocallyOfFiniteType f] (M : S.Modules)
    [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M) :
    IsHQuasiProjective f := by
  have hamp := Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom f M hM
  exact Stacks.QuasiProjectiveCompactification.isHQuasiProjective_of_isAmple f _ hamp inferInstance
    ((Stacks.PowerFamilyBridge.immersionTwistGap_iff f _).mpr (hgap X S f _))

/-- A quasi-projective affine morphism `f : X ⟶ S` to a scheme `S` carrying an ample invertible
module `M` is H-quasi-projective, given
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`. -/
theorem isHQuasiProjective_of_isQuasiProjective_of_isAffineHom
    (hgap : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u}) {X S : Scheme.{u}}
      (f : X ⟶ S)
    [IsAffineHom f] (M : S.Modules) [Stacks.Ample.IsInvertibleModule S M]
    (hM : Stacks.Ample.IsAmple S M) (hf : IsQuasiProjective f) : IsHQuasiProjective f := by
  have := hf.locallyOfFiniteType
  exact isHQuasiProjective_of_isAmple_base_of_isAffineHom hgap f M hM

end Stacks.HProjective

end
