module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineTargetHigherDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherent

/-!
# Higher direct images of quasi-coherent modules are quasi-coherent, unconditionally

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  If `f` is quasi-compact and quasi-separated then every higher direct image `R^i f_*`
carries a quasi-coherent `𝒪_X`-module to a quasi-coherent `𝒪_Y`-module, for every `i`.  This is
Stacks 0720, and it is the statement below.
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward` is the source's
reduction to an affine base, with the affine case and part (1) of Stacks 03F3 as hypotheses;
here both are discharged.

The source's proof has two steps, and both are proved in this development.  The first is the
reduction to the case of an affine base: quasi-coherence of an `𝒪_Y`-module is tested on the
affine étale scheme charts `V` of `Y`, and over such a chart `R^i f_*F` restricts to
`R^i f'_*(F|_U)` for `U = V ×_Y X` and `f' : U ⟶ V` the base change of `f`.  That step is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_forall_affine_chart'`, by
Stacks 03M0, condition (4), and the higher-direct-image clause of Stacks 03LX; the hypotheses of
the base-changed morphism come from those of `f` by Stacks 03HF and Stacks 03KL, part (3).  The
second step is the affine-base case itself, which the source proves by induction on `i` from the
relative Leray spectral sequence of an affine étale cover of `X`; it is
`isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineSpace_target`, where the
spectral sequence is replaced by the dimension shifting it is used for.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward'`: **Stacks 0720**,
  the higher direct images of a quasi-coherent module under a quasi-compact and quasi-separated
  morphism of algebraic spaces are quasi-coherent.

## Implementation notes

*The injective-preservation half of Stacks 03F3* is what identifies `(R^i f_*F)|_V` with
`R^i f'_*(F|_U)`: base change for right derived functors needs étale restriction along the
structure morphism `U ⟶ X` to carry injective `𝒪_X`-modules to injective `𝒪_U`-modules.  On the
small étale site that is
`AlgebraicGeometry.Space.preservesInjectiveObjects_chartBaseChangeModulePullback`, which holds
for every `f`, representable or not, so no representability hypothesis is needed below.

*The degree* runs over all of `ℕ` in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`, the convention the source's proof is written in.  *The
module universe* is the universe `u` of the schemes, because
`AlgebraicGeometry.Space.modulePushforward` exists only there.  *The two local priority raises*
are needed because instance search for `Abelian` and for `EnoughInjectives` on the modules at
module universe `u` otherwise commits to the module-universe-`max u v r w` instances in the
import closure and then fails on the universe constraint.  Both attributes are `local`.

## References

* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0720.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
algebraic spaces over a scheme `S`, and let `F` be a quasi-coherent `𝒪_X`-module on the small
étale site of `X`. Then the higher direct image `R^i f_*F` is quasi-coherent for every `i`. -/
@[stacks 0720]
theorem isQuasicoherentOnSite_rightDerived_modulePushforward' {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived i).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_rightDerived_of_forall_affine_chart' B S hS f hfqc hfqs F i
    fun V hV hqc hqs _ ↦
      isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineSpace_target B S hS
        (chartBaseChangeProjection B S hS f V)
        (isAffineSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V) hV) hqc hqs i _
        (isQuasicoherentOnSite_etaleModulePullback B S hS
          (chartBaseChangeInclusion B S hS f V)
          (isEtale_chartBaseChangeInclusion B S hS f V) F inferInstance)

end AlgebraicGeometry.Space

end
