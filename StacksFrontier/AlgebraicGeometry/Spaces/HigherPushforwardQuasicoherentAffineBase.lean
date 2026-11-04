module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherent

/-!
# Quasi-coherence of the higher direct images from the affine-base case alone

`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward` reduces Stacks 0720
— quasi-coherence of `R^i f_*F` for a quasi-compact and quasi-separated morphism `f : X ⟶ Y` of
algebraic spaces and a quasi-coherent `F` — to its affine-base case `haffine`, carrying beside it
the hypothesis `h03F3`: the restriction of modules along the étale morphism `V ×_Y X ⟶ X` of each
étale scheme chart `V` of `Y` preserves injective modules.  That restriction is the pullback of
modules along an étale morphism of algebraic spaces, and the injective-preservation half of
Stacks 03F3, part (1), for an étale morphism of algebraic spaces is
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback`.  So `h03F3` is
discharged here and Stacks 0720 rests on its affine-base case alone.

No attribute is attached, the affine-base case
`AlgebraicGeometry.Space.AffineTargetHigherPushforwardQuasicoherent` being a hypothesis;
Stacks 0720 with the affine-base case discharged is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward'`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_affineTarget`:
  `R^i f_*F` is quasi-coherent, granted only the affine-base case in degree `i`.

## References

* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The higher direct images of a quasi-coherent module along a quasi-compact and
quasi-separated morphism are quasi-coherent, granted the affine-base case.**  This is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward` with its hypothesis
`h03F3` discharged by `AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback` at
the étale morphism `V ×_Y X ⟶ X` of each étale scheme chart `V` of `Y`. -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_of_affineTarget
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (i : ℕ)
    (haffine : AffineTargetHigherPushforwardQuasicoherent B S hS i) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived i).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_rightDerived_modulePushforward B S hS f hfqc hfqs F i
    (fun V => preservesInjectiveObjects_etaleModulePullback B S hS
      (chartBaseChangeInclusion B S hS f V) (isEtale_chartBaseChangeInclusion B S hS f V))
    haffine

end AlgebraicGeometry.Space

end
