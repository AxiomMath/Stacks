module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CoefficientsGerm

/-!
# The germ of the inverse image of a section, with coefficients in `Λ`-modules

Let `f : X ⟶ Y` be a morphism of a big étale site, let `Λ` be a commutative ring and let `G` be
a sheaf of `Λ`-modules on `Y_étale`. The comparison
`AlgebraicGeometry.SmallEtale.modPullbackStalkIso` of Stacks 03Q1 identifies the stalk of
`f^{-1}G` at a geometric point `x̄` of `X` with the stalk of `G` at the image point. This file
records what it does to the germ of an inverse image
`AlgebraicGeometry.SmallEtale.modPullbackUnitSection` of a section: the germ of `f^{-1}t`,
restricted to a pointed étale neighbourhood of `x̄` over the base change of a pointed étale
neighbourhood `V` of the image point, is carried to the germ of `t` over `V`.

This is the input that the pullback factor of
`AlgebraicGeometry.SmallEtale.stalkFiberSummandIso` needs in the stalk computation behind
[Stacks, Tag 0GKF].

## Main results

* `AlgebraicGeometry.SmallEtale.modPullbackUnitSection_comp_toPresheafFiber` — **the germ of the
  inverse image of a section is the germ of the section.**

## Implementation notes

`AlgebraicGeometry.SmallEtale.modPullbackStalkIso` is
`AlgebraicGeometry.smallEtalePullbackSheafFiberIso` at `Λ`-module coefficients, and
`AlgebraicGeometry.SmallEtale.modPullbackUnitSection` followed by restriction along the chosen
arrow is `AlgebraicGeometry.pullbackSectionAlongHom`, both definitionally. So this is
`AlgebraicGeometry.smallEtalePullbackSheafFiberIso_germ` — which is stated for arbitrary
coefficients, hence as an equality of morphisms — read at these coefficients, with
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber` in place of the colimit inclusion it
is definitionally equal to.

Nothing here carries a `stacks` attribute: Stacks 03Q1 on germs is attributed to
`AlgebraicGeometry.smallEtalePullbackSheafFiberIso_germ`, of which this is a reading at
particular coefficients.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.SmallEtale

universe u v

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- **The germ of the inverse image of a section is the germ of the section.** For a geometric
point `x̄` of `X`, a pointed étale neighbourhood `U` of `x̄`, a pointed étale neighbourhood `V` of
the image of `x̄`, and an arrow `U ⟶ X_V` compatible with the two markings, the comparison of
Stacks 03Q1 carries the germ at `U` of the restriction of `f^{-1}t` to the germ of `t` at
`V`. -/
public theorem modPullbackUnitSection_comp_toPresheafFiber
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (x : GeometricPoint X.obj)
    (U : (geometricPointFiber B X.obj X.property x).Elements)
    (V : (geometricPointFiber B Y.obj Y.property (x.map (B.inclusion.map f))).Elements)
    (a : U.1 ⟶ baseChange B f V.1)
    (ha : U.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map a ≫
      B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1) :
    (modPullbackUnitSection B Λ f G V.1 ≫
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map a.op) ≫
        (geometricPointSitePoint B X.obj X.property x).toPresheafFiber U.1 U.2
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj ≫
          (modPullbackStalkIso.{u, v, max (u + 1) v} B Λ f x).hom.app G =
      (geometricPointSitePoint B Y.obj Y.property (x.map (B.inclusion.map f))).toPresheafFiber
        V.1 V.2 G.obj := by
  let : HasProducts.{u} (ModuleCat.{max (u + 1) v} Λ) := fun _ => ModuleCat.hasLimitsOfShape
  exact smallEtalePullbackSheafFiberIso_germ B f x (ModuleCat.{max (u + 1) v} Λ) G U V a ha

end AlgebraicGeometry.SmallEtale

end
