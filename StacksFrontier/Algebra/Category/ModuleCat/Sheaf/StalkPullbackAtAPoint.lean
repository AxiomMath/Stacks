module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackAtAPointPair
public import StacksFrontier.CategoryTheory.Sites.Point.OfToposPoint
public import StacksFrontier.CategoryTheory.Sites.Point.ToposPoints
public import StacksFrontier.CategoryTheory.Sites.Point.Topos
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a pullback of sheaves of modules at a point

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi and let `p` be a point of
`C` or of `Sh(C)`.  Writing `q = f ∘ p` for the composite point of `Sh(D)`, Stacks 05V5 says

`(f^*𝓕)_p ≅ 𝓕_q ⊗_{𝒪'_q} 𝒪_p`

for every `𝒪'`-module `𝓕`.  This file proves that, naturally in `𝓕`, for an arbitrary morphism
of ringed topoi and with nothing about the point assumed.

## The point `q`, and why nothing has to be assumed about it

`Stacks.Sheaves.StalkPullback.stalkFunctorIso` already proves the formula, but at a *matched
pair* `(Φ, Ψ)`: a point `Φ` of the source site together with a point `Ψ` of the target site and
an isomorphism `Ψ.sheafFiber ≅ f⁻¹ ⋙ Φ.sheafFiber` of stalk functors on sheaves of sets, both
supplied as data.  The pair is what the source produces rather than assumes, so the tag is not
discharged until `Ψ` and the isomorphism are built from `f` and `Φ` alone.

They are, in two steps, and neither step needs anything of `f` beyond its being a morphism of
ringed topoi.  A point `Φ` of the site `C` is a point of the topos `Sh(C)` by Stacks 00YA
part (1), `CategoryTheory.GrothendieckTopology.Point.pointOfTopos`; composing it with the
morphism of topoi underlying `f` gives the point `q = f ∘ p` of `Sh(D)`,
`CategoryTheory.MorphismOfTopoi.compPoint`, whose inverse image is `f⁻¹ ⋙ Φ.sheafFiber` on the
nose.  Stacks 00YA part (2), `CategoryTheory.PointOfTopos.sitePoint`, then presents `q` by a
point of the *site* `D`, and `CategoryTheory.PointOfTopos.sheafFiberIsoInverseImage` is exactly
the isomorphism of stalk functors the pair version wants.

The same two steps handle a point of `Sh(C)` rather than of `C`: the stalk functor on sheaves of
modules is defined over a point of the site, so a point `p` of the topos is first presented by
the point `p.sitePoint` of `C`, again by Stacks 00YA part (2).

## Main definitions

* `Stacks.Sheaves.StalkPullback.targetSitePoint`: the point `q = f ∘ Φ` of the target site.
* `Stacks.Sheaves.StalkPullback.pointStalkRingMap`: the induced map `𝒪'_q ⟶ 𝒪_Φ` of stalk rings,
  along which the comparison extends scalars.

## Main results

* `Stacks.Sheaves.StalkPullback.pointStalkFunctorIso`: **Stacks 05V5** for a morphism of ringed
  topoi and a point of the source site.
* `Stacks.Sheaves.StalkPullback.toposPointStalkFunctorIso`: **Stacks 05V5** for a morphism of
  ringed topoi and a point of the source topos.

## References

* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
* [Stacks Project, Tag 05V2](https://stacks.math.columbia.edu/tag/05V2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

noncomputable section

universe w v u v' u'

namespace Stacks.Sheaves.StalkPullback

section AtAPoint

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C] [Small.{w} Y.C]
  [HasSheafify Y.J (Type w)]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) (Φ : X.J.Point.{w})

/-- **The composite point `q = f ∘ Φ` of the target topos.**  The point `Φ` of the source site
is a point of the source topos by Stacks 00YA part (1); composing it with the morphism of topoi
underlying `f` gives a point of the target topos, Stacks 05V2. -/
def targetToposPoint : PointOfTopos.{w, v', u'} Y.J :=
  f.toToposHom.compPoint Φ.pointOfTopos

/-- **The point `q = f ∘ Φ` of the target site.**  The composite point of the target topos,
presented by a point of the target site through Stacks 00YA part (2). -/
def targetSitePoint : Y.J.Point.{w} := (targetToposPoint f Φ).sitePoint

/-- **The stalk functor at `q = f ∘ Φ` is `f⁻¹` followed by the stalk functor at `Φ`.**  This is
the identification of Stacks 00YA part (2) at the composite point: the inverse image of the
composite point of the topos is `f⁻¹ ⋙ Φ.sheafFiber` on the nose, so the comparison of the
stalk functor of `targetSitePoint` with that inverse image is already the required
isomorphism. -/
def targetSitePointStalkIso :
    (targetSitePoint f Φ).sheafFiber (A := Type w) ≅
      f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w) :=
  (targetToposPoint f Φ).sheafFiberIsoInverseImage

/-- **The map `𝒪'_q ⟶ 𝒪_Φ` of stalk rings**, along which Stacks 05V5 extends scalars: the stalk
at the composite point `q = f ∘ Φ` of the structure sheaf of the target maps to the stalk at `Φ`
of the structure sheaf of the source. -/
def pointStalkRingMap :
    Stacks.ringFiber (targetSitePoint f Φ) Y.O.obj →+* Stacks.ringFiber Φ X.O.obj :=
  stalkRingMap f Φ (targetSitePoint f Φ) (targetSitePointStalkIso f Φ)

/-- **Stacks 05V5**, for a morphism of ringed topoi `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` and a point
`Φ` of the source site `C`: the stalk at `Φ` of the pullback of a sheaf of `𝒪'`-modules is the
extension of scalars along `𝒪'_q ⟶ 𝒪_Φ` of its stalk at the composite point `q = f ∘ Φ`,
naturally in the module.

The point `q` of the target site is `targetSitePoint`, built from `f` and `Φ` by Stacks 00YA;
nothing about it is assumed. -/
@[stacks 05V5 "the formula `(f^*𝓕)_p ≅ 𝓕_q ⊗_{𝒪'_q} 𝒪_p`, naturally in `𝓕`, for an arbitrary
morphism of ringed topoi and a point `p` of the source site, with `q = f ∘ p` built from the
morphism and the point by Stacks 00YA"]
def pointStalkFunctorIso :
    f.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O ≅
      Stacks.sheafModuleFiberOfCommRing (targetSitePoint f Φ) Y.O ⋙
        ModuleCat.extendScalars (pointStalkRingMap f Φ) :=
  stalkFunctorIso f Φ (targetSitePoint f Φ) (targetSitePointStalkIso f Φ)

end AtAPoint

section AtAToposPoint

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C] [Small.{w} X.C] [Small.{w} Y.C]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w)]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) (p : PointOfTopos.{w, v, u} X.J)

/-- **The point `q = f ∘ p` of the target site**, for `p` a point of the source *topos*: the
composite point of the target topos, presented by a point of the target site through Stacks
00YA part (2). -/
def toposTargetSitePoint : Y.J.Point.{w} := (f.toToposHom.compPoint p).sitePoint

/-- **The stalk functor at `q = f ∘ p` is `f⁻¹` followed by the stalk functor of `p`.**  Both
the source and the target point are presented by points of their sites through Stacks 00YA
part (2), and the inverse image of the composite point of the topos is `f⁻¹ ⋙ p⁻¹` on the
nose. -/
def toposTargetSitePointStalkIso :
    (toposTargetSitePoint f p).sheafFiber (A := Type w) ≅
      f.toToposHom.inverseImage ⋙ p.sitePoint.sheafFiber (A := Type w) :=
  (f.toToposHom.compPoint p).sheafFiberIsoInverseImage ≪≫
    Functor.isoWhiskerLeft f.toToposHom.inverseImage p.sheafFiberIsoInverseImage.symm

/-- **The map `𝒪'_q ⟶ 𝒪_p` of stalk rings** for a point `p` of the source topos. -/
def toposPointStalkRingMap :
    Stacks.ringFiber (toposTargetSitePoint f p) Y.O.obj →+* Stacks.ringFiber p.sitePoint X.O.obj :=
  stalkRingMap f p.sitePoint (toposTargetSitePoint f p) (toposTargetSitePointStalkIso f p)

/-- **Stacks 05V5**, for a morphism of ringed topoi and a point `p` of the source *topos*
`Sh(C)`: the stalk at `p` of the pullback of a sheaf of `𝒪'`-modules is the extension of scalars
along `𝒪'_q ⟶ 𝒪_p` of its stalk at `q = f ∘ p`, naturally in the module.

The stalk functor on sheaves of modules is taken over a point of the site, so `p` is presented
by `p.sitePoint` through Stacks 00YA part (2); on sheaves of sets that is `p⁻¹` itself, by
`CategoryTheory.PointOfTopos.sheafFiberIsoInverseImage`. -/
@[stacks 05V5 "the formula `(f^*𝓕)_p ≅ 𝓕_q ⊗_{𝒪'_q} 𝒪_p`, naturally in `𝓕`, for an arbitrary
morphism of ringed topoi and a point `p` of the source topos `Sh(C)`, with `q = f ∘ p` built
from the morphism and the point by Stacks 00YA"]
def toposPointStalkFunctorIso :
    f.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing p.sitePoint X.O ≅
      Stacks.sheafModuleFiberOfCommRing (toposTargetSitePoint f p) Y.O ⋙
        ModuleCat.extendScalars (toposPointStalkRingMap f p) :=
  stalkFunctorIso f p.sitePoint (toposTargetSitePoint f p) (toposTargetSitePointStalkIso f p)

end AtAToposPoint

end Stacks.Sheaves.StalkPullback

end

end
