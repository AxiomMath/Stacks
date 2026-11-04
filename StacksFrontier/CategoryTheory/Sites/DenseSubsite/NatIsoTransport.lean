module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.CategoryTheory.Sites.Point.Topos
public import StacksFrontier.CategoryTheory.Sites.Point.ToposPoints

/-!
# Transporting a natural isomorphism off a dense subsite

Let `G : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)` — for the small affine étale site
inside the small étale site this is [Stacks Project, Tag 04HR],
`AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous`.  Restriction of sheaves
along `G`, `CategoryTheory.Functor.sheafPushforwardContinuous`, is then **full and faithful**
(indeed an equivalence onto the sheaves on the subsite).

Consequently a natural transformation, or isomorphism, between two functors *landing in* sheaves
on the big site may be recovered from its restriction to the subsite.  That is the content of this
file:

`F₁ ⋙ ρ ≅ F₂ ⋙ ρ  ⟹  F₁ ≅ F₂`,

where `ρ` is restriction along `G`.

## This is cancellation on the *right*, and that is the only direction available

It is worth being explicit about which "restriction to the affine charts" a dense subsite buys,
because the useful one is not the obvious one.

*Not* available is cancellation on the **left**: from an isomorphism of `G ⋙ F₁` and `G ⋙ F₂`,
for functors `F₁ F₂ : D ⥤ A` *indexed* by the big site, one cannot conclude `F₁ ≅ F₂`.  Density
of `G` says that every object of `D` is covered by objects in the image of `G`, not that every
object of `D` *is* one; `G` is not essentially surjective, and a covariant functor on `D` is not
determined by its restriction to `C` without a descent argument supplying the colimit
presentation of each object of `D` by a cover.

Available — and this is what the file proves — is cancellation on the **right**, for functors
whose *values* are sheaves on `(D, K)`.  A sheaf on `(D, K)` genuinely is determined by its
restriction to the dense subsite, and so is a morphism of such sheaves; that is exactly the full
faithfulness of restriction.

In the application to the existence half of [Stacks Project, Tag 04I6] the direct images `g_*` and
`f_{small,*}` are functors whose values are sheaves on the small étale site of `Y`, so the
comparison of direct images is obtained by **right** cancellation from its restriction to the
affine charts, and the per-chart comparison itself is never needed at a non-affine chart.

## Main results

* `CategoryTheory.Functor.IsDenseSubsite.natIsoOfRestriction` — right cancellation of a natural
  isomorphism along restriction to a dense subsite.
* `CategoryTheory.Functor.IsDenseSubsite.natTrans_injective_of_restriction` — the same at the
  level of natural transformations: a natural transformation is determined by its restriction.
* `CategoryTheory.GrothendieckTopology.Point.sheafFiber_inverseImage` —
  [Stacks Project, Tag 05V2] read at a point of the *site* rather than of the topos, through the
  already-available bridge `CategoryTheory.GrothendieckTopology.Point.pointOfTopos`.

## References

* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 05V2](https://stacks.math.columbia.edu/tag/05V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u v' u' v'' u''

namespace CategoryTheory.Functor.IsDenseSubsite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  (A : Type u'') [Category.{v''} A] [G.IsDenseSubsite J K]
  {E : Type*} [Category* E] {F₁ F₂ : E ⥤ Sheaf K A}

/-- **A natural isomorphism of sheaf-valued functors is determined by its restriction to a dense
subsite.**  Restriction along `G` is fully faithful
(`CategoryTheory.Functor.IsDenseSubsite.full_sheafPushforwardContinuous` and
`CategoryTheory.Functor.IsDenseSubsite.faithful_sheafPushforwardContinuous`), so it reflects
isomorphisms of functors into it.

This is the transport the existence half of [Stacks Project, Tag 04I6] needs along
[Stacks Project, Tag 04HR]: the comparison of direct images is produced on the affine étale charts
of `Y` and extended to all of `Y_étale` here. -/
def natIsoOfRestriction
    (i : F₁ ⋙ G.sheafPushforwardContinuous A J K ≅ F₂ ⋙ G.sheafPushforwardContinuous A J K) :
    F₁ ≅ F₂ :=
  Functor.fullyFaithfulCancelRight (G.sheafPushforwardContinuous A J K) i

/-- **A natural transformation of sheaf-valued functors is determined by its restriction to a
dense subsite**, restriction along `G` being faithful. -/
theorem natTrans_injective_of_restriction {α β : F₁ ⟶ F₂}
    (h : whiskerRight α (G.sheafPushforwardContinuous A J K) =
      whiskerRight β (G.sheafPushforwardContinuous A J K)) :
    α = β := by
  refine NatTrans.ext (funext fun e => ?_)
  exact (G.sheafPushforwardContinuous A J K).map_injective
    (congrArg (fun γ => γ.app e) h)

end CategoryTheory.Functor.IsDenseSubsite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J)

/-- **[Stacks Project, Tag 05V2] at a point of the site.**  For a morphism of topoi `f` from
`Sh(C, J)` to `Sh(D, K)` and a point `Φ` of the site `(C, J)`, the fibre at `Φ` of the inverse
image of a sheaf `ℱ` on `(D, K)` is the stalk of `ℱ` at the composed point of `Sh(D, K)`.

No bridge between the two notions of point has to be built: a point of a site already *is* a point
of its topos, by `CategoryTheory.GrothendieckTopology.Point.pointOfTopos` (Stacks 00YA (1)), whose
inverse image is the fibre functor on the nose
(`CategoryTheory.GrothendieckTopology.Point.pointOfTopos_inverseImage`).  So
`MorphismOfTopoi.stalk_inverseImage` applies verbatim, and this statement is it. -/
@[stacks 05V2 "at a point of the site"]
theorem sheafFiber_inverseImage {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))) (F : Sheaf K (Type w)) :
    Φ.sheafFiber.obj (f.inverseImage.obj F) = (f.compPoint Φ.pointOfTopos).stalk F :=
  MorphismOfTopoi.stalk_inverseImage f Φ.pointOfTopos F

end CategoryTheory.GrothendieckTopology.Point

end
