module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.SitePoints
public import StacksFrontier.CategoryTheory.Sites.Point.OfToposPoint
public import StacksFrontier.CategoryTheory.Sites.Point.Topos
public import StacksFrontier.CategoryTheory.Sites.Point.ToposPoints

/-!
# Pushing a geometric point forward along a morphism of small étale topoi

Let `B` be a big étale site containing schemes `X` and `Y`, and let
`g : Sh(X_étale) ⟶ Sh(Y_étale)` be a morphism of topoi — an *abstract* one, not assumed to come
from a morphism of schemes.  Let `x̄` be a geometric point of `X`, and `p` the associated point
of the small étale topos of `X`.  This file produces a geometric point `ȳ` of `Y` and an
identification

`g⁻¹(-)_{x̄} ≅ (-)_{ȳ}`

of stalk functors on sheaves of sets, which is the sentence

> Set `q = g ∘ p`.  This is a point of the small étale topos of `Y`.  By Lemma 59.29.12 we see
> that `q` corresponds to a geometric point `ȳ` of `Y`.  Consider the map of stalks
> `(g^♯)_p : (𝒪_Y)_{ȳ} = 𝒪_{Y, q} = (g⁻¹𝒪_Y)_p ⟶ 𝒪_{X, p} = (𝒪_X)_{x̄}`

of the proof of [Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6).  It is the step that
makes the stalk of `g⁻¹𝒪_Y` at `x̄` a stalk *at a geometric point of `Y`*, and so a strictly
henselian local ring; without it the stalk of `g⁻¹𝒪_Y` is the stalk at a point of the topos
about which nothing is known.

Three results of the library are composed, and nothing new is proved about any of them.

1. `CategoryTheory.GrothendieckTopology.Point.pointOfTopos`, Stacks 00YA (1): the point of the
   site `X_étale` attached to `x̄` by Stacks 04FM is a point of the *topos* `Sh(X_étale)`.
2. `CategoryTheory.MorphismOfTopoi.compPoint`, Stacks 05V2: composing it with `g` gives the
   point `q = g ∘ p` of `Sh(Y_étale)`, whose inverse image is `g⁻¹ ⋙ (-)_{x̄}` on the nose.
   `CategoryTheory.PointOfTopos.sitePointOfEssentiallySmall` and
   `CategoryTheory.PointOfTopos.sheafFiberIsoInverseImageOfEssentiallySmall`, Stacks 00YA (2),
   then present `q` by a point of the *site* `Y_étale`.
3. `AlgebraicGeometry.exists_geometricPoint_sitePoint_iso`, Stacks 04HU (1): that point of the
   site is isomorphic to the point attached to a geometric point of `Y`.

The one thing that was missing is that step 2 was stated for a site whose *type of objects* is
small at the universe of the sheaves, which the small étale site of Stacks 021B is not — its
objects lie one universe above its morphisms.  Essential smallness suffices, and that is how
`CategoryTheory.PointOfTopos.sitePointOfEssentiallySmall` is now stated.

Nothing here carries an `@[stacks 04I6]` tag: that tag asserts the existence and uniqueness of
a morphism of schemes `f : X ⟶ Y` together with a 2-isomorphism
`(g, g^♯) ≅ (f_small, f_small^♯)`, and this is one sentence inside its proof.  Nor does it carry
`@[stacks 05V2]` or `@[stacks 04HU]`: those are the general statements composed here, and they
are tagged where they are proved.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.sheafFiberIsoOfPointIso`: isomorphic points of a site
  have isomorphic stalk functors.
* `AlgebraicGeometry.exists_geometricPoint_inverseImage_comp_sheafFiberIso`: **the composite
  point `g ∘ x̄` is a geometric point of `Y`** — there is a geometric point `ȳ` of `Y` with
  `g⁻¹ ⋙ (-)_{x̄} ≅ (-)_{ȳ}` as functors on sheaves of sets.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04HU](https://stacks.math.columbia.edu/tag/04HU)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
* [Stacks Project, Tag 05V2](https://stacks.math.columbia.edu/tag/05V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- **Isomorphic points of a site have isomorphic stalk functors.**  A morphism of points of a
site induces a natural transformation of stalk functors in the opposite direction
(`CategoryTheory.GrothendieckTopology.Point.Hom.sheafFiber`), functorially, so an isomorphism of
points gives an isomorphism of stalk functors. -/
def sheafFiberIsoOfPointIso {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁ ≅ Φ₂) :
    Φ₁.sheafFiber (A := A) ≅ Φ₂.sheafFiber (A := A) where
  hom := Hom.sheafFiber e.inv
  inv := Hom.sheafFiber e.hom
  hom_inv_id := by rw [← Hom.sheafFiber_comp, e.hom_inv_id, Hom.sheafFiber_id]
  inv_hom_id := by rw [← Hom.sheafFiber_comp, e.inv_hom_id, Hom.sheafFiber_id]

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)

/-- **The composite of a morphism of small étale topoi with a geometric point is a geometric
point.**

Let `g : Sh(X_étale) ⟶ Sh(Y_étale)` be a morphism of topoi, not assumed to come from a morphism
of schemes, and let `x̄` be a geometric point of `X`.  Then there is a geometric point `ȳ` of
`Y` such that taking the inverse image along `g` and then the stalk at `x̄` is the stalk at `ȳ`,
naturally in the sheaf of sets.

This is the step `q = g ∘ p`, `q = ȳ` of the proof of
[Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6): the geometric point of `X` is a point
of the topos `Sh(X_étale)` by Stacks 00YA (1), composing with `g` gives a point of
`Sh(Y_étale)` by Stacks 05V2, Stacks 00YA (2) presents that point by a point of the site
`Y_étale`, and Stacks 04HU (1) identifies the latter with a geometric point of `Y`.

For a morphism of *ringed* topoi — which is what Stacks 04I6 is given — apply this to its
underlying morphism of topoi, `AlgebraicGeometry.RingedToposHom.toToposHom`. -/
theorem exists_geometricPoint_inverseImage_comp_sheafFiberIso
    (g : MorphismOfTopoi (Sheaf (SmallEtale.topology B X hX) (Type u))
      (Sheaf (SmallEtale.topology B Y hY) (Type u)))
    (x : GeometricPoint X) :
    ∃ y : GeometricPoint Y,
      Nonempty (g.inverseImage ⋙ (geometricPointSitePoint B X hX x).sheafFiber (A := Type u) ≅
        (geometricPointSitePoint B Y hY y).sheafFiber (A := Type u)) := by
  set q := g.compPoint (geometricPointSitePoint B X hX x).pointOfTopos with hq
  obtain ⟨y, ⟨e⟩⟩ := exists_geometricPoint_sitePoint_iso B Y hY q.sitePointOfEssentiallySmall
  exact ⟨y, ⟨q.sheafFiberIsoInverseImageOfEssentiallySmall.symm ≪≫
    GrothendieckTopology.Point.sheafFiberIsoOfPointIso e⟩⟩

end AlgebraicGeometry

end
