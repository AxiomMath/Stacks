module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization

/-!
# Realizing a morphism of groupoid schemes as a morphism of groupoids in algebraic spaces

`Stacks.Groupoids.GroupoidScheme.realization` realizes a groupoid scheme (Stacks 0231) as a
groupoid in algebraic spaces (Stacks 043W) over a big fppf site containing its object scheme, its
arrow scheme and its scheme of composable pairs. This file makes the realization functorial in
morphisms of groupoid schemes: a morphism `φ : G ⟶ H` of groupoid schemes over `S` induces a
morphism of their realizations whose maps on object and arrow spaces are the Yoneda images of the
maps on object and arrow schemes of `φ`.

This is what is needed to form the 1-morphism `[U/P] ⟶ [U/R]` of Stacks 046Q for a morphism of
groupoid *schemes*, for instance the inclusion of an open subgroupoid in the proofs of
Stacks 0DU3, 0DU4 and 0DU5.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.Hom.realization`: the realization of a morphism of groupoid
  schemes.

## Main results

* `Stacks.Groupoids.GroupoidScheme.Hom.realization_mapObjects` and
  `Stacks.Groupoids.GroupoidScheme.Hom.realization_mapArrows`: its maps on object and arrow spaces
  are the Yoneda images of those of `φ`.
* `Stacks.Groupoids.GroupoidScheme.Hom.yonedaSchemePointEquiv_realization_mapArrows`: on
  generalized points, its map on arrows is composition with the map on arrow schemes of `φ`.

## Implementation notes

The identities of the evaluated groupoids of a realization are not given by a formula — the
groupoid structure is a chosen witness of a `Nonempty` — so compatibility with identities is
proved from compatibility with composition: the image of an identity arrow is an idempotent of a
groupoid, hence an identity.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Space

universe u

namespace Deformation.GroupoidInFunctors

variable {D : Type*} [Category D]

/-- **An idempotent arrow of an evaluated groupoid is the identity.** If the composite of an arrow
`e : x ⟶ x` with itself is `e`, then `e` is the identity arrow at `x`. -/
theorem eq_identity_of_compose_self (G : GroupoidInFunctors D) (T : D) (x : G.Evaluation T)
    (e : G.arrows.obj T) (hs : G.source.app T e = x) (ht : G.target.app T e = x)
    (he : G.compose T e e (hs.trans ht.symm) = e) : e = G.identity T x := by
  let f : x ⟶ x := (G.evaluationArrowEquiv T x x).symm ⟨e, hs, ht⟩
  have hf : (G.evaluationArrowEquiv T x x f).1 = e := by
    simp [f]
  have hff : f ≫ f = f := by
    apply (G.evaluationArrowEquiv T x x).injective
    apply Subtype.ext
    rw [evaluationArrowEquiv_comp]
    simpa only [hf] using he
  have h1 : f = 𝟙 x := by
    simpa using congrArg (· ≫ inv f) hff
  rw [← hf, h1, evaluationArrowEquiv_id]

end Deformation.GroupoidInFunctors

namespace Stacks.Groupoids.GroupoidScheme.Hom

variable {S : Scheme.{u}} (C : BigFppfSite.{u}) (hS : C.Contains S)

/-- On generalized points, the composition of the realization of a groupoid scheme is the
composition of generalized points of the groupoid scheme. -/
theorem yonedaSchemePointEquiv_realization_compose (G : GroupoidScheme S)
    (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (G.realization C hS hU hR hP).arrows.obj.obj T)
    (h : (G.realization C hS hU hR hP).toGroupoidInFunctors.source.app T a =
      (G.realization C hS hU hR hP).toGroupoidInFunctors.target.app T b)
    (w : yonedaSchemePointEquiv C hS hR T a ≫ G.source =
      yonedaSchemePointEquiv C hS hR T b ≫ G.target) :
    yonedaSchemePointEquiv C hS hR T
        ((G.realization C hS hU hR hP).toGroupoidInFunctors.compose T a b h) =
      G.compose (yonedaSchemePointEquiv C hS hR T a) (yonedaSchemePointEquiv C hS hR T b) w :=
  realizationComp_app G C hS hU hR hP T ⟨(a, b), h⟩ w

variable {G H : GroupoidScheme S} (φ : Hom G H)
  (hGU : C.Contains G.objects.left) (hGR : C.Contains G.arrows.left)
  (hGP : C.Contains (pullback G.source G.target).left)
  (hHU : C.Contains H.objects.left) (hHR : C.Contains H.arrows.left)
  (hHP : C.Contains (pullback H.source H.target).left)

/-- The arrow map of the realization of `φ` preserves composition: on generalized points it is
composition with the map on arrow schemes, which preserves composition of generalized arrows. -/
theorem realization_compose_map (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (G.realization C hS hGU hGR hGP).arrows.obj.obj T)
    (h : (G.realization C hS hGU hGR hGP).toGroupoidInFunctors.source.app T a =
      (G.realization C hS hGU hGR hGP).toGroupoidInFunctors.target.app T b)
    (h' : (H.realization C hS hHU hHR hHP).toGroupoidInFunctors.source.app T
        ((yoneda.map (schemeSiteMap C hS hGR hHR φ.mapArrows)).app T a) =
      (H.realization C hS hHU hHR hHP).toGroupoidInFunctors.target.app T
        ((yoneda.map (schemeSiteMap C hS hGR hHR φ.mapArrows)).app T b)) :
    (H.realization C hS hHU hHR hHP).toGroupoidInFunctors.compose T
        ((yoneda.map (schemeSiteMap C hS hGR hHR φ.mapArrows)).app T a)
        ((yoneda.map (schemeSiteMap C hS hGR hHR φ.mapArrows)).app T b) h' =
      (yoneda.map (schemeSiteMap C hS hGR hHR φ.mapArrows)).app T
        ((G.realization C hS hGU hGR hGP).toGroupoidInFunctors.compose T a b h) := by
  have hw : yonedaSchemePointEquiv C hS hGR T a ≫ G.source =
      yonedaSchemePointEquiv C hS hGR T b ≫ G.target := by
    have h₀ : (yoneda.map (schemeSiteMap C hS hGR hGU G.source)).app T a =
        (yoneda.map (schemeSiteMap C hS hGR hGU G.target)).app T b := h
    exact (yonedaSchemePointEquiv_map C hS hGR hGU G.source T a).symm.trans
      ((congrArg (yonedaSchemePointEquiv C hS hGU T) h₀).trans
        (yonedaSchemePointEquiv_map C hS hGR hGU G.target T b))
  have hw' : (yonedaSchemePointEquiv C hS hGR T a ≫ φ.mapArrows) ≫ H.source =
      (yonedaSchemePointEquiv C hS hGR T b ≫ φ.mapArrows) ≫ H.target := by
    rw [Category.assoc, Category.assoc, φ.map_source, φ.map_target, ← Category.assoc,
      ← Category.assoc, hw]
  have ha := yonedaSchemePointEquiv_map C hS hGR hHR φ.mapArrows T a
  have hb := yonedaSchemePointEquiv_map C hS hGR hHR φ.mapArrows T b
  have hcongr : ∀ {X : Over S} (f f' g g' : X ⟶ H.arrows) (_ : f = f') (_ : g = g')
      (w₁ : f ≫ H.source = g ≫ H.target) (w₂ : f' ≫ H.source = g' ≫ H.target),
      H.compose f g w₁ = H.compose f' g' w₂ := by
    rintro X f _ g _ rfl rfl w₁ w₂
    rfl
  apply (yonedaSchemePointEquiv C hS hHR T).injective
  refine (yonedaSchemePointEquiv_realization_compose C hS H hHU hHR hHP T _ _ h'
      (by rwa [ha, hb])).trans ?_
  refine Eq.trans ?_ (yonedaSchemePointEquiv_map C hS hGR hHR φ.mapArrows T _).symm
  rw [yonedaSchemePointEquiv_realization_compose C hS G hGU hGR hGP T a b h hw,
    φ.map_comp _ _ _ hw hw']
  exact hcongr _ _ _ _ ha hb _ _

/-- Yoneda images of a commuting square of arrow-to-object maps commute on generalized points. -/
private theorem yoneda_map_app_comm (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (G.realization C hS hGU hGR hGP).arrows.obj.obj T) (f : G.arrows ⟶ G.objects)
    (g : H.arrows ⟶ H.objects) (hfg : φ.mapArrows ≫ g = f ≫ φ.mapObjects) :
    (yoneda.map (schemeSiteMap C hS hHR hHU g)).app T
        ((yoneda.map (schemeSiteMap C hS hGR hHR φ.mapArrows)).app T a) =
      (yoneda.map (schemeSiteMap C hS hGU hHU φ.mapObjects)).app T
        ((yoneda.map (schemeSiteMap C hS hGR hGU f)).app T a) := by
  apply (yonedaSchemePointEquiv C hS hHU T).injective
  refine (yonedaSchemePointEquiv_map C hS hHR hHU g T _).trans ?_
  refine Eq.trans ?_ (yonedaSchemePointEquiv_map C hS hGU hHU φ.mapObjects T _).symm
  rw [yonedaSchemePointEquiv_map C hS hGR hHR φ.mapArrows T a,
    yonedaSchemePointEquiv_map C hS hGR hGU f T a, Category.assoc, Category.assoc, hfg]

/-- The map on arrow spaces of the realization of `φ` is compatible with the source maps. -/
theorem realization_map_source (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (G.realization C hS hGU hGR hGP).arrows.obj.obj T) :
    (H.realization C hS hHU hHR hHP).toGroupoidInFunctors.source.app T
        ((yoneda.map (schemeSiteMap C hS hGR hHR φ.mapArrows)).app T a) =
      (yoneda.map (schemeSiteMap C hS hGU hHU φ.mapObjects)).app T
        ((G.realization C hS hGU hGR hGP).toGroupoidInFunctors.source.app T a) :=
  yoneda_map_app_comm C hS φ hGU hGR hGP hHU hHR T a _ _ φ.map_source

/-- The map on arrow spaces of the realization of `φ` is compatible with the target maps. -/
theorem realization_map_target (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (G.realization C hS hGU hGR hGP).arrows.obj.obj T) :
    (H.realization C hS hHU hHR hHP).toGroupoidInFunctors.target.app T
        ((yoneda.map (schemeSiteMap C hS hGR hHR φ.mapArrows)).app T a) =
      (yoneda.map (schemeSiteMap C hS hGU hHU φ.mapObjects)).app T
        ((G.realization C hS hGU hGR hGP).toGroupoidInFunctors.target.app T a) :=
  yoneda_map_app_comm C hS φ hGU hGR hGP hHU hHR T a _ _ φ.map_target

/-- **The realization of a morphism of groupoid schemes.** A morphism `φ : G ⟶ H` of groupoid
schemes over `S` induces a morphism of the realizations of `G` and `H` as groupoids in algebraic
spaces over the terminal algebraic space of the site: its maps on object and arrow spaces are the
Yoneda images of the maps on object and arrow schemes of `φ`. Compatibility with source, target
and composition is that of `φ`, read on generalized points; compatibility with identities follows
from compatibility with composition, the image of an identity being an idempotent of a groupoid. -/
noncomputable def realization :
    AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom (G.realization C hS hGU hGR hGP)
      (H.realization C hS hHU hHR hHP) where
  toGroupoidHom :=
    { mapObjects := yoneda.map (schemeSiteMap C hS hGU hHU φ.mapObjects)
      mapArrows := yoneda.map (schemeSiteMap C hS hGR hHR φ.mapArrows)
      map_source := realization_map_source C hS φ hGU hGR hGP hHU hHR hHP
      map_target := realization_map_target C hS φ hGU hGR hGP hHU hHR hHP
      map_id := by
        intro T x
        let K := (H.realization C hS hHU hHR hHP).toGroupoidInFunctors
        let L := (G.realization C hS hGU hGR hGP).toGroupoidInFunctors
        let e := L.identity T x
        have hes : L.source.app T e = x := (L.evaluationArrowEquiv T x x (𝟙 x)).2.1
        have het : L.target.app T e = x := (L.evaluationArrowEquiv T x x (𝟙 x)).2.2
        have hee : L.compose T e e (hes.trans het.symm) = e := by
          have := L.evaluationArrowEquiv_comp T (𝟙 x) (𝟙 x)
          simp only [Category.comp_id] at this
          exact this.symm
        have hs' := (realization_map_source C hS φ hGU hGR hGP hHU hHR hHP T e).trans
          (congrArg _ hes)
        have ht' := (realization_map_target C hS φ hGU hGR hGP hHU hHR hHP T e).trans
          (congrArg _ het)
        exact K.eq_identity_of_compose_self T _ _ hs' ht'
          ((realization_compose_map C hS φ hGU hGR hGP hHU hHR hHP T e e
            (hes.trans het.symm) _).trans (congrArg _ hee))
      map_comp := fun T a b h =>
        realization_compose_map C hS φ hGU hGR hGP hHU hHR hHP T a b h _ }
  mapObjects_over := by
    change yoneda.map (schemeSiteMap C hS hGU hHU φ.mapObjects) ≫
        yoneda.map (schemeSiteMapToBase C hS hHU) = yoneda.map (schemeSiteMapToBase C hS hGU)
    rw [← yoneda.map_comp, schemeSiteMap_toBase]
  mapArrows_over := by
    change yoneda.map (schemeSiteMap C hS hGR hHR φ.mapArrows) ≫
        yoneda.map (schemeSiteMapToBase C hS hHR) = yoneda.map (schemeSiteMapToBase C hS hGR)
    rw [← yoneda.map_comp, schemeSiteMap_toBase]

/-- The map on object spaces of the realization of `φ` is the Yoneda image of the map on object
schemes of `φ`. -/
theorem realization_mapObjects :
    (realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapObjects =
      yoneda.map (schemeSiteMap C hS hGU hHU φ.mapObjects) := rfl

/-- The map on arrow spaces of the realization of `φ` is the Yoneda image of the map on arrow
schemes of `φ`. -/
theorem realization_mapArrows :
    (realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapArrows =
      yoneda.map (schemeSiteMap C hS hGR hHR φ.mapArrows) := rfl

/-- On generalized points, the map on arrows of the realization of `φ` is composition with the
map on arrow schemes of `φ`. -/
theorem yonedaSchemePointEquiv_realization_mapArrows (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (G.realization C hS hGU hGR hGP).arrows.obj.obj T) :
    yonedaSchemePointEquiv C hS hHR T
        ((realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapArrows.app T a) =
      yonedaSchemePointEquiv C hS hGR T a ≫ φ.mapArrows :=
  yonedaSchemePointEquiv_map C hS hGR hHR φ.mapArrows T a

/-- On generalized points, the map on objects of the realization of `φ` is composition with the
map on object schemes of `φ`. -/
theorem yonedaSchemePointEquiv_realization_mapObjects (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : (G.realization C hS hGU hGR hGP).objects.obj.obj T) :
    yonedaSchemePointEquiv C hS hHU T
        ((realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapObjects.app T x) =
      yonedaSchemePointEquiv C hS hGU T x ≫ φ.mapObjects :=
  yonedaSchemePointEquiv_map C hS hGU hHU φ.mapObjects T x

end Stacks.Groupoids.GroupoidScheme.Hom

end
