module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.Deformation.Groupoid.Loops

/-!
# Morphisms and isomorphisms of groupoids in functors from their two maps

A morphism of groupoids in functors carries six fields: the maps on the object and the arrow
functor, and that they respect source, target, identities and composition. The identity clause is
redundant — `AlgebraicGeometry.Space.mapIdentityOfMapComp` derives it from the other three — so a
morphism is determined by the two maps and three compatibilities, and this file packages that.

It also packages the isomorphisms. Given isomorphisms of the object and the arrow functor whose
forward directions respect source, target and composition, the backward directions respect them
too, and the two morphisms they define are mutually inverse because the underlying natural
transformations are: a morphism of groupoids in functors is determined by its two maps, so the
two round trips reduce by the extensionality lemma for `Deformation.GroupoidInFunctors.Hom` to the
two round trips of the given isomorphisms.

This is the shape in which a groupoid in functors described by one construction is compared with a
groupoid in functors described by another: an isomorphism in
`Deformation.GroupoidInFunctors` rather than one of the associated functors to `Grpd`, whose
inverse laws are literal equalities of functors.

## Main definitions

* `Deformation.GroupoidInFunctors.homOfMaps`: a morphism from its two maps.
* `Deformation.GroupoidInFunctors.isoOfMaps`: an isomorphism from two isomorphisms.

## Implementation notes

The file is placed beside `AlgebraicGeometry.GroupoidInAlgebraicSpaces` rather than beside
`Deformation.GroupoidInFunctors` because `AlgebraicGeometry.Space.mapIdentityOfMapComp`, which is
the whole reason the identity clause can be dropped, lives in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupoidInSpaces.lean`; nothing here is about
algebraic spaces.

## References

* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Deformation.GroupoidInFunctors

variable {D : Type u} [Category.{v} D] {G H : GroupoidInFunctors.{u, v, w} D}

/-- Two equal morphisms of type-valued functors agree at every section. -/
theorem app_apply_eq {A E : D ⥤ Type w} {f g : A ⟶ E} (e : f = g) (T : D) (x : A.obj T) :
    f.app T x = g.app T x := by
  rw [e]

/-- **A morphism of groupoids in functors from its two maps.** The clause for identities is not
asked for: `AlgebraicGeometry.Space.mapIdentityOfMapComp` derives it from source, target and
composition. -/
def homOfMaps (fo : G.objects ⟶ H.objects) (fa : G.arrows ⟶ H.arrows)
    (map_source : ∀ (T : D) (a : G.arrows.obj T),
      H.source.app T (fa.app T a) = fo.app T (G.source.app T a))
    (map_target : ∀ (T : D) (a : G.arrows.obj T),
      H.target.app T (fa.app T a) = fo.app T (G.target.app T a))
    (map_comp : ∀ (T : D) (a b : G.arrows.obj T)
        (h : G.source.app T a = G.target.app T b),
      H.compose T (fa.app T a) (fa.app T b)
          ((map_source T a).trans ((congrArg (fo.app T) h).trans (map_target T b).symm)) =
        fa.app T (G.compose T a b h)) :
    G ⟶ H where
  mapObjects := fo
  mapArrows := fa
  map_source := map_source
  map_target := map_target
  map_id := AlgebraicGeometry.Space.mapIdentityOfMapComp fo fa map_source map_target map_comp
  map_comp := map_comp

/-- The map on objects of `homOfMaps fo fa hs ht hc` is `fo`. -/
@[simp]
theorem homOfMaps_mapObjects (fo : G.objects ⟶ H.objects) (fa : G.arrows ⟶ H.arrows)
    (hs : ∀ (T : D) (a : G.arrows.obj T),
      H.source.app T (fa.app T a) = fo.app T (G.source.app T a))
    (ht : ∀ (T : D) (a : G.arrows.obj T),
      H.target.app T (fa.app T a) = fo.app T (G.target.app T a))
    (hc : ∀ (T : D) (a b : G.arrows.obj T) (h : G.source.app T a = G.target.app T b),
      H.compose T (fa.app T a) (fa.app T b)
          ((hs T a).trans ((congrArg (fo.app T) h).trans (ht T b).symm)) =
        fa.app T (G.compose T a b h)) :
    (homOfMaps fo fa hs ht hc).mapObjects = fo := rfl

/-- The map on arrows of `homOfMaps fo fa hs ht hc` is `fa`. -/
@[simp]
theorem homOfMaps_mapArrows (fo : G.objects ⟶ H.objects) (fa : G.arrows ⟶ H.arrows)
    (hs : ∀ (T : D) (a : G.arrows.obj T),
      H.source.app T (fa.app T a) = fo.app T (G.source.app T a))
    (ht : ∀ (T : D) (a : G.arrows.obj T),
      H.target.app T (fa.app T a) = fo.app T (G.target.app T a))
    (hc : ∀ (T : D) (a b : G.arrows.obj T) (h : G.source.app T a = G.target.app T b),
      H.compose T (fa.app T a) (fa.app T b)
          ((hs T a).trans ((congrArg (fo.app T) h).trans (ht T b).symm)) =
        fa.app T (G.compose T a b h)) :
    (homOfMaps fo fa hs ht hc).mapArrows = fa := rfl

section Iso

variable (eo : G.objects ≅ H.objects) (ea : G.arrows ≅ H.arrows)

/-- If an isomorphism of arrow functors respects a map to an isomorphism of object functors, so
does its inverse. -/
private theorem inv_map_of_map {A B E F : D ⥤ Type w} (eo : E ≅ F) (ea : A ≅ B)
    (sG : A ⟶ E) (sH : B ⟶ F)
    (h : ∀ (T : D) (a : A.obj T), sH.app T (ea.hom.app T a) = eo.hom.app T (sG.app T a))
    (T : D) (a : B.obj T) : sG.app T (ea.inv.app T a) = eo.inv.app T (sH.app T a) :=
  ((app_apply_eq eo.hom_inv_id T (sG.app T (ea.inv.app T a))).symm.trans
      (congrArg (eo.inv.app T) (h T (ea.inv.app T a)).symm)).trans
    (congrArg (fun z => eo.inv.app T (sH.app T z)) (app_apply_eq ea.inv_hom_id T a))

/-- The backward direction of the object isomorphism respects the source. -/
theorem inv_map_source
    (map_source : ∀ (T : D) (a : G.arrows.obj T),
      H.source.app T (ea.hom.app T a) = eo.hom.app T (G.source.app T a))
    (T : D) (a : H.arrows.obj T) :
    G.source.app T (ea.inv.app T a) = eo.inv.app T (H.source.app T a) :=
  inv_map_of_map eo ea G.source H.source map_source T a

/-- The backward direction of the object isomorphism respects the target. -/
theorem inv_map_target
    (map_target : ∀ (T : D) (a : G.arrows.obj T),
      H.target.app T (ea.hom.app T a) = eo.hom.app T (G.target.app T a))
    (T : D) (a : H.arrows.obj T) :
    G.target.app T (ea.inv.app T a) = eo.inv.app T (H.target.app T a) :=
  inv_map_of_map eo ea G.target H.target map_target T a

/-- The backward direction of the arrow isomorphism respects composition. -/
theorem inv_map_comp
    (map_source : ∀ (T : D) (a : G.arrows.obj T),
      H.source.app T (ea.hom.app T a) = eo.hom.app T (G.source.app T a))
    (map_target : ∀ (T : D) (a : G.arrows.obj T),
      H.target.app T (ea.hom.app T a) = eo.hom.app T (G.target.app T a))
    (map_comp : ∀ (T : D) (a b : G.arrows.obj T)
        (h : G.source.app T a = G.target.app T b),
      H.compose T (ea.hom.app T a) (ea.hom.app T b)
          ((map_source T a).trans ((congrArg (eo.hom.app T) h).trans (map_target T b).symm)) =
        ea.hom.app T (G.compose T a b h))
    (T : D) (a b : H.arrows.obj T) (h : H.source.app T a = H.target.app T b) :
    G.compose T (ea.inv.app T a) (ea.inv.app T b)
        ((inv_map_source eo ea map_source T a).trans
          ((congrArg (eo.inv.app T) h).trans (inv_map_target eo ea map_target T b).symm)) =
      ea.inv.app T (H.compose T a b h) :=
  ((app_apply_eq ea.hom_inv_id T
        (G.compose T (ea.inv.app T a) (ea.inv.app T b) _)).symm.trans
      (congrArg (ea.inv.app T) (map_comp T (ea.inv.app T a) (ea.inv.app T b) _).symm)).trans
    (congrArg (ea.inv.app T) (compose_congr H T _ h
      (app_apply_eq ea.inv_hom_id T a) (app_apply_eq ea.inv_hom_id T b)))

/-- **An isomorphism of groupoids in functors from an isomorphism of the object functors and an
isomorphism of the arrow functors** which respect source, target and composition. -/
def isoOfMaps
    (map_source : ∀ (T : D) (a : G.arrows.obj T),
      H.source.app T (ea.hom.app T a) = eo.hom.app T (G.source.app T a))
    (map_target : ∀ (T : D) (a : G.arrows.obj T),
      H.target.app T (ea.hom.app T a) = eo.hom.app T (G.target.app T a))
    (map_comp : ∀ (T : D) (a b : G.arrows.obj T)
        (h : G.source.app T a = G.target.app T b),
      H.compose T (ea.hom.app T a) (ea.hom.app T b)
          ((map_source T a).trans ((congrArg (eo.hom.app T) h).trans (map_target T b).symm)) =
        ea.hom.app T (G.compose T a b h)) :
    G ≅ H where
  hom := homOfMaps eo.hom ea.hom map_source map_target map_comp
  inv := homOfMaps eo.inv ea.inv (inv_map_source eo ea map_source)
    (inv_map_target eo ea map_target) (inv_map_comp eo ea map_source map_target map_comp)
  hom_inv_id := Hom.ext eo.hom_inv_id ea.hom_inv_id
  inv_hom_id := Hom.ext eo.inv_hom_id ea.inv_hom_id

/-- The map on objects of the forward morphism of `isoOfMaps eo ea` is `eo.hom`. -/
@[simp]
theorem isoOfMaps_hom_mapObjects
    (map_source : ∀ (T : D) (a : G.arrows.obj T),
      H.source.app T (ea.hom.app T a) = eo.hom.app T (G.source.app T a))
    (map_target : ∀ (T : D) (a : G.arrows.obj T),
      H.target.app T (ea.hom.app T a) = eo.hom.app T (G.target.app T a))
    (map_comp : ∀ (T : D) (a b : G.arrows.obj T)
        (h : G.source.app T a = G.target.app T b),
      H.compose T (ea.hom.app T a) (ea.hom.app T b)
          ((map_source T a).trans ((congrArg (eo.hom.app T) h).trans (map_target T b).symm)) =
        ea.hom.app T (G.compose T a b h)) :
    (isoOfMaps eo ea map_source map_target map_comp).hom.mapObjects = eo.hom := rfl

/-- The map on arrows of the forward morphism of `isoOfMaps eo ea` is `ea.hom`. -/
@[simp]
theorem isoOfMaps_hom_mapArrows
    (map_source : ∀ (T : D) (a : G.arrows.obj T),
      H.source.app T (ea.hom.app T a) = eo.hom.app T (G.source.app T a))
    (map_target : ∀ (T : D) (a : G.arrows.obj T),
      H.target.app T (ea.hom.app T a) = eo.hom.app T (G.target.app T a))
    (map_comp : ∀ (T : D) (a b : G.arrows.obj T)
        (h : G.source.app T a = G.target.app T b),
      H.compose T (ea.hom.app T a) (ea.hom.app T b)
          ((map_source T a).trans ((congrArg (eo.hom.app T) h).trans (map_target T b).symm)) =
        ea.hom.app T (G.compose T a b h)) :
    (isoOfMaps eo ea map_source map_target map_comp).hom.mapArrows = ea.hom := rfl

end Iso

end Deformation.GroupoidInFunctors

end
