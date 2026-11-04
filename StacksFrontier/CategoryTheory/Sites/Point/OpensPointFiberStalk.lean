module

public import Mathlib.Topology.Sheaves.Points
public import Mathlib.Topology.Sheaves.Stalks

/-!
# The fibre of a presheaf at a point of the site of opens is its stalk

Let `X` be a topological space and `x : X`. The point `Opens.pointGrothendieckTopology x` of the
site `(Opens X, grothendieckTopology X)` has fibre functor `U ↦ (x ∈ U)`, so the fibre of a
presheaf `F` at that point is the colimit of `F` over the open sets containing `x`. That colimit
is the stalk `F.stalk x` of `F` at `x`.

This file supplies the resulting isomorphism, its compatibility with the canonical maps out of
the sections — the germ maps on the stalk side, the maps
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber` on the fibre side — and its
naturality in `F`.

## Main definitions

* `Opens.pointFiberStalkHom` and `Opens.pointFiberStalkInv`: the two mutually inverse
  comparison maps between the fibre at the point attached to `x` and the stalk at `x`.
* `Opens.pointFiberStalkIso`: the fibre of a presheaf at the point of the site of opens
  attached to `x` is the stalk at `x`.
* `Opens.pointFiberStalkFunctorIso`: the same isomorphism, as an isomorphism of functors.

## Main results

* `Opens.toPresheafFiber_pointFiberStalkHom`: the comparison map carries the canonical map out
  of the sections on an open neighbourhood of `x` to the germ map.
* `Opens.germ_pointFiberStalkInv`: the inverse comparison map carries the germ map to the
  canonical map out of the sections.
* `Opens.pointFiberStalkIso_natural`: the isomorphism is natural in the presheaf.

## Implementation notes

Both sides are colimits of `F` over a category of open neighbourhoods of `x`: the category of
elements of the fibre functor on the fibre side, and `TopologicalSpace.OpenNhds x` on the stalk
side. The two index categories are equivalent, but the two maps are written down here by the two
universal properties directly, which keeps the compatibility statements free of any comparison
functor.

The target category is arbitrary, subject to having the colimits that both the stalk and the
fibre of a presheaf are defined by. For a space `X : TopCat.{v}` the point lives in
`CategoryTheory.GrothendieckTopology.Point.{v}`, and `HasColimits C` for a category `C` with
morphisms in `Type v` is exactly the hypothesis both constructions need.

## References

* [Stacks Project, Section 7.32 (Tag 00Y3)](https://stacks.math.columbia.edu/tag/00Y3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace Opens

variable {C : Type u} [Category.{v} C] [HasColimits C] {X : TopCat.{v}} (x : X)

/-- **The comparison map from the fibre of a presheaf at the point attached to `x` to its stalk
at `x`.** Both are colimits over the open neighbourhoods of `x`, and this is the map out of the
fibre whose component at an open neighbourhood `U` is the germ map of `U`. -/
def pointFiberStalkHom (F : X.Presheaf C) :
    (pointGrothendieckTopology x).presheafFiber.obj F ⟶ F.stalk x :=
  (pointGrothendieckTopology x).presheafFiberDesc (fun U hU => F.germ U x hU.down.down)
    (fun _ _ g _ => F.germ_res g x _)

/-- The comparison map of `Opens.pointFiberStalkHom` carries the canonical map from the sections
of a presheaf over an open neighbourhood of `x` into the fibre to the germ map at `x`. -/
@[reassoc (attr := simp)]
theorem toPresheafFiber_pointFiberStalkHom (F : X.Presheaf C) (U : Opens X)
    (hU : (pointGrothendieckTopology x).fiber.obj U) :
    (pointGrothendieckTopology x).toPresheafFiber U hU F ≫ pointFiberStalkHom x F =
      F.germ U x hU.down.down := by
  simp [pointFiberStalkHom]

/-- **The comparison map from the stalk of a presheaf at `x` to its fibre at the point attached
to `x`.** It is the map out of the stalk whose component at an open neighbourhood `U` of `x` is
the canonical map from the sections over `U` into the fibre. -/
def pointFiberStalkInv (F : X.Presheaf C) :
    F.stalk x ⟶ (pointGrothendieckTopology x).presheafFiber.obj F :=
  colimit.desc _
    (Cocone.mk ((pointGrothendieckTopology x).presheafFiber.obj F)
      { app := fun U =>
          (pointGrothendieckTopology x).toPresheafFiber (unop U).1 ⟨⟨(unop U).2⟩⟩ F
        naturality := fun _ V g =>
          ((pointGrothendieckTopology x).toPresheafFiber_w
            ((OpenNhds.inclusion x).map g.unop) ⟨⟨(unop V).2⟩⟩ F).trans
              (Category.comp_id _).symm })

/-- The comparison map of `Opens.pointFiberStalkInv` carries the germ map at `x` to the
canonical map from the sections into the fibre. -/
@[reassoc (attr := simp)]
theorem germ_pointFiberStalkInv (F : X.Presheaf C) (U : Opens X) (hx : x ∈ U) :
    F.germ U x hx ≫ pointFiberStalkInv x F =
      (pointGrothendieckTopology x).toPresheafFiber U ⟨⟨hx⟩⟩ F := by
  apply colimit.ι_desc

/-- **The fibre of a presheaf at a point of the site of opens is its stalk.** For `x : X` the
fibre functor of the point `Opens.pointGrothendieckTopology x` sends an open `U` to the
proposition `x ∈ U`, so the fibre of a presheaf `F` at that point is the colimit of `F` over the
open neighbourhoods of `x`, which is the stalk of `F` at `x`. -/
@[simps]
def pointFiberStalkIso (F : X.Presheaf C) :
    (pointGrothendieckTopology x).presheafFiber.obj F ≅ F.stalk x where
  hom := pointFiberStalkHom x F
  inv := pointFiberStalkInv x F
  hom_inv_id := by
    refine (pointGrothendieckTopology x).presheafFiber_hom_ext fun U hU => ?_
    rw [toPresheafFiber_pointFiberStalkHom_assoc, germ_pointFiberStalkInv, Category.comp_id]
    rfl
  inv_hom_id := by
    refine TopCat.Presheaf.stalk_hom_ext F fun U hx => ?_
    rw [germ_pointFiberStalkInv_assoc]
    exact (toPresheafFiber_pointFiberStalkHom x F U ⟨⟨hx⟩⟩).trans (Category.comp_id _).symm

/-- **The isomorphism between the fibre at a point of the site of opens and the stalk is natural
in the presheaf.** -/
theorem pointFiberStalkIso_natural {F G : X.Presheaf C} (f : F ⟶ G) :
    (pointGrothendieckTopology x).presheafFiber.map f ≫ pointFiberStalkHom x G =
      pointFiberStalkHom x F ≫ (TopCat.Presheaf.stalkFunctor C x).map f :=
  (pointGrothendieckTopology x).presheafFiber_hom_ext fun U hU =>
    (((pointGrothendieckTopology x).toPresheafFiber_naturality_assoc f U hU
          (pointFiberStalkHom x G)).trans
        (congrArg (fun g => f.app (op U) ≫ g)
          (toPresheafFiber_pointFiberStalkHom x G U hU))).trans
      ((TopCat.Presheaf.stalkFunctor_map_germ U x hU.down.down f).symm.trans
        (toPresheafFiber_pointFiberStalkHom_assoc x F U hU
          ((TopCat.Presheaf.stalkFunctor C x).map f)).symm)

/-- **The fibre of a presheaf at a point of the site of opens is its stalk, naturally in the
presheaf.** -/
def pointFiberStalkFunctorIso :
    (pointGrothendieckTopology x).presheafFiber ≅ TopCat.Presheaf.stalkFunctor C x :=
  NatIso.ofComponents (pointFiberStalkIso x) fun f => pointFiberStalkIso_natural x f

end Opens

end
