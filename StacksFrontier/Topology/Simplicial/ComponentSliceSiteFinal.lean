module

public import StacksFrontier.Topology.Simplicial.ComponentSliceSite
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.IsConnected

/-!
# The localization at an open of the inclusion of a simplicial degree is final

Let `X` be a simplicial topological space, `n` a simplicial degree and `W` an open of `X_n`. The
inclusion of the open-set site of `X_n` into the total site of `X` localizes at `W` to a functor
`CategoryTheory.Over.post (levelFunctor X n) : Over W ⥤ Over (n, W)` of slices
(`StacksFrontier/Topology/Simplicial/ComponentSliceSite.lean`). This file records that this
localization is faithful and final. Both rest on the slice of an open-set site being thin; for
finality, the comma category of arrows from an object `g` of the slice of the total site into the
image of the localization has a terminal object, `W` itself with the structure arrow of `g`.

## Main results

* `Stacks.Topology.Simplicial.overOpens_isThin`: the slice of the open-set site of a simplicial
  degree is thin.
* `Stacks.Topology.Simplicial.levelFunctor_overPost_faithful`: the localization is faithful.
* `Stacks.Topology.Simplicial.levelFunctor_overPost_final`: the localization is final.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial

/-- The slice of the open-set site of a simplicial degree is a thin category: a morphism of it
is a comparison of opens, and there is at most one. -/
instance overOpens_isThin (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (W : Opens (X.obj n)) : Quiver.IsThin (Over W) :=
  fun _ _ => ⟨fun _ _ => Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

/-- **The localization at an open of the inclusion of a simplicial degree is faithful.** -/
instance levelFunctor_overPost_faithful (X : SimplicialObject TopCat.{u})
    (n : SimplexCategoryᵒᵖ) (W : Opens (X.obj n)) :
    (Over.post (X := W) (levelFunctor X n)).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- **The localization at an open of the inclusion of a simplicial degree is final.** For an
object `g` of the slice of the total site at `(n, W)` the comma category of arrows from `g` into
the image of the localization has a terminal object, namely `W` itself with the structure arrow
of `g`: an arrow of the slice carries the simplex map of the structure arrow it commutes with,
so an object of the comma category is no more than an open `V ≤ W` through which `g` factors,
and `W` is the largest. -/
instance levelFunctor_overPost_final (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (W : Opens (X.obj n)) : (Over.post (X := W) (levelFunctor X n)).Final where
  out g := by
    have hw : g.hom ≫
        ((Over.post (X := W) (levelFunctor X n)).obj (Over.mk (𝟙 W))).hom = g.hom :=
      (congrArg (fun t => g.hom ≫ t) ((levelFunctor X n).map_id W)).trans
        (Category.comp_id g.hom)
    refine isConnected_of_isTerminal _ (x := StructuredArrow.mk
      (show g ⟶ (Over.post (X := W) (levelFunctor X n)).obj (Over.mk (𝟙 W)) from
        Over.homMk g.hom hw)) ?_
    refine IsTerminal.ofUniqueHom
      (fun A => StructuredArrow.homMk (Over.homMk A.right.hom) ?_)
      (fun A m => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _))
    exact Over.OverMorphism.ext (SimplicialOpen.Hom.ext _ _
      (congrArg (fun h => h.base) (Over.w A.hom)))

end Stacks.Topology.Simplicial

end
