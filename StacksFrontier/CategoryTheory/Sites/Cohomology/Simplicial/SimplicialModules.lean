module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Simplicial modules on a site

Let `C` be a site and let `A` be a simplicial sheaf of rings on `C`. Uncurrying the underlying
presheaves of `A` gives a presheaf of rings on `Δ × C`. A *simplicial `A`-module* is a sheaf
of modules over that presheaf of rings, the sheaf condition being taken for the topology on
`Δ × C` inherited from `C` along the second projection.

## Main definitions

* `Stacks.SimplicialModules.associatedRingPresheaf`: the presheaf of rings on `Δ × C`
  associated to a simplicial sheaf of rings.
* `Stacks.SimplicialModules.SimplicialModule`: the category of simplicial modules over it, as the
  full subcategory of presheaves of modules whose underlying abelian-group presheaf is a sheaf for
  the topology `(CategoryTheory.Prod.snd _ _).inheritedTopology J` on `Δ × C`.

## References

* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1)
-/

@[expose] public section

open CategoryTheory

universe w v u r

namespace Stacks.SimplicialModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The presheaf of rings on `Δ × C` obtained by uncurrying a simplicial sheaf of rings. -/
abbrev associatedRingPresheaf (A : SimplicialObject (Sheaf J RingCat.{r})) :
    (SimplexCategory × C)ᵒᵖ ⥤ RingCat.{r} :=
  (prodOpEquiv SimplexCategory (D := C)).functor ⋙
    Functor.uncurry.obj (A ⋙ sheafToPresheaf J RingCat.{r})

/-- A simplicial module over a simplicial sheaf of rings `A` is a presheaf of modules over the
associated ring presheaf on `Δ × C` whose underlying abelian-group presheaf is a sheaf for the
topology inherited from `C`. -/
@[stacks 09D1]
abbrev SimplicialModule (A : SimplicialObject (Sheaf J RingCat.{r})) :=
  ObjectProperty.FullSubcategory
    (fun M : PresheafOfModules.{w} (associatedRingPresheaf J A) ↦
      Presheaf.IsSheaf ((CategoryTheory.Prod.snd SimplexCategory C).inheritedTopology J)
        M.presheaf)

end Stacks.SimplicialModules
