module

public import StacksFrontier.Algebra.DGA.DGCategory
public import StacksCore.Tactic.StacksAttribute

/-! # Natural transformations of functors of differential graded categories

A functor of differential graded categories induces functors on the associated category of
complexes and homotopy category, which is Tag 09L8. A *natural transformation* of such functors
is the corresponding notion one degree down: a closed degree-zero morphism for every object,
strictly natural against homogeneous morphisms of every degree. Such a transformation induces an
ordinary natural transformation of the induced functors on complexes and on homotopy categories.

## Main definitions

* `DGCategory.DGNatTrans`: a natural transformation of functors of differential graded
  categories.
* `DGCategory.DGNatTrans.onComp` and `DGCategory.DGNatTrans.onK`: the induced natural
  transformations of the functors on complexes and on homotopy categories.

## References

* [Stacks Project, Tag 09L8](https://stacks.math.columbia.edu/tag/09L8)
-/

@[expose] public section

open CategoryTheory

namespace DGCategory

variable {R : Type*} [CommRing R] {A B : DGCategory R}

/-- A natural transformation between functors of differential graded categories: a closed
degree-zero morphism `F x ⟶ G x` for every object `x`, commuting strictly with the images of
every homogeneous morphism. -/
structure DGNatTrans (F G : DGFunctor A B) where
  /-- The component at an object, a closed degree-zero morphism. -/
  app (x : A.Obj) : B.Cocycle (F.obj x) (G.obj x)
  /-- Strict naturality against a homogeneous morphism of any degree. -/
  naturality {x y : A.Obj} {n : ℤ} (u : A.Hom x y n) :
    B.comp (zero_add n) (app y).1 (F.map u) = B.comp (add_zero n) (G.map u) (app x).1

namespace DGNatTrans

variable {F G : DGFunctor A B} (τ : DGNatTrans F G)

/-- Naturality of a differential graded natural transformation against a cocycle, as an equality
of cocycles. -/
theorem naturality_compCocycle {x y : A.Obj} (c : A.Cocycle x y) :
    B.compCocycle (τ.app y) (F.mapCocycle c) = B.compCocycle (G.mapCocycle c) (τ.app x) :=
  Subtype.ext (τ.naturality c.1)

/-- The induced natural transformation of the functors on categories of complexes. -/
def onComp : F.onComp ⟶ G.onComp where
  app x := τ.app x
  naturality _ _ c := τ.naturality_compCocycle c

/-- The induced natural transformation of the functors on homotopy categories. -/
def onK : F.onK ⟶ G.onK where
  app x := Quotient.mk _ (τ.app x)
  naturality x y u := by
    refine Quotient.inductionOn u (fun c => ?_)
    change B.compK (Quotient.mk _ (τ.app y)) (F.mapHomotopyClass (Quotient.mk _ c)) =
      B.compK (G.mapHomotopyClass (Quotient.mk _ c)) (Quotient.mk _ (τ.app x))
    simp only [DGFunctor.mapHomotopyClass, compK, Quotient.map_mk, Quotient.map₂_mk]
    exact congrArg (Quotient.mk _) (τ.naturality_compCocycle c)

/-- The component of `onK` at `x` is the homotopy class of the component of `τ` at `x`. -/
@[simp] theorem onK_app (x : A.Obj) : τ.onK.app x = Quotient.mk _ (τ.app x) := rfl

/-- The component of `onComp` at `x` is the component of `τ` at `x`. -/
@[simp] theorem onComp_app (x : A.Obj) : τ.onComp.app x = τ.app x := rfl

end DGNatTrans

end DGCategory

end
