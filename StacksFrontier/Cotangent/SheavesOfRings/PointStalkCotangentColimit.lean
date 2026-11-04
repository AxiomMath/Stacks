module

public import StacksFrontier.CategoryTheory.Sites.Point.DirectedNeighbourhoods
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseCotangentComplex

/-!
# The ring-level cotangent complex of the stalks at a point of a site as a directed colimit

Let `f : A ⟶ B` be a homomorphism of sheaves of commutative rings on a site and let `Φ` be a point
of the site, with stalk rings `A_Φ → B_Φ`. Choose a directed cofinal system of neighbourhoods
`(U_i, x_i)` of `Φ` (`CategoryTheory.GrothendieckTopology.Point.exists_directed_final`). The germ
maps `A(U_i) → A_Φ`, `B(U_i) → B_Φ` form commutative squares over `f`, and this file proves, by
[Stacks, Tag 08S9], that the maps they induce on cotangent complexes exhibit `L_{B_Φ/A_Φ}` as the
directed colimit of the `L_{B(U_i)/A(U_i)}`, in every degree.

This is the site-point form of `CategoryTheory.Sheaf.isDirectedColimitOfTypes_stalkCotangent` of
`StacksFrontier.Cotangent.SheavesOfRings.StalkwiseChangeOfBase`, which treats the points of a
topological space, whose neighbourhoods already form a preorder. It is the first step of the
germwise identification of the stalk of `L_{B/A}` with `L_{B_Φ/A_Φ}` that the proof of
[Stacks, Tag 09DM] needs at the geometric points of an algebraic space, where the neighbourhoods
are étale neighbourhoods and only a cofinal directed subsystem is a preorder.

## Main definitions

* `CategoryTheory.Sheaf.pointStalkAlgebra`: the stalk `B_Φ` as an algebra over `A_Φ`.
* `CategoryTheory.Sheaf.pointGermSquare`: the square of germ maps over a neighbourhood.

## Main results

* `CategoryTheory.Sheaf.isDirectedColimitOfTypes_pointStalkCotangent`: **Tag 08S9 at a point of a
  site.**

## References

* [Stacks Project, Tag 08S9](https://stacks.math.columbia.edu/tag/08S9)
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [LocallySmall.{max u v w} C] (Φ : J.Point.{max u v w})
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- The stalk `B_Φ` of a sheaf of commutative rings at a point of a site, as an algebra over the
stalk `A_Φ` along the map of stalks induced by `f`. -/
abbrev pointStalkAlgebra :
    CommAlgCat.{max u v w} ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) :=
  letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
      ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) :=
    ((Φ.presheafFiber (A := CommRingCat)).map f.hom).hom.toAlgebra
  CommAlgCat.of ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
    ((Φ.presheafFiber (A := CommRingCat)).obj B.obj)

/-- The square of germ maps `A(U) → A_Φ`, `B(U) → B_Φ` over a neighbourhood `(U, x)` of `Φ`. -/
def pointGermSquare (U : C) (x : Φ.fiber.obj U) :
    CommAlgCat.AlgebraSquare.{max u v w, max u v w, max u v w} (A.obj.obj (op U))
      ((Φ.presheafFiber (A := CommRingCat)).obj A.obj) (sectionsAlgebra J f (op U))
      (pointStalkAlgebra J Φ f) where
  base := (Φ.toPresheafFiber U x A.obj).hom
  map := (Φ.toPresheafFiber U x B.obj).hom
  map_algebraMap a := (Φ.toPresheafFiber_naturality_apply f.hom U x a).symm

/-- **Tag 08S9 at a point of a site.** Along a final functor `F` from a directed nonempty preorder
to the opposite of the neighbourhoods of `Φ`, the maps induced by the germ squares exhibit
`L_{B_Φ/A_Φ}` as the directed colimit of the cotangent complexes `L_{B(U_i)/A(U_i)}` over the
neighbourhoods `(U_i, x_i) = F i`, the transition maps being those of the restriction squares, in
every degree. -/
theorem isDirectedColimitOfTypes_pointStalkCotangent {α : Type (max u v w)} [Preorder α]
    [IsDirected α (· ≤ ·)] [Nonempty α] (F : α ⥤ (Φ.fiber.Elements)ᵒᵖ) [F.Final] (n : ℤ) :
    IsDirectedColimitOfTypes (I := α)
      (fun _ _ h a => (CommAlgCat.cotangentComplexAbMap
        (sectionsRestrictionSquare J f (F.map (homOfLE h)).unop.1.op)).f n a)
      (fun i a => (CommAlgCat.cotangentComplexAbMap
        (pointGermSquare J Φ f (F.obj i).unop.1 (F.obj i).unop.2)).f n a) :=
  CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb.{max u v w, max u v w, max u v w, _}
    (fun _ _ h => sectionsRestrictionSquare J f (F.map (homOfLE h)).unop.1.op)
    (fun i => pointGermSquare J Φ f (F.obj i).unop.1 (F.obj i).unop.2)
    (Φ.isDirectedColimitOfTypes_toPresheafFiber_commRingCat F A.obj)
    (Φ.isDirectedColimitOfTypes_toPresheafFiber_commRingCat F B.obj) n

end CategoryTheory.Sheaf

end
