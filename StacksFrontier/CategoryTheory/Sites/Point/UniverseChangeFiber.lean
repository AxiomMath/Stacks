module

public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange
public import StacksFrontier.CategoryTheory.Sites.Point.UliftFiber

/-!
# The fibre functor of a point does not change when its universe is raised

For a point `Φ` of a site `(C, J)` relative to a universe `w`, the point
`CategoryTheory.GrothendieckTopology.Point.ulift` relative to `max w w'` has fibre
`Φ.fiber ⋙ uliftFunctor`, whose category of elements is isomorphic to that of `Φ.fiber`
(`CategoryTheory.Functor.Elements.uliftEquiv`). The fibre of a presheaf at a point is a colimit
over the opposite of that category of elements, so the two points have the same fibre functors on
presheaves and on sheaves, for any coefficient category with colimits of both sizes.

The isomorphisms of fibre functors are assembled from the objectwise isomorphisms
`CategoryTheory.GrothendieckTopology.Point.presheafFiberUliftIso` and
`CategoryTheory.GrothendieckTopology.Point.sheafFiberUliftIso`.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.presheafFiberUliftNatIso`: `Φ.ulift.presheafFiber ≅
  Φ.presheafFiber`.
* `CategoryTheory.GrothendieckTopology.Point.sheafFiberUliftNatIso`: `Φ.ulift.sheafFiber ≅
  Φ.sheafFiber`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w w' v u u' v'

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  [HasColimitsOfSize.{max w w', max w w'} A]

/-- The objectwise identification of the fibres at the universe lift of a point with the fibres
at the point is compatible with the maps from the sections. -/
@[reassoc]
theorem toPresheafFiber_ulift_comp_presheafFiberUliftIso_hom (P : Cᵒᵖ ⥤ A) (X : C)
    (x : (Φ.ulift.{w'} (J := J)).fiber.obj X) :
    (Φ.ulift.{w'} (J := J)).toPresheafFiber X x P ≫ (presheafFiberUliftIso.{w, w'} Φ P).hom =
      Φ.toPresheafFiber X x.down P := by
  unfold presheafFiberUliftIso
  exact IsColimit.comp_coconePointUniqueUpToIso_inv (Φ.isColimitPresheafFiberCocone P)
    ((Functor.Final.isColimitWhiskerEquiv
        ((Functor.Elements.uliftEquiv.{w', w} Φ.fiber).functor.op)
        ((Φ.ulift.{w'} (J := J)).presheafFiberCocone P)).symm
      ((Φ.ulift.{w'} (J := J)).isColimitPresheafFiberCocone P))
    (Opposite.op (α := Φ.fiber.Elements) ⟨X, x.down⟩)

/-- **The fibre functor on presheaves of the universe lift of a point is that of the point**,
with components `CategoryTheory.GrothendieckTopology.Point.presheafFiberUliftIso`. -/
def presheafFiberUliftNatIso : (Φ.ulift.{w'}).presheafFiber (A := A) ≅ Φ.presheafFiber :=
  NatIso.ofComponents (fun P => presheafFiberUliftIso.{w, w'} Φ P) fun {P Q} g => by
    refine (Φ.ulift.{w'} (J := J)).presheafFiber_hom_ext fun X x => ?_
    rw [toPresheafFiber_naturality_assoc, toPresheafFiber_ulift_comp_presheafFiberUliftIso_hom,
      toPresheafFiber_ulift_comp_presheafFiberUliftIso_hom_assoc, toPresheafFiber_naturality]

/-- **The fibre functor on sheaves of the universe lift of a point is that of the point.** -/
def sheafFiberUliftNatIso : (Φ.ulift.{w'}).sheafFiber (A := A) ≅ Φ.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (presheafFiberUliftNatIso Φ A)

end CategoryTheory.GrothendieckTopology.Point

end
