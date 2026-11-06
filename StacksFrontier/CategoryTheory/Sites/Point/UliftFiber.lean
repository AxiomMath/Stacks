module

public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange

/-!
# The fibre of a point is unchanged by raising the point's universe

`CategoryTheory.GrothendieckTopology.Point.ulift` reads a point of a site relative to a universe
`w` as a point relative to a larger universe by composing its fibre functor with `uliftFunctor`.
That operation changes the *shape* of the colimit computing a stalk — the category of elements of
the lifted fibre functor — but not the colimit itself: the comparison functor
`CategoryTheory.Functor.Elements.uliftEquiv` is an equivalence commuting on the nose with the
projections to the site, hence final, so the two stalks agree.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.presheafFiberUliftIso` — the stalk of a presheaf at
  the universe lift of a point is its stalk at the point.
* `CategoryTheory.GrothendieckTopology.Point.sheafFiberUliftIso` — the same for sheaves.

## References

None; this is universe bookkeeping for `CategoryTheory.Sites.Point.Basic`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v₂ u₂ v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : GrothendieckTopology.Point.{w} J) {A : Type u₂} [Category.{v₂} A]
  [HasColimitsOfSize.{w, w} A] [HasColimitsOfSize.{max w w', max w w'} A]

/-- The comparison functor between the categories of elements of the fibre of a point and of the
fibre of its universe lift commutes with the projections to the site, on the nose. -/
theorem uliftElements_comp_π :
    (Functor.Elements.uliftEquiv.{w', w} Φ.fiber).functor ⋙
        CategoryOfElements.π (Φ.ulift.{w'} (J := J)).fiber =
      CategoryOfElements.π Φ.fiber :=
  rfl

/-- **The stalk of a presheaf at the universe lift of a point is its stalk at the point.** The
colimits computing the two are indexed by equivalent categories over the site. -/
def presheafFiberUliftIso (P : Cᵒᵖ ⥤ A) :
    (Φ.ulift.{w'} (J := J)).presheafFiber.obj P ≅ Φ.presheafFiber.obj P :=
  ((Φ.isColimitPresheafFiberCocone P).coconePointUniqueUpToIso
    ((Functor.Final.isColimitWhiskerEquiv
        ((Functor.Elements.uliftEquiv.{w', w} Φ.fiber).functor.op)
        ((Φ.ulift.{w'} (J := J)).presheafFiberCocone P)).symm
      ((Φ.ulift.{w'} (J := J)).isColimitPresheafFiberCocone P))).symm

/-- **The stalk of a sheaf at the universe lift of a point is its stalk at the point.** -/
def sheafFiberUliftIso (F : Sheaf J A) :
    (Φ.ulift.{w'} (J := J)).sheafFiber.obj F ≅ Φ.sheafFiber.obj F :=
  presheafFiberUliftIso.{w, w'} Φ F.obj

end CategoryTheory.GrothendieckTopology.Point

end
