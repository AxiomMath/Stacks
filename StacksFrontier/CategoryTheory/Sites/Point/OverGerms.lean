module

public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint

/-!
# Germs at a point of a localized site

Let `Φ` be a point of a site `(C, J)`, let `X` be an object and let `x ∈ Φ(X)`.  The fibre at
the point `Φ.over x` of `C/X` of the restriction of a presheaf `P` on `C` is the fibre of `P` at
`Φ` (Stacks 04H2, `CategoryTheory.GrothendieckTopology.Point.presheafFiberOverIso`).  This file
records that the comparison is compatible with germs.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberOverIso_hom`: the
  comparison carries the germ at a neighbourhood of `Φ.over x` to the germ at the underlying
  neighbourhood of `Φ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v v' u u'

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J) {X : C}
  (x : Φ.fiber.obj X) [LocallySmall.{w} C] (A : Type u') [Category.{v'} A]
  [HasColimitsOfSize.{w, w} A]

/-- **The comparison of fibres along a localization is compatible with germs.** -/
theorem toPresheafFiber_presheafFiberOverIso_hom (P : Cᵒᵖ ⥤ A) (Y : Over X)
    (y : (Φ.over x).fiber.obj Y) :
    (Φ.over x).toPresheafFiber Y y ((Over.forget X).op ⋙ P) ≫
        (presheafFiberOverIso Φ x A).hom.app P =
      Φ.toPresheafFiber Y.left y.1 P := by
  change colimit.ι _ (op ((Φ.over x).fiber.elementsMk Y y)) ≫
    (Functor.Final.colimitIso (overElements Φ x).op ((Functor.Elements.π Φ.fiber).op ⋙ P)).hom = _
  rw [Functor.Final.colimitIso_hom]
  exact colimit.ι_pre ((Functor.Elements.π Φ.fiber).op ⋙ P) (overElements Φ x).op
    (op ((Φ.over x).fiber.elementsMk Y y))

end CategoryTheory.GrothendieckTopology.Point

end
