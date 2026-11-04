module

public import Mathlib.CategoryTheory.Sites.Point.Category
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint

/-!
# Morphisms of points and fibres of composed sheaves

For a point `Φ` of a site and a functor `F : A ⥤ B` preserving filtered colimits, the fibre of a
presheaf composed with `F` is `F` applied to the fibre, by
`CategoryTheory.GrothendieckTopology.Point.presheafFiberCompIso`. This file shows that the
induced maps of fibres along a morphism of points correspond under these isomorphisms. For the
geometric Frobenius, which acts on stalks as a morphism of points of the small étale site, this
says that the Frobenius on the stalk of a sheaf obtained from another by a change of coefficients
`F` is `F` applied to the Frobenius on the stalk of the other sheaf.

## Main results

The first two results are in the namespace `CategoryTheory.GrothendieckTopology.Point.Hom`.

* `presheafFiber_app_comp_presheafFiberCompIso_hom_app`: the map of fibres of `P ⋙ F` along a
  morphism of points is `F` applied to the map of fibres of `P`.
* `sheafFiber_app_comp_presheafFiberCompIso_hom_app`: the same for sheaves.
* `Stacks.Frobenius.frobeniusStalk_sheafCompose_comp_presheafFiberCompIso_hom_app`: the geometric
  Frobenius on the stalk of `F ∘ P` is `F` applied to the geometric Frobenius on the stalk of `P`.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v v' v'' u u' u''

namespace CategoryTheory.GrothendieckTopology.Point.Hom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  {B : Type u''} [Category.{v''} B] [HasColimitsOfSize.{w, w} B]
  (F : A ⥤ B) [PreservesFilteredColimitsOfSize.{w, w} F] {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂)

/-- A morphism of points `f` sends the germ of `x` at `Φ₂` to the germ of `f x` at `Φ₁`. -/
private theorem toPresheafFiber_comp_presheafFiber_app {D : Type u} [Category.{v} D]
    {K : GrothendieckTopology D} {E : Type u'} [Category.{v'} E] [HasColimitsOfSize.{w, w} E]
    {Ψ₁ Ψ₂ : Point.{w} K} (g : Ψ₁ ⟶ Ψ₂) (P : Dᵒᵖ ⥤ E) (X : D) (x : Ψ₂.fiber.obj X) :
    Ψ₂.toPresheafFiber X x P ≫ g.presheafFiber.app P =
      Ψ₁.toPresheafFiber X (g.hom.app X x) P := by
  rw [presheafFiber_app]
  exact Ψ₂.toPresheafFiber_presheafFiberDesc _ _ X x

/-- **A morphism of points commutes with taking fibres after a change of coefficients.** -/
@[reassoc]
public theorem presheafFiber_app_comp_presheafFiberCompIso_hom_app (P : Cᵒᵖ ⥤ A) :
    f.presheafFiber.app (P ⋙ F) ≫ (Φ₁.presheafFiberCompIso F).hom.app P =
      (Φ₂.presheafFiberCompIso F).hom.app P ≫ F.map (f.presheafFiber.app P) := by
  refine Φ₂.presheafFiber_hom_ext fun X x => ?_
  rw [reassoc_of% toPresheafFiber_comp_presheafFiber_app,
    Φ₁.toPresheafFiber_presheafFiberCompIso_hom_app,
    Φ₂.toPresheafFiber_presheafFiberCompIso_hom_app_assoc, ← F.map_comp,
    toPresheafFiber_comp_presheafFiber_app]

/-- **A morphism of points commutes with taking fibres of sheaves after a change of
coefficients.** The comparison is `presheafFiberCompIso` at the underlying presheaf. -/
@[reassoc]
public theorem sheafFiber_app_comp_presheafFiberCompIso_hom_app [J.HasSheafCompose F]
    (P : Sheaf J A) :
    f.sheafFiber.app ((sheafCompose J F).obj P) ≫ (Φ₁.presheafFiberCompIso F).hom.app P.obj =
      (Φ₂.presheafFiberCompIso F).hom.app P.obj ≫ F.map (f.sheafFiber.app P) :=
  f.presheafFiber_app_comp_presheafFiberCompIso_hom_app F P.obj

end CategoryTheory.GrothendieckTopology.Point.Hom

namespace Stacks.Frobenius

open AlgebraicGeometry

variable {X : Scheme.{u}} {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{u, u} A]
  {B : Type u''} [Category.{v''} B] [HasColimitsOfSize.{u, u} B]
  (F : A ⥤ B) [PreservesFilteredColimitsOfSize.{u, u} F]
  [X.smallEtaleTopology.HasSheafCompose F]

/-- **The geometric Frobenius commutes with a change of coefficients.** At a point `y` with finite
residue field, under the identification of the stalk of `F ∘ P` with `F` applied to the stalk of
`P`, the geometric Frobenius on the former is `F` applied to the geometric Frobenius on the
latter. -/
@[reassoc]
public theorem frobeniusStalk_sheafCompose_comp_presheafFiberCompIso_hom_app (y : X)
    [Finite (X.residueField y)] (P : Sheaf X.smallEtaleTopology A) :
    frobeniusStalk B X y ((sheafCompose X.smallEtaleTopology F).obj P) ≫
        ((Scheme.pointSmallEtale (geometricPointAt X y).hom).presheafFiberCompIso F).hom.app
          P.obj =
      ((Scheme.pointSmallEtale (geometricPointAt X y).hom).presheafFiberCompIso F).hom.app P.obj ≫
        F.map (frobeniusStalk A X y P) :=
  GrothendieckTopology.Point.Hom.sheafFiber_app_comp_presheafFiberCompIso_hom_app.{u, u, v', v'',
    u + 1, u', u''} F (smallEtalePointHom X (frobeniusPointHom X y)) P

end Stacks.Frobenius

end
