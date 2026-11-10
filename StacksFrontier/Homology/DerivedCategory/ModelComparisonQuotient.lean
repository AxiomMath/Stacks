module

public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# The comparison of the two localizations of the homotopy category, at a complex

For a Grothendieck abelian category `C`, `StacksDraft.DerivedModel.shrinkComparisonQhIso`
identifies `Qh : K(C) ⥤ D(C)` at the locally small model with `Qh` at the standard model followed
by the comparison equivalence `G`. At the class of a cochain complex `K` its components are the
identifications `Qh (K) ≅ Q K` of the two models: `Q K` is the same object at both models and `G`
carries `Q_std` to `Q_ls` on the nose.

## Main results

* `StacksDraft.DerivedModel.shrinkComparisonQhIso_hom_app_quotient` and
  `StacksDraft.DerivedModel.shrinkComparisonQhIso_inv_app_quotient`: the components at
  `quotient K`.
* `StacksDraft.DerivedModel.shrinkComparisonQhIso_hom_app_quotient_comp`,
  `StacksDraft.DerivedModel.shrinkComparisonQhIso_inv_app_quotient_comp` and
  `StacksDraft.DerivedModel.map_quotientCompQhIso_inv_app_comp_shrinkComparisonQhIso_inv_app`:
  the same, composed with the identification at one of the two models.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

universe u v w

namespace StacksDraft.DerivedModel

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- If `e.hom = a.hom ≫ G.map b.inv` then `e.inv = G.map b.hom ≫ a.inv`. -/
private lemma inv_eq_of_hom_eq_aux {D E : Type*} [Category D] [Category E] (G : D ⥤ E)
    {X Y : D} {P : E} (a : P ≅ G.obj Y) (b : X ≅ Y) (e : P ≅ G.obj X)
    (h : e.hom = a.hom ≫ G.map b.inv) : e.inv = G.map b.hom ≫ a.inv := by
  refine Iso.inv_ext ?_
  simp [h]

private lemma id_comp_comp_id_aux {E : Type*} [Category E] {P Q R : E} (a : P ⟶ Q) (g : Q ⟶ R) :
    a ≫ 𝟙 Q ≫ g ≫ 𝟙 R = a ≫ g := by
  simp

private lemma inv_comp_aux {E : Type*} [Category E] {P Q R : E} (g : P ⟶ R) (a : Q ≅ R)
    (e : P ⟶ Q) (h : e = g ≫ a.inv) : e ≫ a.hom = g := by
  simp [h]

private lemma comp_map_hom_aux {D E : Type*} [Category D] [Category E] (G : D ⥤ E)
    {X Y : D} {P : E} (a : P ⟶ G.obj Y) (b : X ≅ Y) (e : P ⟶ G.obj X)
    (h : e = a ≫ G.map b.inv) : e ≫ G.map b.hom = a := by
  simp [h]

private lemma map_comp_aux {D E : Type*} [Category D] [Category E] (G : D ⥤ E)
    {X Y : D} {P : E} (b : X ≅ Y) (a : P ≅ G.obj Y) (e : G.obj X ⟶ P)
    (h : e = G.map b.hom ≫ a.inv) : G.map b.inv ≫ e = a.inv := by
  simp [h]

/-- The component of `shrinkComparisonQhIso` at the class of a complex `K`: the identification
`Qh_ls K ≅ Q K` at the locally small model, followed by the image under the comparison of the
identification `Q K ≅ Qh_std K` at the standard model. -/
theorem shrinkComparisonQhIso_hom_app_quotient (K : CochainComplex C ℤ) :
    (shrinkComparisonQhIso.{u, v, w} C).hom.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (@DerivedCategory.quotientCompQhIso C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).hom.app K ≫
        (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor.map
          ((@DerivedCategory.quotientCompQhIso C _ _ (HasDerivedCategory.standard C)).inv.app K) :=
              by
  change (@DerivedCategory.quotientCompQhIso C _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).hom.app K ≫
    𝟙 _ ≫ (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor.map
      ((@DerivedCategory.quotientCompQhIso C _ _ (HasDerivedCategory.standard C)).inv.app K) ≫
    𝟙 _ = _
  exact id_comp_comp_id_aux _ _

/-- The inverse component of `shrinkComparisonQhIso` at the class of a complex `K`. -/
theorem shrinkComparisonQhIso_inv_app_quotient (K : CochainComplex C ℤ) :
    (shrinkComparisonQhIso.{u, v, w} C).inv.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor.map
          ((@DerivedCategory.quotientCompQhIso C _ _ (HasDerivedCategory.standard C)).hom.app K) ≫
        (@DerivedCategory.quotientCompQhIso C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).inv.app K :=
  inv_eq_of_hom_eq_aux (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor
    ((@DerivedCategory.quotientCompQhIso C _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).app K)
    ((@DerivedCategory.quotientCompQhIso C _ _ (HasDerivedCategory.standard C)).app K)
    ((shrinkComparisonQhIso.{u, v, w} C).app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))
    (shrinkComparisonQhIso_hom_app_quotient C K)

/-- `shrinkComparisonQhIso_inv_app_quotient`, after the identification at the locally small
model: the image under the comparison of the identification `Qh_std K ≅ Q K`. -/
@[reassoc]
theorem shrinkComparisonQhIso_inv_app_quotient_comp (K : CochainComplex C ℤ) :
    (shrinkComparisonQhIso.{u, v, w} C).inv.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≫
      (@DerivedCategory.quotientCompQhIso C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).hom.app K =
      (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor.map
          ((@DerivedCategory.quotientCompQhIso C _ _ (HasDerivedCategory.standard C)).hom.app K) :=
  inv_comp_aux _ ((@DerivedCategory.quotientCompQhIso C _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).app K) _
    (shrinkComparisonQhIso_inv_app_quotient C K)

/-- The identification `Q K ≅ Qh_ls K` at the locally small model is the image under the
comparison of that at the standard model, followed by `shrinkComparisonQhIso`. -/
@[reassoc]
theorem map_quotientCompQhIso_inv_app_comp_shrinkComparisonQhIso_inv_app
    (K : CochainComplex C ℤ) :
    (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor.map
        ((@DerivedCategory.quotientCompQhIso C _ _ (HasDerivedCategory.standard C)).inv.app K) ≫
      (shrinkComparisonQhIso.{u, v, w} C).inv.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (@DerivedCategory.quotientCompQhIso C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).inv.app K :=
  map_comp_aux (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor
    ((@DerivedCategory.quotientCompQhIso C _ _ (HasDerivedCategory.standard C)).app K)
    ((@DerivedCategory.quotientCompQhIso C _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).app K) _
    (shrinkComparisonQhIso_inv_app_quotient C K)

/-- `shrinkComparisonQhIso_hom_app_quotient`, after the image of the identification at the
standard model: the identification `Qh_ls K ≅ Q K` at the locally small model. -/
@[reassoc]
theorem shrinkComparisonQhIso_hom_app_quotient_comp (K : CochainComplex C ℤ) :
    (shrinkComparisonQhIso.{u, v, w} C).hom.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≫
      (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor.map
        ((@DerivedCategory.quotientCompQhIso C _ _ (HasDerivedCategory.standard C)).hom.app K) =
      (@DerivedCategory.quotientCompQhIso C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).hom.app K :=
  comp_map_hom_aux (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor _
    ((@DerivedCategory.quotientCompQhIso C _ _ (HasDerivedCategory.standard C)).app K) _
    (shrinkComparisonQhIso_hom_app_quotient C K)

end StacksDraft.DerivedModel

end
