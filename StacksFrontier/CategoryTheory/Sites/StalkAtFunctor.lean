module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# The stalk of a presheaf at an arbitrary functor `u : C ⥤ Type w`

Stacks 04EH. Let `C` be a category and `p = u : C ⥤ Type w` an arbitrary functor; no
conditions are imposed on `u`. A *neighbourhood* of `p` is a pair `(U, x)` with `x ∈ u(U)`, and
a morphism of neighbourhoods `(V, y) ⟶ (U, x)` is a morphism `α : V ⟶ U` with `u(α)(y) = x`;
these form the category of elements `u.Elements`. The *stalk* of a presheaf `F` at `p` is
`F_p = colim_{{(U, x)}ᵒᵖ} F(U)`, the colimit of `(CategoryOfElements.π u).op ⋙ F` over
`u.Elementsᵒᵖ`.

## Main definitions

* `CategoryTheory.Functor.presheafStalk u F`: the stalk `F_u`, for a presheaf `F` with values
  in any category `A` in which the colimit exists.
* `CategoryTheory.Functor.toPresheafStalk u U x F`: the canonical map `F(U) ⟶ F_u` attached to
  the neighbourhood `(U, x)`.
* `CategoryTheory.Functor.presheafStalkFunctor u`: the stalk functor `PSh(C, A) ⥤ A`.
* `CategoryTheory.Functor.presheafStalkEquivColimitType u F`: for a presheaf of sets,
  elements of `F_u`
  are classes of triples `(U, x, s)` with `s ∈ F(U)`, under the equivalence relation generated
  by `(U, x, s) ∼ (V, y, α^* s)`.

## Comparison with points of sites

For a point `Φ` of a site, Mathlib's `GrothendieckTopology.Point.presheafFiber` is the stalk
functor at `Φ.fiber` (`Point.presheafFiber_eq_presheafStalkFunctor`,
`Point.toPresheafFiber_eq_toPresheafStalk`): the conditions
in the definition of a point are not used to define it.

## References

* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory.Functor

open Opposite Limits

variable {C : Type u} [Category.{v} C] (u : C ⥤ Type w) {A : Type u'} [Category.{v'} A]

/-- The stalk `F_u = colim_{{(U, x)}ᵒᵖ} F(U)` of a presheaf `F` at an arbitrary functor
`u : C ⥤ Type w`: the colimit of `F(U)` over the opposite of the category of neighbourhoods
`(U, x)`, `x ∈ u(U)`, of `u`. -/
@[stacks 04EH "The stalk `F_p = colim_{{(U, x)}^opp} F(U)` of a presheaf at an arbitrary
  functor `p = u : C → Sets`, with no conditions on `u`; the presheaf takes values in any
  category `A` in which this colimit exists (the case of presheaves of sets is
  `A := Type _`, see `presheafStalkEquivColimitType`)."]
noncomputable def presheafStalk (F : Cᵒᵖ ⥤ A) [HasColimit ((CategoryOfElements.π u).op ⋙ F)] : A :=
  colimit ((CategoryOfElements.π u).op ⋙ F)

/-- The canonical map `F(U) ⟶ F_u` attached to a neighbourhood `(U, x)` of `u`. -/
@[stacks 04EH "The canonical map `F(U) → F_p` sending `s` to the class of `(U, x, s)`."]
noncomputable def toPresheafStalk (U : C) (x : u.obj U) (F : Cᵒᵖ ⥤ A)
    [HasColimit ((CategoryOfElements.π u).op ⋙ F)] : F.obj (op U) ⟶ u.presheafStalk F :=
  colimit.ι ((CategoryOfElements.π u).op ⋙ F) (op (u.elementsMk U x))

/-- The canonical maps are compatible with morphisms of neighbourhoods: for
`α : (V, y) ⟶ (U, x)`, i.e. `α : V ⟶ U` with `u(α)(y) = x`, the class of `(U, x, s)` equals the
class of `(V, y, α^* s)`. -/
@[stacks 04EH "The relation `(U, x, s) ∼ (V, y, α^* s)` for a morphism of neighbourhoods
  `α : (V, y) → (U, x)`."]
theorem toPresheafStalk_w {V U : C} (α : V ⟶ U) (y : u.obj V) (F : Cᵒᵖ ⥤ A)
    [HasColimit ((CategoryOfElements.π u).op ⋙ F)] :
    F.map α.op ≫ u.toPresheafStalk V y F = u.toPresheafStalk U (u.map α y) F :=
  colimit.w ((CategoryOfElements.π u).op ⋙ F)
    (show u.elementsMk V y ⟶ u.elementsMk U (u.map α y) from ⟨α, rfl⟩).op

@[reassoc]
lemma presheafStalk_hom_ext {F : Cᵒᵖ ⥤ A} [HasColimit ((CategoryOfElements.π u).op ⋙ F)] {T : A}
    {f g : u.presheafStalk F ⟶ T}
    (h : ∀ (U : C) (x : u.obj U), u.toPresheafStalk U x F ≫ f = u.toPresheafStalk U x F ≫ g) :
    f = g :=
  colimit.hom_ext fun _ ↦ h _ _

/-- The stalk functor `PSh(C, A) ⥤ A`, `F ↦ F_u`, at an arbitrary functor `u : C ⥤ Type w`. -/
@[stacks 04EH "The stalk functor `PSh(C) → Sets`, `F ↦ F_p`, here for presheaves with values
  in a category `A` with colimits of shape `u.Elementsᵒᵖ`."]
noncomputable def presheafStalkFunctor [HasColimitsOfShape u.Elementsᵒᵖ A] :
    (Cᵒᵖ ⥤ A) ⥤ A :=
  (whiskeringLeft _ _ _).obj (CategoryOfElements.π u).op ⋙ colim

lemma presheafStalkFunctor_obj [HasColimitsOfShape u.Elementsᵒᵖ A] (F : Cᵒᵖ ⥤ A) :
    u.presheafStalkFunctor.obj F = u.presheafStalk F :=
  rfl

/-- The map of stalks `φ_u : F_u ⟶ G_u` induced by a morphism of presheaves is compatible with
the canonical maps. -/
@[reassoc]
lemma toPresheafStalk_presheafStalkFunctor_map [HasColimitsOfShape u.Elementsᵒᵖ A]
    {F G : Cᵒᵖ ⥤ A} (φ : F ⟶ G) (U : C) (x : u.obj U) :
    u.toPresheafStalk U x F ≫ u.presheafStalkFunctor.map φ =
      φ.app (op U) ≫ u.toPresheafStalk U x G := by
  exact colimit.ι_map _ _

section Types

variable (F : Cᵒᵖ ⥤ Type (max u v w))

/-- For a presheaf of sets, an element of the stalk `F_u` is the class of a triple `(U, x, s)`
with `(U, x)` a neighbourhood of `u` and `s ∈ F(U)`, for the equivalence relation generated by
`(U, x, s) ∼ (V, y, α^* s)`: the quotient `Functor.ColimitType` of the diagram
`(CategoryOfElements.π u).op ⋙ F`. -/
@[stacks 04EH "Description of the stalk of a presheaf of sets: elements are triples
  `(U, x, s)` modulo the equivalence relation generated by `(U, x, s) ∼ (V, y, α^* s)`."]
noncomputable def presheafStalkEquivColimitType :
    u.presheafStalk F ≃ ((CategoryOfElements.π u).op ⋙ F).ColimitType :=
  Types.colimitEquivColimitType _

/-- Under `presheafStalkEquivColimitType`, the image of `s ∈ F(U)` under the canonical map
attached to `(U, x)` is the class of the triple `(U, x, s)`. -/
lemma presheafStalkEquivColimitType_toPresheafStalk (U : C) (x : u.obj U) (s : F.obj (op U)) :
    u.presheafStalkEquivColimitType F (u.toPresheafStalk U x F s) =
      Quot.mk _ ⟨op (u.elementsMk U x), s⟩ :=
  Types.colimitEquivColimitType_apply _ _ _

end Types

end CategoryTheory.Functor

namespace CategoryTheory.GrothendieckTopology.Point

open Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [Limits.HasColimitsOfSize.{w, w} A]

/-- For a point `Φ` of a site, Mathlib's fiber `Φ.presheafFiber.obj P` is by definition the
stalk of Stacks 04EH at the functor `Φ.fiber`. -/
lemma presheafFiber_obj_eq_presheafStalk (P : Cᵒᵖ ⥤ A) :
    Φ.presheafFiber.obj P = Φ.fiber.presheafStalk P :=
  rfl

/-- For a point `Φ` of a site, Mathlib's fiber functor `Φ.presheafFiber` is the stalk functor
of Stacks 04EH at `Φ.fiber`. -/
lemma presheafFiber_eq_presheafStalkFunctor :
    Φ.presheafFiber (A := A) = Φ.fiber.presheafStalkFunctor :=
  rfl

/-- For a point `Φ` of a site, Mathlib's `Φ.toPresheafFiber` is the canonical map of
Stacks 04EH at `Φ.fiber`. -/
lemma toPresheafFiber_eq_toPresheafStalk (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    Φ.toPresheafFiber X x P = Φ.fiber.toPresheafStalk X x P :=
  rfl

end CategoryTheory.GrothendieckTopology.Point
