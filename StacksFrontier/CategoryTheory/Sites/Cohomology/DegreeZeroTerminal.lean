module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Degree-zero cohomology at two terminal objects

`H⁰(F) ≅ F(T)` (`CategoryTheory.Sheaf.H.equiv₀`) depends on the choice of a terminal object `T`
of the site. For two terminal objects `T₁`, `T₂` the two identifications differ by restriction
along the unique morphism `T₂ ⟶ T₁`.

## Main results

* `CategoryTheory.Sheaf.H.equiv₀_eq_map_of_isTerminal`
* `CategoryTheory.Sheaf.H.equiv₀_mk₀`
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe w w' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

omit [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] in
/-- The unit of `constantSheaf ⊣ Γ(T, -)` at two terminal objects differ by restriction along
the unique morphism `T₂ ⟶ T₁`. -/
theorem constantSheafAdj_unit_app_comp_map {T₁ T₂ : C} (h₁ : IsTerminal T₁) (h₂ : IsTerminal T₂)
    (A : AddCommGrpCat.{w}) :
    (constantSheafAdj J AddCommGrpCat.{w} h₁).unit.app A ≫
        ((constantSheaf J AddCommGrpCat.{w}).obj A).obj.map (h₁.from T₂).op =
      (constantSheafAdj J AddCommGrpCat.{w} h₂).unit.app A := by
  have h := (toSheafify J ((Functor.const Cᵒᵖ).obj A)).naturality (h₁.from T₂).op
  simp only [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj_unit_app,
    sheafificationAdjunction_unit_app, Functor.const_obj_map, Category.id_comp] at h ⊢
  exact h.symm

/-- `H⁰(F) ≅ F(T)` on the class of a morphism `ℤ ⟶ F`: the transpose of the morphism, evaluated
at `1`. -/
theorem Sheaf.H.equiv₀_mk₀ {T : C} (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{w}}
    (f : (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) :
    Sheaf.H.equiv₀ F hT (Abelian.Ext.mk₀ f) = AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj J AddCommGrpCat.{w} hT).homEquiv _ F f) := by
  show AddCommGrpCat.uliftZMultiplesAddEquiv _ ((constantSheafAdj J AddCommGrpCat.{w} hT).homEquiv
    _ F (Abelian.Ext.addEquiv₀ (Abelian.Ext.addEquiv₀.symm f))) = _
  rw [AddEquiv.apply_symm_apply]

/-- **`H⁰(F) ≅ F(T)` at two terminal objects**: the identification at `T₂` is the one at `T₁`
followed by restriction along the unique morphism `T₂ ⟶ T₁`. -/
theorem Sheaf.H.equiv₀_eq_map_of_isTerminal {T₁ T₂ : C} (h₁ : IsTerminal T₁)
    (h₂ : IsTerminal T₂) (F : Sheaf J AddCommGrpCat.{w}) (x : Sheaf.H F 0) :
    Sheaf.H.equiv₀ F h₂ x = F.obj.map (h₁.from T₂).op (Sheaf.H.equiv₀ F h₁ x) := by
  set f := Abelian.Ext.addEquiv₀ x
  have key : (constantSheafAdj J AddCommGrpCat.{w} h₂).homEquiv _ F f =
      (constantSheafAdj J AddCommGrpCat.{w} h₁).homEquiv _ F f ≫ F.obj.map (h₁.from T₂).op := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
      ← constantSheafAdj_unit_app_comp_map h₁ h₂]
    exact congrArg (fun t => (constantSheafAdj J AddCommGrpCat.{w} h₁).unit.app _ ≫ t)
      (f.hom.naturality (h₁.from T₂).op)
  show AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj J AddCommGrpCat.{w} h₂).homEquiv _ F f) =
    F.obj.map (h₁.from T₂).op (AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj J AddCommGrpCat.{w} h₁).homEquiv _ F f))
  rw [key]
  rfl

end CategoryTheory
