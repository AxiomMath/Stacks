module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsTensorUnit

/-! # Base change of a tensor product of sheaves of modules, on local sections

Let `θ : A₁ ⟶ A₂` be a morphism of presheaves of commutative rings on a site whose underlying
presheaves of rings are sheaves. **Tag 03CU** gives the base-change comparison

`A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)`

of `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`, which is **step 6 of the chain of
bijections of Tag 03EL**.  That comparison came with its naturality
(`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_naturality`) and with nothing on
sections, and the naturality is not enough to *evaluate* it: a statement about the comparison of
Tag 03EL on an individual local section has to say what each of the six bijections does to a
section, and this was the one step with no formula at all.  This file supplies it.

The comparison is a three-fold composite — the sheafification comparison for extension of scalars,
the presheaf-level base change of Tag 03CU, and the comparison of Tag 05NA — and only the middle
link had a value formula
(`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorObjIso_hom_app`, which is
`TensorProduct.AlgebraTensorModule.distribBaseChange`).  So the two sheafification comparisons are
computed here first, and the first of them is traversed *backwards*, which is why both a `hom` and
an `inv` formula appear for it.

## Main results

* `Stacks.SheafOfModules.TensorSheafification.sheafification_map_val_app_unit`: the sheafification
  of a morphism of presheaves of modules, read on the sheafification-unit image of a local
  section.  This is the naturality of that unit, and it is the one move every formula below is
  read off from.
* `Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso_hom_val_app_unit_tmul`: **the
  comparison of Tag 05NA on a pure tensor.** It carries the unit image of `x ⊗ₜ y` to the unit
  image of the tensor of the two unit images.
* `Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso_hom_val_app_unit_tmul` and
  `Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso_inv_val_app_unit_tmul`: **the
  comparison `(A₂ ⊗_{p,A₁} P)^# ≅ A₂ ⊗_{A₁} P^#` on a pure tensor, in both directions.** It
  carries the unit image of `a ⊗ₜ p` to the unit image of `a ⊗ₜ (unit p)`.
* `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_val_app_unit_tmul'`: **step 6 of
  the chain of Tag 03EL on a pure tensor** — the formula this file exists for. On the unit image
  of `a ⊗ₜ (unit (x ⊗ₜ y))` the base-change comparison is the unit image of
  `(unit (a ⊗ₜ x)) ⊗ₜ (unit (1 ⊗ₜ y))`.
* `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_val_app_extendScalarsUnit_tmul`:
  **steps 5 and 6 of the chain of Tag 03EL on a pure tensor.** Composing with the unit of the
  adjunction of Tag 03CZ removes the scalar `a` and the formula becomes the clean statement that
  a pure tensor of two local sections goes to the pure tensor of their images under the unit of
  extension of scalars.

## Implementation notes

Everything is stated with the sheaf of rings spelled `commRingSheaf J A h`, the underlying sheaf of
rings of a presheaf of commutative rings, rather than
`Stacks.SheafOfModules.TensorSheafification.structureSheaf A h`.  The two are equal — both are
`⟨ringPresheaf A, h⟩` — but the first is an `abbrev` and the second a `def`, so only the first lets
instance search find Mathlib's monoidal structure on presheaves of modules and only in the first
does `⊗ₘ` elaborate.  This is the spelling of
`Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso_hom_eq` and of
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`, and it is why the proofs below can use
`rw` at all.

The two sheafification units are nevertheless not interchangeable for `rw`: the target of
`extendScalarsTensorIso` is spelled `tensorSheaf A₂ h₂ ((extendScalars …).obj F) …`, whose index is
`structureSheaf A₂ h₂`, so a `rw` whose motive mentions that target is reported ill-typed at
`implicit` transparency.  Each formula is therefore assembled in term position, by
`CategoryTheory.comp_apply` and `CategoryTheory.congr_fun` rather than by rewriting with
`PresheafOfModules.comp_app`, exactly as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearValueFormulas`; and in
`extendScalarsTensorIso_hom_val_app_extendScalarsUnit_tmul` the two steps that mention the
comparison are done first, so that the one `rw` left happens in a goal the comparison has already
left.

The `Algebra` instance on the sections, `(θ.app V).hom.toAlgebra`, has to be named by a `let` in
every statement that writes a pure tensor over `A₁.obj V`; this is the idiom of
`Stacks.PresheafOfModules.ChangeOfRings.cofHom_app_tmul` and of
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply`.  Where
the statement is meant to be used by `rw` the `let` is placed on the right-hand side only, so that
the left-hand side is a bare application and the pattern is found: a `let` wrapping the whole
equation makes the statement a term `rw` cannot match against.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open Stacks.Sheaves.RingedToposModules Stacks.PresheafOfModules.ChangeOfRings
open scoped TensorProduct

universe w v u

namespace Stacks.SheafOfModules.TensorSheafification

section Sheafify

/-- A composite of morphisms of presheaves of modules equal to `h` evaluates to `h` on sections. -/
private theorem app_comp_apply_eq_of_comp_eq {C : Type u} [Category.{v} C]
    {R : Cᵒᵖ ⥤ RingCat.{w}} {P Q S : PresheafOfModules.{w} R} {f : P ⟶ Q} {g : Q ⟶ S} {h : P ⟶ S}
    (e : f ≫ g = h) (V : Cᵒᵖ) (z : P.obj V) : g.app V (f.app V z) = h.app V z := by
  subst e
  rfl

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (h𝒪 : Presheaf.IsSheaf J (ringPresheaf 𝒪))

/-- **The sheafification of a morphism of presheaves of modules, on the sheafification-unit image
of a local section.** It is the unit image of the value of the morphism. This is the naturality of
the sheafification unit, read at a section, and it is the move every value formula in this file is
read off from. -/
lemma sheafification_map_val_app_unit {P Q : PresheafOfModules.{w} (ringPresheaf 𝒪)} (m : P ⟶ Q)
    (V : Cᵒᵖ) (z : P.obj V) :
    ((PresheafOfModules.sheafification (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).map m).val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app P).app V z) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app Q).app V (m.app V z) :=
  app_comp_apply_eq_of_comp_eq (sheafificationUnit_naturality 𝒪 h𝒪 m).symm V z

/-- **The comparison of Tag 05NA, as a square of sheafification units.** Precomposed with the
sheafification unit of the objectwise tensor product, it is the tensor of the two sheafification
units followed by the sheafification unit of the objectwise tensor product of the two sheaves.
This is the naturality of the sheafification unit at the morphism the comparison is the
sheafification of, and `tensorSheafifyIso_hom_val_app_unit_tmul` is its sectionwise form. -/
lemma unit_comp_tensorSheafifyIso_hom_val (P Q : PresheafOfModules.{w} (ringPresheaf 𝒪)) :
    (PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app
          (P ⊗ Q) ≫ (tensorSheafifyIso 𝒪 h𝒪 P Q).hom.val =
      ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app P ⊗ₘ
          (PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app Q) ≫
        (PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app
          (((PresheafOfModules.sheafification
                (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).obj P).val ⊗
            ((PresheafOfModules.sheafification
              (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).obj Q).val) :=
  (sheafificationUnit_naturality 𝒪 h𝒪
    ((PresheafOfModules.sheafificationAdjunction
        (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app P ⊗ₘ
      (PresheafOfModules.sheafificationAdjunction
        (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app Q)).symm

/-- **The comparison of Tag 05NA on a pure tensor.** The sheafification unit carries a pure tensor
`x ⊗ₜ y` of local sections of two presheaves of modules to a local section of `(P ⊗ Q)^#`, and the
comparison `(P ⊗ Q)^# ≅ (P^# ⊗ Q^#)^#` takes that section to the unit image of the tensor of the
unit images of `x` and of `y`. -/
lemma tensorSheafifyIso_hom_val_app_unit_tmul
    (P Q : PresheafOfModules.{w} (ringPresheaf 𝒪)) (V : Cᵒᵖ) (x : P.obj V) (y : Q.obj V) :
    (tensorSheafifyIso 𝒪 h𝒪 P Q).hom.val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app (P ⊗ Q)).app V
          (x ⊗ₜ[(ringPresheaf 𝒪).obj V] y)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app
          (((PresheafOfModules.sheafification
                (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).obj P).val ⊗
            ((PresheafOfModules.sheafification
              (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).obj Q).val)).app V
        ((((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app P).app V x) ⊗ₜ[(ringPresheaf 𝒪).obj V]
          (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app Q).app V y)) :=
  (app_comp_apply_eq_of_comp_eq (unit_comp_tensorSheafifyIso_hom_val 𝒪 h𝒪 P Q) V _).trans
    (congrArg _ (ModuleCat.MonoidalCategory.tensorHom_tmul
      (((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app P).app V)
      (((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app Q).app V) x y))

end Sheafify

end Stacks.SheafOfModules.TensorSheafification

namespace Stacks.Sheaves.RingedToposModules

open Stacks.SheafOfModules.TensorSheafification

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))

/-- **The comparison `(A₂ ⊗_{p,A₁} P)^# ≅ A₂ ⊗_{A₁} P^#`, as a square of sheafification units.**
Precomposed with the sheafification unit of `A₂ ⊗_{p,A₁} P`, it is the change-of-rings image of the
sheafification unit of `P` followed by the sheafification unit of `A₂ ⊗_{p,A₁} P^#`. This is the
naturality of the sheafification unit at the morphism the comparison is the sheafification of; the
comparison is `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsUnit` sheafified. -/
lemma extendScalarsSheafifyIso_unit_comp (P : PresheafOfModules.{w} (ringPresheaf A₁)) :
    (PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          ((changeOfRings θ).obj P) ≫ (extendScalarsSheafifyIso θ h₁ h₂ P).hom.val =
      changeOfRingsUnit θ h₁ P ≫
        (PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          ((changeOfRings θ).obj
            ((PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).obj P).val) :=
  (Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality A₂ h₂
    (changeOfRingsUnit θ h₁ P)).symm

/-- **The comparison `(A₂ ⊗_{p,A₁} P)^# ≅ A₂ ⊗_{A₁} P^#` on a pure tensor.** It carries the unit
image of `a ⊗ₜ p` to the unit image of `a ⊗ₜ (unit p)`: extension of scalars commutes with
sheafification by doing nothing to the scalar. -/
lemma extendScalarsSheafifyIso_hom_val_app_unit_tmul
    (P : PresheafOfModules.{w} (ringPresheaf A₁)) (V : Cᵒᵖ) (a : A₂.obj V) (p : P.obj V) :
    let _ := (θ.app V).hom.toAlgebra
    (extendScalarsSheafifyIso θ h₁ h₂ P).hom.val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
              ((changeOfRings θ).obj P)).app V (a ⊗ₜ[A₁.obj V] p)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
            ((changeOfRings θ).obj
              ((PresheafOfModules.sheafification
                (R := commRingSheaf J A₁ h₁) (𝟙 _)).obj P).val)).app V
        (a ⊗ₜ[A₁.obj V]
          (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app P).app V p)) := by
  let _ := (θ.app V).hom.toAlgebra
  exact (app_comp_apply_eq_of_comp_eq (extendScalarsSheafifyIso_unit_comp θ h₁ h₂ P) V _).trans
    (congrArg _ (cofHom_app_tmul θ _ V a p))

/-- **The inverse of the comparison `(A₂ ⊗_{p,A₁} P)^# ≅ A₂ ⊗_{A₁} P^#` on a pure tensor.** It
carries the unit image of `a ⊗ₜ (unit p)` back to the unit image of `a ⊗ₜ p`. This is the direction
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` traverses, so it is the form step 6 of
the chain of Tag 03EL needs. -/
lemma extendScalarsSheafifyIso_inv_val_app_unit_tmul
    (P : PresheafOfModules.{w} (ringPresheaf A₁)) (V : Cᵒᵖ) (a : A₂.obj V) (p : P.obj V) :
    let _ := (θ.app V).hom.toAlgebra
    (extendScalarsSheafifyIso θ h₁ h₂ P).inv.val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
              ((changeOfRings θ).obj
                ((PresheafOfModules.sheafification
                  (R := commRingSheaf J A₁ h₁) (𝟙 _)).obj P).val)).app V
          (a ⊗ₜ[A₁.obj V]
            (((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app P).app V p))) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
            ((changeOfRings θ).obj P)).app V (a ⊗ₜ[A₁.obj V] p) := by
  let _ := (θ.app V).hom.toAlgebra
  refine Eq.trans (congrArg ((extendScalarsSheafifyIso θ h₁ h₂ P).inv.val.app V)
    (extendScalarsSheafifyIso_hom_val_app_unit_tmul θ h₁ h₂ P V a p).symm) ?_
  exact app_comp_apply_eq_of_comp_eq
    (congrArg SheafOfModules.Hom.val (extendScalarsSheafifyIso θ h₁ h₂ P).hom_inv_id) V _

/-- **Steps 5 and 6 of the chain of Tag 03EL on a pure tensor.** Composed with the unit of the
adjunction of Tag 03CZ, the base-change comparison carries the unit image of a pure tensor `x ⊗ₜ y`
of local sections of `F` and of `G` to the unit image of the tensor of the images of `x` and of `y`
under that same unit.

This is the clean statement that the two steps together take a pair of local sections to the pure
tensor of their images in the two extensions of scalars, with no scalar left over: the `1` of
`extendScalarsTensorIso_hom_val_app_unit_tmul'` is absorbed by the unit on the second factor.
In the chain of Tag 03EL at a morphism of ringed topoi it is the statement that the bottom two
steps carry a pair of local sections of `f⁻¹F` and `f⁻¹G` to the pure tensor of their images in
`f^*F ⊗_{O_C} f^*G`. -/
lemma extendScalarsTensorIso_hom_val_app_extendScalarsUnit_tmul
    (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : Cᵒᵖ)
    (x : F.val.obj V) (y : G.val.obj V) :
    (extendScalarsTensorIso θ h₁ h₂ F G).hom.val.app V
        (((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
                F).obj G))).val.app V
          (((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (F.val ⊗ G.val)).app V
            (x ⊗ₜ[(ringPresheaf A₁).obj V] y))) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
            (((extendScalars J θ h₁ h₂).obj F).val ⊗
              ((extendScalars J θ h₁ h₂).obj G).val)).app V
        ((((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app F).val.app V x)
            ⊗ₜ[(ringPresheaf A₂).obj V]
          (((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app G).val.app V y)) := by
  have := Stacks.hasSheafCompose_forget₂_commRingCat.{w, v, u} J
  exact extendScalarsTensorIso_hom_val_app_unit_tmul θ h₁ h₂ F G V x y

end Sections

end Stacks.Sheaves.RingedToposModules

end
