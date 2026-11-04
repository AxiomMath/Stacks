module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsTensorValue

/-!
# Sheafification units through the comparisons of extension of scalars

Extension of scalars for sheaves of modules along a morphism `θ : A₁ ⟶ A₂` of presheaves of
commutative rings whose underlying presheaves of rings are sheaves is a change of rings followed
by a sheafification, and the two comparison isomorphisms it comes with —
`Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso`, that extension of scalars commutes
with sheafification, and `Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso`, which is
Tag 05NA — are both sheafifications of an explicit morphism of presheaves of modules. Each
therefore has a *value formula*: precomposed with the sheafification unit of its source it is the
explicit morphism followed by the sheafification unit of its target.

Those two value formulas are what this file proves, and the files defining the two comparisons
carry naturality only. A value formula is what any computation with these comparisons on local
sections needs, because a morphism out of a sheafification is pinned down by its restriction
along the unit; naturality alone never reaches a section.

What the two formulas combine into is also proved here, both as morphisms and on local sections:
the comparison `A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)` of Tag 03EL's
step 4 carries the extension-unit image of a pure tensor `a ⊗ₜ b` to the pure tensor of the
extension-unit images of `a` and of `b`.

## Main results

* `Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso_hom_eq_map_unit`: the comparison
  isomorphism of `extendScalarsSheafifyIso` is the sheafification of the change-of-rings image of
  a sheafification unit.
* `Stacks.Sheaves.RingedToposModules.sheafificationUnit_comp_extendScalarsSheafifyIso_hom_val`:
  **the value formula for `extendScalarsSheafifyIso`.** Composing the sheafification unit of
  `A₂ ⊗_{p,A₁} P` with the comparison is the change-of-rings image of the sheafification unit of
  `P`, followed by the sheafification unit of `A₂ ⊗_{p,A₁} P^#`.
* `Stacks.Sheaves.RingedToposModules.sheafificationUnit_comp_tensorSheafifyIso_hom_val`: **the
  value formula for the comparison of Tag 05NA.** Composing the sheafification unit of `P ⊗ Q`
  with the comparison is the tensor product of the two sheafification units, followed by the
  sheafification unit of `P^# ⊗ Q^#`.
* `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_one_tmul`:
  the unit of Tag 03CZ sends a local section `x` to the sheafification-unit image of `1 ⊗ₜ x`.

* `Stacks.Sheaves.RingedToposModules.sheafificationUnit_comp_extendScalarsTensorIso_hom_val`:
  **base change of a tensor product, on a pure tensor.** The comparison
  `A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)` carries the extension-unit image
  of a pure tensor to the pure tensor of the two extension-unit images — on elements,
  `1 ⊗ (x ⊗ y) ↦ (1 ⊗ x) ⊗ (1 ⊗ y)`.
* `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_val_app_unit_tmul`: that last
  statement **on local sections**, with the two `1 ⊗ₜ`'s read as values of the unit of Tag 03CZ.
  This is the form a computation with step 4 of the chain of Tag 03EL consumes.

## Implementation notes

Both value formulas are in term mode, from
`Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality` — the naturality of
the sheafification unit — and a `congrArg` that moves the identification of the comparison with a
sheafification map under the composition. There is nothing to rewrite: the identification is a
`rfl` whose two sides are definitionally equal only at default transparency, so a `rw` of it
inside a composition fails its motive check.

The third layer any computation with the base change of a tensor product needs — the value
formula for the sheafification of an arbitrary morphism of presheaves of modules — is not proved
here, because it already *is*
`Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ) — extension and
  restriction of scalars.
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA) — the tensor product of
  sheaves of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.SheafOfModules.TensorSheafification

namespace Stacks.Sheaves.RingedToposModules

universe w v u

section UnitFormulas

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))

/-- **The comparison isomorphism of
`Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso` is the sheafification of the
change-of-rings image of a sheafification unit.** This is its definition, restated so that the
morphism it is the sheafification of can be named; the two sides are definitionally equal only at
default transparency, so this identity cannot be used as a rewrite inside a composition. -/
theorem extendScalarsSheafifyIso_hom_eq_map_unit
    (P : PresheafOfModules.{w} (ringPresheaf A₁)) :
    (extendScalarsSheafifyIso θ h₁ h₂ P).hom =
      (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
        ((changeOfRings θ).map
          ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app P)) :=
  rfl

/-- A morphism of sheaves of modules equal to a sheafified morphism `f` has underlying morphism
`f` along the sheafification units. -/
private theorem unit_comp_val_eq_of_eq_map {P Q : PresheafOfModules.{w} (ringPresheaf A₂)}
    (f : P ⟶ Q) (m : (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj P ⟶
      (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj Q)
    (hm : m = (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map f) :
    (PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app P ≫
        m.val =
      f ≫ (PresheafOfModules.sheafificationAdjunction
        (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app Q :=
  hm ▸ (sheafificationUnit_naturality A₂ h₂ f).symm

/-- **The value formula for `Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso`.** The
sheafification unit of `A₂ ⊗_{p,A₁} P` followed by the comparison isomorphism is the
change-of-rings image of the sheafification unit of `P`, followed by the sheafification unit of
`A₂ ⊗_{p,A₁} P^#`.

This is what pins the comparison down on local sections, and it is also what lets the
comparison's *inverse* be cancelled without ever being computed: the inverse appears in
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` precomposed by exactly the morphism
this formula produces. -/
theorem sheafificationUnit_comp_extendScalarsSheafifyIso_hom_val
    (P : PresheafOfModules.{w} (ringPresheaf A₁)) :
    (PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          ((changeOfRings θ).obj P) ≫
        (extendScalarsSheafifyIso θ h₁ h₂ P).hom.val =
      (changeOfRings θ).map
          ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app P) ≫
        (PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          ((changeOfRings θ).obj
            ((PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).obj P).val) :=
  unit_comp_val_eq_of_eq_map h₂ _ _ (extendScalarsSheafifyIso_hom_eq_map_unit θ h₁ h₂ P)

/-- **The value formula for the comparison of Tag 05NA.** The sheafification unit of the
objectwise tensor product `P ⊗ Q`, followed by the comparison
`(P ⊗ Q)^# ≅ P^# ⊗_{A₂} Q^#`, is the tensor product of the two sheafification units followed by
the sheafification unit of `P^# ⊗ Q^#`.

This is the companion of
`Stacks.Sheaves.RingedToposModules.sheafificationUnit_comp_extendScalarsSheafifyIso_hom_val` for
the other comparison that extension of scalars for sheaves of modules is assembled from, and it
is what carries a pure tensor of local sections across Tag 05NA: the right-hand side sends the
unit image of `a ⊗ₜ b` to the unit image of the tensor of the two unit images. -/
theorem sheafificationUnit_comp_tensorSheafifyIso_hom_val
    (P Q : PresheafOfModules.{w} (ringPresheaf A₂)) :
    (PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          (P ⊗ Q) ≫ (tensorSheafifyIso A₂ h₂ P Q).hom.val =
      ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app P ⊗ₘ
          (PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app Q) ≫
        (PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          (((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj P).val ⊗
            ((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj Q).val) :=
  unit_comp_val_eq_of_eq_map h₂ _ _ (tensorSheafifyIso_hom_eq A₂ h₂ P Q)

open scoped TensorProduct in
/-- **The unit of Tag 03CZ on local sections, in the sheafification-unit spelling**: a section
`x` of a sheaf of `A₁`-modules `L` is carried by the unit of the extension-restriction adjunction
to the sheafification-unit image of `1 ⊗ₜ x`.

This is
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply` with
the sheafification written as the unit of the sheafification adjunction rather than as
`CategoryTheory.toSheafify`, which is the spelling the value formulas of this file use. -/
theorem extendRestrictScalarsAdjunction_unit_app_one_tmul
    (L : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : Cᵒᵖ) (x : L.val.obj V) :
    (((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L).val.app V).hom x =
      letI := (θ.app V).hom.toAlgebra
      ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          ((changeOfRings θ).obj L.val)).app V ((1 : A₂.obj V) ⊗ₜ[A₁.obj V] x) := by
  rw [show ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L).val
      = (SheafOfModules.forget (commRingSheaf J A₁ h₁)).map
          ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app L) from rfl,
    forget_map_extendRestrictScalarsAdjunction_unit_app, PresheafOfModules.comp_app]
  rw (transparency := .default) [ModuleCat.hom_comp, LinearMap.comp_apply,
    changeOfRingsAdjunction_unit_app_apply]

end UnitFormulas

/-! ## The pure-tensor identity for base change of a tensor product -/

section TensorIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
  (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁))


/-- **The base change of a tensor product of sheaves of modules, on a pure tensor.** Carry the
sheafification unit image of `a ⊗ₜ b` into the extension of scalars of `F ⊗_{A₁} G` and apply the
comparison `A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)`; the result is the
presheaf-level base change of Tag 03CU followed by the tensor product of the two sheafification
units and one more sheafification unit.

On an element the right-hand side is `1 ⊗ₜ (a ⊗ₜ b) ↦ (1 ⊗ₜ a) ⊗ₜ (1 ⊗ₜ b)` — the presheaf-level
base change is
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorObjIso_hom_app`, i.e.
`TensorProduct.AlgebraTensorModule.distribBaseChange` — and `1 ⊗ₜ a` carried along the
sheafification unit is the value of the unit of Tag 03CZ's adjunction at `a`, by
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply`. So
this is the statement that the comparison of Tag 03EL's step 4 takes the extension-unit image of
a pure tensor to the pure tensor of the two extension-unit images.

Every layer is discharged by a value formula and nothing is computed on sections here: the
inverse of `extendScalarsSheafifyIso` is cancelled by
`extendScalarsSheafifyIso_hom_comp_extendScalarsTensorIso_hom`, the sheafified presheaf
comparison by `Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality`, and
the comparison of Tag 05NA by `sheafificationUnit_comp_tensorSheafifyIso_hom_val`. -/
theorem sheafificationUnit_comp_extendScalarsTensorIso_hom_val :
    (changeOfRings θ).map
          ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (F.val ⊗ G.val)) ≫
        ((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
            ((changeOfRings θ).obj
              ((PresheafOfModules.sheafification
                (R := commRingSheaf J A₁ h₁) (𝟙 _)).obj (F.val ⊗ G.val)).val) ≫
          (extendScalarsTensorIso θ h₁ h₂ F G).hom.val) =
      (changeOfRingsTensorObjIso θ F.val G.val).hom ≫
        (((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app ((changeOfRings θ).obj F.val) ⊗ₘ
            (PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app ((changeOfRings θ).obj G.val)) ≫
          (PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
            (((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj
                  ((changeOfRings θ).obj F.val)).val ⊗
              ((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj
                  ((changeOfRings θ).obj G.val)).val)) :=
  have hval : ((extendScalarsSheafifyIso θ h₁ h₂ (F.val ⊗ G.val)).hom.val ≫
        (extendScalarsTensorIso θ h₁ h₂ F G).hom.val) =
      (((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
            (changeOfRingsTensorObjIso θ F.val G.val).hom).val ≫
        (tensorSheafifyIso A₂ h₂ ((changeOfRings θ).obj F.val)
          ((changeOfRings θ).obj G.val)).hom.val) :=
    congrArg SheafOfModules.Hom.val
      (extendScalarsSheafifyIso_hom_comp_extendScalarsTensorIso_hom θ h₁ h₂ F G)
  ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun m ↦ m ≫ (extendScalarsTensorIso θ h₁ h₂ F G).hom.val)
        (sheafificationUnit_comp_extendScalarsSheafifyIso_hom_val θ h₁ h₂
          (F.val ⊗ G.val)).symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun m ↦ (PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app ((changeOfRings θ).obj
            (F.val ⊗ G.val)) ≫ m) hval)))).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m ↦ m ≫ (tensorSheafifyIso A₂ h₂ ((changeOfRings θ).obj F.val)
            ((changeOfRings θ).obj G.val)).hom.val)
          (sheafificationUnit_naturality A₂ h₂
            (changeOfRingsTensorObjIso θ F.val G.val).hom).symm).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun m ↦ (changeOfRingsTensorObjIso θ F.val G.val).hom ≫ m)
            (sheafificationUnit_comp_tensorSheafifyIso_hom_val h₂
              ((changeOfRings θ).obj F.val) ((changeOfRings θ).obj G.val))))))

open scoped TensorProduct in
/-- **The base change of a tensor product carries the extension-unit image of a pure tensor to
the pure tensor of the two extension-unit images.** Take two local sections `a` of `F` and `b` of
`G`, form the section `a ⊗ₜ b` of `F ⊗_{A₁} G`, carry it into the extension of scalars by the
unit of Tag 03CZ and apply the comparison
`A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)`; the result is the pure tensor of
the unit images of `a` and of `b`.

This is the element form of
`Stacks.Sheaves.RingedToposModules.sheafificationUnit_comp_extendScalarsTensorIso_hom_val`, which
it is obtained from by evaluating at `1 ⊗ₜ (a ⊗ₜ b)`: the unit of Tag 03CZ contributes the `1 ⊗ₜ`
on each side by
`extendRestrictScalarsAdjunction_unit_app_one_tmul`, and the presheaf-level
comparison `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorObjIso` — objectwise
`TensorProduct.AlgebraTensorModule.distribBaseChange`, which sends `1 ⊗ₜ (a ⊗ₜ b)` to
`(1 ⊗ₜ a) ⊗ₜ (1 ⊗ₜ b)` — accounts for the rest. It is the identity that step 4 of the chain of
Tag 03EL is pinned down by on local sections. -/
theorem extendScalarsTensorIso_hom_val_app_unit_tmul (U : Cᵒᵖ)
    (a : F.val.obj U) (b : G.val.obj U) :
    ((extendScalarsTensorIso θ h₁ h₂ F G).hom.val.app U).hom
        ((((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app
              (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat)
          h₁⟩).obj F).obj G)).val.app U).hom
          (((PresheafOfModules.sheafificationAdjunction
                (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (F.val ⊗ G.val)).app U
            (a ⊗ₜ[(A₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b))) =
      ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          (((extendScalars J θ h₁ h₂).obj F).val ⊗ ((extendScalars J θ h₁ h₂).obj G).val)).app U
        ((((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app F).val.app U).hom a ⊗ₜ
          (((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app G).val.app U).hom b) := by
  refine (congrArg (fun z ↦ ((extendScalarsTensorIso θ h₁ h₂ F G).hom.val.app U).hom z)
    (extendRestrictScalarsAdjunction_unit_app_one_tmul θ h₁ h₂
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat)
          h₁⟩).obj F).obj G) U _)).trans ?_
  let := (θ.app U).hom.toAlgebra
  refine (CategoryTheory.congr_fun
    (congrArg (fun m ↦ PresheafOfModules.Hom.app m U)
      (sheafificationUnit_comp_extendScalarsTensorIso_hom_val θ h₁ h₂ F G))
    ((1 : A₂.obj U) ⊗ₜ[A₁.obj U]
      (show (F.val ⊗ G.val).obj U from
        a ⊗ₜ[(A₁ ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b))).trans ?_
  rw [extendRestrictScalarsAdjunction_unit_app_one_tmul θ h₁ h₂ F U a,
    extendRestrictScalarsAdjunction_unit_app_one_tmul θ h₁ h₂ G U b]
  rfl

end TensorIso

end Stacks.Sheaves.RingedToposModules

end
