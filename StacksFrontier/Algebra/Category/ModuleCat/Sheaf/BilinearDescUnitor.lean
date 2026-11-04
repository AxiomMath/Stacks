module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

/-!
# A morphism out of a tensor product given by a bilinear map, evaluated at a global section

Let `𝒪` be a sheaf of commutative rings and let `β : F × D ⟶ Q` be a bilinear map of sheaves of
`𝒪`-modules, given on sections.  For the monoidal structure on sheaves of modules obtained by
localizing along sheafification (`Stacks.SheafOfModules.monoidalCategory`), `β` descends to a
morphism `F ⊗ D ⟶ Q` (`Stacks.SheafOfModules.bilinearDesc`).  This file computes the composite

`D ≅ 𝟙 ⊗ D ⟶ F ⊗ D ⟶ Q`

of the inverse left unitor, the whiskering by a global section `s : 𝟙 ⟶ F` and that descent: on a
section `d` it is `β(s(1), d)`.  The computation transports to the strict monoidal structure
`Stacks.SheafOfModules.Strict.monoidalCategory`, whose unitor and whiskering are the localized
ones conjugated by `Stacks.SheafOfModules.tensorObjIso` and have section formulas.

## Main definitions

* `Stacks.SheafOfModules.bilinearDesc`: the morphism `F ⊗ D ⟶ Q` induced by `β`.

## Main results

* `Stacks.SheafOfModules.bilinearDesc_unit_tmul`: it is `β` on pure tensors.
* `Stacks.SheafOfModules.leftUnitor_inv_whiskerRight_bilinearDesc_val_app`: the composite with
  `λ⁻¹` and `s ▷ D` is `d ↦ β(s(1), d)`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules Opposite

open scoped TensorProduct

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Osharp : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
    Osharp.obj))

/-- **The morphism out of a tensor product induced by a bilinear map**, for the localized monoidal
structure: the comparison with the tensor product sheaf followed by the descent of `β` along
sheafification. -/
def bilinearDesc {F D Q : _root_.SheafOfModules.{w} (toRingCat J Osharp)}
    (β : Stacks.BilinearMap F.val D.val Q.val) :
    letI : MonoidalCategory (_root_.SheafOfModules.{w} (toRingCat J Osharp)) :=
      Stacks.SheafOfModules.monoidalCategory Osharp.obj hO
    F ⊗ D ⟶ Q :=
  (tensorObjIso Osharp.obj hO F D).hom ≫ tensorSheafDesc (PresheafOfModules.ofBilinear β)

/-- **The left unitor, the whiskering by a global section and the descent of a bilinear map**:
`D ≅ 𝟙 ⊗ D ⟶ F ⊗ D ⟶ Q` is `d ↦ β(s(1), d)` on sections. -/
theorem leftUnitor_inv_whiskerRight_bilinearDesc_val_app
    {F D Q : _root_.SheafOfModules.{w} (toRingCat J Osharp)}
    (β : Stacks.BilinearMap F.val D.val Q.val)
    (s : _root_.SheafOfModules.unit (toRingCat J Osharp) ⟶ F) (V : Cᵒᵖ) (d : D.val.obj V) :
    letI : MonoidalCategory (_root_.SheafOfModules.{w} (toRingCat J Osharp)) :=
      Stacks.SheafOfModules.monoidalCategory Osharp.obj hO
    ((λ_ D).inv ≫ s ▷ D ≫ bilinearDesc Osharp hO β).val.app V d =
      β.app V (s.val.app V (1 : (toRingCat J Osharp).obj.obj V)) d := by
  let : MonoidalCategory (_root_.SheafOfModules.{w} (toRingCat J Osharp)) :=
    Stacks.SheafOfModules.monoidalCategory Osharp.obj hO
  let T := tensorObjIso Osharp.obj hO
  let U := _root_.SheafOfModules.unit (toRingCat J Osharp)
  -- the strict left unitor, on the sheafification unit of a pure tensor
  have h1 : (@MonoidalCategoryStruct.leftUnitor _ _
      (Stacks.TensorSheafWorld.monoidalCategory Osharp).toMonoidalCategoryStruct D).hom.val.app V
        ((tensorSheafUnit U D).app V ((1 : (toRingCat J Osharp).obj.obj V) ⊗ₜ d)) = d := by
    have h := @Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit _ _ _ _ Osharp _ _
      hO D V 1 d
    rwa [one_smul] at h
  -- the strict left unitor is the localized one followed by `T`
  have h2 : (T U D).hom.val.app V ((λ_ D).inv.val.app V d) =
      (tensorSheafUnit U D).app V ((1 : (toRingCat J Osharp).obj.obj V) ⊗ₜ d) := by
    have h := Stacks.SheafOfModules.inv_val_app_hom_val_app (@MonoidalCategoryStruct.leftUnitor _ _
      (Stacks.TensorSheafWorld.monoidalCategory Osharp).toMonoidalCategoryStruct D) V
      ((tensorSheafUnit U D).app V ((1 : (toRingCat J Osharp).obj.obj V) ⊗ₜ d))
    rwa [h1] at h
  have h3 : (λ_ D).inv.val.app V d = (T U D).inv.val.app V
      ((tensorSheafUnit U D).app V ((1 : (toRingCat J Osharp).obj.obj V) ⊗ₜ d)) :=
    (Stacks.SheafOfModules.inv_val_app_hom_val_app (T U D) V ((λ_ D).inv.val.app V d)).symm.trans
      (congrArg (fun x ↦ (T U D).inv.val.app V x) h2)
  show (tensorSheafDesc (PresheafOfModules.ofBilinear β)).val.app V
    ((T F D).hom.val.app V ((s ▷ D).val.app V ((λ_ D).inv.val.app V d))) = _
  rw [h3]
  -- the strict whiskering is the localized one conjugated by `T`
  show (tensorSheafDesc (PresheafOfModules.ofBilinear β)).val.app V
    ((@MonoidalCategoryStruct.whiskerRight _ _
        (Stacks.TensorSheafWorld.monoidalCategory Osharp).toMonoidalCategoryStruct
          _ _ s D).val.app V
        ((tensorSheafUnit U D).app V ((1 : (toRingCat J Osharp).obj.obj V) ⊗ₜ d))) = _
  exact (congrArg (fun x ↦ (tensorSheafDesc (PresheafOfModules.ofBilinear β)).val.app V x)
      (@Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit _ _ _ _ Osharp _ _ hO V
        _ _ s D (1 : (toRingCat J Osharp).obj.obj V) d)).trans
    ((tensorSheafDesc_unit _ _ _ _).trans (PresheafOfModules.ofBilinear_tmul _ _ _ _))

/-- **The descent of a bilinear map, on a pure tensor**: `bilinearDesc β` sends the image of
`x ⊗ y` in `F ⊗ D` (through the comparison with the tensor product sheaf) to `β(x, y)`. -/
theorem bilinearDesc_val_app_tensorSheafUnit
    {F D Q : _root_.SheafOfModules.{w} (toRingCat J Osharp)}
    (β : Stacks.BilinearMap F.val D.val Q.val) (V : Cᵒᵖ) (x : F.val.obj V) (y : D.val.obj V) :
    (bilinearDesc Osharp hO β).val.app V ((tensorObjIso Osharp.obj hO F D).inv.val.app V
      ((tensorSheafUnit F D).app V (x ⊗ₜ y))) = β.app V x y := by
  show (tensorSheafDesc (PresheafOfModules.ofBilinear β)).val.app V
    ((tensorObjIso Osharp.obj hO F D).hom.val.app V ((tensorObjIso Osharp.obj hO F D).inv.val.app V
      ((tensorSheafUnit F D).app V (x ⊗ₜ y)))) = _
  exact (congrArg (fun z ↦ (tensorSheafDesc (PresheafOfModules.ofBilinear β)).val.app V z)
    (Stacks.SheafOfModules.hom_val_app_inv_val_app (tensorObjIso Osharp.obj hO F D) V _)).trans
    ((tensorSheafDesc_unit _ _ _ _).trans (PresheafOfModules.ofBilinear_tmul _ _ _ _))

/-- **Right whiskering followed by the descent of a bilinear map, on a pure tensor**:
`φ ▷ F ≫ bilinearDesc β` sends the image of `m ⊗ y` to `β(φ(m), y)`. -/
theorem whiskerRight_bilinearDesc_val_app_tensorSheafUnit
    {M D F Q : _root_.SheafOfModules.{w} (toRingCat J Osharp)} (φ : M ⟶ D)
    (β : Stacks.BilinearMap D.val F.val Q.val) (V : Cᵒᵖ) (m : M.val.obj V) (y : F.val.obj V) :
    letI : MonoidalCategory (_root_.SheafOfModules.{w} (toRingCat J Osharp)) :=
      Stacks.SheafOfModules.monoidalCategory Osharp.obj hO
    (φ ▷ F ≫ bilinearDesc Osharp hO β).val.app V ((tensorObjIso Osharp.obj hO M F).inv.val.app V
      ((tensorSheafUnit M F).app V (m ⊗ₜ y))) = β.app V (φ.val.app V m) y := by
  let : MonoidalCategory (_root_.SheafOfModules.{w} (toRingCat J Osharp)) :=
    Stacks.SheafOfModules.monoidalCategory Osharp.obj hO
  show (tensorSheafDesc (PresheafOfModules.ofBilinear β)).val.app V
    ((@MonoidalCategoryStruct.whiskerRight _ _
        (Stacks.TensorSheafWorld.monoidalCategory Osharp).toMonoidalCategoryStruct
          _ _ φ F).val.app V
        ((tensorSheafUnit M F).app V (m ⊗ₜ y))) = _
  exact (congrArg (fun z ↦ (tensorSheafDesc (PresheafOfModules.ofBilinear β)).val.app V z)
      (@Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit _ _ _ _ Osharp _ _ hO V
        _ _ φ F m y)).trans
    ((tensorSheafDesc_unit _ _ _ _).trans (PresheafOfModules.ofBilinear_tmul _ _ _ _))

/-- **Maps out of `F ⊗ D` are determined on pure tensors**, for the localized monoidal structure:
the comparison with the tensor product sheaf is an isomorphism, and maps out of the tensor
product sheaf are determined on the sheafification unit of pure tensors. -/
theorem hom_ext_of_tensorSheafUnit {F D Q : _root_.SheafOfModules.{w} (toRingCat J Osharp)}
    {ψ₁ ψ₂ : (Stacks.SheafOfModules.monoidalCategory Osharp.obj hO).tensorObj F D ⟶ Q}
    (h : ∀ (V : Cᵒᵖ) (x : F.val.obj V) (y : D.val.obj V),
      ψ₁.val.app V ((tensorObjIso Osharp.obj hO F D).inv.val.app V
        ((tensorSheafUnit F D).app V (x ⊗ₜ y))) =
      ψ₂.val.app V ((tensorObjIso Osharp.obj hO F D).inv.val.app V
        ((tensorSheafUnit F D).app V (x ⊗ₜ y)))) :
    ψ₁ = ψ₂ :=
  (Iso.cancel_iso_inv_left (tensorObjIso Osharp.obj hO F D) ψ₁ ψ₂).1
    (tensorSheaf_hom_ext fun U x y ↦ h U x y)

end Stacks.SheafOfModules

end
