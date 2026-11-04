module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorBraiding
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings

/-!
# Morphisms out of iterated tensor products of sheaves of modules

Let `R` be a sheaf of commutative rings on a site. The tensor product of two sheaves of
`R`-modules is `Stacks.SheafOfModules.Tensor.sheafTensor`, the sheafification of the sectionwise
tensor product, so a morphism out of `F ⊗ G` is determined by its values on the classes
`x ⊗ y` of local pure tensors. This file proves the three-fold analogue: a morphism out of
`(F ⊗ G) ⊗ H`, or out of `F ⊗ (G ⊗ H)`, is determined by its values on the classes of iterated
local pure tensors `(x ⊗ y) ⊗ z`, respectively `x ⊗ (y ⊗ z)`. It also records the values on
local pure tensors of the symmetry `Stacks.SheafOfModules.Tensor.sheafTensorBraiding` and of the
two constraints `α_` and `β_` of the symmetric monoidal structure
`SheafOfModules.monoidalCategorySheafTensor` of Stacks 0FPQ, whose tensor product is
`sheafTensor` on the nose.

## Main results

* `Stacks.SheafOfModules.Tensor.sheafTensorBraiding_hom_app_sheafifyUnit_tmul`: the symmetry
  `F ⊗ G ≅ G ⊗ F` sends `x ⊗ y` to `y ⊗ x`.
* `Stacks.SheafOfModules.Tensor.sheafTensor_hom_ext_sheafify_left` and
  `Stacks.SheafOfModules.Tensor.sheafTensor_hom_ext_sheafify_right`: a morphism out of
  `P^# ⊗ H` (or `H ⊗ P^#`) for a presheaf of modules `P` is determined on the classes `p ⊗ z`
  (or `z ⊗ p`) with `p` a local section of `P`.
* `Stacks.SheafOfModules.Tensor.sheafTensor_hom_ext₁₂` and
  `Stacks.SheafOfModules.Tensor.sheafTensor_hom_ext₂₃`: **morphisms out of a triple tensor product
  are determined on iterated local pure tensors.**
* `Stacks.SheafOfModules.Tensor.associator_hom_app_sheafifyUnit_tmul`: the associator `α_` of
  `SheafOfModules.monoidalCategorySheafTensor` sends `(x ⊗ y) ⊗ z` to `x ⊗ (y ⊗ z)`.
* `Stacks.SheafOfModules.Tensor.braiding_hom_app_sheafifyUnit_tmul`: its braiding `β_` sends
  `x ⊗ y` to `y ⊗ x`.

The two-variable statement — a morphism out of `F ⊗ G` is determined on the classes of local
pure tensors — is `Stacks.SheafOfModules.FlatSquareZero.tensorSheaf_hom_ext`.

## Implementation notes

A section of `F ⊗ G` is only locally a sum of classes of pure tensors, so the three-fold
statements use local surjectivity of the sheafification unit
(`PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app`) together with the
separatedness of the target sheaf.

The class of a local pure tensor is spelled, as everywhere in this development, as the image of
`x ⊗ₜ y` under the unit of `PresheafOfModules.sheafificationAdjunction`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct

universe u v w

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The symmetry of the tensor product of sheaves of modules on a local pure tensor**:
`x ⊗ y ↦ y ⊗ x`. -/
theorem sheafTensorBraiding_hom_app_sheafifyUnit_tmul
    (F G : _root_.SheafOfModules.{w} (ringSheaf R)) (U : Cᵒᵖ) (x : F.val.obj U)
    (y : G.val.obj U) :
    (((sheafTensorBraiding.{u, v, w} R).app F).hom.app G).val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) F.val G.val)).app U
            (x ⊗ₜ[R.obj.obj U] y)) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) G.val F.val)).app U
            (y ⊗ₜ[R.obj.obj U] x) :=
  PresheafOfModules.hom_congr_apply'
    (PresheafOfModules.unit_comp_map (α := 𝟙 (ringSheaf R).obj)
      (β_ F.val G.val).hom) U (x ⊗ₜ[R.obj.obj U] y)

/-- The class of a local pure tensor restricts factorwise. -/
private theorem unit_tmul_map (F G : _root_.SheafOfModules.{w} (ringSheaf R)) {U V : Cᵒᵖ}
    (i : U ⟶ V) (x : F.val.obj U) (y : G.val.obj U) :
    (((sheafTensor.{u, v, w, w, w} R).obj F).obj G).val.map i
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) F.val G.val)).app U
            (x ⊗ₜ[R.obj.obj U] y)) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) F.val G.val)).app V
            (F.val.map i x ⊗ₜ[R.obj.obj V] G.val.map i y) :=
  (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
      (PresheafOfModules.tensorObj (O := R.obj) F.val G.val)) i (x ⊗ₜ[R.obj.obj U] y)).symm


variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- **Two morphisms out of `P^# ⊗ H` that agree on the classes of the local pure tensors
`p ⊗ z`, with `p` a local section of the presheaf `P`, are equal.** The sections of `P`
generate `P^#` locally. -/
theorem sheafTensor_hom_ext_sheafify_left {P : PresheafOfModules.{w} (ringSheaf R).obj}
    {H N : _root_.SheafOfModules.{w} (ringSheaf R)}
    {f g : ((sheafTensor.{u, v, w, w, w} R).obj
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P)).obj H ⟶ N}
    (h : ∀ (U : Cᵒᵖ) (p : P.obj U) (z : H.val.obj U),
      f.val.app U (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj)
            ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P).val H.val)).app U
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app P).app U p
            ⊗ₜ[R.obj.obj U] z)) =
        g.val.app U (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj)
            ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P).val H.val)).app U
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app P).app U p
            ⊗ₜ[R.obj.obj U] z))) : f = g := by
  refine PresheafOfModules.sheafification_hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.MonoidalCategory.tensor_ext fun s z => ?_)
  have hS := Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app P)) s
  refine Presheaf.IsSheaf.isSeparated N.isSheaf _ _ hS _ _ fun V i hi => ?_
  obtain ⟨t, ht⟩ := hi
  have key : ∀ k : ((sheafTensor.{u, v, w, w, w} R).obj
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P)).obj H ⟶ N,
      N.val.map i.op (k.val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj)
            ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P).val H.val)).app U
          (s ⊗ₜ[R.obj.obj U] z))) =
        k.val.app (op V)
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
            (PresheafOfModules.tensorObj (O := R.obj)
              ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P).val H.val)).app
            (op V)
            (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
              P).app (op V) t ⊗ₜ[R.obj.obj (op V)] H.val.map i.op z)) := by
    intro k
    refine (PresheafOfModules.naturality_apply k.val i.op _).symm.trans ?_
    refine congrArg (fun w => k.val.app (op V) w) ((unit_tmul_map R _ H i.op s z).trans ?_)
    exact congrArg (fun w => ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf R).obj)).unit.app (PresheafOfModules.tensorObj (O := R.obj)
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P).val H.val)).app (op V)
          (w ⊗ₜ[R.obj.obj (op V)] H.val.map i.op z)) ht.symm
  exact (key f).trans ((h _ t _).trans (key g).symm)

/-- **Two morphisms out of `H ⊗ P^#` that agree on the classes of the local pure tensors
`z ⊗ p`, with `p` a local section of the presheaf `P`, are equal.** -/
theorem sheafTensor_hom_ext_sheafify_right {P : PresheafOfModules.{w} (ringSheaf R).obj}
    {H N : _root_.SheafOfModules.{w} (ringSheaf R)}
    {f g : ((sheafTensor.{u, v, w, w, w} R).obj H).obj
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P) ⟶ N}
    (h : ∀ (U : Cᵒᵖ) (z : H.val.obj U) (p : P.obj U),
      f.val.app U (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) H.val
            ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P).val)).app U
          (z ⊗ₜ[R.obj.obj U]
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app P).app U
              p)) =
        g.val.app U (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) H.val
            ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P).val)).app U
          (z ⊗ₜ[R.obj.obj U]
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app P).app U
              p))) : f = g := by
  refine PresheafOfModules.sheafification_hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.MonoidalCategory.tensor_ext fun z s => ?_)
  have hS := Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app P)) s
  refine Presheaf.IsSheaf.isSeparated N.isSheaf _ _ hS _ _ fun V i hi => ?_
  obtain ⟨t, ht⟩ := hi
  have key : ∀ k : ((sheafTensor.{u, v, w, w, w} R).obj H).obj
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P) ⟶ N,
      N.val.map i.op (k.val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) H.val
            ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P).val)).app U
          (z ⊗ₜ[R.obj.obj U] s))) =
        k.val.app (op V)
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
            (PresheafOfModules.tensorObj (O := R.obj) H.val
              ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P).val)).app
            (op V)
            (H.val.map i.op z ⊗ₜ[R.obj.obj (op V)]
              ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
                P).app (op V) t)) := by
    intro k
    refine (PresheafOfModules.naturality_apply k.val i.op _).symm.trans ?_
    refine congrArg (fun w => k.val.app (op V) w) ((unit_tmul_map R H _ i.op z s).trans ?_)
    exact congrArg (fun w => ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf R).obj)).unit.app (PresheafOfModules.tensorObj (O := R.obj) H.val
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P).val)).app (op V)
          (H.val.map i.op z ⊗ₜ[R.obj.obj (op V)] w)) ht.symm
  exact (key f).trans ((h _ _ t).trans (key g).symm)

/-- **Two morphisms out of `(F ⊗ G) ⊗ H` that agree on the classes of the iterated local pure
tensors `(x ⊗ y) ⊗ z` are equal.** -/
theorem sheafTensor_hom_ext₁₂ {F G H N : _root_.SheafOfModules.{w} (ringSheaf R)}
    {f g : ((sheafTensor.{u, v, w, w, w} R).obj
      (((sheafTensor.{u, v, w, w, w} R).obj F).obj G)).obj H ⟶ N}
    (h : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U) (z : H.val.obj U),
      f.val.app U (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj)
            (((sheafTensor.{u, v, w, w, w} R).obj F).obj G).val H.val)).app U
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
            (PresheafOfModules.tensorObj (O := R.obj) F.val G.val)).app U
              (x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z)) =
        g.val.app U (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj)
            (((sheafTensor.{u, v, w, w, w} R).obj F).obj G).val H.val)).app U
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
            (PresheafOfModules.tensorObj (O := R.obj) F.val G.val)).app U
              (x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z))) : f = g := by
  refine sheafTensor_hom_ext_sheafify_left R (P := PresheafOfModules.tensorObj (O := R.obj)
    F.val G.val) fun U t z => ?_
  induction t using TensorProduct.induction_on with
  | zero =>
    erw [map_zero, TensorProduct.zero_tmul, map_zero, map_zero, map_zero]
  | tmul x y => exact h U x y z
  | add t t' ht ht' =>
    erw [map_add, TensorProduct.add_tmul, map_add, map_add, map_add, ht, ht']

/-- **Two morphisms out of `F ⊗ (G ⊗ H)` that agree on the classes of the iterated local pure
tensors `x ⊗ (y ⊗ z)` are equal.** -/
theorem sheafTensor_hom_ext₂₃ {F G H N : _root_.SheafOfModules.{w} (ringSheaf R)}
    {f g : ((sheafTensor.{u, v, w, w, w} R).obj F).obj
      (((sheafTensor.{u, v, w, w, w} R).obj G).obj H) ⟶ N}
    (h : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U) (z : H.val.obj U),
      f.val.app U (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) F.val
            (((sheafTensor.{u, v, w, w, w} R).obj G).obj H).val)).app U
          (x ⊗ₜ[R.obj.obj U]
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
              (PresheafOfModules.tensorObj (O := R.obj) G.val H.val)).app U
                (y ⊗ₜ[R.obj.obj U] z))) =
        g.val.app U (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) F.val
            (((sheafTensor.{u, v, w, w, w} R).obj G).obj H).val)).app U
          (x ⊗ₜ[R.obj.obj U]
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
              (PresheafOfModules.tensorObj (O := R.obj) G.val H.val)).app U
                (y ⊗ₜ[R.obj.obj U] z)))) : f = g := by
  refine sheafTensor_hom_ext_sheafify_right R (P := PresheafOfModules.tensorObj (O := R.obj)
    G.val H.val) fun U x t => ?_
  induction t using TensorProduct.induction_on with
  | zero =>
    erw [map_zero, TensorProduct.tmul_zero, map_zero, map_zero, map_zero]
  | tmul y z => exact h U x y z
  | add t t' ht ht' =>
    erw [map_add, TensorProduct.tmul_add, map_add, map_add, map_add, ht, ht']

/-! ### The constraints of the symmetric monoidal structure of Stacks 0FPQ on pure tensors -/

section Monoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **The commutativity constraint `β_` of `SheafOfModules.monoidalCategorySheafTensor` on a local
pure tensor**: `x ⊗ y ↦ y ⊗ x`. -/
theorem braiding_hom_app_sheafifyUnit_tmul
    (F G : _root_.SheafOfModules.{max u v} (ringSheaf R)) (U : Cᵒᵖ) (x : F.val.obj U)
    (y : G.val.obj U) :
    (@BraidedCategory.braiding _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor R)
        (_root_.SheafOfModules.symmetricCategorySheafTensor R).toBraidedCategory F G).hom.val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) F.val G.val)).app U
            (x ⊗ₜ[R.obj.obj U] y)) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) G.val F.val)).app U
            (y ⊗ₜ[R.obj.obj U] x) := by
  rw [_root_.SheafOfModules.braiding_eq_sheafTensorBraiding]
  exact sheafTensorBraiding_hom_app_sheafifyUnit_tmul R F G U x y

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]

/-- **The associativity constraint `α_` of `SheafOfModules.monoidalCategorySheafTensor` on an
iterated local pure tensor**: `(x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z)`. -/
theorem associator_hom_app_sheafifyUnit_tmul
    (F G H : _root_.SheafOfModules.{max u v} (ringSheaf R)) (U : Cᵒᵖ) (x : F.val.obj U)
    (y : G.val.obj U) (z : H.val.obj U) :
    (@MonoidalCategoryStruct.associator _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor R).toMonoidalCategoryStruct
        F G H).hom.val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj)
            (((sheafTensor.{u, v, max u v, max u v, max u v} R).obj F).obj G).val H.val)).app U
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
            (PresheafOfModules.tensorObj (O := R.obj) F.val G.val)).app U
              (x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z)) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
          (PresheafOfModules.tensorObj (O := R.obj) F.val
            (((sheafTensor.{u, v, max u v, max u v, max u v} R).obj G).obj H).val)).app U
          (x ⊗ₜ[R.obj.obj U]
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
              (PresheafOfModules.tensorObj (O := R.obj) G.val H.val)).app U
                (y ⊗ₜ[R.obj.obj U] z)) :=
  Stacks.SheafOfModules.associator_hom_val_app_tmul R.obj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf R) F G H U x y z

end Monoidal

end Stacks.SheafOfModules.Tensor

end
