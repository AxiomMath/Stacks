module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import StacksCore.CategoryTheory.GradedObject.GradedVectorSpace

/-!
# The total space of a tensor product of graded vector spaces

For `ℤ`-graded `F`-vector spaces `V` and `W` with the monoidal structure of Stacks, Homology,
Example 0FFX, the total space of `V ⊗ W` is the tensor product of the total spaces:
`(⨁ᵢ Vⁱ) ⊗_F (⨁ⱼ Wʲ) ≅ ⨁ₙ (V ⊗ W)ⁿ`, `vᵢ ⊗ wⱼ ↦ ι(vᵢ ⊗ wⱼ) ∈ (V ⊗ W)^{i+j}`.

## Main definitions

* `CategoryTheory.GradedObject.Monoidal.totalTensorEquiv`: the isomorphism of total spaces.

## Main results

* `CategoryTheory.GradedObject.Monoidal.totalTensorEquiv_tmul`: its value on `vᵢ ⊗ wⱼ`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.GradedObject.Monoidal

open CategoryTheory MonoidalCategory DirectSum
open scoped TensorProduct

universe w

variable {F : Type w} [Field F] (V W : GradedObject ℤ (ModuleCat.{w} F))

/-- The bilinear map `Vⁱ × Wʲ → (V ⊗ W)^{i+j}`, `(v, w) ↦ ι(v ⊗ w)`, into the total space. -/
def totalTensorPiece (i j : ℤ) : V i →ₗ[F] W j →ₗ[F] ⨁ n, (V ⊗ W) n :=
  (TensorProduct.mk F (V i) (W j)).compr₂
    ((lof F ℤ (fun n ↦ (V ⊗ W) n) (i + j)).comp (ιTensorObj V W i j _ rfl).hom)

/-- The map `(⨁ᵢ Vⁱ) ⊗ (⨁ⱼ Wʲ) → ⨁ₙ (V ⊗ W)ⁿ`, `vᵢ ⊗ wⱼ ↦ ι(vᵢ ⊗ wⱼ)`. -/
def totalTensorHom : (⨁ i, V i) ⊗[F] (⨁ j, W j) →ₗ[F] ⨁ n, (V ⊗ W) n :=
  TensorProduct.lift (toModule F ℤ _ fun i ↦
    (toModule F ℤ _ fun j ↦ (totalTensorPiece V W i j).flip).flip)

/-- `totalTensorHom` sends `vᵢ ⊗ wⱼ` to `ι(vᵢ ⊗ wⱼ)` in the summand `(V ⊗ W)^{i+j}`. -/
theorem totalTensorHom_tmul (i j : ℤ) (v : V i) (w : W j) :
    totalTensorHom V W (lof F ℤ (fun i ↦ V i) i v ⊗ₜ lof F ℤ (fun j ↦ W j) j w) =
      lof F ℤ (fun n ↦ (V ⊗ W) n) (i + j) (ιTensorObj V W i j _ rfl (v ⊗ₜ w)) := by
  simp only [totalTensorHom, TensorProduct.lift.tmul, toModule_lof, LinearMap.flip_apply,
    totalTensorPiece, LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.coe_comp,
    Function.comp_apply]

/-- The map `⨁ₙ (V ⊗ W)ⁿ → (⨁ᵢ Vⁱ) ⊗ (⨁ⱼ Wʲ)` inverse to `totalTensorHom`. -/
def totalTensorInv : (⨁ n, (V ⊗ W) n) →ₗ[F] (⨁ i, V i) ⊗[F] (⨁ j, W j) :=
  toModule F ℤ _ fun _ ↦ (tensorObjDesc (X₁ := V) (X₂ := W)
    (A := ModuleCat.of F ((⨁ i, V i) ⊗[F] (⨁ j, W j))) fun i j _ ↦
      ModuleCat.ofHom (TensorProduct.map (lof F ℤ (fun i ↦ V i) i)
        (lof F ℤ (fun j ↦ W j) j))).hom

/-- `totalTensorInv` sends `ι(v ⊗ w)`, for `v ∈ Vⁱ` and `w ∈ Wʲ`, to `vᵢ ⊗ wⱼ`. -/
theorem totalTensorInv_ι (i j n : ℤ) (h : i + j = n) (v : V i) (w : W j) :
    totalTensorInv V W (lof F ℤ (fun n ↦ (V ⊗ W) n) n (ιTensorObj V W i j n h (v ⊗ₜ w))) =
      lof F ℤ (fun i ↦ V i) i v ⊗ₜ lof F ℤ (fun j ↦ W j) j w := by
  rw [totalTensorInv, toModule_lof, ← ConcreteCategory.comp_apply, ι_tensorObjDesc]
  rfl

/-- **The total space of `V ⊗ W` is the tensor product of the total spaces.** -/
def totalTensorEquiv : (⨁ i, V i) ⊗[F] (⨁ j, W j) ≃ₗ[F] ⨁ n, (V ⊗ W) n :=
  LinearEquiv.ofLinearMap (totalTensorHom V W) (totalTensorInv V W)
    (by
      refine linearMap_ext F fun n ↦ ?_
      refine ModuleCat.hom_ext_iff.1 (tensorObj_ext (A := ModuleCat.of F (⨁ n, (V ⊗ W) n))
        (ModuleCat.ofHom ((totalTensorHom V W ∘ₗ totalTensorInv V W) ∘ₗ
          lof F ℤ (fun n ↦ (V ⊗ W) n) n))
        (ModuleCat.ofHom (lof F ℤ (fun n ↦ (V ⊗ W) n) n)) fun i j h ↦
          ModuleCat.hom_ext (TensorProduct.ext' fun v w ↦ ?_))
      subst h
      change totalTensorHom V W (totalTensorInv V W (lof F ℤ (fun n ↦ (V ⊗ W) n) (i + j)
        (ιTensorObj V W i j _ rfl (v ⊗ₜ w)))) = _
      rw [totalTensorInv_ι, totalTensorHom_tmul]
      rfl)
    (by
      refine TensorProduct.ext (linearMap_ext F fun i ↦ LinearMap.ext fun v ↦
        linearMap_ext F fun j ↦ LinearMap.ext fun w ↦ ?_)
      change totalTensorInv V W (totalTensorHom V W
        (lof F ℤ (fun i ↦ V i) i v ⊗ₜ lof F ℤ (fun j ↦ W j) j w)) = _
      rw [totalTensorHom_tmul, totalTensorInv_ι]
      rfl)

/-- `totalTensorEquiv` sends `vᵢ ⊗ wⱼ` to `ι(vᵢ ⊗ wⱼ)` in the summand `(V ⊗ W)^{i+j}`. -/
theorem totalTensorEquiv_tmul (i j : ℤ) (v : V i) (w : W j) :
    totalTensorEquiv V W (lof F ℤ (fun i ↦ V i) i v ⊗ₜ lof F ℤ (fun j ↦ W j) j w) =
      lof F ℤ (fun n ↦ (V ⊗ W) n) (i + j) (ιTensorObj V W i j _ rfl (v ⊗ₜ w)) :=
  totalTensorHom_tmul V W i j v w

end CategoryTheory.GradedObject.Monoidal

end
