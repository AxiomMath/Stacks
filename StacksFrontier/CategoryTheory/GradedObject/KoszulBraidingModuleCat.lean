module

public import StacksFrontier.CategoryTheory.GradedObject.KoszulBraiding
public import StacksCore.CategoryTheory.GradedObject.GradedVectorSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# The Koszul-signed symmetric monoidal category of graded vector spaces

Stacks 0FFX equips the category of graded `F`-vector spaces with the degreewise tensor product
`(V ⊗ W)ⁿ = ⨁_{n = p + q} Vᵖ ⊗_F W^q`, and says there are two commutativity constraints making it
symmetric monoidal: "one involves the intervention of signs and the other does not. We will
usually use the one that does", namely `ψ : V ⊗ W → W ⊗ V`, `v ⊗ w ↦ (-1)^{pq} w ⊗ v` on
`Vᵖ ⊗_F W^q`.

The signed constraint on `ℤ`-graded objects of a preadditive symmetric monoidal category, with the
verification of the hexagon and symmetry axioms that the source omits, is
`CategoryTheory.GradedObject.koszulSymmetricCategory`
(`StacksFrontier.CategoryTheory.GradedObject.KoszulBraiding`). This file specialises it to graded
`F`-vector spaces and computes the constraint on elements.

## Main definitions

* `CategoryTheory.GradedObject.koszulSymmetricCategoryModuleCat`: the symmetric monoidal category
  of graded `F`-vector spaces of Stacks 0FFX, with the signed constraint.

## Main results

* `CategoryTheory.GradedObject.koszulBraiding_hom_apply_tmul`: the Koszul braiding sends
  `v ⊗ w ∈ Vᵖ ⊗_F W^q` to `(-1)^{pq} w ⊗ v`.
* `CategoryTheory.GradedObject.koszulSymmetricCategoryModuleCat_braiding_hom_apply_tmul`: the
  commutativity constraint of `koszulSymmetricCategoryModuleCat` is `v ⊗ w ↦ (-1)^{pq} w ⊗ v`.

## Implementation notes

The signed structure is a definition, not an instance, because Mathlib's sign-free
`GradedObject.symmetricCategory` is already an instance on the same type. A user activates the
signed structure with `letI`.

## References

* [Stacks Project, Tag 0FFX](https://stacks.math.columbia.edu/tag/0FFX)
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

namespace GradedObject

variable (F : Type*) [Field F]

/-- **Stacks Project, Tag 0FFX.** The category of `ℤ`-graded `F`-vector spaces is symmetric
monoidal with the degreewise tensor product, the usual associativity constraint, the unit `F`
in degree `0`, and the commutativity constraint with signs, `v ⊗ w ↦ (-1)^{pq} w ⊗ v` on
`Vᵖ ⊗_F W^q`. This is the constraint the tag says it will usually use. -/
@[stacks 0FFX "graded F-vector spaces are symmetric monoidal with the Koszul-signed commutativity \
constraint, the one the tag says it will usually use", instance_reducible]
noncomputable def koszulSymmetricCategoryModuleCat :
    SymmetricCategory (GradedObject ℤ (ModuleCat F)) :=
  koszulSymmetricCategory

variable {F}

/-- The commutativity constraint of `koszulSymmetricCategoryModuleCat` is `koszulBraiding`. -/
theorem koszulSymmetricCategoryModuleCat_braiding (V W : GradedObject ℤ (ModuleCat F)) :
    @BraidedCategory.braiding _ _ _ (koszulSymmetricCategoryModuleCat F).toBraidedCategory V W =
      Monoidal.koszulBraiding V W :=
  rfl

/-- The elementwise formula for `Monoidal.koszulBraiding` on graded `F`-vector spaces. -/
theorem koszulBraiding_hom_apply_tmul (V W : GradedObject ℤ (ModuleCat F)) (p q n : ℤ)
    (h : p + q = n) (v : V p) (w : W q) :
    ((Monoidal.koszulBraiding V W).hom n).hom
        ((Monoidal.ιTensorObj V W p q n h).hom (v ⊗ₜ[F] w)) =
      ((p * q).negOnePow : ℤ) • (Monoidal.ιTensorObj W V q p n (by omega)).hom (w ⊗ₜ[F] v) := by
  have := congrArg (fun φ => φ.hom (v ⊗ₜ[F] w)) (Monoidal.ι_koszulBraiding_hom V W p q n h)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, Units.smul_def,
    ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.MonoidalCategory.braiding_hom_apply]
    at this
  exact this

/-- **Stacks Project, Tag 0FFX.** The commutativity constraint `ψ : V ⊗ W → W ⊗ V` of the
Koszul-signed symmetric monoidal category of graded `F`-vector spaces sends
`v ⊗ w ∈ Vᵖ ⊗_F W^q` to `(-1)^{pq} w ⊗ v`. -/
@[stacks 0FFX "the signed commutativity constraint is v ⊗ w ↦ (-1)^{pq} w ⊗ v on V^p ⊗ W^q"]
theorem koszulSymmetricCategoryModuleCat_braiding_hom_apply_tmul
    (V W : GradedObject ℤ (ModuleCat F)) (p q n : ℤ) (h : p + q = n) (v : V p) (w : W q) :
    ((@BraidedCategory.braiding _ _ _ (koszulSymmetricCategoryModuleCat F).toBraidedCategory
        V W).hom n).hom ((Monoidal.ιTensorObj V W p q n h).hom (v ⊗ₜ[F] w)) =
      ((p * q).negOnePow : ℤ) • (Monoidal.ιTensorObj W V q p n (by omega)).hom (w ⊗ₜ[F] v) := by
  rw [koszulSymmetricCategoryModuleCat_braiding]
  exact koszulBraiding_hom_apply_tmul V W p q n h v w

end GradedObject

end CategoryTheory
