module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.HomCongr
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectDual
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleTransport

/-!
# Objects by which whiskering is bijective

An object `Z` of a monoidal category is *right cancellable* when `f ↦ f ▷ Z` is a bijection
`(A ⟶ B) ≃ (A ⊗ Z ⟶ B ⊗ Z)` for all `A`, `B`, and *left cancellable* when `f ↦ Z ◁ f` is.
Both classes contain the unit and the invertible objects and are closed under tensor products
and isomorphisms. Left cancellability is reflected by fully faithful monoidal functors. The
invertible objects are closed under tensor products, and preserved by monoidal functors.

## Main definitions

* `CategoryTheory.InvertingObject.RightCancel`, `CategoryTheory.InvertingObject.LeftCancel`.
* `CategoryTheory.MonoidalCategory.HasInverse.tensor`: the inverse `Y⁻¹ ⊗ X⁻¹` of `X ⊗ Y`.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

namespace MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- The two-sided tensor inverse `Y⁻¹ ⊗ X⁻¹` of `X ⊗ Y`. -/
def HasInverse.tensor {X Y : C} (hX : HasInverse X) (hY : HasInverse Y) : HasInverse (X ⊗ Y) where
  inv := hY.inv ⊗ hX.inv
  isoLeft := α_ X Y _ ≪≫ whiskerLeftIso X (α_ Y hY.inv hX.inv).symm ≪≫
    whiskerLeftIso X (whiskerRightIso hY.isoLeft _ ≪≫ λ_ _) ≪≫ hX.isoLeft
  isoRight := α_ hY.inv hX.inv (X ⊗ Y) ≪≫ whiskerLeftIso _ (α_ hX.inv X Y).symm ≪≫
    whiskerLeftIso _ (whiskerRightIso hX.isoRight Y ≪≫ λ_ Y) ≪≫ hY.isoRight

/-- The tensor product of two invertible objects is invertible. -/
theorem IsInvertible.tensor {X Y : C} (hX : IsInvertible X) (hY : IsInvertible Y) :
    IsInvertible (X ⊗ Y) :=
  let ⟨hX⟩ := hX
  let ⟨hY⟩ := hY
  ⟨hX.tensor hY⟩

variable {D : Type*} [Category D] [MonoidalCategory D]

/-- For a monoidal functor `Ψ`, if `Ψ.obj X` and `Ψ.obj Y` are invertible, then so is
`Ψ.obj (X ⊗ Y)`. -/
theorem IsInvertible.map_tensor (Ψ : C ⥤ D) [Ψ.Monoidal] {X Y : C} (hX : IsInvertible (Ψ.obj X))
    (hY : IsInvertible (Ψ.obj Y)) : IsInvertible (Ψ.obj (X ⊗ Y)) :=
  isInvertible_of_iso (μIso Ψ X Y) (hX.tensor hY)

/-- A monoidal functor sends the unit object to an invertible object. -/
theorem isInvertible_map_tensorUnit (Ψ : C ⥤ D) [Ψ.Monoidal] : IsInvertible (Ψ.obj (𝟙_ C)) :=
  isInvertible_of_iso (εIso Ψ) isInvertible_unit

end MonoidalCategory

namespace InvertingObject

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- `f ↦ f ▷ Z` is bijective on all hom-sets. -/
def RightCancel (Z : C) : Prop :=
  ∀ ⦃A B : C⦄, Function.Bijective (fun f : A ⟶ B => f ▷ Z)

/-- `f ↦ Z ◁ f` is bijective on all hom-sets. -/
def LeftCancel (Z : C) : Prop :=
  ∀ ⦃A B : C⦄, Function.Bijective (fun f : A ⟶ B => Z ◁ f)

/-- A map that is pointwise an equivalence applied to a bijection is bijective. -/
private theorem bijective_of_eq_equiv_apply {α β γ : Sort*} {F : α → γ} {G : α → β} (e : β ≃ γ)
    (hG : Function.Bijective G) (h : ∀ x, F x = e (G x)) : Function.Bijective F :=
  (funext h : F = e ∘ G) ▸ e.bijective.comp hG

/-- The unit object is right cancellable. -/
theorem rightCancel_unit : RightCancel (𝟙_ C) := fun A B =>
  bijective_of_eq_equiv_apply ((ρ_ A).symm.homCongr (ρ_ B).symm) Function.bijective_id
    fun f => by simp [whiskerRight_id]

/-- The unit object is left cancellable. -/
theorem leftCancel_unit : LeftCancel (𝟙_ C) := fun A B =>
  bijective_of_eq_equiv_apply ((λ_ A).symm.homCongr (λ_ B).symm) Function.bijective_id
    fun f => by simp [id_whiskerLeft]

/-- The tensor product of two right cancellable objects is right cancellable. -/
theorem RightCancel.tensor {Z W : C} (hZ : RightCancel Z) (hW : RightCancel W) :
    RightCancel (Z ⊗ W) := fun A B =>
  bijective_of_eq_equiv_apply ((α_ A Z W).homCongr (α_ B Z W))
    ((hW (A := A ⊗ Z) (B := B ⊗ Z)).comp (hZ (A := A) (B := B)))
    fun f => by simp [whiskerRight_tensor]

/-- The tensor product of two left cancellable objects is left cancellable. -/
theorem LeftCancel.tensor {Z W : C} (hZ : LeftCancel Z) (hW : LeftCancel W) :
    LeftCancel (Z ⊗ W) := fun A B =>
  bijective_of_eq_equiv_apply ((α_ Z W A).symm.homCongr (α_ Z W B).symm)
    ((hZ (A := W ⊗ A) (B := W ⊗ B)).comp (hW (A := A) (B := B)))
    fun f => by simp [tensor_whiskerLeft]

/-- An object isomorphic to a right cancellable object is right cancellable. -/
theorem RightCancel.of_iso {Z Z' : C} (hZ : RightCancel Z) (e : Z ≅ Z') : RightCancel Z' :=
  fun A B =>
  bijective_of_eq_equiv_apply ((whiskerLeftIso A e).homCongr (whiskerLeftIso B e))
    (hZ (A := A) (B := B)) fun f => by
    simp only [Iso.homCongr_apply, whiskerLeftIso_inv, whiskerLeftIso_hom]
    rw [whisker_exchange_assoc, ← whiskerLeft_comp, e.inv_hom_id, whiskerLeft_id,
      Category.comp_id]

/-- An object isomorphic to a left cancellable object is left cancellable. -/
theorem LeftCancel.of_iso {Z Z' : C} (hZ : LeftCancel Z) (e : Z ≅ Z') : LeftCancel Z' :=
  fun A B =>
  bijective_of_eq_equiv_apply ((whiskerRightIso e A).homCongr (whiskerRightIso e B))
    (hZ (A := A) (B := B)) fun f => by
    simp only [Iso.homCongr_apply, whiskerRightIso_inv, whiskerRightIso_hom]
    rw [← whisker_exchange_assoc, ← comp_whiskerRight, e.inv_hom_id, id_whiskerRight,
      Category.comp_id]

/-- An object with a tensor inverse is right cancellable. -/
theorem rightCancel_of_hasInverse {Z : C} (h : HasInverse Z) : RightCancel Z := fun A B =>
  h.tensorRightEquivalence.fullyFaithfulFunctor.map_bijective A B

/-- An object with a tensor inverse is left cancellable. -/
theorem leftCancel_of_hasInverse {Z : C} (h : HasInverse Z) : LeftCancel Z := fun A B =>
  h.tensorLeftEquivalence.fullyFaithfulFunctor.map_bijective A B

/-- An invertible object is right cancellable. -/
theorem IsInvertible.rightCancel {Z : C} (h : IsInvertible Z) : RightCancel Z :=
  let ⟨h⟩ := h
  rightCancel_of_hasInverse h

/-- An invertible object is left cancellable. -/
theorem IsInvertible.leftCancel {Z : C} (h : IsInvertible Z) : LeftCancel Z :=
  let ⟨h⟩ := h
  leftCancel_of_hasInverse h

variable {D : Type*} [Category D] [MonoidalCategory D]

/-- A fully faithful monoidal functor reflects left cancellability. -/
theorem LeftCancel.of_map (K : C ⥤ D) [K.Monoidal] (hK : K.FullyFaithful) {P : C}
    (h : LeftCancel (K.obj P)) : LeftCancel P := fun A B => by
  refine (Function.Bijective.of_comp_iff' (hK.map_bijective _ _) _).1
    (bijective_of_eq_equiv_apply ((μIso K P A).homCongr (μIso K P B))
      (h.comp (hK.map_bijective A B)) fun f => ?_)
  simp only [Function.comp_apply, Iso.homCongr_apply, μIso_inv, μIso_hom]
  exact map_whiskerLeft K P f

end InvertingObject

end CategoryTheory
