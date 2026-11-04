module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.HigherDirectImageSliceAction

/-!
# The étale-local action of `R^q g_* ∘ g⁻¹` is functorial

The action of `R^q g_* ∘ g⁻¹` on a morphism `α : A|_V ⟶ K|_V` between restrictions of abelian
sheaves to the slice over an étale `V ⟶ U`
(`Stacks.EtaleCohomology.higherDirectImageInverseImageSliceHom`) respects composition of local
morphisms, not only composition with morphisms coming from `U`: the transport of local morphisms
to inverse images along `V ⟶ U` and the action on such morphisms are both functorial.

## Main results

* `Stacks.EtaleCohomology.higherDirectImageInverseImageSliceHom_comp`.
* `Stacks.EtaleCohomology.higherDirectImageInverseImageSectionMap_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe u

namespace Stacks.EtaleCohomology

variable {X U : Scheme.{u}} (g : X ⟶ U) (q : ℕ) {A K L : Sheaf (smallEtaleTopology U) Ab.{u + 1}}
  (V : U.Etale)

/-- **The action on local morphisms, read on `V_étale`, respects composition.** -/
theorem higherDirectImageInverseImageSliceMap_comp
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K)
    (β : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj L) :
    higherDirectImageInverseImageSliceMap g q V (α ≫ β) =
      higherDirectImageInverseImageSliceMap g q V α ≫
        higherDirectImageInverseImageSliceMap g q V β := by
  rw [higherDirectImageInverseImageSliceMap, higherDirectImageInverseImageSliceMap,
    higherDirectImageInverseImageSliceMap, pullbackSliceHom_comp,
    higherDirectImageInverseImageLocalMap_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- **The action on local morphisms respects composition.** -/
theorem higherDirectImageInverseImageSliceHom_comp
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K)
    (β : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj L) :
    higherDirectImageInverseImageSliceHom g q V (α ≫ β) =
      higherDirectImageInverseImageSliceHom g q V α ≫
        higherDirectImageInverseImageSliceHom g q V β := by
  apply sliceToRestriction_injective V
  rw [sliceToRestriction_higherDirectImageInverseImageSliceHom, sliceToRestriction_comp,
    sliceToRestriction_higherDirectImageInverseImageSliceHom,
    sliceToRestriction_higherDirectImageInverseImageSliceHom,
    higherDirectImageInverseImageSliceMap_comp]

/-- **The action on sections over `V` respects composition of local morphisms.** -/
theorem higherDirectImageInverseImageSectionMap_comp
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K)
    (β : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj L) :
    higherDirectImageInverseImageSectionMap g q V (α ≫ β) =
      higherDirectImageInverseImageSectionMap g q V α ≫
        higherDirectImageInverseImageSectionMap g q V β := by
  rw [higherDirectImageInverseImageSectionMap, higherDirectImageInverseImageSliceHom_comp]
  rfl

end Stacks.EtaleCohomology

end
