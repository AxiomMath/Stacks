module

public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryC.CechCupProduct

/-!
# The universe-independent tensor product of modules is additive in each variable

The bifunctor `Stacks.Cech.CupProduct.tensorModules`, which is `- ⊗_R -` on module categories
with independent universes, is additive in each variable.

## Main results

* `Stacks.Cech.CupProduct.tensorModules_additive`: `- ⊗_R N` is additive.
* `Stacks.Cech.CupProduct.tensorModules_obj_additive`: `M ⊗_R -` is additive.

## References

* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 07MC](https://stacks.math.columbia.edu/tag/07MC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' r

namespace Stacks.Cech.CupProduct

open scoped TensorProduct

variable (R : Type r) [CommRing R]

/-- `- ⊗_R N` is additive: `(f + g) ⊗ 1 = f ⊗ 1 + g ⊗ 1`. -/
instance tensorModules_additive : (tensorModules.{w, w'} R).Additive where
  map_add {M N f g} := by
    ext P : 2
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    simp [tensorModules, TensorProduct.add_tmul]

/-- `M ⊗_R -` is additive: `1 ⊗ (f + g) = 1 ⊗ f + 1 ⊗ g`. -/
instance tensorModules_obj_additive (M : ModuleCat.{w} R) :
    ((tensorModules.{w, w'} R).obj M).Additive where
  map_add {N N' f g} := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    simp [tensorModules, TensorProduct.tmul_add]

end Stacks.Cech.CupProduct

end
