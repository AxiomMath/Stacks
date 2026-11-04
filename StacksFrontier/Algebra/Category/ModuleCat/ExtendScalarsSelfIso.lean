module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsTranspose
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing

/-!
# Extension of scalars takes the regular module to the regular module

Let `g : A →+* A₂` be a homomorphism of commutative rings. Extension of scalars along `g` sends
the regular `A`-module `A` to `A₂ ⊗_A A`, and the transpose of the structure map `A → A₂` under
the extension–restriction adjunction is the canonical `A₂`-linear map `A₂ ⊗_A A ⟶ A₂`. This file
proves that this canonical map is an isomorphism.

## Main definitions

* `ModuleCat.extendScalarsSelfIso`: the isomorphism `A₂ ⊗_A A ≅ A₂` of `A₂`-modules, carried by
  the transpose of the structure map.

## Main results

* `ModuleCat.extendScalarsTranspose_structureHom_eq`: the transpose of the structure map is the
  right unitor `ModuleCat.ExtendScalars.objSelfIso`.
* `ModuleCat.isIso_extendScalarsTranspose_structureHom`: **the canonical map `A₂ ⊗_A A ⟶ A₂` is
  an isomorphism.**

## Implementation notes

The identification is proved by comparing the two morphisms on pure tensors, through
`ModuleCat.ExtendScalars.hom_ext_one_tmul`, rather than by exhibiting a two-sided inverse by
hand. The reason is the `Module A₂` instance on the carrier of
`(ModuleCat.extendScalars g).obj (ModuleCat.of A A)`: it is only definitionally, not
syntactically, the one that `TensorProduct.AlgebraTensorModule.rid` carries, so a map built by
hand out of that carrier is rejected at the transparency the elaborator uses for instance
arguments. Both the extension-side lemma and the unitor are already stated in the spelling the
`ModuleCat.ExtendScalars` namespace uses, which is what keeps this proof short.

## References

* [Stacks Project, Tag 00HL](https://stacks.math.columbia.edu/tag/00HL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace ModuleCat

variable {A A₂ : Type u} [CommRing A] [CommRing A₂] (g : A →+* A₂)

/-- The transpose of the structure map `A → A₂` is the right unitor `A₂ ⊗_A A ≅ A₂`, i.e. the
isomorphism `ModuleCat.ExtendScalars.objSelfIso`. Both morphisms are `A₂`-linear maps out of
`A₂ ⊗_A A`, so they agree as soon as they agree on the pure tensors `1 ⊗ m`, and each sends
`1 ⊗ m` to `g m`: for the transpose this is its defining adjunction property, and for the unitor
it is `ModuleCat.ExtendScalars.objSelfIso_hom_tmul`. -/
theorem extendScalarsTranspose_structureHom_eq :
    extendScalarsTranspose g (structureHom g) = (ExtendScalars.objSelfIso g).hom := by
  refine ExtendScalars.hom_ext_one_tmul g fun m => ?_
  have h := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
    (unit_comp_restrictScalars_map_extendScalarsTranspose g (structureHom g))) m
  rw [ModuleCat.comp_apply, ModuleCat.extendRestrictScalarsAdj_unit_app_apply] at h
  rw [ExtendScalars.objSelfIso_hom_tmul, one_mul]
  exact h

/-- **Extension of scalars carries the regular module to the regular module.** The transpose of
the structure map `A → A₂` is the canonical isomorphism `A₂ ⊗_A A ≅ A₂`. -/
instance isIso_extendScalarsTranspose_structureHom :
    IsIso (extendScalarsTranspose g (structureHom g)) := by
  rw [extendScalarsTranspose_structureHom_eq]
  infer_instance

/-- The isomorphism `A₂ ⊗_A A ≅ A₂` of `A₂`-modules. -/
def extendScalarsSelfIso :
    (ModuleCat.extendScalars.{u, u, u} g).obj (ModuleCat.of A A) ≅ ModuleCat.of A₂ A₂ :=
  asIso (ModuleCat.extendScalarsTranspose g (ModuleCat.structureHom g))

end ModuleCat

end
