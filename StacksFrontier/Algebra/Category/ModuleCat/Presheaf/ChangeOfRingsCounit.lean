module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction

/-!
# The counit of the change-of-rings adjunction for presheaves of modules, on sections

Let `θ : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a category `C`.  Change of
rings along `θ` is left adjoint to restriction of scalars
(`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`, Stacks 03CU).  This file
computes the counit of that adjunction on sections: over an object `X`, the component at `X` of

`(changeOfRingsAdjunction θ).counit.app F : O₂ ⊗_{O₁} F_{O₁} ⟶ F`

sends `a ⊗ x` to `a • x`.

This is the counit counterpart of
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_unit_app_apply`, which computes
the unit on sections as `x ↦ 1 ⊗ x`.

## Main results

* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_counit_app`: the counit at `F`
  is `counitHom θ` applied to the identity of `F_{O₁}`.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_counit_app_app`: its component
  at an object `X` is `counitApp θ` applied to that identity.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_counit_app_apply`: **the counit
  on sections is `a ⊗ x ↦ a • x`.**

## Implementation notes

`changeOfRingsAdjunction` is built by `CategoryTheory.Adjunction.mkOfHomEquiv` from the explicit
hom-set bijection `Stacks.PresheafOfModules.ChangeOfRings.homEquivCore`, whose inverse is
`Stacks.PresheafOfModules.ChangeOfRings.counitHom`.  The counit of an adjunction presented that
way is the inverse bijection applied to an identity, so the first two statements below hold by
`rfl` and the third is `counitApp_tmul` at the identity.  That is the whole reason the adjunction
is a `def` built from an explicit bijection rather than an inhabitant of a `Nonempty` type: a
counit obtained through `Classical.choice` cannot be computed with.

The algebra structure on `O₂.obj X` over `O₁.obj X` is introduced by a `letI` in the statement,
in the style of the unit lemma, because it is not found by instance search: it comes from the
ring homomorphism `θ.app X`.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU), change of rings is left
  adjoint to restriction of scalars for presheaves of modules.
-/

@[expose] public section

open CategoryTheory TensorProduct

namespace Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type*} [Category C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat}

/-- The counit of `changeOfRingsAdjunction θ` at `F` is `counitHom θ` applied to the identity of
`F_{O₁}`.

This holds by `rfl`: the adjunction is built by `CategoryTheory.Adjunction.mkOfHomEquiv` from
`homEquivCore`, whose inverse is `counitHom θ`. -/
theorem changeOfRingsAdjunction_counit_app (θ : O₁ ⟶ O₂) (F : PMod O₂) :
    (changeOfRingsAdjunction θ).counit.app F =
      counitHom θ (𝟙 ((restrictScalars θ).obj F)) :=
  rfl

/-- The component at `X` of the counit of `changeOfRingsAdjunction θ` at `F` is `counitApp`
applied to the identity. -/
theorem changeOfRingsAdjunction_counit_app_app (θ : O₁ ⟶ O₂) (F : PMod O₂) (X : Cᵒᵖ) :
    ((changeOfRingsAdjunction θ).counit.app F).app X =
      counitApp θ (𝟙 ((restrictScalars θ).obj F)) X :=
  rfl

/-- **The counit of the change-of-rings adjunction on sections: `a ⊗ x ↦ a • x`.**

For `F` a presheaf of `O₂`-modules, `X` an object, `a : O₂(X)` and `x : F(X)`, the component at
`X` of `(changeOfRingsAdjunction θ).counit.app F` sends `a ⊗ x` to `a • x`, the action being the
genuine `O₂(X)`-action on `F(X)`. -/
@[simp]
theorem changeOfRingsAdjunction_counit_app_apply (θ : O₁ ⟶ O₂) (F : PMod O₂) (X : Cᵒᵖ)
    (a : O₂.obj X) (x : F.obj X) :
    letI := (θ.app X).hom.toAlgebra
    (((changeOfRingsAdjunction θ).counit.app F).app X).hom (a ⊗ₜ[O₁.obj X] x) = a • x := by
  let := (θ.app X).hom.toAlgebra
  exact counitApp_tmul θ (𝟙 ((restrictScalars θ).obj F)) X a x

end Stacks.PresheafOfModules.ChangeOfRings

end
