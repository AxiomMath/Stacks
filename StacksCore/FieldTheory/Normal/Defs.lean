module

public import Mathlib.FieldTheory.Normal.Defs

/-! # Normal extensions -/

@[expose] public section

/-- The underlying function of `AlgEquiv.restrictNormalHom` is `σ ↦ σ.restrictNormal E`. -/
@[simp] theorem AlgEquiv.coe_restrictNormalHom (F E K₁ : Type*) [Field F] [Field K₁] [Field E]
    [Algebra F K₁] [Algebra F E] [Algebra E K₁] [IsScalarTower F E K₁] [Normal F E] :
    ⇑(AlgEquiv.restrictNormalHom (F := F) (K₁ := K₁) E) = (restrictNormal · E) := rfl
