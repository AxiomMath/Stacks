module

public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Uniqueness of left adjoints along an isomorphism of right adjoints

Declarations extending `StacksFrontier.CategoryTheory.Adjunction.UniqueComp`
(`leftAdjointUniq_symm_trans_leftAdjointUniq_ofNatIsoRight`), kept in their own module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]

end CategoryTheory.Adjunction

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {CX : Type u₁} [Category.{v₁} CX] {DX : Type u₂} [Category.{v₂} DX]
  {CY : Type u₃} [Category.{v₃} CY] {DY : Type u₄} [Category.{v₄} DY]

end CategoryTheory

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {Fc Ft : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {Gc Gt : C₂ ⥤ C₀}

/-- **A comparison of left adjoints through an intermediate adjunction.**  Let `Fc ⊣ Gc` and
`Ft ⊣ Gt` be adjunctions with `PC : Gc ≅ G₂₁ ⋙ G₁₀` and `T : Gc ≅ Gt`.  Comparing
`F₀₁ ⋙ F₁₂` with `Fc` by uniqueness of a left adjoint of `Gc` (through `PC`), and then `Fc` with
`Ft` by uniqueness of a left adjoint of `Gc` (through `T`), gives the comparison induced by
`PC.symm ≪≫ T`. -/
theorem leftAdjointUniq_symm_trans_leftAdjointUniq_ofNatIsoRight (adj₀₁ : F₀₁ ⊣ G₁₀)
    (adj₁₂ : F₁₂ ⊣ G₂₁) (adjc : Fc ⊣ Gc) (adjt : Ft ⊣ Gt) (PC : Gc ≅ G₂₁ ⋙ G₁₀)
    (T : Gc ≅ Gt) :
    ((adjc.ofNatIsoRight PC).leftAdjointUniq (adj₀₁.comp adj₁₂)).symm ≪≫
        adjc.leftAdjointUniq (adjt.ofNatIsoRight T.symm) =
      leftAdjointCompIso adj₀₁ adj₁₂ adjt (PC.symm ≪≫ T) := by
  refine Iso.ext ((conjugateEquiv adjt (adj₀₁.comp adj₁₂)).injective ?_)
  rw [Iso.trans_hom, Iso.symm_hom, ← conjugateEquiv_comp adjt adjc (adj₀₁.comp adj₁₂)]
  have key : ∀ {L₁ L₂ : C₀ ⥤ C₂} {R₁ R₂ : C₂ ⥤ C₀} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₂)
      (f : R₁ ≅ R₂), conjugateEquiv b a e.hom = f.inv → conjugateEquiv a b e.inv = f.hom := by
    intro L₁ L₂ R₁ R₂ a b e f hf
    have h := conjugateEquiv_comm (adj₁ := b) (adj₂ := a) (α := e.hom) (β := e.inv)
      (Iso.inv_hom_id _)
    rwa [hf, Iso.inv_comp_eq_id] at h
  have hi : (adjc.leftAdjointUniq (adjt.ofNatIsoRight T.symm)).hom =
      ((adjt.ofNatIsoRight T.symm).leftAdjointUniq adjc).inv := by
    ext K
    exact (leftAdjointUniq_inv_app _ _ K).symm
  rw [key adjc (adj₀₁.comp adj₁₂) _ PC
      (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _), hi,
    key adjt adjc _ T.symm
      (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _)]
  simp [leftAdjointCompIso]

end CategoryTheory.Adjunction

end
