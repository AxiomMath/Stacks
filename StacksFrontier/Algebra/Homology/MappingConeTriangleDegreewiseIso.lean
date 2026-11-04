module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import StacksFrontier.Algebra.Homology.MappingConeDegreewiseIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The connecting morphism of the cone triangle in a degree where the target vanishes

Let `φ : F ⟶ G` be a morphism of cochain complexes. If `G^p` is a zero object then the
degree-`p` component of the connecting morphism `mappingCone φ ⟶ F⟦1⟧` of the cone triangle is an
isomorphism, being, up to sign and the identification of `(F⟦1⟧)^p` with `F^{p+1}`, the inverse
of the degree-`(p+1, p)` component of `mappingCone.inl φ`, which is an isomorphism there by
`CochainComplex.mappingCone.isIso_inl_v`.

## Main results

* `CochainComplex.mappingCone.isIso_triangle_mor₃_f`: the connecting morphism of the cone
  triangle in a degree where the target of `φ` contributes nothing.

## Implementation notes

The statement is about `CochainComplex.mappingCone.triangle`, which lives in
`Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`; it is kept apart from
`StacksFrontier.Algebra.Homology.MappingConeDegreewiseIso` so that that file keeps its smaller
import closure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] {F G : CochainComplex C ℤ} (φ : F ⟶ G)
  [HasHomotopyCofiber φ]

/-- **In a degree where the target of `φ` contributes nothing, the connecting morphism of the
cone triangle is an isomorphism.** If `G^p` is a zero object then the degree-`p` component of
`(mappingCone.triangle φ).mor₃` is an isomorphism: composed with the degree-`(p+1, p)` component
of `mappingCone.inl φ`, which is an isomorphism there, it is minus the identification of
`(F⟦1⟧)^p` with `F^{p+1}`. -/
@[sga "4 XVII 1.1.1" "Clause"]
theorem isIso_triangle_mor₃_f [HasBinaryBiproducts C] (p : ℤ) (hp : IsZero (G.X p)) :
    IsIso ((triangle φ).mor₃.f p) := by
  obtain ⟨u, hu⟩ : ∃ u : F.X (p + 1) ⟶ (mappingCone φ).X p,
      u = (inl φ).v (p + 1) p (by omega) := ⟨_, rfl⟩
  have h₁ : IsIso u := by rw [hu]; exact isIso_inl_v φ (p + 1) p (by omega) hp
  have hneg : IsIso (-(F.shiftFunctorObjXIso 1 p (p + 1) (by omega)).inv) := by
    refine ⟨-(F.shiftFunctorObjXIso 1 p (p + 1) (by omega)).hom, ?_, ?_⟩
    · rw [Preadditive.neg_comp_neg]
      exact (F.shiftFunctorObjXIso 1 p (p + 1) (by omega)).inv_hom_id
    · rw [Preadditive.neg_comp_neg]
      exact (F.shiftFunctorObjXIso 1 p (p + 1) (by omega)).hom_inv_id
  have h₂ : IsIso (u ≫ (triangle φ).mor₃.f p) := by
    rw [hu, inl_v_triangle_mor₃_f φ (p + 1) p (by omega)]
    exact hneg
  exact IsIso.of_isIso_comp_left u _

end CochainComplex.mappingCone

end
