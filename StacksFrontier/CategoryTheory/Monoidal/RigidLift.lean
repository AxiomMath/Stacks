module

public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# Lifting morphisms out of a dualizable object along a monoidal functor

Let `F : C ⥤ D` be a monoidal functor and let `Y` be a left dual of `X` in `C`. The bijection
`(I ⊗ X ⟶ Z) ≃ (I ⟶ Z ⊗ Y)` of `CategoryTheory.tensorRightHomEquiv` is compatible with `F`: the
image of the transpose of `c : I ⟶ Z ⊗ Y` is the transpose of `F c`, for the image pairing of
`CategoryTheory.ExactPairing.map`.

Consequently a lifting statement for morphisms out of the unit propagates to morphisms out of
`X`: if every morphism `F 𝟙 ⟶ F W` is, after precomposition with `F b` for some `b : I ⟶ 𝟙`,
the image of a morphism `I ⟶ W`, then every morphism `F X ⟶ F Z` is, after precomposition with
`F (b ▷ X ≫ λ_X)`, the image of a morphism `I ⊗ X ⟶ Z`.

## Main results

* `CategoryTheory.map_tensorRightHomEquiv_symm`: the transpose commutes with `F`.
* `CategoryTheory.exists_map_whiskerRight_leftUnitor_comp_eq_map`: the lifting statement.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- **The transpose across an exact pairing commutes with a monoidal functor.** For a left dual
`Y` of `X` and `c : I ⟶ Z ⊗ Y`, the image under `F` of the transpose `I ⊗ X ⟶ Z` of `c` is the
transpose of `F c ≫ δ`, for the image pairing, precomposed with `δ`. -/
theorem map_tensorRightHomEquiv_symm (F : C ⥤ D) [F.Monoidal] (I X Y Z : C) [ExactPairing X Y]
    (c : I ⟶ Z ⊗ Y) :
    letI := ExactPairing.map F X Y
    F.map ((tensorRightHomEquiv I X Y Z).symm c) =
      δ F I X ≫ (tensorRightHomEquiv (F.obj I) (F.obj X) (F.obj Y) (F.obj Z)).symm
        (F.map c ≫ δ F Z Y) := by
  let := ExactPairing.map F X Y
  simp only [tensorRightHomEquiv, Equiv.coe_fn_symm_mk, Functor.map_comp,
    ExactPairing.map_evaluation]
  rw [Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_rightUnitor]
  simp [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]

/-- **Lifting a morphism out of a dualizable object.** Let `F : C ⥤ D` be a monoidal functor,
`Y` a left dual of `X` and `Z` an object of `C`. Suppose the morphism
`η ≫ (λ ≫ α)ᵗ ≫ μ : F 𝟙 ⟶ F (Z ⊗ Y)` is, after precomposition with `F b` for a morphism
`b : I ⟶ 𝟙` satisfying `P`, the image of a morphism `I ⟶ Z ⊗ Y`. Then `F (b ▷ X ≫ λ_X) ≫ α`
is the image of a morphism `I ⊗ X ⟶ Z`, for the same kind of `b`. -/
theorem exists_map_whiskerRight_leftUnitor_comp_eq_map (F : C ⥤ D) [F.Monoidal] (X Y Z : C)
    [ExactPairing X Y] (P : ∀ I : C, (I ⟶ 𝟙_ C) → Prop) (α : F.obj X ⟶ F.obj Z)
    (hlift : ∀ a : F.obj (𝟙_ C) ⟶ F.obj (Z ⊗ Y), ∃ (I : C) (b : I ⟶ 𝟙_ C) (c : I ⟶ Z ⊗ Y),
      P I b ∧ F.map b ≫ a = F.map c) :
    ∃ (I : C) (b : I ⟶ 𝟙_ C) (γ : I ⊗ X ⟶ Z),
      P I b ∧ F.map (b ▷ X ≫ (λ_ X).hom) ≫ α = F.map γ := by
  let := ExactPairing.map F X Y
  obtain ⟨I, b, c, hP, hc⟩ := hlift (η F ≫ tensorRightHomEquiv _ (F.obj X) (F.obj Y) (F.obj Z)
    ((λ_ (F.obj X)).hom ≫ α) ≫ μ F Z Y)
  refine ⟨I, b, (tensorRightHomEquiv I X Y Z).symm c, hP, ?_⟩
  rw [map_tensorRightHomEquiv_symm, ← hc]
  simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  rw [← Category.assoc (F.map b), tensorRightHomEquiv_symm_naturality,
    Equiv.symm_apply_apply, Functor.map_comp, Functor.Monoidal.map_whiskerRight,
    Functor.Monoidal.map_leftUnitor]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc, comp_whiskerRight]

/-- **Composing monoidal functors across two monoidal structures on one type.** The composite of
a monoidal functor `(C, M₁) ⥤ (D, M₂)` and a monoidal functor `(D, M₂) ⥤ (E, M₃)` is monoidal
`(C, M₁) ⥤ (E, M₃)`. -/
@[instance_reducible]
def Functor.monoidalCompOf {C' D' E' : Type*} [Category C'] [Category D'] [Category E']
    (M₁ : MonoidalCategory C') (M₂ : MonoidalCategory D') (M₃ : MonoidalCategory E')
    (F : C' ⥤ D') (G : D' ⥤ E') (hF : @Functor.Monoidal C' _ M₁ D' _ M₂ F)
    (hG : @Functor.Monoidal D' _ M₂ E' _ M₃ G) : @Functor.Monoidal C' _ M₁ E' _ M₃ (F ⋙ G) :=
  letI := M₁; letI := M₂; letI := M₃; letI := hF; letI := hG; inferInstance

end CategoryTheory

end
