module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transposes of the left-adjoint transports of identifications of right adjoints

For an adjunction `F ⊣ G` and an identification `e : G ≅ 𝟭`, the induced identification
`CategoryTheory.Adjunction.leftAdjointIdIso` of `F` with the identity transposes to the inverse of
`e`; for three adjunctions and an identification `e : G₂₁ ⋙ G₁₀ ≅ G₂₀` of right adjoints, the
transpose of a composite of two left-adjoint arrows compared by
`CategoryTheory.Adjunction.leftAdjointCompIso` is the composite of the two transposes compared by
`e`.

## Main results

* `CategoryTheory.Adjunction.homEquiv_leftAdjointIdIso_hom_app`
* `CategoryTheory.Adjunction.homEquiv_leftAdjointCompIso_inv_app`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

/-- **The adjoint transpose of the unit law of a left adjoint.**  If a right adjoint `G` is
identified with the identity functor by `e`, then the induced identification
`CategoryTheory.Adjunction.leftAdjointIdIso` of the left adjoint transposes, componentwise, to the
inverse of `e`. -/
theorem homEquiv_leftAdjointIdIso_hom_app {C₀ : Type*} [Category C₀] {F G : C₀ ⥤ C₀}
    (adj : F ⊣ G) (e : G ≅ 𝟭 C₀) (A : C₀) :
    adj.homEquiv A A ((Adjunction.leftAdjointIdIso adj e).hom.app A) = e.inv.app A := by
  rw [adj.homEquiv_unit, ← Adjunction.conjugateEquiv_leftAdjointIdIso_hom adj e]
  exact (unit_conjugateEquiv Adjunction.id adj _ A).symm.trans (Category.id_comp _)

/-- The transpose of a composite of two left-adjoint arrows, compared by the left-adjoint
transport of an isomorphism of right adjoints, is the composite of the two transposes, compared
by that isomorphism. -/
@[ega "0 4.4.8" "more general"]
theorem homEquiv_leftAdjointCompIso_inv_app {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀) (e : G₂₁ ⋙ G₁₀ ≅ G₂₀)
    {X : C₀} {Y : C₁} {Z : C₂} (a : F₀₁.obj X ⟶ Y) (b : F₁₂.obj Y ⟶ Z) :
    adj₀₂.homEquiv X Z ((leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).inv.app X ≫ F₁₂.map a ≫ b) =
      adj₀₁.homEquiv X Y a ≫ G₁₀.map (adj₁₂.homEquiv Y Z b) ≫ e.hom.app Z := by
  have hunit := unit_conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂
    (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).inv X
  rw [conjugateEquiv_leftAdjointCompIso_inv] at hunit
  have hkey : (adj₀₁.comp adj₁₂).homEquiv X Z (F₁₂.map a ≫ b) =
      adj₀₁.homEquiv X Y a ≫ G₁₀.map (adj₁₂.homEquiv Y Z b) := by
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← reassoc_of% hunit, ← e.hom.naturality _]
  rw [Adjunction.homEquiv_unit] at hkey
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ e.hom.app Z) hkey).trans (Category.assoc _ _ _))

end CategoryTheory.Adjunction

end
