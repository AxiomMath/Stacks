module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The hom-bijection of a composite adjunction transported on both sides

Let `adj₁ : F ⊣ G` with `F : C ⥤ D`, `G : D ⥤ C` and `adj₂ : H ⊣ I` with `H : D ⥤ E`,
`I : E ⥤ D`. Composing them gives `F ⋙ H ⊣ I ⋙ G`, and if `F ⋙ H` is identified with some
`T : C ⥤ E` and `I ⋙ G` with some `R : E ⥤ C`, transporting along those two identifications
gives `T ⊣ R`.

The hom-bijection of the transported composite is the two hom-bijections applied in turn,
conjugated by the two identifications.

## Main results

* `CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_ofNatIsoRight_comp`: the hom-bijection of
  the transported composite adjunction, in the forward direction.
* `CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_ofNatIsoRight_comp_symm`: the same in the
  inverse direction.
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D} {T : C ⥤ E} {R : E ⥤ C}

/-- **The pasting law for the hom-bijection of a transported composite adjunction.** For
`adj₁ : F ⊣ G`, `adj₂ : H ⊣ I`, an identification `eL : F ⋙ H ≅ T` of the composite left
adjoint and an identification `eR : I ⋙ G ≅ R` of the composite right adjoint, the
hom-bijection of the resulting adjunction `T ⊣ R` sends `f : T A ⟶ B` to the transpose under
`adj₁` of the transpose under `adj₂` of `eL ≫ f`, followed by `eR`. -/
theorem homEquiv_ofNatIsoLeft_ofNatIsoRight_comp (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)
    (eL : F ⋙ H ≅ T) (eR : I ⋙ G ≅ R) (A : C) (B : E) (f : T.obj A ⟶ B) :
    (ofNatIsoLeft (ofNatIsoRight (adj₁.comp adj₂) eR) eL).homEquiv A B f =
      adj₁.homEquiv _ _ (adj₂.homEquiv _ _ (eL.hom.app A ≫ f)) ≫ eR.hom.app B := by
  rw [homEquiv_ofNatIsoLeft_apply, homEquiv_ofNatIsoRight_apply, comp_homEquiv]
  rfl

/-- **The pasting law of `homEquiv_ofNatIsoLeft_ofNatIsoRight_comp`, read in the inverse
direction.** The inverse hom-bijection sends `g : A ⟶ R B` to the inverse of `eL` followed by the
inverse transpose under `adj₂` of the inverse transpose under `adj₁` of `g` followed by the
inverse of `eR`. -/
theorem homEquiv_ofNatIsoLeft_ofNatIsoRight_comp_symm (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)
    (eL : F ⋙ H ≅ T) (eR : I ⋙ G ≅ R) (A : C) (B : E) (g : A ⟶ R.obj B) :
    ((ofNatIsoLeft (ofNatIsoRight (adj₁.comp adj₂) eR) eL).homEquiv A B).symm g =
      eL.inv.app A ≫ (adj₂.homEquiv _ _).symm
        ((adj₁.homEquiv _ _).symm (g ≫ eR.inv.app B)) := by
  rw [Equiv.symm_apply_eq, homEquiv_ofNatIsoLeft_ofNatIsoRight_comp]
  simp

end CategoryTheory.Adjunction

end
