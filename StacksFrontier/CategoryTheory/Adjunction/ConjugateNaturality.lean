module

public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Conjugate transformations: a recognition criterion, and naturality of `leftAdjointUniq`

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be two adjunctions between the same pair of categories.
`CategoryTheory.conjugateEquiv` turns a transformation `L₂ ⟶ L₁` of the left adjoints into one
`R₁ ⟶ R₂` of the right adjoints. This file records three facts about that bijection.

First, a conjugate is recognized by what it does to the two hom-set bijections: `β` is the
conjugate of `τ` exactly when transposing `τ.app X ≫ b` along the second adjunction is
transposing `b` along the first and then appending `β`.

Second, changing the right adjoints of both adjunctions along isomorphisms conjugates by those
isomorphisms.

Third, uniqueness of a left adjoint is natural in a parameter: given two families of
adjunctions with a common right adjoint at each index, the comparison isomorphisms of the left
adjoints commute with any pair of transformations whose conjugates agree. This is the step that
upgrades an isomorphism obtained from uniqueness of left adjoints at each value of a parameter
to an isomorphism of functors in that parameter.

Fourth, the dual of the third: uniqueness of a *right* adjoint is natural, with no hypothesis at
all. Given `L₁ ⊣ R₁`, `L₁ ⊣ R₁'`, `L₂ ⊣ R₂` and `L₂ ⊣ R₂'` and a transformation `α : L₂ ⟶ L₁`,
the conjugates of `α` for the two pairs of adjunctions commute with the two comparisons of right
adjoints. Unlike the left-adjoint statement this needs no compatibility hypothesis, because here
the two left adjoints are literally the same functor and the transformation between them is
literally the same transformation: the square is two instances of
`CategoryTheory.conjugateEquiv_comp` at an identity.

## Main results

* `Stacks.CategoryTheory.conjugateEquiv_eq_of_homEquiv`: the recognition criterion.
* `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight`: conjugation after changing the right
  adjoints along isomorphisms.
* `Stacks.CategoryTheory.leftAdjointUniq_naturality` and
  `Stacks.CategoryTheory.leftAdjointUniq_naturality_of_eq`: naturality of the comparison of two
  left adjoints, the second with the comparison isomorphisms supplied by equations so that no
  unfolding is needed at the point of use.
* `Stacks.CategoryTheory.rightAdjointUniq_naturality` and
  `Stacks.CategoryTheory.rightAdjointUniq_naturality_of_eq`: naturality of the comparison of two
  right adjoints, again with a variant taking the comparisons as equations.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The component of a conjugate transformation, written through the hom-set bijection: it is
the adjunct of the given transformation followed by the counit. -/
theorem conjugateEquiv_app_eq {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (τ : L₂ ⟶ L₁) (Y : D) :
    (conjugateEquiv adj₁ adj₂ τ).app Y =
      adj₂.homEquiv (R₁.obj Y) Y (τ.app (R₁.obj Y) ≫ adj₁.counit.app Y) := by
  simp [Adjunction.homEquiv_apply]

/-- A conjugate transformation is pinned down by how it compares the two hom-set bijections:
if transposing `τ.app X ≫ b` along `adj₂` is transposing `b` along `adj₁` followed by `β`, then
`β` is the conjugate of `τ`. -/
theorem conjugateEquiv_eq_of_homEquiv {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (τ : L₂ ⟶ L₁) (β : R₁ ⟶ R₂)
    (h : ∀ (X : C) (Y : D) (b : L₁.obj X ⟶ Y),
      adj₂.homEquiv X Y (τ.app X ≫ b) = adj₁.homEquiv X Y b ≫ β.app Y) :
    conjugateEquiv adj₁ adj₂ τ = β := by
  ext Y
  rw [conjugateEquiv_app_eq, h (R₁.obj Y) Y (adj₁.counit.app Y),
    Adjunction.homEquiv_unit, adj₁.right_triangle_components, Category.id_comp]

/-- Changing the right adjoints of two adjunctions along isomorphisms `i₁` and `i₂` conjugates
by `i₁` and `i₂`. -/
theorem conjugateEquiv_ofNatIsoRight {L₁ L₂ : C ⥤ D} {R₁ R₂ R₁' R₂' : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (i₁ : R₁ ≅ R₁') (i₂ : R₂ ≅ R₂') (τ : L₂ ⟶ L₁) :
    conjugateEquiv (adj₁.ofNatIsoRight i₁) (adj₂.ofNatIsoRight i₂) τ =
      i₁.inv ≫ conjugateEquiv adj₁ adj₂ τ ≫ i₂.hom := by
  ext Y
  rw [conjugateEquiv_app_eq, Adjunction.homEquiv_ofNatIsoRight_apply]
  have hc : (adj₁.ofNatIsoRight i₁).counit.app Y =
      L₁.map (i₁.inv.app Y) ≫ adj₁.counit.app Y := rfl
  rw [hc, ← NatTrans.naturality_assoc τ (i₁.inv.app Y),
    Adjunction.homEquiv_naturality_left, ← conjugateEquiv_app_eq]
  simp

/-- Uniqueness of a left adjoint is natural in a parameter: if the conjugates of `α` and `β`
agree, then the canonical comparisons of the left adjoints form a commuting square. -/
theorem leftAdjointUniq_naturality {L₁ L₂ L₁' L₂' : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adjA₁ : L₁ ⊣ R₁) (adjB₁ : L₁' ⊣ R₁) (adjA₂ : L₂ ⊣ R₂) (adjB₂ : L₂' ⊣ R₂)
    (α : L₁ ⟶ L₂) (β : L₁' ⟶ L₂')
    (h : conjugateEquiv adjA₂ adjA₁ α = conjugateEquiv adjB₂ adjB₁ β) :
    α ≫ (Adjunction.leftAdjointUniq adjA₂ adjB₂).hom =
      (Adjunction.leftAdjointUniq adjA₁ adjB₁).hom ≫ β := by
  apply (conjugateEquiv adjB₂ adjA₁).injective
  rw [← conjugateEquiv_comp adjB₂ adjA₂ adjA₁
      (Adjunction.leftAdjointUniq adjA₂ adjB₂).hom α,
    ← conjugateEquiv_comp adjB₂ adjB₁ adjA₁ β
      (Adjunction.leftAdjointUniq adjA₁ adjB₁).hom,
    conjugateEquiv_leftAdjointUniq_hom, conjugateEquiv_leftAdjointUniq_hom,
    Category.id_comp, Category.comp_id, h]

/-- `leftAdjointUniq_naturality` with the two comparison isomorphisms supplied by equations, so
that no unfolding of the isomorphisms is needed at the point of use. -/
theorem leftAdjointUniq_naturality_of_eq {L₁ L₂ L₁' L₂' : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adjA₁ : L₁ ⊣ R₁) (adjB₁ : L₁' ⊣ R₁) (adjA₂ : L₂ ⊣ R₂) (adjB₂ : L₂' ⊣ R₂)
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')
    (he₁ : e₁ = Adjunction.leftAdjointUniq adjA₁ adjB₁)
    (he₂ : e₂ = Adjunction.leftAdjointUniq adjA₂ adjB₂)
    (α : L₁ ⟶ L₂) (β : L₁' ⟶ L₂')
    (h : conjugateEquiv adjA₂ adjA₁ α = conjugateEquiv adjB₂ adjB₁ β) :
    α ≫ e₂.hom = e₁.hom ≫ β := by
  subst he₁
  subst he₂
  exact leftAdjointUniq_naturality adjA₁ adjB₁ adjA₂ adjB₂ α β h

/-- **The inverse of the conjugate of a monoidality comparison, transposed.** Let `F ⊣ G`,
`LM ⊣ RM` on `C`, `LM' ⊣ RM'` on `D` be adjunctions and `μ : LM ⋙ F ≅ F ⋙ LM'`, with conjugate
`RM' ⋙ G ≅ G ⋙ RM` along the composite adjunctions. Its inverse at `L` is the unit of `F ⊣ G` at
`RM (G L)` followed by `G` of the `LM' ⊣ RM'`-transpose of `μ⁻¹ ≫ F(counit)` and of `RM'` of the
counit of `F ⊣ G`. -/
theorem conjugateIsoEquiv_inv_app_eq_unit_comp {F : C ⥤ D} {G : D ⥤ C} {LM RM : C ⥤ C}
    {LM' RM' : D ⥤ D} (adjF : F ⊣ G) (a : LM ⊣ RM) (a' : LM' ⊣ RM') (μ : LM ⋙ F ≅ F ⋙ LM')
    (L : D) :
    ((conjugateIsoEquiv (adjF.comp a') (a.comp adjF)) μ).inv.app L =
      adjF.unit.app (RM.obj (G.obj L)) ≫ G.map (a'.homEquiv _ _
        (μ.inv.app (RM.obj (G.obj L)) ≫ F.map (a.counit.app (G.obj L))) ≫
          RM'.map (adjF.counit.app L)) := by
  have h : ((conjugateIsoEquiv (adjF.comp a') (a.comp adjF)) μ).inv =
      conjugateEquiv (a.comp adjF) (adjF.comp a') μ.inv := rfl
  rw [h, conjugateEquiv_app_eq, Adjunction.comp_homEquiv]
  simp [Adjunction.homEquiv_unit, Adjunction.comp_counit_app]

/-- **Uniqueness of a right adjoint is natural.** For adjunctions `L₁ ⊣ R₁`, `L₁ ⊣ R₁'`,
`L₂ ⊣ R₂` and `L₂ ⊣ R₂'` and a transformation `α : L₂ ⟶ L₁` of the left adjoints, the two
conjugates of `α` and the two canonical comparisons of right adjoints form a commuting square.

This is what moves a conjugate from one presentation of the right adjoints to another: it says
that the conjugate does not depend on which right adjoint one chose, beyond the canonical
comparison. -/
theorem rightAdjointUniq_naturality {L₁ L₂ : C ⥤ D} {R₁ R₁' R₂ R₂' : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁ ⊣ R₁') (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂ ⊣ R₂') (α : L₂ ⟶ L₁) :
    conjugateEquiv adj₁ adj₂ α ≫ (Adjunction.rightAdjointUniq adj₂ adj₂').hom =
      (Adjunction.rightAdjointUniq adj₁ adj₁').hom ≫ conjugateEquiv adj₁' adj₂' α := by
  change _ ≫ conjugateEquiv adj₂ adj₂' (𝟙 L₂) = conjugateEquiv adj₁ adj₁' (𝟙 L₁) ≫ _
  rw [conjugateEquiv_comp, conjugateEquiv_comp, Category.id_comp, Category.comp_id]

/-- `rightAdjointUniq_naturality` with the two comparison isomorphisms supplied by equations, so
that no unfolding of the isomorphisms is needed at the point of use. -/
theorem rightAdjointUniq_naturality_of_eq {L₁ L₂ : C ⥤ D} {R₁ R₁' R₂ R₂' : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁ ⊣ R₁') (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂ ⊣ R₂')
    (e₁ : R₁ ≅ R₁') (e₂ : R₂ ≅ R₂')
    (he₁ : e₁ = Adjunction.rightAdjointUniq adj₁ adj₁')
    (he₂ : e₂ = Adjunction.rightAdjointUniq adj₂ adj₂') (α : L₂ ⟶ L₁) :
    conjugateEquiv adj₁ adj₂ α ≫ e₂.hom = e₁.hom ≫ conjugateEquiv adj₁' adj₂' α := by
  subst he₁
  subst he₂
  exact rightAdjointUniq_naturality adj₁ adj₁' adj₂ adj₂' α

end Stacks.CategoryTheory

end
