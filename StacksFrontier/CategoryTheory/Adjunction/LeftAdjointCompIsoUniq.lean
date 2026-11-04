module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Composition isomorphisms of left adjoints and the comparison of left adjoints

For adjunctions `F₀₁ ⊣ G₁₀`, `F₁₂ ⊣ G₂₁`, `F₀₂ ⊣ G₂₀` and an isomorphism
`e : G₂₁ ⋙ G₁₀ ≅ G₂₀`, Mathlib's `CategoryTheory.Adjunction.leftAdjointCompIso` is the induced
isomorphism `F₀₁ ⋙ F₁₂ ≅ F₀₂`. This file shows that it does not depend on the choice of the left
adjoints: replacing each of `F₀₁`, `F₁₂`, `F₀₂` by another left adjoint of the same functor changes
it by the comparisons `CategoryTheory.Adjunction.leftAdjointUniq`.

This is the form in which the composition isomorphism of inverse images of modules on the
spaces-étale models, a composition isomorphism of left adjoints of direct images, is carried to
restriction along postcomposition.

## Main results

* `CategoryTheory.Adjunction.leftAdjointCompIso_trans_leftAdjointUniq`.
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]

/-- The conjugate of the inverse of `leftAdjointUniq` is the identity. -/
private theorem conjugateEquiv_leftAdjointUniq_inv {A B : Type*} [Category* A] [Category* B]
    {L L' : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) (adj' : L' ⊣ R) :
    conjugateEquiv adj adj' (adj.leftAdjointUniq adj').inv = 𝟙 _ :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom adj' adj

/-- **The composition isomorphism of left adjoints is independent of the left adjoints**: for
other left adjoints `F₀₁'`, `F₁₂'`, `F₀₂'` of `G₁₀`, `G₂₁`, `G₂₀`, the isomorphism
`F₀₁ ⋙ F₁₂ ≅ F₀₂` induced by `e` followed by `F₀₂ ≅ F₀₂'` is `F₀₁ ⋙ F₁₂ ≅ F₀₁' ⋙ F₁₂'`
followed by the isomorphism `F₀₁' ⋙ F₁₂' ≅ F₀₂'` induced by `e`. -/
theorem leftAdjointCompIso_trans_leftAdjointUniq
    {F₀₁ F₀₁' : C₀ ⥤ C₁} {F₁₂ F₁₂' : C₁ ⥤ C₂} {F₀₂ F₀₂' : C₀ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₀₁' : F₀₁' ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₁₂' : F₁₂' ⊣ G₂₁)
    (adj₀₂ : F₀₂ ⊣ G₂₀) (adj₀₂' : F₀₂' ⊣ G₂₀) (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e ≪≫ adj₀₂.leftAdjointUniq adj₀₂' =
      isoWhiskerRight (adj₀₁.leftAdjointUniq adj₀₁') F₁₂ ≪≫
        isoWhiskerLeft F₀₁' (adj₁₂.leftAdjointUniq adj₁₂') ≪≫
        leftAdjointCompIso adj₀₁' adj₁₂' adj₀₂' e := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).mp ?_)
  apply (conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂').injective
  simp only [Iso.trans_inv, isoWhiskerRight_inv, isoWhiskerLeft_inv,
    Category.assoc]
  rw [← conjugateEquiv_comp (adj₀₁.comp adj₁₂) adj₀₂ adj₀₂',
    ← conjugateEquiv_comp (adj₀₁.comp adj₁₂) (adj₀₁'.comp adj₁₂') adj₀₂',
    ← conjugateEquiv_comp (adj₀₁.comp adj₁₂) (adj₀₁'.comp adj₁₂) (adj₀₁'.comp adj₁₂'),
    conjugateEquiv_leftAdjointCompIso_inv, conjugateEquiv_leftAdjointCompIso_inv,
    conjugateEquiv_leftAdjointUniq_inv,
    conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
    conjugateEquiv_leftAdjointUniq_inv,
    conjugateEquiv_leftAdjointUniq_inv]
  simp

end CategoryTheory.Adjunction
