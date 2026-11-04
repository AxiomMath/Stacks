module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Adjunction.UnitOfRightAdjointIsoId
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp
public import StacksFrontier.CategoryTheory.Comma.Over.PullbackCoherence

/-!
# The two unit laws for a compositor of right adjoints

A compositor `τ : L₀₁ ⋙ L₁₂ ⟶ L₀₂` of left adjoints has a mate
`CategoryTheory.Adjunction.rightAdjointCompNatTrans` between the right adjoints, and
`CategoryTheory.Adjunction.rightAdjointCompNatTrans_assoc` already says that the mate inherits
the associativity cocycle law. This file supplies the two remaining coherences of a
pseudofunctor: if the compositor of the left adjoints satisfies a unit law, so does its mate.

Both are the duals of what Mathlib proves in `Mathlib.CategoryTheory.Adjunction.CompositionIso`
for a compositor of left adjoints induced by one of right adjoints
(`CategoryTheory.Adjunction.leftAdjointCompIso_comp_id` and
`CategoryTheory.Adjunction.leftAdjointCompIso_id_comp`), and they are *deduced* from those: the
mate operation is the bijection `CategoryTheory.conjugateEquiv`, and Mathlib's lemmas compute
its inverse on the isomorphism the right-hand side of the conclusion names.

## Main results

All in the namespace `CategoryTheory.Adjunction`.

* `leftAdjointIdIso_rightAdjointUniq_ofNatIsoLeft` — if the left adjoint of `adj` is identified
  with the identity functor by `eL`, the comparison of the right adjoint with the identity
  functor that uniqueness of a right adjoint produces has `eL` as its own mate. This is what
  lets a unit datum constructed as a `CategoryTheory.Adjunction.rightAdjointUniq` — the shape in
  which such data usually arrive — be fed to the two unit laws below.
* `rightAdjointUniq_ofNatIsoLeft_comp_inv` — a compositor of right adjoints constructed by
  uniqueness of a right adjoint of the composite is the mate of the compositor of the left
  adjoints it was built from.
* `rightAdjointCompNatTrans_comp_id` and `rightAdjointCompNatTrans_id_comp` — the two unit laws.

## Implementation notes

The hypothesis of each unit law is stated on `CategoryTheory.Adjunction.leftAdjointIdIso`, the
mate of the identification of the right adjoint with the identity functor, because that is the
form Mathlib's lemmas produce. In practice the identification available is the one of the *left*
adjoints, and `leftAdjointIdIso_rightAdjointUniq_ofNatIsoLeft` is the bridge.

This file is generic category theory; it lives here because it was written for
[Stacks, Tag 0ATY], where the pseudofunctor in question is built from right adjoints
throughout -- the twisted inverse image is a right adjoint of derived direct image, which is a
right adjoint of derived pullback -- so every coherence has to be transported in the direction
Mathlib does not cover.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Adjunction

universe v₀ v₁ v₂ u₀ u₁ u₂

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]

/-- **The mate of the unit datum produced by uniqueness of a right adjoint is the unit datum it
was produced from.** Let `adj : L ⊣ R` be an adjunction between endofunctors and let
`eL : L ≅ 𝟭` identify the left adjoint with the identity functor. Reading `adj` through `eL`
exhibits `R` as a right adjoint of `𝟭`, so uniqueness of a right adjoint compares it with `𝟭`;
the mate of that comparison, `CategoryTheory.Adjunction.leftAdjointIdIso`, is `eL` again. -/
theorem leftAdjointIdIso_rightAdjointUniq_ofNatIsoLeft {L R : C₀ ⥤ C₀} (adj : L ⊣ R)
    (eL : L ≅ 𝟭 C₀) :
    leftAdjointIdIso adj (rightAdjointUniq (adj.ofNatIsoLeft eL) Adjunction.id) = eL := by
  refine Iso.ext ((conjugateEquiv Adjunction.id adj).injective ?_)
  rw [conjugateEquiv_leftAdjointIdIso_hom]
  show _ = conjugateEquiv Adjunction.id adj eL.hom
  ext c
  simp [conjugateEquiv, Adjunction.ofNatIsoLeft, Adjunction.id, mateEquiv, rightAdjointUniq]

variable {L₀₁ : C₀ ⥤ C₁} {R₁₀ : C₁ ⥤ C₀} {L₁₂ : C₁ ⥤ C₂} {R₂₁ : C₂ ⥤ C₁}
  {L₀₂ : C₀ ⥤ C₂} {R₂₀ : C₂ ⥤ C₀}

/-- **A compositor of right adjoints built by uniqueness is a mate.** Composing
`adj₀₁ : L₀₁ ⊣ R₁₀` with `adj₁₂ : L₁₂ ⊣ R₂₁` and reading the result through a compositor
`e : L₀₁ ⋙ L₁₂ ≅ L₀₂` of the left adjoints exhibits `R₂₁ ⋙ R₁₀` as a right adjoint of `L₀₂`;
uniqueness of a right adjoint then compares it with `R₂₀`, and that comparison is inverse to the
mate of `e`. -/
theorem rightAdjointUniq_ofNatIsoLeft_comp_inv (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₀₂ : L₀₂ ⊣ R₂₀) (e : L₀₁ ⋙ L₁₂ ≅ L₀₂) :
    (rightAdjointUniq ((adj₀₁.comp adj₁₂).ofNatIsoLeft e) adj₀₂).inv =
      rightAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ e.hom := by
  ext K
  simp [rightAdjointCompNatTrans, Adjunction.rightAdjointUniq, Adjunction.ofNatIsoLeft,
    conjugateEquiv]

/-- The mate of `τ` is `e.inv` when `τ` is the hom of an iso equal to `leftAdjointCompIso e`. -/
private theorem rightAdjointCompNatTrans_eq_inv {adj₀₁ : L₀₁ ⊣ R₁₀} {adj₁₂ : L₁₂ ⊣ R₂₁}
    {adj₀₂ : L₀₂ ⊣ R₂₀} {e : R₂₁ ⋙ R₁₀ ≅ R₂₀} {τ : L₀₁ ⋙ L₁₂ ⟶ L₀₂} {i : L₀₁ ⋙ L₁₂ ≅ L₀₂}
    (key : leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e = i) (h : τ = i.hom) :
    rightAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ τ = e.inv := by
  subst h key
  exact (conjugateEquiv _ _).apply_symm_apply _

/-- **The right unit law passes from a compositor of left adjoints to its mate.** If the
compositor `τ : L₀₁ ⋙ L₁₁' ⟶ L₀₁` is the identification of the inner left adjoint with the
identity functor, whiskered by `L₀₁`, then its mate `R₁₀ ⟶ R₁'₁ ⋙ R₁₀` is the inverse of the
identification of `R₁'₁` with the identity functor, whiskered by `R₁₀`.

This is the dual of `CategoryTheory.Adjunction.leftAdjointCompIso_comp_id`, and is deduced from
it: the mate operation is the bijection `CategoryTheory.conjugateEquiv`, and that lemma says the
isomorphism named on the right-hand side is sent by its inverse to `τ`. -/
theorem rightAdjointCompNatTrans_comp_id {L₁₁' : C₁ ⥤ C₁} {R₁'₁ : C₁ ⥤ C₁}
    (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₁' : L₁₁' ⊣ R₁'₁) (eR : R₁'₁ ≅ 𝟭 C₁) (τ : L₀₁ ⋙ L₁₁' ⟶ L₀₁)
    (h : τ = (isoWhiskerLeft L₀₁ (leftAdjointIdIso adj₁₁' eR) ≪≫ rightUnitor L₀₁).hom) :
    rightAdjointCompNatTrans adj₀₁ adj₁₁' adj₀₁ τ =
      (isoWhiskerRight eR R₁₀ ≪≫ leftUnitor R₁₀).inv := by
  exact rightAdjointCompNatTrans_eq_inv (leftAdjointCompIso_comp_id adj₀₁ adj₁₁' _ eR rfl) h

/-- **The left unit law passes from a compositor of left adjoints to its mate.** If the
compositor `τ : L₀₀' ⋙ L₀'₁ ⟶ L₀'₁` is the identification of the outer left adjoint with the
identity functor, whiskered by `L₀'₁`, then its mate `R₁₀' ⟶ R₁₀' ⋙ R₀'₀` is the inverse of the
identification of `R₀'₀` with the identity functor, whiskered by `R₁₀'`.

The dual of `CategoryTheory.Adjunction.leftAdjointCompIso_id_comp`, deduced from it the same
way. -/
theorem rightAdjointCompNatTrans_id_comp {L₀₀' : C₀ ⥤ C₀} {R₀'₀ : C₀ ⥤ C₀} {L₀'₁ : C₀ ⥤ C₁}
    {R₁₀' : C₁ ⥤ C₀} (adj₀₀' : L₀₀' ⊣ R₀'₀) (adj₀'₁ : L₀'₁ ⊣ R₁₀') (eR : R₀'₀ ≅ 𝟭 C₀)
    (τ : L₀₀' ⋙ L₀'₁ ⟶ L₀'₁)
    (h : τ = (isoWhiskerRight (leftAdjointIdIso adj₀₀' eR) L₀'₁ ≪≫ leftUnitor L₀'₁).hom) :
    rightAdjointCompNatTrans adj₀₀' adj₀'₁ adj₀'₁ τ =
      (isoWhiskerLeft R₁₀' eR ≪≫ rightUnitor R₁₀').inv := by
  exact rightAdjointCompNatTrans_eq_inv (leftAdjointCompIso_id_comp adj₀₀' adj₀'₁ _ eR rfl) h

end CategoryTheory.Adjunction

end
