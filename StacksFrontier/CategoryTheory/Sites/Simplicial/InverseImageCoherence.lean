module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.PushforwardCoherence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SheavesPseudofunctorBridge

/-!
# Coherence of the inverse-image comparisons of a simplicial-site situation

Stacks 09WF presents sheaves on the total site of a simplicial site as a lax section of a
pseudofunctor built from the inverse images `φ ↦ (f_φ)⁻¹`. Building that pseudofunctor needs the
unitality and associativity laws for the canonical comparisons
`SimplicialSiteSituation.canonicalIdentityComparison` and
`.canonicalCompositionComparison`, and this file proves them.

They are not proved directly: the comparisons are mates of the direct-image comparisons, which
is why `StacksFrontier.CategoryTheory.Sites.Simplicial.SheavesPseudofunctorBridge` identifies them
with Mathlib's `Adjunction.leftAdjointIdIso` and `Adjunction.leftAdjointCompIso`. Mathlib's
`Adjunction.leftAdjointCompIso_comp_id`, `_id_comp` and `_assoc` then deduce each law from the
corresponding law for the direct images, which is what
`StacksFrontier.CategoryTheory.Sites.Simplicial.PushforwardCoherence` supplies.

## Main results

* `CategoryTheory.Adjunction.leftAdjointCompIso_congr`: transporting the third adjunction of
  `Adjunction.leftAdjointCompIso` along an equality of indices moves the transport from the left
  adjoints to the right adjoints. This is what lets the unit and cocycle laws be stated with the
  `eqToIso` transport that the coherence axioms of a pseudofunctor out of a locally discrete
  bicategory carry.
* `CategoryTheory.SimplicialSiteSituation.canonicalCompositionComparison_comp_id`,
  `_id_comp`, `_assoc`: the two unit laws and the cocycle law for the inverse-image
  comparisons.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory Functor

universe u

namespace CategoryTheory

namespace Adjunction

/-- Transporting the third adjunction of `Adjunction.leftAdjointCompIso` along an equality of
indices: the transport of the left adjoints on one side matches the transport of the right
adjoints inside the comparison on the other. -/
theorem leftAdjointCompIso_congr {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {α : Type*} {L : α → C₀ ⥤ C₂} {R : α → C₂ ⥤ C₀} (adj : ∀ a, L a ⊣ R a)
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁)
    {a₁ a₂ : α} (h : a₁ = a₂) (e : G₂₁ ⋙ G₁₀ ≅ R a₁) :
    leftAdjointCompIso adj₀₁ adj₁₂ (adj a₁) e ≪≫ eqToIso (congrArg L h) =
      leftAdjointCompIso adj₀₁ adj₁₂ (adj a₂) (e ≪≫ eqToIso (congrArg R h)) := by
  subst h
  simp

end Adjunction

namespace SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- The transport of an inverse image along an equality of simplex maps. -/
noncomputable def inverseImageCongr {m n : SimplexCategory} {φ₁ φ₂ : m ⟶ n} (h : φ₁ = φ₂) :
    (S.transitionMorphism φ₁).inverseImage ≅ (S.transitionMorphism φ₂).inverseImage :=
  eqToIso (by subst h; rfl)

/-- Transporting the inverse-image compositor along an equality of simplex maps moves the
transport to the direct-image comparison inside `Adjunction.leftAdjointCompIso`. -/
private theorem leftAdjointCompIso_inverseImageCongr {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) {θ₁ θ₂ : l ⟶ n} (h : θ₁ = θ₂)
    (e : (S.transitionMorphism φ).pushforward ⋙ (S.transitionMorphism ψ).pushforward ≅
      (S.transitionMorphism θ₁).pushforward) :
    Adjunction.leftAdjointCompIso (S.transitionMorphism ψ).adj (S.transitionMorphism φ).adj
        (S.transitionMorphism θ₁).adj e ≪≫ S.inverseImageCongr h =
      Adjunction.leftAdjointCompIso (S.transitionMorphism ψ).adj (S.transitionMorphism φ).adj
        (S.transitionMorphism θ₂).adj
        (e ≪≫ eqToIso (congrArg (fun α => (S.transitionMorphism α).pushforward) h)) :=
  Adjunction.leftAdjointCompIso_congr (fun α => (S.transitionMorphism α).adj) _ _ h e

/-- The right unit law for the inverse-image comparisons: the compositor at `φ ≫ 𝟙` is the
unit comparison in the second variable. -/
theorem canonicalCompositionComparison_comp_id {m n : SimplexCategory} (φ : m ⟶ n) :
    (canonicalCompositionComparison S φ (𝟙 n)).symm ≪≫ S.inverseImageCongr (Category.comp_id φ) =
      Functor.isoWhiskerLeft (S.transitionMorphism φ).inverseImage
          (canonicalIdentityComparison S n) ≪≫
        Functor.rightUnitor _ := by
  rw [canonicalCompositionComparison_eq_leftAdjointCompIso, Iso.symm_symm_eq,
    S.leftAdjointCompIso_inverseImageCongr _ _ (Category.comp_id φ),
    canonicalIdentityComparison_eq_leftAdjointIdIso]
  exact Adjunction.leftAdjointCompIso_comp_id _ _ _ (S.pushforwardId n)
    (S.pushforwardCompSymm_comp_id φ)

/-- The left unit law for the inverse-image comparisons: the compositor at `𝟙 ≫ φ` is the
unit comparison in the first variable. -/
theorem canonicalCompositionComparison_id_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (canonicalCompositionComparison S (𝟙 m) φ).symm ≪≫
        S.inverseImageCongr (Category.id_comp φ) =
      Functor.isoWhiskerRight (canonicalIdentityComparison S m)
          (S.transitionMorphism φ).inverseImage ≪≫
        Functor.leftUnitor _ := by
  rw [canonicalCompositionComparison_eq_leftAdjointCompIso, Iso.symm_symm_eq,
    S.leftAdjointCompIso_inverseImageCongr _ _ (Category.id_comp φ),
    canonicalIdentityComparison_eq_leftAdjointIdIso]
  exact Adjunction.leftAdjointCompIso_id_comp _ _ _ (S.pushforwardId m)
    (S.pushforwardCompSymm_id_comp φ)

/-- The cocycle law for the inverse-image comparisons. -/
theorem canonicalCompositionComparison_assoc {k l m n : SimplexCategory}
    (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n) :
    Functor.isoWhiskerLeft (S.transitionMorphism χ).inverseImage
          (canonicalCompositionComparison S ψ φ).symm ≪≫
        (canonicalCompositionComparison S χ (ψ ≫ φ)).symm =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (canonicalCompositionComparison S χ ψ).symm
            (S.transitionMorphism φ).inverseImage ≪≫
          ((canonicalCompositionComparison S (χ ≫ ψ) φ).symm ≪≫
            S.inverseImageCongr (Category.assoc χ ψ φ)) := by
  rw [canonicalCompositionComparison_eq_leftAdjointCompIso,
    canonicalCompositionComparison_eq_leftAdjointCompIso,
    canonicalCompositionComparison_eq_leftAdjointCompIso,
    canonicalCompositionComparison_eq_leftAdjointCompIso, Iso.symm_symm_eq, Iso.symm_symm_eq,
    Iso.symm_symm_eq, Iso.symm_symm_eq,
    S.leftAdjointCompIso_inverseImageCongr _ _ (Category.assoc χ ψ φ)]
  exact Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _
    (S.pushforwardCompSymm_assoc χ ψ φ)

end SimplicialSiteSituation

end CategoryTheory

end
