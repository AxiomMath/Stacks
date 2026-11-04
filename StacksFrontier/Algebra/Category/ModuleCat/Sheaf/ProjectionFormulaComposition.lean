module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap

/-!
# The projection-formula map of a composite adjunction

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions `C ⇄ D` and `D ⇄ E`, let `A`, `A'` and
`B` be bifunctors on `C`, `D` and `E`, and let `α₁ : A ⋙ L₁ ⟶ L₁ × L₁ ⋙ A'` and
`α₂ : A' ⋙ L₂ ⟶ L₂ × L₂ ⋙ B` be comparisons. The composite adjunction
`adj₁.comp adj₂ : L₁ ⋙ L₂ ⊣ R₂ ⋙ R₁` carries the comparison whose component at `(H, K)` is
`L₂(α₁) ≫ α₂`, and this file proves that its projection-formula map
`Stacks.ProjectionFormula.adjunctionTensorMapSnd` factors accordingly:

`A(H, R₁R₂G) ⟶ R₁(A'(L₁H, R₂G)) ⟶ R₁R₂(B(L₂L₁H, G))`,

the first map being the projection-formula map of `adj₁` at `R₂G` and the second the image under
`R₁` of the projection-formula map of `adj₂` at `L₁H`.

This is what reduces the invertibility of a projection-formula map to the invertibility of the two
factors of a factored adjunction. The pullback of sheaves of modules along a morphism of ringed
topoi is the inverse image of Stacks 03D2 followed by extension of scalars along the structure
map, and `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` is by construction the
`CategoryTheory.Adjunction.comp` of the two adjunctions, so this is the shape in which the
projection-formula map of Stacks 04G0 splits into a closed-immersion factor and a
change-of-rings factor.

## Main results

* `Stacks.ProjectionFormula.adjunctionTensorMapSnd_comp`: the factorization above.
* `Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd_comp`: hence the projection-formula map
  of the composite is an isomorphism as soon as each factor is.

## Implementation notes

The comparison `α` of the composite is taken as an argument together with the hypothesis `hα`
identifying its components with `L₂(α₁) ≫ α₂`, rather than being constructed here from `α₁` and
`α₂`. Both forms are needed by the consumer and only this one avoids a transport: the comparison
the consumer has is `Stacks.SheafOfModules.pullbackTensorIso`, defined by a chain of
Hom-bijections, and what is available about it is an identity of its *components*, not an identity
of natural transformations through the isomorphism
`(L₁ ⋙ L₂).prod (L₁ ⋙ L₂) = L₁.prod L₁ ⋙ L₂.prod L₂` of functors. Asking for the componentwise
identity keeps that isomorphism out of the statement; nothing is lost, since a natural
transformation is determined by its components.

## References

* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.ProjectionFormula

universe u₁ v₁ u₂ v₂ u₃ v₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  (A : C × C ⥤ C) (A' : D × D ⥤ D) (B : E × E ⥤ E)
  (α₁ : A ⋙ L₁ ⟶ L₁.prod L₁ ⋙ A') (α₂ : A' ⋙ L₂ ⟶ L₂.prod L₂ ⋙ B)

/-- **The projection-formula map of a composite adjunction factors.** If the comparison `α` of
the composite adjunction has components `L₂(α₁) ≫ α₂`, then its projection-formula map with the
counit in the second tensor factor is the projection-formula map of `adj₁` at `R₂G` followed by
the image under `R₁` of the projection-formula map of `adj₂` at `L₁H`.

Both sides are, by `CategoryTheory.Adjunction.comp_homEquiv`, the image under `adj₁.homEquiv` of
a morphism `L₁(A(H, R₁R₂G)) ⟶ R₂(B(L₂L₁H, G))`; the two morphisms agree by the naturality of
`α₂` at `(𝟙, ε₁)` together with the formula for the counit of a composite adjunction. -/
lemma adjunctionTensorMapSnd_comp
    (α : A ⋙ (L₁ ⋙ L₂) ⟶ (L₁ ⋙ L₂).prod (L₁ ⋙ L₂) ⋙ B)
    (hα : ∀ H K : C, α.app (H, K) =
      L₂.map (α₁.app (H, K)) ≫ α₂.app (L₁.obj H, L₁.obj K))
    (H : C) (G : E) :
    adjunctionTensorMapSnd (adj₁.comp adj₂) A B α H G =
      adjunctionTensorMapSnd adj₁ A A' α₁ H (R₂.obj G) ≫
        R₁.map (adjunctionTensorMapSnd adj₂ A' B α₂ (L₁.obj H) G) := by
  unfold adjunctionTensorMapSnd
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
  refine congrArg (adj₁.homEquiv _ _) (congrArg (adj₂.homEquiv _ _) ?_)
  have hnat := α₂.naturality
    ((𝟙 (L₁.obj H), adj₁.counit.app (R₂.obj G)) :
      ((L₁.obj H, L₁.obj (R₁.obj (R₂.obj G))) : D × D) ⟶ (L₁.obj H, R₂.obj G))
  change L₂.map (A'.map (𝟙 (L₁.obj H) ×ₘ adj₁.counit.app (R₂.obj G))) ≫
      α₂.app (L₁.obj H, R₂.obj G) =
    α₂.app (L₁.obj H, L₁.obj (R₁.obj (R₂.obj G))) ≫
      B.map (L₂.map (𝟙 (L₁.obj H)) ×ₘ L₂.map (adj₁.counit.app (R₂.obj G))) at hnat
  have hε : (adj₁.comp adj₂).counit.app G =
      L₂.map (adj₁.counit.app (R₂.obj G)) ≫ adj₂.counit.app G := by
    simp [Adjunction.comp]
  have key : α₂.app (L₁.obj H, L₁.obj (R₁.obj (R₂.obj G))) ≫
        B.map (𝟙 (L₂.obj (L₁.obj H)) ×ₘ
          (L₂.map (adj₁.counit.app (R₂.obj G)) ≫ adj₂.counit.app G)) =
      L₂.map (A'.map (𝟙 (L₁.obj H) ×ₘ adj₁.counit.app (R₂.obj G))) ≫
        α₂.app (L₁.obj H, R₂.obj G) ≫
          B.map (𝟙 (L₂.obj (L₁.obj H)) ×ₘ adj₂.counit.app G) := by
    rw [← Category.assoc, hnat, Category.assoc, ← B.map_comp]
    refine congrArg (fun m ↦ α₂.app (L₁.obj H, L₁.obj (R₁.obj (R₂.obj G))) ≫ B.map m) ?_
    refine Prod.ext ?_ ?_
    · simp
    · simp
  rw [hα, hε]
  simp only [Functor.comp_obj]
  rw [Category.assoc, key, Functor.map_comp, Category.assoc]

/-- **The projection-formula map of a composite adjunction is an isomorphism as soon as each
factor is.** This is `Stacks.ProjectionFormula.adjunctionTensorMapSnd_comp` together with the
closure of isomorphisms under composition and under the action of `R₁`. -/
lemma isIso_adjunctionTensorMapSnd_comp
    (α : A ⋙ (L₁ ⋙ L₂) ⟶ (L₁ ⋙ L₂).prod (L₁ ⋙ L₂) ⋙ B)
    (hα : ∀ H K : C, α.app (H, K) =
      L₂.map (α₁.app (H, K)) ≫ α₂.app (L₁.obj H, L₁.obj K))
    (H : C) (G : E)
    (h₁ : IsIso (adjunctionTensorMapSnd adj₁ A A' α₁ H (R₂.obj G)))
    (h₂ : IsIso (adjunctionTensorMapSnd adj₂ A' B α₂ (L₁.obj H) G)) :
    IsIso (adjunctionTensorMapSnd (adj₁.comp adj₂) A B α H G) := by
  rw [adjunctionTensorMapSnd_comp adj₁ adj₂ A A' B α₁ α₂ α hα H G]
  have := h₁
  have := h₂
  infer_instance

end Stacks.ProjectionFormula

end
