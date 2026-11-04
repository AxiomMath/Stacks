module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackDinaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomEquivalenceTransport
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Abstract

/-!
# The comparison of a functor with internal hom, computed on models

Let `P : D₁ ⥤ D₂` carry the data of the transpose construction of Tag 08I3: internal homs
`H₁, H₂`, tensor products `T₁, T₂`, tensor–hom bijections `e₁, e₂` and a monoidality comparison
`m`, so that `Transpose.homComparison` is defined.  Suppose the same data is given one level
down, on categories `C₁, C₂` of *models* with a functor `p : C₁ ⥤ C₂`, and that `Q₁ : C₁ ⥤ D₁`,
`Q₂ : C₂ ⥤ D₂` relate the two levels through a transformation `ν : Q₁ ⋙ P ⟶ p ⋙ Q₂`, comparisons
`σᵢ : Qᵢ Hcᵢ(A, B) ⟶ Hᵢ(Qᵢ A, Qᵢ B)` of internal homs and comparisons
`κᵢ : Tᵢ(Qᵢ A, Qᵢ B) ⟶ Qᵢ Tcᵢ(A, B)` of tensor products.

This file proves that the comparison of `P` at `(Q₁ E, Q₁ F)`, precomposed with `P σ₁`, is the
image of the comparison of `p` at `(E, F)`, read through `ν`, `σ₂` and `ν` again, as soon as the
`σᵢ` transpose to the evaluations of the models through the `κᵢ`, the monoidality comparisons of
the two levels agree through `κ` and `ν`, and `ν` is invertible at `F`.

For the derived pullback along a morphism of ringed spaces, with complexes of modules as models,
this is the description of the canonical map of Tag 08I3 by the comparison of internal Hom
complexes on representatives.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.map_comp_homComparison_of_models`
-/

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback.Transpose

section Models

variable {D₁ D₂ C₁ C₂ : Type*} [Category D₁] [Category D₂] [Category C₁] [Category C₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)
  (p : C₁ ⥤ C₂) (Hc₁ : C₁ᵒᵖ ⥤ C₁ ⥤ C₁) (Hc₂ : C₂ᵒᵖ ⥤ C₂ ⥤ C₂)
  (Tc₁ : C₁ × C₁ ⥤ C₁) (Tc₂ : C₂ × C₂ ⥤ C₂)
  (ec₁ : ∀ A B C : C₁, (A ⟶ (Hc₁.obj (op B)).obj C) ≃ (Tc₁.obj (A, B) ⟶ C))
  (ec₂ : ∀ A B C : C₂, (A ⟶ (Hc₂.obj (op B)).obj C) ≃ (Tc₂.obj (A, B) ⟶ C))
  (mc : Tc₁ ⋙ p ≅ p.prod p ⋙ Tc₂)
  (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (ν : Q₁ ⋙ P ⟶ p ⋙ Q₂)

/-- The inverse monoidality comparison is natural in the first variable. -/
private theorem tensor_map_comp_monoidality_inv {X X' : D₁} (f : X ⟶ X') (A : D₁) :
    T₂.map (P.map f ×ₘ 𝟙 (P.obj A)) ≫ m.inv.app (X', A) =
      m.inv.app (X, A) ≫ P.map (T₁.map (f ×ₘ 𝟙 A)) := by
  have hm := m.inv.naturality (f ×ₘ 𝟙 A)
  dsimp only [Functor.comp_map, Functor.prod_map] at hm
  rwa [P.map_id] at hm

/-- The comparison of `P` with internal hom is compatible with the evaluations. -/
private theorem tensor_map_homComparison_comp_evaluation
    (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂) (A B : D₁) :
    T₂.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ×ₘ 𝟙 (P.obj A)) ≫
        evaluation H₂ T₂ e₂ (P.obj A) (P.obj B) =
      m.inv.app ((H₁.obj (op A)).obj B, A) ≫ P.map (evaluation H₁ T₁ e₁ A B) := by
  have hn := hnat₂ (P.obj ((H₁.obj (op A)).obj B))
    ((H₂.obj (op (P.obj A))).obj (P.obj B)) (P.obj A) (P.obj B)
    (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) (𝟙 _)
  rw [Category.comp_id] at hn
  rw [evaluation, ← hn, homComparison_adjoint, homComparisonDatum]

/-- The transpose of `P σ₁` followed by the comparison of `P` is the monoidality comparison
followed by `P` of the transpose of `σ₁`. -/
theorem adjoint_map_comp_homComparison
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁) (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (A B W : D₁) (s : W ⟶ (H₁.obj (op A)).obj B) :
    e₂ (P.obj W) (P.obj A) (P.obj B) (P.map s ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) =
      m.inv.app (W, A) ≫ P.map (e₁ W A B s) := by
  rw [hnat₂, homComparison_adjoint, homComparisonDatum]
  rw [reassoc_of% (tensor_map_comp_monoidality_inv P T₁ T₂ m s A), ← P.map_comp, evaluation,
    ← hnat₁, Category.comp_id]

/-- The transpose of the image of the comparison of the models, read through `ν`, `σ₂` and `ν`. -/
theorem adjoint_models_comp
    (_hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂) (hdin₂ : TensorHomEquivDinatural H₂ T₂ e₂)
    (htgt₂ : EquivalenceTranspose.CurriedTargetNatural H₂ T₂ e₂)
    (W : D₂) (E F : C₁) (νinv : Q₂.obj (p.obj F) ⟶ P.obj (Q₁.obj F))
    (g : W ⟶ (H₂.obj (op (Q₂.obj (p.obj E)))).obj (Q₂.obj (p.obj F))) :
    e₂ W (P.obj (Q₁.obj E)) (P.obj (Q₁.obj F))
        (g ≫ (H₂.map (ν.app E).op).app (Q₂.obj (p.obj F)) ≫
          (H₂.obj (op (P.obj (Q₁.obj E)))).map νinv) =
      T₂.map (𝟙 W ×ₘ ν.app E) ≫ e₂ W (Q₂.obj (p.obj E)) (Q₂.obj (p.obj F)) g ≫ νinv := by
  rw [← Category.assoc, htgt₂, hdin₂]
  simp only [Category.assoc]

variable {P H₁ H₂ T₁ T₂ e₁ e₂ m p Hc₁ Hc₂ Tc₁ Tc₂ ec₁ ec₂ mc Q₁ Q₂ ν}

/-- **The comparison of a functor with internal hom, computed on models.**  Under the hypotheses
displayed, the comparison `P H₁(Q₁E, Q₁F) ⟶ H₂(P Q₁E, P Q₁F)` precomposed with `P σ₁` is

`P Q₁ Hc₁(E, F) ⟶ Q₂ p Hc₁(E, F) ⟶ Q₂ Hc₂(pE, pF) ⟶ H₂(Q₂ pE, Q₂ pF) ⟶ H₂(P Q₁E, P Q₁F)`,

the first arrow `ν`, the second the image of the comparison of `p`, the third `σ₂` and the last
the two maps induced by `ν` at `E` and `F`.

The hypotheses: `hσ₁` and `hσ₂` say that each `σᵢ` transposes to the evaluation of the models
through `κᵢ`; `hκ₂` is the naturality of `κ₂` in its first variable at the comparison of `p`;
`hm` says that the monoidality comparisons of the two levels agree through `κ` and `ν`; the
remaining ones are the functoriality of the bijections in each variable. -/
theorem map_comp_homComparison_of_models
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁) (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (hdin₂ : TensorHomEquivDinatural H₂ T₂ e₂)
    (htgt₂ : EquivalenceTranspose.CurriedTargetNatural H₂ T₂ e₂)
    (hnatc₂ : TensorHomEquivNaturalLeft Hc₂ Tc₂ ec₂)
    (σ₁ : ∀ A B : C₁, Q₁.obj ((Hc₁.obj (op A)).obj B) ⟶ (H₁.obj (op (Q₁.obj A))).obj (Q₁.obj B))
    (σ₂ : ∀ A B : C₂, Q₂.obj ((Hc₂.obj (op A)).obj B) ⟶ (H₂.obj (op (Q₂.obj A))).obj (Q₂.obj B))
    (κ₁ : ∀ A B : C₁, T₁.obj (Q₁.obj A, Q₁.obj B) ⟶ Q₁.obj (Tc₁.obj (A, B)))
    (κ₂ : ∀ A B : C₂, T₂.obj (Q₂.obj A, Q₂.obj B) ⟶ Q₂.obj (Tc₂.obj (A, B)))
    (E F : C₁) (νinv : Q₂.obj (p.obj F) ⟶ P.obj (Q₁.obj F)) (hνinv : ν.app F ≫ νinv = 𝟙 _)
    (hσ₁ : e₁ _ _ _ (σ₁ E F) = κ₁ ((Hc₁.obj (op E)).obj F) E ≫ Q₁.map (evaluation Hc₁ Tc₁ ec₁ E F))
    (hσ₂ : e₂ _ _ _ (σ₂ (p.obj E) (p.obj F)) =
      κ₂ ((Hc₂.obj (op (p.obj E))).obj (p.obj F)) (p.obj E) ≫
        Q₂.map (evaluation Hc₂ Tc₂ ec₂ (p.obj E) (p.obj F)))
    (hκ₂ : T₂.map (Q₂.map (homComparison p Hc₁ Hc₂ Tc₁ Tc₂ ec₁ ec₂ mc E F) ×ₘ
          𝟙 (Q₂.obj (p.obj E))) ≫
        κ₂ ((Hc₂.obj (op (p.obj E))).obj (p.obj F)) (p.obj E) =
      κ₂ (p.obj ((Hc₁.obj (op E)).obj F)) (p.obj E) ≫
        Q₂.map (Tc₂.map (homComparison p Hc₁ Hc₂ Tc₁ Tc₂ ec₁ ec₂ mc E F ×ₘ 𝟙 (p.obj E))))
    (hm : m.inv.app (Q₁.obj ((Hc₁.obj (op E)).obj F), Q₁.obj E) ≫
        P.map (κ₁ ((Hc₁.obj (op E)).obj F) E) ≫ ν.app (Tc₁.obj ((Hc₁.obj (op E)).obj F, E)) =
      T₂.map (ν.app ((Hc₁.obj (op E)).obj F) ×ₘ ν.app E) ≫
        κ₂ (p.obj ((Hc₁.obj (op E)).obj F)) (p.obj E) ≫
          Q₂.map (mc.inv.app ((Hc₁.obj (op E)).obj F, E))) :
    P.map (σ₁ E F) ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m (Q₁.obj E) (Q₁.obj F) =
      ν.app ((Hc₁.obj (op E)).obj F) ≫
        Q₂.map (homComparison p Hc₁ Hc₂ Tc₁ Tc₂ ec₁ ec₂ mc E F) ≫
          σ₂ (p.obj E) (p.obj F) ≫ (H₂.map (ν.app E).op).app (Q₂.obj (p.obj F)) ≫
            (H₂.obj (op (P.obj (Q₁.obj E)))).map νinv := by
  apply (e₂ _ _ _).injective
  rw [adjoint_map_comp_homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m hnat₁ hnat₂, hσ₁, P.map_comp]
  rw [← Category.assoc (ν.app _), ← Category.assoc (ν.app _ ≫ _),
    adjoint_models_comp P H₂ T₂ e₂ p Q₁ Q₂ ν hnat₂ hdin₂ htgt₂, hnat₂, hσ₂]
  have hcomp : T₂.map (𝟙 (P.obj (Q₁.obj ((Hc₁.obj (op E)).obj F))) ×ₘ ν.app E) ≫
      T₂.map ((ν.app ((Hc₁.obj (op E)).obj F) ≫
        Q₂.map (homComparison p Hc₁ Hc₂ Tc₁ Tc₂ ec₁ ec₂ mc E F)) ×ₘ 𝟙 (Q₂.obj (p.obj E))) =
      T₂.map (ν.app ((Hc₁.obj (op E)).obj F) ×ₘ ν.app E) ≫
        T₂.map (Q₂.map (homComparison p Hc₁ Hc₂ Tc₁ Tc₂ ec₁ ec₂ mc E F) ×ₘ
          𝟙 (Q₂.obj (p.obj E))) := by
    rw [← T₂.map_comp, ← T₂.map_comp]
    congr 1
    ext <;> simp
  have hev : Tc₂.map (homComparison p Hc₁ Hc₂ Tc₁ Tc₂ ec₁ ec₂ mc E F ×ₘ 𝟙 (p.obj E)) ≫
      evaluation Hc₂ Tc₂ ec₂ (p.obj E) (p.obj F) =
      mc.inv.app ((Hc₁.obj (op E)).obj F, E) ≫ p.map (evaluation Hc₁ Tc₁ ec₁ E F) := by
    exact tensor_map_homComparison_comp_evaluation p Hc₁ Hc₂ Tc₁ Tc₂ ec₁ ec₂ mc hnatc₂ E F
  have hν := ν.naturality (evaluation Hc₁ Tc₁ ec₁ E F)
  dsimp only [Functor.comp_map] at hν
  simp only [Category.assoc]
  rw [reassoc_of% hcomp, reassoc_of% hκ₂, ← Q₂.map_comp_assoc, hev, Q₂.map_comp,
    Category.assoc, ← reassoc_of% hm, ← reassoc_of% hν, hνinv]
  exact (congrArg _ (congrArg _ (Category.comp_id _))).symm

/-- `map_comp_homComparison_of_models` with the internal hom of the models presented through an
object function `hc` equal to its values, the comparisons `σᵢ` and the evaluations `evᵢ` being
given at `hc`.  The canonical maps `κᵢ` are asked to be natural in their first variable. -/
theorem map_comp_homComparison_of_models'
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁) (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (hdin₂ : TensorHomEquivDinatural H₂ T₂ e₂)
    (htgt₂ : EquivalenceTranspose.CurriedTargetNatural H₂ T₂ e₂)
    (hnatc₂ : TensorHomEquivNaturalLeft Hc₂ Tc₂ ec₂)
    (hc₁ : C₁ → C₁ → C₁) (hHc₁ : ∀ A B, (Hc₁.obj (op A)).obj B = hc₁ A B)
    (hc₂ : C₂ → C₂ → C₂) (hHc₂ : ∀ A B, (Hc₂.obj (op A)).obj B = hc₂ A B)
    (σ₁ : ∀ A B : C₁, Q₁.obj (hc₁ A B) ⟶ (H₁.obj (op (Q₁.obj A))).obj (Q₁.obj B))
    (σ₂ : ∀ A B : C₂, Q₂.obj (hc₂ A B) ⟶ (H₂.obj (op (Q₂.obj A))).obj (Q₂.obj B))
    (κ₁ : ∀ A B : C₁, T₁.obj (Q₁.obj A, Q₁.obj B) ⟶ Q₁.obj (Tc₁.obj (A, B)))
    (κ₂ : ∀ A B : C₂, T₂.obj (Q₂.obj A, Q₂.obj B) ⟶ Q₂.obj (Tc₂.obj (A, B)))
    (hκ₁ : ∀ {A A' : C₁} (B : C₁) (g : A ⟶ A'),
      T₁.map (Q₁.map g ×ₘ 𝟙 (Q₁.obj B)) ≫ κ₁ A' B = κ₁ A B ≫ Q₁.map (Tc₁.map (g ×ₘ 𝟙 B)))
    (hκ₂ : ∀ {A A' : C₂} (B : C₂) (g : A ⟶ A'),
      T₂.map (Q₂.map g ×ₘ 𝟙 (Q₂.obj B)) ≫ κ₂ A' B = κ₂ A B ≫ Q₂.map (Tc₂.map (g ×ₘ 𝟙 B)))
    (E F : C₁) (νinv : Q₂.obj (p.obj F) ⟶ P.obj (Q₁.obj F)) (hνinv : ν.app F ≫ νinv = 𝟙 _)
    (ev₁ : Tc₁.obj (hc₁ E F, E) ⟶ F)
    (hev₁ : Tc₁.map (eqToHom (hHc₁ E F) ×ₘ 𝟙 E) ≫ ev₁ = evaluation Hc₁ Tc₁ ec₁ E F)
    (ev₂ : Tc₂.obj (hc₂ (p.obj E) (p.obj F), p.obj E) ⟶ p.obj F)
    (hev₂ : Tc₂.map (eqToHom (hHc₂ (p.obj E) (p.obj F)) ×ₘ 𝟙 (p.obj E)) ≫ ev₂ =
      evaluation Hc₂ Tc₂ ec₂ (p.obj E) (p.obj F))
    (hσ₁ : e₁ _ _ _ (σ₁ E F) = κ₁ (hc₁ E F) E ≫ Q₁.map ev₁)
    (hσ₂ : e₂ _ _ _ (σ₂ (p.obj E) (p.obj F)) =
      κ₂ (hc₂ (p.obj E) (p.obj F)) (p.obj E) ≫ Q₂.map ev₂)
    (hm : m.inv.app (Q₁.obj ((Hc₁.obj (op E)).obj F), Q₁.obj E) ≫
        P.map (κ₁ ((Hc₁.obj (op E)).obj F) E) ≫ ν.app (Tc₁.obj ((Hc₁.obj (op E)).obj F, E)) =
      T₂.map (ν.app ((Hc₁.obj (op E)).obj F) ×ₘ ν.app E) ≫
        κ₂ (p.obj ((Hc₁.obj (op E)).obj F)) (p.obj E) ≫
          Q₂.map (mc.inv.app ((Hc₁.obj (op E)).obj F, E))) :
    P.map (Q₁.map (eqToHom (hHc₁ E F)) ≫ σ₁ E F) ≫
        homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m (Q₁.obj E) (Q₁.obj F) =
      ν.app ((Hc₁.obj (op E)).obj F) ≫
        Q₂.map (homComparison p Hc₁ Hc₂ Tc₁ Tc₂ ec₁ ec₂ mc E F) ≫
          (Q₂.map (eqToHom (hHc₂ (p.obj E) (p.obj F))) ≫ σ₂ (p.obj E) (p.obj F)) ≫
            (H₂.map (ν.app E).op).app (Q₂.obj (p.obj F)) ≫
              (H₂.obj (op (P.obj (Q₁.obj E)))).map νinv := by
  have key₁ : ∀ {A A' : C₁} (B W : C₁) (g : A ⟶ A') (x : T₁.obj (Q₁.obj A', Q₁.obj B) ⟶ Q₁.obj W)
      (ev : Tc₁.obj (A', B) ⟶ W) (hx : x = κ₁ A' B ≫ Q₁.map ev),
      T₁.map (Q₁.map g ×ₘ 𝟙 (Q₁.obj B)) ≫ x = κ₁ A B ≫ Q₁.map (Tc₁.map (g ×ₘ 𝟙 B) ≫ ev) := by
    intro A A' B W g x ev hx
    rw [hx, reassoc_of% (hκ₁ B g), Q₁.map_comp]
  have key₂ : ∀ {A A' : C₂} (B W : C₂) (g : A ⟶ A') (x : T₂.obj (Q₂.obj A', Q₂.obj B) ⟶ Q₂.obj W)
      (ev : Tc₂.obj (A', B) ⟶ W) (hx : x = κ₂ A' B ≫ Q₂.map ev),
      T₂.map (Q₂.map g ×ₘ 𝟙 (Q₂.obj B)) ≫ x = κ₂ A B ≫ Q₂.map (Tc₂.map (g ×ₘ 𝟙 B) ≫ ev) := by
    intro A A' B W g x ev hx
    rw [hx, reassoc_of% (hκ₂ B g), Q₂.map_comp]
  refine map_comp_homComparison_of_models hnat₁ hnat₂ hdin₂ htgt₂ hnatc₂
    (fun A B => Q₁.map (eqToHom (hHc₁ A B)) ≫ σ₁ A B)
    (fun A B => Q₂.map (eqToHom (hHc₂ A B)) ≫ σ₂ A B) κ₁ κ₂ E F νinv hνinv ?_ ?_ ?_ hm
  · rw [hnat₁, key₁ _ _ _ _ _ hσ₁, hev₁]
  · rw [hnat₂, key₂ _ _ _ _ _ hσ₂, hev₂]
  · exact hκ₂ _ _

/-- An `eqToHom` is invertible. -/
private instance isIso_eqToHom' {C : Type*} [Category C] {A B : C} (e : A = B) :
    IsIso (eqToHom e) :=
  ⟨⟨eqToHom e.symm, by simp, by simp⟩⟩

/-- A morphism `g` with `f ≫ g` invertible and `f` invertible is invertible. -/
private lemma isIso_of_comp_eq {C : Type*} [Category C] {A X W : C} (f : A ⟶ X) (g : X ⟶ W)
    (k : A ⟶ W) [IsIso f] [IsIso k] (h : f ≫ g = k) : IsIso g := by
  rw [show g = inv f ≫ k by rw [← h]; simp]
  infer_instance

/-- **Invertibility of the comparison of a functor with internal hom, from models.**  Under the
hypotheses of `map_comp_homComparison_of_models'`, if the comparisons `σᵢ` are invertible,
`ν` is invertible at `E`, at `F` and at the internal Hom of the models, and the comparison of the
models becomes invertible under `Q₂`, then the comparison of `P` at `(Q₁E, Q₁F)` is invertible. -/
theorem isIso_homComparison_of_models
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁) (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (hdin₂ : TensorHomEquivDinatural H₂ T₂ e₂)
    (htgt₂ : EquivalenceTranspose.CurriedTargetNatural H₂ T₂ e₂)
    (hnatc₂ : TensorHomEquivNaturalLeft Hc₂ Tc₂ ec₂)
    (hc₁ : C₁ → C₁ → C₁) (hHc₁ : ∀ A B, (Hc₁.obj (op A)).obj B = hc₁ A B)
    (hc₂ : C₂ → C₂ → C₂) (hHc₂ : ∀ A B, (Hc₂.obj (op A)).obj B = hc₂ A B)
    (σ₁ : ∀ A B : C₁, Q₁.obj (hc₁ A B) ⟶ (H₁.obj (op (Q₁.obj A))).obj (Q₁.obj B))
    (σ₂ : ∀ A B : C₂, Q₂.obj (hc₂ A B) ⟶ (H₂.obj (op (Q₂.obj A))).obj (Q₂.obj B))
    (κ₁ : ∀ A B : C₁, T₁.obj (Q₁.obj A, Q₁.obj B) ⟶ Q₁.obj (Tc₁.obj (A, B)))
    (κ₂ : ∀ A B : C₂, T₂.obj (Q₂.obj A, Q₂.obj B) ⟶ Q₂.obj (Tc₂.obj (A, B)))
    (hκ₁ : ∀ {A A' : C₁} (B : C₁) (g : A ⟶ A'),
      T₁.map (Q₁.map g ×ₘ 𝟙 (Q₁.obj B)) ≫ κ₁ A' B = κ₁ A B ≫ Q₁.map (Tc₁.map (g ×ₘ 𝟙 B)))
    (hκ₂ : ∀ {A A' : C₂} (B : C₂) (g : A ⟶ A'),
      T₂.map (Q₂.map g ×ₘ 𝟙 (Q₂.obj B)) ≫ κ₂ A' B = κ₂ A B ≫ Q₂.map (Tc₂.map (g ×ₘ 𝟙 B)))
    (E F : C₁)
    (ev₁ : Tc₁.obj (hc₁ E F, E) ⟶ F)
    (hev₁ : Tc₁.map (eqToHom (hHc₁ E F) ×ₘ 𝟙 E) ≫ ev₁ = evaluation Hc₁ Tc₁ ec₁ E F)
    (ev₂ : Tc₂.obj (hc₂ (p.obj E) (p.obj F), p.obj E) ⟶ p.obj F)
    (hev₂ : Tc₂.map (eqToHom (hHc₂ (p.obj E) (p.obj F)) ×ₘ 𝟙 (p.obj E)) ≫ ev₂ =
      evaluation Hc₂ Tc₂ ec₂ (p.obj E) (p.obj F))
    (hσ₁ : e₁ _ _ _ (σ₁ E F) = κ₁ (hc₁ E F) E ≫ Q₁.map ev₁)
    (hσ₂ : e₂ _ _ _ (σ₂ (p.obj E) (p.obj F)) =
      κ₂ (hc₂ (p.obj E) (p.obj F)) (p.obj E) ≫ Q₂.map ev₂)
    (hm : m.inv.app (Q₁.obj ((Hc₁.obj (op E)).obj F), Q₁.obj E) ≫
        P.map (κ₁ ((Hc₁.obj (op E)).obj F) E) ≫ ν.app (Tc₁.obj ((Hc₁.obj (op E)).obj F, E)) =
      T₂.map (ν.app ((Hc₁.obj (op E)).obj F) ×ₘ ν.app E) ≫
        κ₂ (p.obj ((Hc₁.obj (op E)).obj F)) (p.obj E) ≫
          Q₂.map (mc.inv.app ((Hc₁.obj (op E)).obj F, E)))
    [IsIso (σ₁ E F)] [IsIso (σ₂ (p.obj E) (p.obj F))] [IsIso (ν.app F)] [IsIso (ν.app E)]
    [IsIso (ν.app ((Hc₁.obj (op E)).obj F))]
    [IsIso (Q₂.map (homComparison p Hc₁ Hc₂ Tc₁ Tc₂ ec₁ ec₂ mc E F))] :
    IsIso (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m (Q₁.obj E) (Q₁.obj F)) :=
  isIso_of_comp_eq _ _ _ (map_comp_homComparison_of_models' hnat₁ hnat₂ hdin₂ htgt₂ hnatc₂
    hc₁ hHc₁ hc₂ hHc₂ σ₁ σ₂ κ₁ κ₂ hκ₁ hκ₂ E F (inv (ν.app F)) (IsIso.hom_inv_id _) ev₁ hev₁
    ev₂ hev₂ hσ₁ hσ₂ hm)

end Models

section Equivalence

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)

/-- **The evaluation out of an object by which tensoring is an equivalence is an isomorphism.**
If `- ⊗ A` is an equivalence, then `hom(A, B) ⊗ A ⟶ B` is invertible. -/
theorem isIso_evaluation_of_isEquivalence {D : Type*} [Category D] (H : Dᵒᵖ ⥤ D ⥤ D)
    (T : D × D ⥤ D) (e : ∀ A B C : D, (A ⟶ (H.obj (op B)).obj C) ≃ (T.obj (A, B) ⟶ C))
    (hnat : TensorHomEquivNaturalLeft H T e) (A : D)
    [(Stacks.ProjectionFormula.tensorRightOf T A).IsEquivalence] (B : D) :
    IsIso (evaluation H T e A B) := by
  let F := Stacks.ProjectionFormula.tensorRightOf T A
  have hF : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  have key : ∀ W : D, Function.Bijective
      (fun x : F.obj W ⟶ F.obj ((H.obj (op A)).obj B) => x ≫ evaluation H T e A B) := fun W => by
    have hcomp : (fun x : F.obj W ⟶ F.obj ((H.obj (op A)).obj B) =>
        x ≫ evaluation H T e A B) = (e W A B) ∘ hF.homEquiv.symm := by
      funext x
      have hn := hnat W ((H.obj (op A)).obj B) A B (hF.preimage x) (𝟙 _)
      rw [Category.comp_id] at hn
      exact (congrArg (· ≫ evaluation H T e A B) (hF.map_preimage x).symm).trans hn.symm
    rw [hcomp]
    exact (e W A B).bijective.comp hF.homEquiv.symm.bijective
  refine isIso_of_yoneda_map_bijective _ fun Z => ?_
  let i : F.obj (F.objPreimage Z) ≅ Z := F.objObjPreimageIso Z
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · have hab' : (i.hom ≫ a) ≫ evaluation H T e A B = (i.hom ≫ b) ≫ evaluation H T e A B := by
      simp only [Category.assoc]
      exact congrArg (i.hom ≫ ·) hab
    exact (cancel_epi i.hom).1 ((key _).1 hab')
  · obtain ⟨x', hx'⟩ := (key (F.objPreimage Z)).2 (i.hom ≫ y)
    exact ⟨i.inv ≫ x', (Category.assoc _ _ _).trans
      ((congrArg (i.inv ≫ ·) hx').trans (Iso.inv_hom_id_assoc i y))⟩

/-- **The comparison of a functor with internal hom is invertible at an object by which
tensoring is an equivalence**, as soon as tensoring by its image is an equivalence too. -/
theorem isIso_homComparison_of_isEquivalence
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁) (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (A : D₁) [(Stacks.ProjectionFormula.tensorRightOf T₁ A).IsEquivalence]
    [(Stacks.ProjectionFormula.tensorRightOf T₂ (P.obj A)).IsEquivalence] (B : D₁) :
    IsIso (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) := by
  have := isIso_evaluation_of_isEquivalence H₁ T₁ e₁ hnat₁ A B
  have := isIso_evaluation_of_isEquivalence H₂ T₂ e₂ hnat₂ (P.obj A) (P.obj B)
  have : IsIso (m.inv.app ((H₁.obj (op A)).obj B, A)) := Iso.isIso_inv (m.app _)
  have : IsIso (P.map (evaluation H₁ T₁ e₁ A B)) := Functor.map_isIso _ _
  have hT : IsIso ((Stacks.ProjectionFormula.tensorRightOf T₂ (P.obj A)).map
      (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B)) := by
    have : IsIso (T₂.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ×ₘ 𝟙 (P.obj A)) ≫
        evaluation H₂ T₂ e₂ (P.obj A) (P.obj B)) := by
      rw [tensor_map_homComparison_comp_evaluation P H₁ H₂ T₁ T₂ e₁ e₂ m hnat₂]; infer_instance
    exact IsIso.of_isIso_comp_right
      (T₂.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ×ₘ 𝟙 (P.obj A)))
      (evaluation H₂ T₂ e₂ (P.obj A) (P.obj B))
  exact isIso_of_reflects_iso _ (Stacks.ProjectionFormula.tensorRightOf T₂ (P.obj A))

end Equivalence

section Target

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)

/-- **The comparison of a functor with internal hom is natural in its target variable.** -/
theorem homComparison_naturality_target
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (htgt₁ : EquivalenceTranspose.CurriedTargetNatural H₁ T₁ e₁)
    (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (htgt₂ : EquivalenceTranspose.CurriedTargetNatural H₂ T₂ e₂)
    (A : D₁) {B B' : D₁} (k : B ⟶ B') :
    P.map ((H₁.obj (op A)).map k) ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B' =
      homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ≫ (H₂.obj (op (P.obj A))).map (P.map k) := by
  apply (e₂ _ _ _).injective
  rw [hnat₂, homComparison_adjoint, htgt₂, homComparison_adjoint, homComparisonDatum,
    homComparisonDatum]
  have hev : T₁.map ((H₁.obj (op A)).map k ×ₘ 𝟙 A) ≫ evaluation H₁ T₁ e₁ A B' =
      evaluation H₁ T₁ e₁ A B ≫ k := by
    have h₁ := hnat₁ _ _ A B' ((H₁.obj (op A)).map k) (𝟙 _)
    have h₂ := htgt₁ ((H₁.obj (op A)).obj B) A B B' k (𝟙 _)
    rw [Category.comp_id] at h₁
    rw [Category.id_comp] at h₂
    rw [evaluation, evaluation, ← h₁, h₂]
  rw [reassoc_of% (tensor_map_comp_monoidality_inv P T₁ T₂ m ((H₁.obj (op A)).map k) A),
    ← P.map_comp, hev, P.map_comp, Category.assoc]

end Target

end Stacks.Cohomology.DerivedInternalHomPullback.Transpose

end
