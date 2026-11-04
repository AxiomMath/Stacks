module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility
public import StacksFrontier.CategoryTheory.BifunctorProdMap

/-!
# The comparison of a functor with internal hom, on `K ⊗ hom(E, 𝟙)`

Let `P : D₁ ⥤ D₂` carry the data of the transpose construction of Tag 08I3: internal homs
`H₁, H₂`, tensor products `T₁, T₂` on pairs, tensor–hom bijections `e₁, e₂` and a monoidality
comparison `m : P(A ⊗ B) ≅ P A ⊗ P B`.  Suppose moreover that each side has an associativity
morphism `a` and a unit object `𝟙` with a right unit morphism `u`, and that `P` is monoidal for
them through `m` and a morphism `ν : P 𝟙 ⟶ 𝟙`.

For objects `E`, `K` there is a canonical map

`K ⊗ hom(E, 𝟙) ⟶ hom(E, K)`,

the transpose of `(K ⊗ hom(E, 𝟙)) ⊗ E ⟶ K ⊗ (hom(E, 𝟙) ⊗ E) ⟶ K ⊗ 𝟙 ⟶ K`.  This file proves
that `P` carries it, followed by the comparison `P hom(E, K) ⟶ hom(P E, P K)`, to the map of the
same kind for `P E` and `P K`, preceded by `m` and by the comparison
`P hom(E, 𝟙) ⟶ hom(P E, P 𝟙) ⟶ hom(P E, 𝟙)` on the dual.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.dualTensorMap`: the map
  `K ⊗ hom(E, 𝟙) ⟶ hom(E, K)`.
* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.dualComparison`: the comparison
  `P hom(E, 𝟙) ⟶ hom(P E, 𝟙)`.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.map_dualTensorMap_comp_homComparison`:
  `P` carries `dualTensorMap`, followed by the comparison with internal hom, to `dualTensorMap`
  of the images, preceded by `m` and by the comparison on the dual.
* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.dualTensorMap_naturality`:
  `dualTensorMap` is natural in `K`.
* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.map_comp_homComparison`: `P` carries
  the composition of internal homs to composition, through the comparison with internal hom.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback.Transpose

section OneCategory

variable {D : Type*} [Category D] (H : Dᵒᵖ ⥤ D ⥤ D) (T : D × D ⥤ D)
  (e : ∀ A B C : D, (A ⟶ (H.obj (op B)).obj C) ≃ (T.obj (A, B) ⟶ C))
  (a : ∀ A B C : D, T.obj (T.obj (A, B), C) ⟶ T.obj (A, T.obj (B, C)))
  (I : D) (u : ∀ W : D, T.obj (W, I) ⟶ W)

/-- **The map `K ⊗ hom(E, 𝟙) ⟶ hom(E, K)`**: the transpose of the composite
`(K ⊗ hom(E, 𝟙)) ⊗ E ⟶ K ⊗ (hom(E, 𝟙) ⊗ E) ⟶ K ⊗ 𝟙 ⟶ K` of the associativity morphism, the
evaluation and the right unit morphism. -/
def dualTensorMap (E K : D) : T.obj (K, (H.obj (op E)).obj I) ⟶ (H.obj (op E)).obj K :=
  (e _ E K).symm (a K ((H.obj (op E)).obj I) E ≫ T.map (𝟙 K ×ₘ evaluation H T e E I) ≫ u K)

/-- The transpose of `dualTensorMap` is the composite it is defined from. -/
theorem dualTensorMap_adjoint (E K : D) :
    e _ E K (dualTensorMap H T e a I u E K) =
      a K ((H.obj (op E)).obj I) E ≫ T.map (𝟙 K ×ₘ evaluation H T e E I) ≫ u K :=
  (e _ E K).apply_symm_apply _

/-- **`dualTensorMap` is natural in `K`**, as soon as the bijection is natural in its source and
target variables and the associativity and unit morphisms are natural in their first
variable. -/
theorem dualTensorMap_naturality (hnat : TensorHomEquivNaturalLeft H T e)
    (htgt : ∀ (A B C C' : D) (f : A ⟶ (H.obj (op B)).obj C) (g : C ⟶ C'),
      e A B C' (f ≫ (H.obj (op B)).map g) = e A B C f ≫ g)
    (ha : ∀ {A A' : D} (f : A ⟶ A') (B C : D),
      T.map (T.map (f ×ₘ 𝟙 B) ×ₘ 𝟙 C) ≫ a A' B C = a A B C ≫ T.map (f ×ₘ 𝟙 (T.obj (B, C))))
    (hu : ∀ {W W' : D} (f : W ⟶ W'), T.map (f ×ₘ 𝟙 I) ≫ u W' = u W ≫ f)
    (E : D) {K K' : D} (f : K ⟶ K') :
    dualTensorMap H T e a I u E K ≫ (H.obj (op E)).map f =
      T.map (f ×ₘ 𝟙 _) ≫ dualTensorMap H T e a I u E K' := by
  apply (e _ E K').injective
  rw [htgt, hnat, dualTensorMap_adjoint, dualTensorMap_adjoint]
  have h1 : T.map (𝟙 K ×ₘ evaluation H T e E I) ≫ T.map (f ×ₘ 𝟙 I) =
      T.map (f ×ₘ 𝟙 _) ≫ T.map (𝟙 K' ×ₘ evaluation H T e E I) := by
    rw [← T.map_comp, ← T.map_comp, prod_comp, prod_comp]
    simp
  simp only [Category.assoc]
  rw [← hu f, reassoc_of% h1, reassoc_of% (ha f _ E)]

/-- Tensoring with `𝟙 B` and evaluating recovers the transpose, as soon as the bijection is
natural in its source variable. -/
private theorem map_prod_id_comp_evaluation (hnat : TensorHomEquivNaturalLeft H T e)
    {X B C : D} (f : X ⟶ (H.obj (op B)).obj C) :
    T.map (f ×ₘ 𝟙 B) ≫ evaluation H T e B C = e X B C f := by
  have hn := hnat X _ B C f (𝟙 _)
  rw [Category.comp_id] at hn
  exact hn.symm

/-- **The evaluation out of a unit is natural in the target.**  For a unit `A` of `T` with a
natural unitor `v`, the morphisms `hom(A, B) ⟶ B` given by the unitor followed by the evaluation
are natural in `B`, as soon as the bijection is natural in its source and target variables. -/
theorem unitEvaluation_naturality (hnat : TensorHomEquivNaturalLeft H T e)
    (htgt : ∀ (X B C C' : D) (f : X ⟶ (H.obj (op B)).obj C) (g : C ⟶ C'),
      e X B C' (f ≫ (H.obj (op B)).map g) = e X B C f ≫ g)
    (A : D) (v : ∀ W : D, T.obj (W, A) ≅ W)
    (hv : ∀ (W W' : D) (g : W ⟶ W'), T.map (g ×ₘ 𝟙 A) ≫ (v W').hom = (v W).hom ≫ g)
    {B B' : D} (g : B ⟶ B') :
    (H.obj (op A)).map g ≫ (v ((H.obj (op A)).obj B')).inv ≫ evaluation H T e A B' =
      ((v ((H.obj (op A)).obj B)).inv ≫ evaluation H T e A B) ≫ g := by
  have h1 : (H.obj (op A)).map g ≫ (v ((H.obj (op A)).obj B')).inv =
      (v ((H.obj (op A)).obj B)).inv ≫ T.map ((H.obj (op A)).map g ×ₘ 𝟙 A) := by
    rw [Iso.comp_inv_eq, Category.assoc, hv, Iso.inv_hom_id_assoc]
  have h2 : T.map ((H.obj (op A)).map g ×ₘ 𝟙 A) ≫ evaluation H T e A B' =
      evaluation H T e A B ≫ g := by
    have ht := htgt _ A B B' (𝟙 _) g
    rw [Category.id_comp] at ht
    exact (map_prod_id_comp_evaluation H T e hnat _).trans ht
  rw [reassoc_of% h1, h2, Category.assoc]

/-- **`dualTensorMap` for two right unit morphisms.**  For right unit morphisms `u` and `ρ`, with
`ρ'` a right inverse of `ρ K`, `dualTensorMap` for `u` is `dualTensorMap` for `ρ` followed by
`hom(E, ρ' ≫ u K)`. -/
theorem dualTensorMap_eq_dualTensorMap_comp
    (htgt : ∀ (A B C C' : D) (f : A ⟶ (H.obj (op B)).obj C) (g : C ⟶ C'),
      e A B C' (f ≫ (H.obj (op B)).map g) = e A B C f ≫ g)
    (ρ : ∀ W : D, T.obj (W, I) ⟶ W) (E K : D) (ρ' : K ⟶ T.obj (K, I)) (hρ : ρ K ≫ ρ' = 𝟙 _) :
    dualTensorMap H T e a I u E K =
      dualTensorMap H T e a I ρ E K ≫ (H.obj (op E)).map (ρ' ≫ u K) := by
  apply (e _ E K).injective
  rw [htgt, dualTensorMap_adjoint, dualTensorMap_adjoint]
  simp only [Category.assoc, reassoc_of% hρ]

/-- **`dualTensorMap` from a transpose.**  If `μ : S ⟶ hom(E, K)` has transpose `r` in the sense
that `c ≫ μ` corresponds to `(c ⊗ E) ≫ r` for every `c`, and `c₀` carries the defining composite
of `dualTensorMap` to `r`, then `dualTensorMap` is `c₀ ≫ μ`. -/
theorem dualTensorMap_eq_of_transpose (E K : D) {S : D} (μ : S ⟶ (H.obj (op E)).obj K)
    (r : T.obj (S, E) ⟶ K)
    (hμ : ∀ (A : D) (c : A ⟶ S), e A E K (c ≫ μ) = T.map (c ×ₘ 𝟙 E) ≫ r)
    (c₀ : T.obj (K, (H.obj (op E)).obj I) ⟶ S)
    (hr : T.map (c₀ ×ₘ 𝟙 E) ≫ r =
      a K ((H.obj (op E)).obj I) E ≫ T.map (𝟙 K ×ₘ evaluation H T e E I) ≫ u K) :
    dualTensorMap H T e a I u E K = c₀ ≫ μ := by
  apply (e _ E K).injective
  rw [dualTensorMap_adjoint, hμ, hr]

end OneCategory

section TwoCategories

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)
  (a₁ : ∀ A B C : D₁, T₁.obj (T₁.obj (A, B), C) ⟶ T₁.obj (A, T₁.obj (B, C)))
  (a₂ : ∀ A B C : D₂, T₂.obj (T₂.obj (A, B), C) ⟶ T₂.obj (A, T₂.obj (B, C)))
  (I₁ : D₁) (I₂ : D₂) (u₁ : ∀ W : D₁, T₁.obj (W, I₁) ⟶ W) (u₂ : ∀ W : D₂, T₂.obj (W, I₂) ⟶ W)
  (ν : P.obj I₁ ⟶ I₂)

/-- **The comparison on the dual**, `P hom(E, 𝟙) ⟶ hom(P E, P 𝟙) ⟶ hom(P E, 𝟙)`: the comparison
of `P` with internal hom followed by `ν`. -/
def dualComparison (E : D₁) :
    P.obj ((H₁.obj (op E)).obj I₁) ⟶ (H₂.obj (op (P.obj E))).obj I₂ :=
  homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m E I₁ ≫ (H₂.obj (op (P.obj E))).map ν

/-- The inverse of the monoidality comparison is natural in the first variable. -/
private theorem m_inv_naturality_left {A A' : D₁} (f : A ⟶ A') (B : D₁) :
    T₂.map (P.map f ×ₘ 𝟙 (P.obj B)) ≫ m.inv.app (A', B) =
      m.inv.app (A, B) ≫ P.map (T₁.map (f ×ₘ 𝟙 B)) := by
  have h := m.inv.naturality (f ×ₘ 𝟙 B)
  dsimp only [Functor.comp_map, Functor.prod_map] at h
  rwa [P.map_id] at h

/-- The monoidality comparison is natural in the second variable. -/
private theorem m_hom_naturality_right (A : D₁) {B B' : D₁} (g : B ⟶ B') :
    P.map (T₁.map (𝟙 A ×ₘ g)) ≫ m.hom.app (A, B') =
      m.hom.app (A, B) ≫ T₂.map (𝟙 (P.obj A) ×ₘ P.map g) := by
  have h := m.hom.naturality (𝟙 A ×ₘ g)
  dsimp only [Functor.comp_map, Functor.prod_map] at h
  rwa [P.map_id] at h

/-- The two whiskerings of `m.hom` and `m.inv` by `𝟙 X` are mutually inverse. -/
private theorem map_prod_hom_inv_app (X : D₂) (B C : D₁) :
    T₂.map (𝟙 X ×ₘ m.hom.app (B, C)) ≫ T₂.map (𝟙 X ×ₘ m.inv.app (B, C)) = 𝟙 _ := by
  rw [← T₂.map_comp, prod_comp, Category.comp_id, Iso.hom_inv_id_app]
  exact T₂.map_id _

/-- **`P` carries `dualTensorMap`, followed by the comparison with internal hom, to
`dualTensorMap` of the images, preceded by `m` and the comparison on the dual.** -/
theorem map_dualTensorMap_comp_homComparison
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁) (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (htgt₂ : ∀ (A B C C' : D₂) (f : A ⟶ (H₂.obj (op B)).obj C) (g : C ⟶ C'),
      e₂ A B C' (f ≫ (H₂.obj (op B)).map g) = e₂ A B C f ≫ g)
    (ha₂ : ∀ (A : D₂) {B B' : D₂} (g : B ⟶ B') (C : D₂),
      T₂.map (T₂.map (𝟙 A ×ₘ g) ×ₘ 𝟙 C) ≫ a₂ A B' C =
        a₂ A B C ≫ T₂.map (𝟙 A ×ₘ T₂.map (g ×ₘ 𝟙 C)))
    (hassoc : ∀ A B C : D₁,
      m.hom.app (T₁.obj (A, B), C) ≫ T₂.map (m.hom.app (A, B) ×ₘ 𝟙 (P.obj C)) ≫
          a₂ (P.obj A) (P.obj B) (P.obj C) =
        P.map (a₁ A B C) ≫ m.hom.app (A, T₁.obj (B, C)) ≫
          T₂.map (𝟙 (P.obj A) ×ₘ m.hom.app (B, C)))
    (hunit : ∀ W : D₁,
      m.hom.app (W, I₁) ≫ T₂.map (𝟙 (P.obj W) ×ₘ ν) ≫ u₂ (P.obj W) = P.map (u₁ W))
    (E K : D₁) :
    P.map (dualTensorMap H₁ T₁ e₁ a₁ I₁ u₁ E K) ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m E K =
      m.hom.app (K, (H₁.obj (op E)).obj I₁) ≫
        T₂.map (𝟙 (P.obj K) ×ₘ dualComparison P H₁ H₂ T₁ T₂ e₁ e₂ m I₁ I₂ ν E) ≫
          dualTensorMap H₂ T₂ e₂ a₂ I₂ u₂ (P.obj E) (P.obj K) := by
  set Dl := (H₁.obj (op E)).obj I₁
  set ev₁ := evaluation H₁ T₁ e₁ E I₁
  set c := homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m E K
  set cI := homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m E I₁
  apply (e₂ _ (P.obj E) (P.obj K)).injective
  have hL : e₂ _ (P.obj E) (P.obj K) (P.map (dualTensorMap H₁ T₁ e₁ a₁ I₁ u₁ E K) ≫ c) =
      m.inv.app (T₁.obj (K, Dl), E) ≫
        P.map (a₁ K Dl E ≫ T₁.map (𝟙 K ×ₘ ev₁) ≫ u₁ K) := by
    rw [hnat₂, homComparison_adjoint]
    dsimp only [homComparisonDatum]
    rw [← Category.assoc, m_inv_naturality_left P T₁ T₂ m _ E, Category.assoc, ← P.map_comp]
    congr 2
    rw [map_prod_id_comp_evaluation H₁ T₁ e₁ hnat₁, dualTensorMap_adjoint]
  have hε : T₂.map (dualComparison P H₁ H₂ T₁ T₂ e₁ e₂ m I₁ I₂ ν E ×ₘ 𝟙 (P.obj E)) ≫
        evaluation H₂ T₂ e₂ (P.obj E) I₂ =
      m.inv.app (Dl, E) ≫ P.map ev₁ ≫ ν := by
    rw [map_prod_id_comp_evaluation H₂ T₂ e₂ hnat₂]
    dsimp only [dualComparison]
    rw [htgt₂, homComparison_adjoint]
    dsimp only [homComparisonDatum]
    simp only [Category.assoc]
    rfl
  have hR : e₂ _ (P.obj E) (P.obj K)
      (m.hom.app (K, Dl) ≫ T₂.map (𝟙 (P.obj K) ×ₘ dualComparison P H₁ H₂ T₁ T₂ e₁ e₂ m I₁ I₂ ν E) ≫
          dualTensorMap H₂ T₂ e₂ a₂ I₂ u₂ (P.obj E) (P.obj K)) =
      T₂.map (m.hom.app (K, Dl) ×ₘ 𝟙 (P.obj E)) ≫ a₂ (P.obj K) (P.obj Dl) (P.obj E) ≫
        T₂.map (𝟙 (P.obj K) ×ₘ (m.inv.app (Dl, E) ≫ P.map ev₁ ≫ ν)) ≫ u₂ (P.obj K) := by
    rw [hnat₂, hnat₂, dualTensorMap_adjoint,
      reassoc_of% (ha₂ (P.obj K) (dualComparison P H₁ H₂ T₁ T₂ e₁ e₂ m I₁ I₂ ν E) (P.obj E))]
    congr 2
    rw [← hε, ← T₂.map_comp_assoc, prod_comp, Category.id_comp]
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hm : P.map (T₁.map (𝟙 K ×ₘ ev₁)) ≫ m.hom.app (K, I₁) =
      m.hom.app (K, T₁.obj (Dl, E)) ≫ T₂.map (𝟙 (P.obj K) ×ₘ P.map ev₁) :=
    m_hom_naturality_right P T₁ T₂ m K ev₁
  have hA : P.map (a₁ K Dl E) ≫ m.hom.app (K, T₁.obj (Dl, E)) =
      m.hom.app (T₁.obj (K, Dl), E) ≫ T₂.map (m.hom.app (K, Dl) ×ₘ 𝟙 (P.obj E)) ≫
        a₂ (P.obj K) (P.obj Dl) (P.obj E) ≫ T₂.map (𝟙 (P.obj K) ×ₘ m.inv.app (Dl, E)) := by
    rw [reassoc_of% (hassoc K Dl E), map_prod_hom_inv_app P T₁ T₂ m (P.obj K) Dl E]
    exact P.map (a₁ K Dl E) ≫= (Category.comp_id _).symm
  rw [P.map_comp, P.map_comp, ← hunit K, reassoc_of% hm, reassoc_of% hA]
  simp only [Iso.inv_hom_id_app_assoc]
  congr 2
  rw [← T₂.map_comp_assoc, ← T₂.map_comp_assoc, prod_comp, prod_comp, Category.id_comp,
    Category.id_comp]
  simp only [Category.assoc]

/-- **`P` carries composition of internal homs to composition, through the comparison.**  If
the composition morphisms `cmp` of the two sides are the transposes of the double evaluation,
and `P` is monoidal for the associativity morphisms through `m`, then
`P(cmp) ≫ c = m ≫ (c ⊗ c) ≫ cmp`, where `c` is the comparison of `P` with internal hom. -/
theorem map_comp_homComparison
    (cmp₁ : ∀ A B C : D₁,
      T₁.obj ((H₁.obj (op B)).obj C, (H₁.obj (op A)).obj B) ⟶ (H₁.obj (op A)).obj C)
    (cmp₂ : ∀ A B C : D₂,
      T₂.obj ((H₂.obj (op B)).obj C, (H₂.obj (op A)).obj B) ⟶ (H₂.obj (op A)).obj C)
    (hcomp₁ : ∀ A B C : D₁,
      T₁.map (cmp₁ A B C ×ₘ 𝟙 A) ≫ evaluation H₁ T₁ e₁ A C =
        a₁ _ _ A ≫ T₁.map (𝟙 _ ×ₘ evaluation H₁ T₁ e₁ A B) ≫ evaluation H₁ T₁ e₁ B C)
    (hcomp₂ : ∀ A B C : D₂,
      T₂.map (cmp₂ A B C ×ₘ 𝟙 A) ≫ evaluation H₂ T₂ e₂ A C =
        a₂ _ _ A ≫ T₂.map (𝟙 _ ×ₘ evaluation H₂ T₂ e₂ A B) ≫ evaluation H₂ T₂ e₂ B C)
    (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (ha₂ : ∀ {A A' B B' : D₂} (x : A ⟶ A') (y : B ⟶ B') (C : D₂),
      T₂.map (T₂.map (x ×ₘ y) ×ₘ 𝟙 C) ≫ a₂ A' B' C = a₂ A B C ≫ T₂.map (x ×ₘ T₂.map (y ×ₘ 𝟙 C)))
    (hassoc : ∀ A B C : D₁,
      m.hom.app (T₁.obj (A, B), C) ≫ T₂.map (m.hom.app (A, B) ×ₘ 𝟙 (P.obj C)) ≫
          a₂ (P.obj A) (P.obj B) (P.obj C) =
        P.map (a₁ A B C) ≫ m.hom.app (A, T₁.obj (B, C)) ≫
          T₂.map (𝟙 (P.obj A) ×ₘ m.hom.app (B, C)))
    (A B C : D₁) :
    P.map (cmp₁ A B C) ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A C =
      m.hom.app ((H₁.obj (op B)).obj C, (H₁.obj (op A)).obj B) ≫
        T₂.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m B C ×ₘ
          homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) ≫
          cmp₂ (P.obj A) (P.obj B) (P.obj C) := by
  set HBC := (H₁.obj (op B)).obj C
  set HAB := (H₁.obj (op A)).obj B
  set cAB := homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B
  set cBC := homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m B C
  have hdat : ∀ (X Y : D₁), T₂.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m X Y ×ₘ 𝟙 (P.obj X)) ≫
      evaluation H₂ T₂ e₂ (P.obj X) (P.obj Y) =
      m.inv.app ((H₁.obj (op X)).obj Y, X) ≫ P.map (evaluation H₁ T₁ e₁ X Y) := by
    intro X Y
    rw [map_prod_id_comp_evaluation H₂ T₂ e₂ hnat₂, homComparison_adjoint]
    rfl
  apply (e₂ _ (P.obj A) (P.obj C)).injective
  have hL : e₂ _ (P.obj A) (P.obj C)
      (P.map (cmp₁ A B C) ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A C) =
      m.inv.app (T₁.obj (HBC, HAB), A) ≫
        P.map (a₁ HBC HAB A ≫ T₁.map (𝟙 HBC ×ₘ evaluation H₁ T₁ e₁ A B) ≫
          evaluation H₁ T₁ e₁ B C) := by
    rw [hnat₂, homComparison_adjoint]
    dsimp only [homComparisonDatum]
    rw [← Category.assoc, m_inv_naturality_left P T₁ T₂ m _ A, Category.assoc, ← P.map_comp,
      hcomp₁]
  have hR : e₂ _ (P.obj A) (P.obj C) (m.hom.app (HBC, HAB) ≫ T₂.map (cBC ×ₘ cAB) ≫
        cmp₂ (P.obj A) (P.obj B) (P.obj C)) =
      T₂.map (m.hom.app (HBC, HAB) ×ₘ 𝟙 (P.obj A)) ≫ a₂ (P.obj HBC) (P.obj HAB) (P.obj A) ≫
        T₂.map (𝟙 (P.obj HBC) ×ₘ (m.inv.app (HAB, A) ≫ P.map (evaluation H₁ T₁ e₁ A B))) ≫
          m.inv.app (HBC, B) ≫ P.map (evaluation H₁ T₁ e₁ B C) := by
    have hc := (map_prod_id_comp_evaluation H₂ T₂ e₂ hnat₂
      (cmp₂ (P.obj A) (P.obj B) (P.obj C))).symm.trans (hcomp₂ (P.obj A) (P.obj B) (P.obj C))
    rw [hnat₂, hnat₂, hc, reassoc_of% (ha₂ cBC cAB (P.obj A))]
    congr 2
    rw [← hdat A B, ← hdat B C, ← T₂.map_comp_assoc, ← T₂.map_comp_assoc, prod_comp, prod_comp]
    simp only [Category.comp_id, Category.id_comp]
    rfl
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hA : m.inv.app (T₁.obj (HBC, HAB), A) ≫ P.map (a₁ HBC HAB A) =
      T₂.map (m.hom.app (HBC, HAB) ×ₘ 𝟙 (P.obj A)) ≫ a₂ (P.obj HBC) (P.obj HAB) (P.obj A) ≫
        T₂.map (𝟙 (P.obj HBC) ×ₘ m.inv.app (HAB, A)) ≫ m.inv.app (HBC, T₁.obj (HAB, A)) := by
    rw [← cancel_epi (m.hom.app (T₁.obj (HBC, HAB), A)), Iso.hom_inv_id_app_assoc,
      reassoc_of% (hassoc HBC HAB A),
      reassoc_of% (map_prod_hom_inv_app P T₁ T₂ m (P.obj HBC) HAB A)]
    simp only [Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hm : m.inv.app (HBC, T₁.obj (HAB, A)) ≫ P.map (T₁.map (𝟙 HBC ×ₘ evaluation H₁ T₁ e₁ A B)) =
      T₂.map (𝟙 (P.obj HBC) ×ₘ P.map (evaluation H₁ T₁ e₁ A B)) ≫ m.inv.app (HBC, B) := by
    rw [← cancel_epi (m.hom.app (HBC, T₁.obj (HAB, A))), Iso.hom_inv_id_app_assoc,
      ← reassoc_of% (m_hom_naturality_right P T₁ T₂ m HBC (evaluation H₁ T₁ e₁ A B))]
    simp only [Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [P.map_comp, P.map_comp, reassoc_of% hA, reassoc_of% hm, ← T₂.map_comp_assoc, prod_comp,
    Category.id_comp]

/-- **The comparison at a tensor unit, read through the unit evaluations.**  If `A` is a unit
for `T₁` and `P A` a unit for `T₂`, with unitors compatible with `m`, then the comparison
`P hom(A, B) ⟶ hom(P A, P B)`, followed by the evaluation out of the unit, is `P` of the
evaluation out of the unit. -/
theorem homComparison_comp_unitEvaluation
    (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂)
    (A : D₁) (v₁ : ∀ W : D₁, T₁.obj (W, A) ≅ W) (v₂ : ∀ W : D₂, T₂.obj (W, P.obj A) ≅ W)
    (hv₂ : ∀ (W W' : D₂) (g : W ⟶ W'),
      T₂.map (g ×ₘ 𝟙 (P.obj A)) ≫ (v₂ W').hom = (v₂ W).hom ≫ g)
    (hcoh : ∀ W : D₁, m.hom.app (W, A) ≫ (v₂ (P.obj W)).hom = P.map (v₁ W).hom)
    (B : D₁) :
    homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ≫
        ((v₂ ((H₂.obj (op (P.obj A))).obj (P.obj B))).inv ≫
          evaluation H₂ T₂ e₂ (P.obj A) (P.obj B)) =
      P.map ((v₁ ((H₁.obj (op A)).obj B)).inv ≫ evaluation H₁ T₁ e₁ A B) := by
  have hstep1 : (v₂ (P.obj ((H₁.obj (op A)).obj B))).inv ≫
        T₂.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ×ₘ 𝟙 (P.obj A)) =
      homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ≫
        (v₂ ((H₂.obj (op (P.obj A))).obj (P.obj B))).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc,
      ← hv₂ (P.obj ((H₁.obj (op A)).obj B)) ((H₂.obj (op (P.obj A))).obj (P.obj B))
        (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B)]
    simp
  have hstep2 : T₂.map (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B ×ₘ 𝟙 (P.obj A)) ≫
        evaluation H₂ T₂ e₂ (P.obj A) (P.obj B) =
      homComparisonDatum P H₁ T₁ T₂ e₁ m A B := by
    rw [map_prod_id_comp_evaluation H₂ T₂ e₂ hnat₂, homComparison_adjoint]
  have hstep3 : (v₂ (P.obj ((H₁.obj (op A)).obj B))).inv ≫
      m.inv.app ((H₁.obj (op A)).obj B, A) = P.map (v₁ ((H₁.obj (op A)).obj B)).inv := by
    have hone : P.map (v₁ ((H₁.obj (op A)).obj B)).hom ≫
        (v₂ (P.obj ((H₁.obj (op A)).obj B))).inv ≫
          m.inv.app ((H₁.obj (op A)).obj B, A) = 𝟙 _ := by
      rw [← hcoh ((H₁.obj (op A)).obj B)]
      simp
    have htwo : P.map (v₁ ((H₁.obj (op A)).obj B)).hom ≫
        P.map (v₁ ((H₁.obj (op A)).obj B)).inv = 𝟙 _ := by
      rw [← P.map_comp, Iso.hom_inv_id, P.map_id]
    exact (cancel_epi (P.map (v₁ ((H₁.obj (op A)).obj B)).hom)).1 (hone.trans htwo.symm)
  have hdatum : homComparisonDatum P H₁ T₁ T₂ e₁ m A B =
      m.inv.app ((H₁.obj (op A)).obj B, A) ≫ P.map (evaluation H₁ T₁ e₁ A B) := rfl
  rw [← Category.assoc, ← hstep1, Category.assoc, hstep2, hdatum, P.map_comp, ← hstep3,
    Category.assoc]

end TwoCategories

end Stacks.Cohomology.DerivedInternalHomPullback.Transpose

end
