module

public import Mathlib.CategoryTheory.NatIso

/-!
# Pushing a cocycle condition forward along comparison functors

Let `c_k : D_k ⥤ E_k` (`k = 0, 1, 2`) be functors intertwining functors `F_i : D₀ ⥤ D₁`,
`F'_j : D₁ ⥤ D₂` with `G_i : E₀ ⥤ E₁`, `G'_j : E₁ ⥤ E₂`, and let identifications `P_{ij}` of the
composites `F'_j F_i` on the `D_k` and `Q_{ij}` of the composites `G'_j G_i` on the `E_k` be
compatible. If `α : F₁ K ≅ F₀ K` satisfies the cocycle condition read through the `P_{ij}`, its
image `T₁⁻¹ ≫ c₁ α ≫ T₀ : G₁ (c₀ K) ≅ G₀ (c₀ K)` satisfies the cocycle condition read through
the `Q_{ij}`. No faithfulness is needed in this direction (compare
`CategoryTheory.cocycle_of_faithful`).

## Main results

* `CategoryTheory.comp_inv_app_eq_of_comparison`, `CategoryTheory.cocycle_of_comparison`.
-/

@[expose] public section

namespace CategoryTheory

universe v₀ v₁ v₂ w₀ w₁ w₂ u₀ u₁ u₂ t₀ t₁ t₂

variable {D₀ : Type u₀} {D₁ : Type u₁} {D₂ : Type u₂} [Category.{v₀} D₀] [Category.{v₁} D₁]
  [Category.{v₂} D₂] {E₀ : Type t₀} {E₁ : Type t₁} {E₂ : Type t₂} [Category.{w₀} E₀]
  [Category.{w₁} E₁] [Category.{w₂} E₂]

/-- A compatibility at `K` through `t` solves for `Q.hom` at `c₀ K`. -/
private theorem hom_app_eq_of_comparison {c₀ : D₀ ⥤ E₀} {c₁ : D₁ ⥤ E₁} {c₂ : D₂ ⥤ E₂}
    {F : D₀ ⥤ D₁} {F' : D₁ ⥤ D₂} {G : E₀ ⥤ E₁} {G' : E₁ ⥤ E₂} {L : D₀ ⥤ D₂} {H : E₀ ⥤ E₂}
    {T : F ⋙ c₁ ≅ c₀ ⋙ G} {S : F' ⋙ c₂ ≅ c₁ ⋙ G'} {Q : G ⋙ G' ≅ H} {P : F ⋙ F' ≅ L}
    {t : L ⋙ c₂ ≅ c₀ ⋙ H} {K : D₀}
    (h : c₂.map (P.hom.app K) ≫ t.hom.app K =
      S.hom.app (F.obj K) ≫ G'.map (T.hom.app K) ≫ Q.hom.app (c₀.obj K)) :
    Q.hom.app (c₀.obj K) =
      G'.map (T.inv.app K) ≫ S.inv.app (F.obj K) ≫ c₂.map (P.hom.app K) ≫ t.hom.app K := by
  rw [h, Iso.inv_hom_id_app_assoc, ← G'.map_comp_assoc, Iso.inv_hom_id_app, G'.map_id,
    Category.id_comp]

/-- **Two compatible identifications through the same comparison, composed.** Let
`P : F ⋙ F' ≅ L`, `P₂ : F₂ ⋙ F'₂ ≅ L` on the `D_k` and `Q : G ⋙ G' ≅ H`, `Q₂ : G₂ ⋙ G'₂ ≅ H` on
the `E_k` be compatible at `K` through `t : L ⋙ c₂ ≅ c₀ ⋙ H` and the comparisons `T`, `T₂`, `S`,
`S₂`. Then `Q ≫ Q₂⁻¹` at `c₀ K` is `c₂(P ≫ P₂⁻¹)` read through the comparisons. -/
theorem comp_inv_app_eq_of_comparison {c₀ : D₀ ⥤ E₀} {c₁ : D₁ ⥤ E₁} {c₂ : D₂ ⥤ E₂}
    {F F₂ : D₀ ⥤ D₁} {F' F'₂ : D₁ ⥤ D₂} {G G₂ : E₀ ⥤ E₁} {G' G'₂ : E₁ ⥤ E₂} {L : D₀ ⥤ D₂}
    {H : E₀ ⥤ E₂} {T : F ⋙ c₁ ≅ c₀ ⋙ G} {T₂ : F₂ ⋙ c₁ ≅ c₀ ⋙ G₂}
    {S : F' ⋙ c₂ ≅ c₁ ⋙ G'} {S₂ : F'₂ ⋙ c₂ ≅ c₁ ⋙ G'₂} {Q : G ⋙ G' ≅ H} {Q₂ : G₂ ⋙ G'₂ ≅ H}
    {P : F ⋙ F' ≅ L} {P₂ : F₂ ⋙ F'₂ ≅ L} {t : L ⋙ c₂ ≅ c₀ ⋙ H} {K : D₀}
    (h : c₂.map (P.hom.app K) ≫ t.hom.app K =
      S.hom.app (F.obj K) ≫ G'.map (T.hom.app K) ≫ Q.hom.app (c₀.obj K))
    (h₂ : c₂.map (P₂.hom.app K) ≫ t.hom.app K =
      S₂.hom.app (F₂.obj K) ≫ G'₂.map (T₂.hom.app K) ≫ Q₂.hom.app (c₀.obj K)) :
    Q.hom.app (c₀.obj K) ≫ Q₂.inv.app (c₀.obj K) =
      G'.map (T.inv.app K) ≫ S.inv.app (F.obj K) ≫ c₂.map (P.hom.app K) ≫
        c₂.map (P₂.inv.app K) ≫ S₂.hom.app (F₂.obj K) ≫ G'₂.map (T₂.hom.app K) := by
  have hQ := hom_app_eq_of_comparison h
  have hQ₂ := hom_app_eq_of_comparison h₂
  rw [← cancel_mono (Q₂.hom.app (c₀.obj K))]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [hQ, hQ₂, ← Iso.app_hom T₂ K, ← Iso.app_inv T₂ K, Iso.map_hom_inv_id_assoc,
    Iso.hom_inv_id_app_assoc, ← Iso.app_hom P₂ K, ← Iso.app_inv P₂ K, Iso.map_inv_hom_id_assoc]

/-- **Transport of the cocycle condition forward along comparison functors.** Let
`c_k : D_k ⥤ E_k` intertwine `F_i : D₀ ⥤ D₁`, `F'_j : D₁ ⥤ D₂` with `G_i`, `G'_j` through `T_i`,
`S_j`, and let the composites `Q_{11} ≫ Q_{12}⁻¹`, `Q_{02} ≫ Q_{10}⁻¹`, `Q_{00} ≫ Q_{01}⁻¹` of the
identifications on the `E_k` at `c₀ K` be those of identifications `P_{ij}` on the `D_k`, read
through the comparisons (`CategoryTheory.comp_inv_app_eq_of_comparison`). If `α : F₁ K ≅ F₀ K`
satisfies the cocycle condition through the `P_{ij}`, then `α' = T₁⁻¹ ≫ c₁ α ≫ T₀` satisfies the
cocycle condition through the `Q_{ij}`. -/
theorem cocycle_of_comparison {c₀ : D₀ ⥤ E₀} {c₁ : D₁ ⥤ E₁} {c₂ : D₂ ⥤ E₂}
    {F₀ F₁ : D₀ ⥤ D₁} {F'₀ F'₁ F'₂ : D₁ ⥤ D₂} {G₀ G₁ : E₀ ⥤ E₁} {G'₀ G'₁ G'₂ : E₁ ⥤ E₂}
    {L₀ L₁ L₂ : D₀ ⥤ D₂} {H₀ H₁ H₂ : E₀ ⥤ E₂}
    {T₀ : F₀ ⋙ c₁ ≅ c₀ ⋙ G₀} {T₁ : F₁ ⋙ c₁ ≅ c₀ ⋙ G₁}
    {S₀ : F'₀ ⋙ c₂ ≅ c₁ ⋙ G'₀} {S₁ : F'₁ ⋙ c₂ ≅ c₁ ⋙ G'₁} {S₂ : F'₂ ⋙ c₂ ≅ c₁ ⋙ G'₂}
    {Q₁₁ : G₁ ⋙ G'₁ ≅ H₀} {Q₁₂ : G₁ ⋙ G'₂ ≅ H₀} {Q₀₂ : G₀ ⋙ G'₂ ≅ H₁} {Q₁₀ : G₁ ⋙ G'₀ ≅ H₁}
    {Q₀₀ : G₀ ⋙ G'₀ ≅ H₂} {Q₀₁ : G₀ ⋙ G'₁ ≅ H₂}
    {P₁₁ : F₁ ⋙ F'₁ ≅ L₀} {P₁₂ : F₁ ⋙ F'₂ ≅ L₀} {P₀₂ : F₀ ⋙ F'₂ ≅ L₁} {P₁₀ : F₁ ⋙ F'₀ ≅ L₁}
    {P₀₀ : F₀ ⋙ F'₀ ≅ L₂} {P₀₁ : F₀ ⋙ F'₁ ≅ L₂} {K : D₀}
    (hA : Q₁₁.hom.app (c₀.obj K) ≫ Q₁₂.inv.app (c₀.obj K) =
      G'₁.map (T₁.inv.app K) ≫ S₁.inv.app (F₁.obj K) ≫ c₂.map (P₁₁.hom.app K) ≫
        c₂.map (P₁₂.inv.app K) ≫ S₂.hom.app (F₁.obj K) ≫ G'₂.map (T₁.hom.app K))
    (hB : Q₀₂.hom.app (c₀.obj K) ≫ Q₁₀.inv.app (c₀.obj K) =
      G'₂.map (T₀.inv.app K) ≫ S₂.inv.app (F₀.obj K) ≫ c₂.map (P₀₂.hom.app K) ≫
        c₂.map (P₁₀.inv.app K) ≫ S₀.hom.app (F₁.obj K) ≫ G'₀.map (T₁.hom.app K))
    (hC : Q₀₀.hom.app (c₀.obj K) ≫ Q₀₁.inv.app (c₀.obj K) =
      G'₀.map (T₀.inv.app K) ≫ S₀.inv.app (F₀.obj K) ≫ c₂.map (P₀₀.hom.app K) ≫
        c₂.map (P₀₁.inv.app K) ≫ S₁.hom.app (F₀.obj K) ≫ G'₁.map (T₀.hom.app K))
    (α : F₁.obj K ≅ F₀.obj K)
    (hα : F'₁.map α.hom = P₁₁.hom.app K ≫ P₁₂.inv.app K ≫ F'₂.map α.hom ≫ P₀₂.hom.app K ≫
      P₁₀.inv.app K ≫ F'₀.map α.hom ≫ P₀₀.hom.app K ≫ P₀₁.inv.app K)
    (α' : G₁.obj (c₀.obj K) ≅ G₀.obj (c₀.obj K))
    (hα' : α'.hom = T₁.inv.app K ≫ c₁.map α.hom ≫ T₀.hom.app K) :
    G'₁.map α'.hom = Q₁₁.hom.app (c₀.obj K) ≫ Q₁₂.inv.app (c₀.obj K) ≫ G'₂.map α'.hom ≫
      Q₀₂.hom.app (c₀.obj K) ≫ Q₁₀.inv.app (c₀.obj K) ≫ G'₀.map α'.hom ≫
        Q₀₀.hom.app (c₀.obj K) ≫ Q₀₁.inv.app (c₀.obj K) := by
  rw [hα']
  have ghi : ∀ {G' : E₁ ⥤ E₂} {G : E₀ ⥤ E₁} {F : D₀ ⥤ D₁} (T : F ⋙ c₁ ≅ c₀ ⋙ G)
      {Y : E₂} (y : G'.obj (F ⋙ c₁ |>.obj K) ⟶ Y),
      G'.map (T.hom.app K) ≫ G'.map (T.inv.app K) ≫ y = y := fun {G' G F} T {Y} y ↦ by
    rw [← G'.map_comp_assoc, Iso.hom_inv_id_app, G'.map_id, Category.id_comp]
  have hF : ∀ {F' : D₁ ⥤ D₂} {G' : E₁ ⥤ E₂} (S : F' ⋙ c₂ ≅ c₁ ⋙ G') {A B : D₁} (x : A ⟶ B),
      G'.map (c₁.map x) = S.inv.app A ≫ c₂.map (F'.map x) ≫ S.hom.app B :=
    fun {F' G'} S {A B} x ↦ (NatIso.naturality_1 S x).symm
  simp only [Functor.map_comp, Category.assoc, hF S₀, hF S₁, hF S₂, hα, reassoc_of% hA,
    reassoc_of% hB, hC, Iso.hom_inv_id_app_assoc, ghi]

end CategoryTheory
