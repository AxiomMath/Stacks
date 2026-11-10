module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.NatIso

/-!
# Transport of a cocycle condition along comparison functors

Let `G_i : E₀ ⥤ E₁` (`i = 0, 1`) and `G'_j : E₁ ⥤ E₂` (`j = 0, 1, 2`) be functors, thought of as
pullbacks along the faces of a simplicial object, with identifications `Q_{ij} : G_i ⋙ G'_j ≅ H_v`
of the composites with the pullbacks `H_v` to the three vertices. An isomorphism
`α : G₁ L ≅ G₀ L` satisfies the *cocycle condition* when `G'₁ α` is the composite of `G'₂ α` and
`G'₀ α` read through the `Q_{ij}`.

## Main results

* `CategoryTheory.cocycle_conj`: the cocycle condition is transported along an isomorphism
  `e : L' ≅ L`.
* `CategoryTheory.cocycle_of_faithful`: given comparison functors `c_k : D_k ⥤ E_k` intertwining
  functors `F_i`, `F'_j` on the `D_k` with the `G_i`, `G'_j`, compatible with identifications
  `P_{ij}` on the `D_k`, and `c₂` faithful, an isomorphism `α'` with `c₁ α'` the conjugate of a
  cocycle `α` is a cocycle.
-/

@[expose] public section

namespace CategoryTheory

universe v₀ v₁ v₂ w₀ w₁ w₂ u₀ u₁ u₂ t₀ t₁ t₂

section

variable {E₀ : Type t₀} {E₁ : Type t₁} {E₂ : Type t₂} [Category.{w₀} E₀] [Category.{w₁} E₁]
  [Category.{w₂} E₂] {G₀ G₁ : E₀ ⥤ E₁} {G'₀ G'₁ G'₂ : E₁ ⥤ E₂} {H₀ H₁ H₂ : E₀ ⥤ E₂}
  (Q₁₁ : G₁ ⋙ G'₁ ≅ H₀) (Q₁₂ : G₁ ⋙ G'₂ ≅ H₀) (Q₀₂ : G₀ ⋙ G'₂ ≅ H₁) (Q₁₀ : G₁ ⋙ G'₀ ≅ H₁)
  (Q₀₀ : G₀ ⋙ G'₀ ≅ H₂) (Q₀₁ : G₀ ⋙ G'₁ ≅ H₂)

omit [Category.{w₂} E₂] in
private theorem map_map_inv_hom_assoc {G : E₀ ⥤ E₁} {E₂' : Type t₂} [Category.{w₂} E₂']
    (G' : E₁ ⥤ E₂') {L L' : E₀} (e : L' ≅ L) {Y : E₂'} (y : G'.obj (G.obj L) ⟶ Y) :
    G'.map (G.map e.inv) ≫ G'.map (G.map e.hom) ≫ y = y := by
  rw [← G'.map_comp_assoc, ← G.map_comp, e.inv_hom_id, G.map_id, G'.map_id, Category.id_comp]

/-- **The cocycle condition is transported along an isomorphism.** If `α : G₁ L ≅ G₀ L`
satisfies the cocycle condition, so does its conjugate `G₁ e ≫ α ≫ G₀ e⁻¹` at `L'`. -/
theorem cocycle_conj {L L' : E₀} (e : L' ≅ L) (α : G₁.obj L ≅ G₀.obj L)
    (h : G'₁.map α.hom = Q₁₁.hom.app L ≫ Q₁₂.inv.app L ≫ G'₂.map α.hom ≫ Q₀₂.hom.app L ≫
      Q₁₀.inv.app L ≫ G'₀.map α.hom ≫ Q₀₀.hom.app L ≫ Q₀₁.inv.app L) :
    G'₁.map (G₁.map e.hom ≫ α.hom ≫ G₀.map e.inv) =
      Q₁₁.hom.app L' ≫ Q₁₂.inv.app L' ≫ G'₂.map (G₁.map e.hom ≫ α.hom ≫ G₀.map e.inv) ≫
        Q₀₂.hom.app L' ≫ Q₁₀.inv.app L' ≫ G'₀.map (G₁.map e.hom ≫ α.hom ≫ G₀.map e.inv) ≫
          Q₀₀.hom.app L' ≫ Q₀₁.inv.app L' := by
  have n : ∀ {G : E₀ ⥤ E₁} {G' : E₁ ⥤ E₂} {H : E₀ ⥤ E₂} (Q : G ⋙ G' ≅ H),
      Q.hom.app L' = G'.map (G.map e.hom) ≫ Q.hom.app L ≫ H.map e.inv := fun {G G' H} Q ↦ by
    rw [← Functor.comp_map G G' e.hom, Q.hom.naturality_assoc]
    simp
  have ni : ∀ {G : E₀ ⥤ E₁} {G' : E₁ ⥤ E₂} {H : E₀ ⥤ E₂} (Q : G ⋙ G' ≅ H),
      Q.inv.app L' = H.map e.hom ≫ Q.inv.app L ≫ G'.map (G.map e.inv) := fun {G G' H} Q ↦ by
    rw [← Functor.comp_map G G' e.inv, reassoc_of% (Q.inv.naturality e.hom)]
    simp only [Functor.comp_map, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
      Category.comp_id]
  simp only [n, ni, Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc,
    map_map_inv_hom_assoc, h]

end

section

variable {D₀ : Type u₀} {D₁ : Type u₁} {D₂ : Type u₂} [Category.{v₀} D₀] [Category.{v₁} D₁]
  [Category.{v₂} D₂] {E₀ : Type t₀} {E₁ : Type t₁} {E₂ : Type t₂} [Category.{w₀} E₀]
  [Category.{w₁} E₁] [Category.{w₂} E₂]

/-- **Transport of the cocycle condition along comparison functors.** Let `c_k : D_k ⥤ E_k`
intertwine `F_i : D₀ ⥤ D₁`, `F'_j : D₁ ⥤ D₂` with `G_i`, `G'_j` through `T_i`, `S_j`, and let
the identifications `P_{ij} : F'_j F_i K ≅ K_v` and `Q_{ij}` be compatible through
`t_v : c₂ K_v ≅ H_v (c₀ K)`. If `c₂` is faithful and `c₁ α' = T₁ ≫ G₁ e ≫ α ≫ G₀ e⁻¹ ≫ T₀⁻¹`
for a cocycle `α` at `L` and `e : c₀ K ≅ L`, then `α'` satisfies the cocycle condition. -/
theorem cocycle_of_faithful {c₀ : D₀ ⥤ E₀} {c₁ : D₁ ⥤ E₁} {c₂ : D₂ ⥤ E₂} [c₂.Faithful]
    {F₀ F₁ : D₀ ⥤ D₁} {F'₀ F'₁ F'₂ : D₁ ⥤ D₂} {G₀ G₁ : E₀ ⥤ E₁} {G'₀ G'₁ G'₂ : E₁ ⥤ E₂}
    {H₀ H₁ H₂ : E₀ ⥤ E₂}
    (T₀ : F₀ ⋙ c₁ ≅ c₀ ⋙ G₀) (T₁ : F₁ ⋙ c₁ ≅ c₀ ⋙ G₁)
    (S₀ : F'₀ ⋙ c₂ ≅ c₁ ⋙ G'₀) (S₁ : F'₁ ⋙ c₂ ≅ c₁ ⋙ G'₁) (S₂ : F'₂ ⋙ c₂ ≅ c₁ ⋙ G'₂)
    (Q₁₁ : G₁ ⋙ G'₁ ≅ H₀) (Q₁₂ : G₁ ⋙ G'₂ ≅ H₀) (Q₀₂ : G₀ ⋙ G'₂ ≅ H₁) (Q₁₀ : G₁ ⋙ G'₀ ≅ H₁)
    (Q₀₀ : G₀ ⋙ G'₀ ≅ H₂) (Q₀₁ : G₀ ⋙ G'₁ ≅ H₂)
    {K : D₀} {K₀ K₁ K₂ : D₂} (t₀ : c₂.obj K₀ ≅ H₀.obj (c₀.obj K))
    (t₁ : c₂.obj K₁ ≅ H₁.obj (c₀.obj K)) (t₂ : c₂.obj K₂ ≅ H₂.obj (c₀.obj K))
    (P₁₁ : F'₁.obj (F₁.obj K) ≅ K₀) (P₁₂ : F'₂.obj (F₁.obj K) ≅ K₀)
    (P₀₂ : F'₂.obj (F₀.obj K) ≅ K₁) (P₁₀ : F'₀.obj (F₁.obj K) ≅ K₁)
    (P₀₀ : F'₀.obj (F₀.obj K) ≅ K₂) (P₀₁ : F'₁.obj (F₀.obj K) ≅ K₂)
    (h₁₁ : c₂.map P₁₁.hom ≫ t₀.hom =
      S₁.hom.app (F₁.obj K) ≫ G'₁.map (T₁.hom.app K) ≫ Q₁₁.hom.app (c₀.obj K))
    (h₁₂ : c₂.map P₁₂.hom ≫ t₀.hom =
      S₂.hom.app (F₁.obj K) ≫ G'₂.map (T₁.hom.app K) ≫ Q₁₂.hom.app (c₀.obj K))
    (h₀₂ : c₂.map P₀₂.hom ≫ t₁.hom =
      S₂.hom.app (F₀.obj K) ≫ G'₂.map (T₀.hom.app K) ≫ Q₀₂.hom.app (c₀.obj K))
    (h₁₀ : c₂.map P₁₀.hom ≫ t₁.hom =
      S₀.hom.app (F₁.obj K) ≫ G'₀.map (T₁.hom.app K) ≫ Q₁₀.hom.app (c₀.obj K))
    (h₀₀ : c₂.map P₀₀.hom ≫ t₂.hom =
      S₀.hom.app (F₀.obj K) ≫ G'₀.map (T₀.hom.app K) ≫ Q₀₀.hom.app (c₀.obj K))
    (h₀₁ : c₂.map P₀₁.hom ≫ t₂.hom =
      S₁.hom.app (F₀.obj K) ≫ G'₁.map (T₀.hom.app K) ≫ Q₀₁.hom.app (c₀.obj K))
    {L : E₀} (e : c₀.obj K ≅ L) (α : G₁.obj L ≅ G₀.obj L)
    (hα : G'₁.map α.hom = Q₁₁.hom.app L ≫ Q₁₂.inv.app L ≫ G'₂.map α.hom ≫ Q₀₂.hom.app L ≫
      Q₁₀.inv.app L ≫ G'₀.map α.hom ≫ Q₀₀.hom.app L ≫ Q₀₁.inv.app L)
    (α' : F₁.obj K ≅ F₀.obj K)
    (hα' : c₁.map α'.hom = T₁.hom.app K ≫ G₁.map e.hom ≫ α.hom ≫ G₀.map e.inv ≫ T₀.inv.app K) :
    F'₁.map α'.hom = P₁₁.hom ≫ P₁₂.inv ≫ F'₂.map α'.hom ≫ P₀₂.hom ≫ P₁₀.inv ≫
      F'₀.map α'.hom ≫ P₀₀.hom ≫ P₀₁.inv := by
  have hα₀ := cocycle_conj Q₁₁ Q₁₂ Q₀₂ Q₁₀ Q₀₀ Q₀₁ e α hα
  generalize ha : G₁.map e.hom ≫ α.hom ≫ G₀.map e.inv = a at hα₀
  replace hα' : c₁.map α'.hom = T₁.hom.app K ≫ a ≫ T₀.inv.app K := by
    rw [hα', ← ha]
    simp only [Category.assoc]
  refine c₂.map_injective ?_
  have hF : ∀ {F' : D₁ ⥤ D₂} {G' : E₁ ⥤ E₂} (S : F' ⋙ c₂ ≅ c₁ ⋙ G'),
      c₂.map (F'.map α'.hom) = S.hom.app _ ≫ G'.map (T₁.hom.app K ≫ a ≫ T₀.inv.app K) ≫
        S.inv.app _ := fun {F' G'} S ↦ by
    rw [← hα']
    exact (NatIso.naturality_2 S α'.hom).symm
  have hP : ∀ {F' : D₁ ⥤ D₂} {G' : E₁ ⥤ E₂} {H : E₀ ⥤ E₂} {F : D₀ ⥤ D₁} {G : E₀ ⥤ E₁}
      {Kv : D₂} (S : F' ⋙ c₂ ≅ c₁ ⋙ G') (T : F ⋙ c₁ ≅ c₀ ⋙ G) (Q : G ⋙ G' ≅ H)
      (t : c₂.obj Kv ≅ H.obj (c₀.obj K)) (P : F'.obj (F.obj K) ≅ Kv)
      (_ : c₂.map P.hom ≫ t.hom = S.hom.app (F.obj K) ≫ G'.map (T.hom.app K) ≫
        Q.hom.app (c₀.obj K)),
      c₂.map P.hom = S.hom.app _ ≫ G'.map (T.hom.app K) ≫ Q.hom.app _ ≫ t.inv ∧
        c₂.map P.inv = t.hom ≫ Q.inv.app _ ≫ G'.map (T.inv.app K) ≫ S.inv.app _ :=
    fun {F' G' H F G Kv} S T Q t P h ↦ by
      have h' : c₂.map P.hom = S.hom.app _ ≫ G'.map (T.hom.app K) ≫ Q.hom.app _ ≫ t.inv := by
        simpa using (Iso.eq_comp_inv t).mpr h
      refine ⟨h', ?_⟩
      rw [← cancel_epi (c₂.map P.hom), ← c₂.map_comp, P.hom_inv_id, c₂.map_id, h']
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_app_assoc]
      rw [← G'.map_comp_assoc, ← NatTrans.comp_app, T.hom_inv_id, NatTrans.id_app]
      refine Eq.trans ?_ (congrArg (fun x ↦ S.hom.app (F.obj K) ≫ x ≫ S.inv.app (F.obj K))
        (G'.map_id ((F ⋙ c₁).obj K))).symm
      simp
  simp only [Functor.map_comp, hF S₀, hF S₁, hF S₂,
    (hP S₁ T₁ Q₁₁ t₀ P₁₁ h₁₁).1, (hP S₂ T₁ Q₁₂ t₀ P₁₂ h₁₂).2, (hP S₂ T₀ Q₀₂ t₁ P₀₂ h₀₂).1,
    (hP S₀ T₁ Q₁₀ t₁ P₁₀ h₁₀).2, (hP S₀ T₀ Q₀₀ t₂ P₀₀ h₀₀).1, (hP S₁ T₀ Q₀₁ t₂ P₀₁ h₀₁).2,
    Category.assoc, Iso.inv_hom_id_assoc,
    ← Iso.app_inv, ← Iso.app_hom, Iso.inv_hom_id_map_assoc, hα₀]

end

end CategoryTheory
