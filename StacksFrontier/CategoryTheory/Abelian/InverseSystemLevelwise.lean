module

public import StacksFrontier.CategoryTheory.Abelian.InverseSystem

/-!
# The Mittag-Leffler condition through levelwise identifications

Let `F` and `G` be inverse systems indexed by `ℕ` in an abelian category, `G` satisfying the
Mittag-Leffler condition. Suppose that for every `n` the truncations of `F` and `G` to the
indices `j ≤ n` are isomorphic, by isomorphisms which may depend on `n`. Then `F` satisfies the
Mittag-Leffler condition. This is how Stacks 09C5 compares a system of sections with a system
of modules: one isomorphism in the derived category at level `n` induces, by base change,
compatible identifications at all levels `j ≤ n`, but no identification of the whole systems.

## Main results

* `IsMittagLefflerCategorical.of_forall_le_iso`: the Mittag-Leffler condition passes along
  levelwise identifications of truncations.
* `exists_le_iso_comp_of_iso`: a levelwise identification of the truncations of
  `X ⋙ Φ` and `Y ⋙ Ψ`, built from one isomorphism of functors `a ⋙ Φ ≅ b ⋙ Ψ` and levelwise
  identifications of `X` with `T ⋙ a` and of `Y` with `T ⋙ b`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

/-- **The Mittag-Leffler condition through levelwise identifications.** If `G` is
Mittag-Leffler, and for every `n` the truncations of `F` and `G` to the indices `j ≤ n` are
isomorphic compatibly with the transition maps, then `F` is Mittag-Leffler. -/
theorem IsMittagLefflerCategorical.of_forall_le_iso {C : Type*} [Category C] [Abelian C]
    {F G : ℕᵒᵖ ⥤ C} (hG : IsMittagLefflerCategorical G)
    (h : ∀ n : ℕ, ∃ e : ∀ j : ℕ, j ≤ n → (F.obj (op j) ≅ G.obj (op j)),
      ∀ (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n),
        F.map (homOfLE hij).op ≫ (e i (hij.trans hjn)).hom =
          (e j hjn).hom ≫ G.map (homOfLE hij).op) :
    IsMittagLefflerCategorical F :=
  hG.of_forall_iso_of_le_of_le fun k m n hkm hmn => by
    obtain ⟨e, he⟩ := h n
    exact ⟨e k (hkm.trans hmn), e m hmn, e n le_rfl, he k m hkm hmn, he m n hmn le_rfl⟩

/-- **Levelwise identifications from one isomorphism of functors.** Given an isomorphism of
functors `τ : a ⋙ Φ ≅ b ⋙ Ψ` and, up to the level `n`, compatible identifications of the
systems `X` with `T ⋙ a` and `Y` with `T ⋙ b`, the truncations of `X ⋙ Φ` and `Y ⋙ Ψ` to the
indices `j ≤ n` are compatibly isomorphic. -/
theorem exists_le_iso_comp_of_iso {D D₁ D₂ C : Type*} [Category D] [Category D₁] [Category D₂]
    [Category C] {X : ℕᵒᵖ ⥤ D₁} {Y : ℕᵒᵖ ⥤ D₂} {T : ℕᵒᵖ ⥤ D} {a : D ⥤ D₁} {b : D ⥤ D₂}
    {Φ : D₁ ⥤ C} {Ψ : D₂ ⥤ C} (τ : a ⋙ Φ ≅ b ⋙ Ψ) (n : ℕ)
    (α : ∀ j : ℕ, j ≤ n → (X.obj (op j) ≅ a.obj (T.obj (op j))))
    (hα : ∀ (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n),
      X.map (homOfLE hij).op ≫ (α i (hij.trans hjn)).hom =
        (α j hjn).hom ≫ a.map (T.map (homOfLE hij).op))
    (β : ∀ j : ℕ, j ≤ n → (Y.obj (op j) ≅ b.obj (T.obj (op j))))
    (hβ : ∀ (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n),
      Y.map (homOfLE hij).op ≫ (β i (hij.trans hjn)).hom =
        (β j hjn).hom ≫ b.map (T.map (homOfLE hij).op)) :
    ∃ e : ∀ j : ℕ, j ≤ n → ((X ⋙ Φ).obj (op j) ≅ (Y ⋙ Ψ).obj (op j)),
      ∀ (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n),
        (X ⋙ Φ).map (homOfLE hij).op ≫ (e i (hij.trans hjn)).hom =
          (e j hjn).hom ≫ (Y ⋙ Ψ).map (homOfLE hij).op := by
  refine ⟨fun j hj => Φ.mapIso (α j hj) ≪≫ τ.app (T.obj (op j)) ≪≫ (Ψ.mapIso (β j hj)).symm,
    fun i j hij hjn => ?_⟩
  have hτ := τ.hom.naturality (T.map (homOfLE hij).op)
  have hβ' : (β j hjn).inv ≫ Y.map (homOfLE hij).op =
      b.map (T.map (homOfLE hij).op) ≫ (β i (hij.trans hjn)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hβ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.app_hom, Category.assoc] at hτ ⊢
  rw [← Φ.map_comp_assoc, hα, Φ.map_comp_assoc, reassoc_of% hτ, ← Ψ.map_comp, ← Ψ.map_comp,
    hβ']
