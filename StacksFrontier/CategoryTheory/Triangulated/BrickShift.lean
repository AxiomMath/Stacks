module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Autoequivalences of a pretriangulated category and the shift on bricks

An equivalence of the underlying category of a pretriangulated category need not commute with
the shift functor. This file shows that it does on suitable objects. Call `K` a *brick* when
each endomorphism of `K` is zero or an isomorphism. Suppose `K` is a nonzero brick with a
nonzero morphism `e : K ⟶ K⟦1⟧` and no nonzero morphism `K⟦1⟧ ⟶ K`. Then for every
autoequivalence `F` of the category, `F (K⟦1⟧) ≅ (F K)⟦1⟧`, and therefore
`F (K⟦n⟧) ≅ (F K)⟦n⟧` for every integer `n`.

The proof uses only the additive structure that an equivalence preserves. In a distinguished
triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` the map `Y ⟶ Z` is a weak cokernel of `X ⟶ Y`, and `Z ⟶ X⟦1⟧`
is a weak cokernel of `Y ⟶ Z`. Weak cokernels are defined by a universal property of
morphisms, so `F` preserves them. Apply this to a triangle `K ⟶ Y ⟶ K ⟶ K⟦1⟧` whose last map
is `e`. The image of `Y ⟶ K` is a weak cokernel of the image of `K ⟶ Y`, and so is the
corresponding map of a cone of that image. Comparing the two weak cokernels identifies the
cone with `F K`, because the endomorphisms of a brick are zero or invertible. Comparing the
weak cokernels at the next step identifies `F (K⟦1⟧)` with `(F K)⟦1⟧`.

## Main definitions

* `CategoryTheory.IsBrick`: every endomorphism is zero or an isomorphism.

## Main results

* `CategoryTheory.Pretriangulated.nonempty_iso_map_shift_one`: `F (K⟦1⟧) ≅ (F K)⟦1⟧`.
* `CategoryTheory.Pretriangulated.nonempty_iso_map_shift`: `F (K⟦n⟧) ≅ (F K)⟦n⟧` for all `n`.
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory

/-- An object whose endomorphisms are all either zero or invertible. -/
def IsBrick {D : Type*} [Category D] [Preadditive D] (K : D) : Prop :=
  ∀ f : K ⟶ K, f = 0 ∨ IsIso f

namespace IsBrick

variable {D E : Type*} [Category D] [Preadditive D] [Category E] [Preadditive E]

/-- A fully faithful functor sends a brick to a brick. -/
theorem map (G : D ⥤ E) [G.Full] [G.Faithful] [G.PreservesZeroMorphisms] {K : D}
    (hK : IsBrick K) : IsBrick (G.obj K) := by
  intro f
  obtain ⟨g, rfl⟩ := G.map_surjective f
  rcases hK g with h | h
  · left
    rw [h, G.map_zero]
  · right
    infer_instance

/-- A fully faithful functor reflects bricks. -/
theorem of_map (G : D ⥤ E) [G.Full] [G.Faithful] [G.PreservesZeroMorphisms] {K : D}
    (hK : IsBrick (G.obj K)) : IsBrick K := by
  intro f
  rcases hK (G.map f) with h | h
  · left
    exact G.map_injective (by rw [h, G.map_zero])
  · right
    exact isIso_of_fully_faithful G f

/-- Being a brick is invariant under isomorphism. -/
theorem of_iso {K L : D} (e : K ≅ L) (hK : IsBrick K) : IsBrick L := by
  intro f
  have hf : f = e.inv ≫ (e.hom ≫ f ≫ e.inv) ≫ e.hom := by simp
  rcases hK (e.hom ≫ f ≫ e.inv) with h | h
  · left
    rw [hf, h, zero_comp, comp_zero]
  · right
    rw [hf]
    infer_instance

end IsBrick

namespace Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- An equivalence preserves the weak-cokernel property of a composable pair: if every morphism
out of `Y` killing `f` factors through `g`, the same holds for `F.map f` and `F.map g`. -/
theorem map_weakCokernel {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.IsEquivalence] [F.PreservesZeroMorphisms] {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : ∀ {W : C} (k : Y ⟶ W), f ≫ k = 0 → ∃ k' : Z ⟶ W, k = g ≫ k')
    {W : D} (k : F.obj Y ⟶ W) (hk : F.map f ≫ k = 0) :
    ∃ k' : F.obj Z ⟶ W, k = F.map g ≫ k' := by
  let ε := F.objObjPreimageIso W
  let k₀ : Y ⟶ F.objPreimage W := F.preimage (k ≫ ε.inv)
  have hk₀ : f ≫ k₀ = 0 := by
    apply F.map_injective
    rw [F.map_comp, F.map_preimage, F.map_zero, ← Category.assoc, hk, zero_comp]
  obtain ⟨k₁, hk₁⟩ := h k₀ hk₀
  refine ⟨F.map k₁ ≫ ε.hom, ?_⟩
  rw [← Category.assoc, ← F.map_comp, ← hk₁, F.map_preimage]
  simp

/-- **Shift transfer.** Let `F` be an autoequivalence of the underlying category of a
pretriangulated category. Let `K` be a nonzero brick with a nonzero morphism `K ⟶ K⟦1⟧` and no
nonzero morphism `K⟦1⟧ ⟶ K`. Then `F (K⟦1⟧) ≅ (F K)⟦1⟧`. -/
theorem nonempty_iso_map_shift_one (F : C ⥤ C) [F.IsEquivalence] [F.Additive]
    {K : C} (hK : IsBrick K) (e : K ⟶ K⟦(1 : ℤ)⟧) (he : e ≠ 0)
    (hvan : ∀ l : K⟦(1 : ℤ)⟧ ⟶ K, l = 0) (hK0 : ¬ IsZero K) :
    Nonempty (F.obj (K⟦(1 : ℤ)⟧) ≅ (F.obj K)⟦(1 : ℤ)⟧) := by
  obtain ⟨Y, f, g, hT⟩ := distinguished_cocone_triangle₂ e
  have hf : f ≠ 0 := by
    intro hf0
    obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₁ _ hT (𝟙 (K⟦(1 : ℤ)⟧))
      (by dsimp; rw [hf0, Functor.map_zero, comp_zero])
    apply hK0
    have h1 : IsZero (K⟦(1 : ℤ)⟧) := by
      rw [IsZero.iff_id_eq_zero, hl, hvan l, zero_comp]
    exact IsZero.of_iso ((shiftFunctor C (-1 : ℤ)).map_isZero h1)
      ((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by norm_num)).app K).symm
  have hg : g ≠ 0 := by
    intro hg0
    obtain ⟨l, hl⟩ := Triangle.yoneda_exact₃ _ hT (𝟙 K) (by dsimp; rw [hg0, zero_comp])
    apply hK0
    rw [IsZero.iff_id_eq_zero]
    dsimp at hl
    rw [hl, hvan l, comp_zero]
  let f' := F.map f
  let g' := F.map g
  have hfg' : f' ≫ g' = 0 := by
    rw [← F.map_comp, show f ≫ g = 0 from comp_distTriang_mor_zero₁₂ _ hT, F.map_zero]
  have hge' : g' ≫ F.map e = 0 := by
    rw [← F.map_comp, show g ≫ e = 0 from comp_distTriang_mor_zero₂₃ _ hT, F.map_zero]
  have hf' : f' ≠ 0 := fun h => hf (F.map_injective (by rw [F.map_zero]; exact h))
  have hg' : g' ≠ 0 := fun h => hg (F.map_injective (by rw [F.map_zero]; exact h))
  have he' : F.map e ≠ 0 := fun h => he (F.map_injective (by rw [F.map_zero]; exact h))
  have hBK : IsBrick (F.obj K) := hK.map F
  have hBK1 : IsBrick ((F.obj K)⟦(1 : ℤ)⟧) := hBK.map (shiftFunctor C (1 : ℤ))
  have hB1K : IsBrick (F.obj (K⟦(1 : ℤ)⟧)) :=
    (hK.map (shiftFunctor C (1 : ℤ))).map F
  -- `g'` and `F e` are weak cokernels of `f'` and `g'`.
  have hwc₁ : ∀ {W : C} (k : F.obj Y ⟶ W), f' ≫ k = 0 → ∃ k' : F.obj K ⟶ W, k = g' ≫ k' :=
    fun k hk => map_weakCokernel F f g (fun k hk => Triangle.yoneda_exact₂ _ hT k hk) k hk
  have hwc₂ : ∀ {W : C} (k : F.obj K ⟶ W), g' ≫ k = 0 →
      ∃ k' : F.obj (K⟦(1 : ℤ)⟧) ⟶ W, k = F.map e ≫ k' :=
    fun k hk => map_weakCokernel F g e (fun k hk => Triangle.yoneda_exact₃ _ hT k hk) k hk
  -- A cone of `f'`.
  obtain ⟨Z, c, d, hT'⟩ := distinguished_cocone_triangle f'
  have hfc : f' ≫ c = 0 := comp_distTriang_mor_zero₁₂ _ hT'
  have hdf : d ≫ f'⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT'
  obtain ⟨α, hα⟩ := Triangle.yoneda_exact₂ _ hT' g' hfg'
  obtain ⟨β, hβ⟩ := hwc₁ c hfc
  dsimp at hα
  let φ : F.obj K ⟶ F.obj K := β ≫ α
  have hgφ : g' ≫ φ = g' := by
    dsimp only [φ]
    rw [← Category.assoc, ← hβ, ← hα]
  have hφ : IsIso φ := (hBK φ).resolve_left fun h => hg' (by rw [← hgφ, h, comp_zero])
  have hginv : g' ≫ inv φ = g' := by rw [IsIso.comp_inv_eq, hgφ]
  let ψ : Z ⟶ Z := α ≫ inv φ ≫ β
  have hcψ : c ≫ ψ = c := by
    dsimp only [ψ]
    rw [← Category.assoc, ← hα, ← Category.assoc, hginv, ← hβ]
  have hψψ : ψ ≫ ψ = ψ := by
    dsimp only [ψ]
    have : β ≫ α = φ := rfl
    simp only [Category.assoc]
    rw [reassoc_of% this, IsIso.inv_hom_id_assoc]
  obtain ⟨ρ, hρ⟩ := Triangle.yoneda_exact₃ _ hT' (𝟙 Z - ψ)
    (by dsimp; rw [Preadditive.comp_sub, Category.comp_id, hcψ, sub_self])
  dsimp at hρ
  have hψ : ψ = 𝟙 Z := by
    rcases hBK1 (ρ ≫ d) with h | h
    · have hsq : (𝟙 Z - ψ) ≫ (𝟙 Z - ψ) = 0 := by
        rw [hρ, Category.assoc, ← Category.assoc ρ, h, zero_comp, comp_zero]
      have hidem : (𝟙 Z - ψ) ≫ (𝟙 Z - ψ) = 𝟙 Z - ψ := by
        simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
          Category.id_comp, hψψ]
        abel
      rw [hidem] at hsq
      exact (sub_eq_zero.mp hsq).symm
    · exfalso
      apply hf'
      apply (shiftFunctor C (1 : ℤ)).map_injective
      rw [Functor.map_zero]
      have h0 : (ρ ≫ d) ≫ f'⟦(1 : ℤ)⟧' = 0 := by rw [Category.assoc, hdf, comp_zero]
      simpa using (cancel_epi (ρ ≫ d)).mp (h0.trans (comp_zero).symm)
  let eβ : F.obj K ≅ Z :=
    { hom := β
      inv := α ≫ inv φ
      hom_inv_id := by rw [← Category.assoc]; exact IsIso.hom_inv_id φ
      inv_hom_id := by rw [Category.assoc]; exact hψ }
  let θ : F.obj K ⟶ (F.obj K)⟦(1 : ℤ)⟧ := β ≫ d
  have hT'' : Triangle.mk f' g' θ ∈ distTriang C := by
    refine isomorphic_distinguished _ hT' _
      (Triangle.isoMk (Triangle.mk f' g' θ) (Triangle.mk f' c d) (Iso.refl _) (Iso.refl _) eβ
        (by simp) (by simpa using hβ.symm) (by simp [θ, eβ]))
  have hθ : θ ≠ 0 := by
    intro hθ0
    obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT'') (𝟙 (F.obj K))
      (by simp only [Triangle.invRotate_mor₁, Triangle.mk_mor₃, hθ0, Functor.map_zero,
        zero_comp, neg_zero]; exact zero_comp)
    change 𝟙 (F.obj K) = f' ≫ r at hr
    apply he
    obtain ⟨r₀, rfl⟩ := F.map_surjective r
    have hfr : f ≫ r₀ = 𝟙 K := F.map_injective (by
      rw [F.map_comp, F.map_id]
      exact hr.symm)
    have h0 : e ≫ f⟦(1 : ℤ)⟧' ≫ r₀⟦(1 : ℤ)⟧' = 0 := by
      rw [← Category.assoc, show e ≫ f⟦(1 : ℤ)⟧' = 0 from comp_distTriang_mor_zero₃₁ _ hT,
        zero_comp]
    rwa [← Functor.map_comp, hfr, CategoryTheory.Functor.map_id, Category.comp_id] at h0
  obtain ⟨γ, hγ⟩ := hwc₂ θ (comp_distTriang_mor_zero₂₃ _ hT'')
  obtain ⟨δ, hδ⟩ := Triangle.yoneda_exact₃ _ hT'' (F.map e) hge'
  dsimp at hδ
  have h₁ : IsIso (δ ≫ γ) := (hBK1 (δ ≫ γ)).resolve_left fun h =>
    hθ (by rw [hγ, hδ, Category.assoc, h, comp_zero])
  have h₂ : IsIso (γ ≫ δ) := (hB1K (γ ≫ δ)).resolve_left fun h =>
    he' (by rw [hδ, hγ, Category.assoc, h, comp_zero])
  have : Mono γ := mono_of_mono γ δ
  have : IsSplitEpi γ := IsSplitEpi.mk' ⟨inv (δ ≫ γ) ≫ δ, by simp⟩
  have : IsIso γ := isIso_of_mono_of_isSplitEpi γ
  exact ⟨asIso γ⟩

/-- **Shift transfer in every degree.** Under the hypotheses of
`CategoryTheory.Pretriangulated.nonempty_iso_map_shift_one`, `F (K⟦n⟧) ≅ (F K)⟦n⟧` for every
integer `n`: the hypotheses pass to every shift of `K`, and the single steps compose. -/
theorem nonempty_iso_map_shift (F : C ⥤ C) [F.IsEquivalence] [F.Additive]
    {K : C} (hK : IsBrick K) (e : K ⟶ K⟦(1 : ℤ)⟧) (he : e ≠ 0)
    (hvan : ∀ l : K⟦(1 : ℤ)⟧ ⟶ K, l = 0) (hK0 : ¬ IsZero K) (n : ℤ) :
    Nonempty (F.obj (K⟦n⟧) ≅ (F.obj K)⟦n⟧) := by
  have step : ∀ n : ℤ, Nonempty (F.obj (K⟦n⟧⟦(1 : ℤ)⟧) ≅ (F.obj (K⟦n⟧))⟦(1 : ℤ)⟧) := by
    intro n
    let σ := (shiftFunctorComm C (1 : ℤ) n).hom.app K
    refine nonempty_iso_map_shift_one F (hK.map (shiftFunctor C n)) (e⟦n⟧' ≫ σ) ?_ ?_ ?_
    · intro h
      apply he
      apply (shiftFunctor C n).map_injective
      rw [Functor.map_zero]
      exact (cancel_mono σ).mp (h.trans zero_comp.symm)
    · intro l
      have h0 : σ ≫ l = 0 := by
        obtain ⟨l₀, hl₀⟩ := (shiftFunctor C n).map_surjective (σ ≫ l)
        rw [← hl₀, hvan l₀, Functor.map_zero]
      exact (cancel_epi σ).mp (h0.trans comp_zero.symm)
    · intro h
      exact hK0 (IsZero.of_iso ((shiftFunctor C (-n)).map_isZero h)
        ((shiftFunctorCompIsoId C n (-n) (by omega)).app K).symm)
  induction n using Int.induction_on with
  | zero =>
    exact ⟨F.mapIso ((shiftFunctorZero C ℤ).app K) ≪≫ ((shiftFunctorZero C ℤ).app (F.obj K)).symm⟩
  | succ i ih =>
    obtain ⟨j⟩ := ih
    obtain ⟨s⟩ := step i
    exact ⟨F.mapIso ((shiftFunctorAdd' C (i : ℤ) 1 (i + 1) rfl).app K) ≪≫ s ≪≫
      (shiftFunctor C (1 : ℤ)).mapIso j ≪≫
      ((shiftFunctorAdd' C (i : ℤ) 1 (i + 1) rfl).app (F.obj K)).symm⟩
  | pred i ih =>
    obtain ⟨j⟩ := ih
    obtain ⟨s⟩ := step (-(i : ℤ) - 1)
    let t : (F.obj (K⟦-(i : ℤ) - 1⟧))⟦(1 : ℤ)⟧ ≅ (F.obj K)⟦-(i : ℤ)⟧ :=
      s.symm ≪≫ F.mapIso ((shiftFunctorAdd' C (-(i : ℤ) - 1) 1 (-(i : ℤ)) (by omega)).app K).symm ≪≫
        j
    exact ⟨((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)).app _).symm ≪≫
      (shiftFunctor C (-1 : ℤ)).mapIso t ≪≫
      ((shiftFunctorAdd' C (-(i : ℤ)) (-1) (-(i : ℤ) - 1) (by omega)).app _).symm⟩

end Pretriangulated

end CategoryTheory
