module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# Conjugates of pasted squares of adjunctions

Consider two squares of left adjoints pasted horizontally,

```
  D₀ --T--> D₁ --T₂--> D₂
  |F        |F₁        |F₂
  v         v          v
  X  --L--> X₁ --L₂--> X₂
```

with adjunctions `F ⊣ G`, `F₁ ⊣ G₁`, `F₂ ⊣ G₂`, `T ⊣ R`, `T₂ ⊣ R₂`, `L ⊣ P`, `L₂ ⊣ P₂`,
isomorphisms `s₁ : T ⋙ F₁ ≅ F ⋙ L` and `s₂ : T₂ ⋙ F₂ ≅ F₁ ⋙ L₂` filling the squares, and an outer
square `s₀ : T₀ ⋙ F₂ ≅ F ⋙ L₀` for left adjoints `T₀ ⊣ R₀`, `L₀ ⊣ P₀` compared with the composites
by `ρ : T ⋙ T₂ ≅ T₀` and `γ : L ⋙ L₂ ≅ L₀`. If `s₀` is the pasting of `s₁` and `s₂` through `ρ`
and `γ`, then the conjugate isomorphism `P₀ ⋙ G ≅ G₂ ⋙ R₀` of `s₀` is the pasting of the
conjugates of `s₁` and `s₂`, through the conjugates of `ρ⁻¹` and `γ⁻¹`.

## Main results

* `CategoryTheory.conjugateIsoEquiv_pasting`.
* `CategoryTheory.squareIso_hom_app_eq_of_baseChangeMap`: the pasting of the squares from the
  composition of their base change maps.
* `CategoryTheory.conjugateIsoEquiv_pasting_of_baseChangeMap`.
-/

@[expose] public section

namespace CategoryTheory

open Category _root_.CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {D₀ : Type u₁} {D₁ : Type u₂} {D₂ : Type u₃} {X : Type u₄} {X₁ : Type u₅} {X₂ : Type u₆}
  [Category.{v₁} D₀] [Category.{v₂} D₁] [Category.{v₃} D₂] [Category.{v₄} X] [Category.{v₅} X₁]
  [Category.{v₆} X₂]
  {F : D₀ ⥤ X} {G : X ⥤ D₀} {F₁ : D₁ ⥤ X₁} {G₁ : X₁ ⥤ D₁} {F₂ : D₂ ⥤ X₂} {G₂ : X₂ ⥤ D₂}
  {T : D₀ ⥤ D₁} {R : D₁ ⥤ D₀} {T₂ : D₁ ⥤ D₂} {R₂ : D₂ ⥤ D₁} {T₀ : D₀ ⥤ D₂} {R₀ : D₂ ⥤ D₀}
  {L : X ⥤ X₁} {P : X₁ ⥤ X} {L₂ : X₁ ⥤ X₂} {P₂ : X₂ ⥤ X₁} {L₀ : X ⥤ X₂} {P₀ : X₂ ⥤ X}
  (aF : F ⊣ G) (aF₁ : F₁ ⊣ G₁) (aF₂ : F₂ ⊣ G₂) (aT : T ⊣ R) (aT₂ : T₂ ⊣ R₂) (aT₀ : T₀ ⊣ R₀)
  (aL : L ⊣ P) (aL₂ : L₂ ⊣ P₂) (aL₀ : L₀ ⊣ P₀)
  (s₁ : T ⋙ F₁ ≅ F ⋙ L) (s₂ : T₂ ⋙ F₂ ≅ F₁ ⋙ L₂) (s₀ : T₀ ⋙ F₂ ≅ F ⋙ L₀)
  (ρ : T ⋙ T₂ ≅ T₀) (γ : L ⋙ L₂ ≅ L₀)

/-- **The conjugate of a pasted square is the pasting of the conjugates.** If
`s₀ = ρ⁻¹ F₂ ≫ T s₂ ≫ s₁ L₂ ≫ F γ` componentwise, then
`G (c_γ) ≫ π₀ = π₁ P₂ ≫ R π₂ ≫ c_ρ G₂` componentwise, where `π₀, π₁, π₂` are the conjugates of
`s₀, s₁, s₂` and `c_γ : P₂ ⋙ P ⟶ P₀`, `c_ρ : R₂ ⋙ R ⟶ R₀` those of `γ⁻¹`, `ρ⁻¹`. -/
theorem conjugateIsoEquiv_pasting
    (hs : ∀ M : D₀, s₀.hom.app M = F₂.map (ρ.inv.app M) ≫ s₂.hom.app (T.obj M) ≫
      L₂.map (s₁.hom.app M) ≫ γ.hom.app (F.obj M)) (M : X₂) :
    G.map ((conjugateEquiv (aL.comp aL₂) aL₀ γ.inv).app M) ≫
        (conjugateIsoEquiv (aF.comp aL₀) (aT₀.comp aF₂) s₀).hom.app M =
      (conjugateIsoEquiv (aF.comp aL) (aT.comp aF₁) s₁).hom.app (P₂.obj M) ≫
        R.map ((conjugateIsoEquiv (aF₁.comp aL₂) (aT₂.comp aF₂) s₂).hom.app M) ≫
        (conjugateEquiv (aT.comp aT₂) aT₀ ρ.inv).app (G₂.obj M) := by
  apply ((aT₀.comp aF₂).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, conjugateIsoEquiv_apply_hom]
  have hL : (T₀ ⋙ F₂).map (G.map ((conjugateEquiv (aL.comp aL₂) aL₀ γ.inv).app M) ≫
        (conjugateEquiv (aF.comp aL₀) (aT₀.comp aF₂) s₀.hom).app M) ≫
          (aT₀.comp aF₂).counit.app M =
      s₀.hom.app _ ≫ γ.inv.app _ ≫ (L ⋙ L₂).map (aF.counit.app (P.obj (P₂.obj M))) ≫
        (aL.comp aL₂).counit.app M := by
    rw [Functor.map_comp, Category.assoc, conjugateEquiv_counit, ← Category.assoc]
    dsimp only [Functor.comp_obj]
    rw [s₀.hom.naturality, Category.assoc, Adjunction.comp_counit_app, Functor.comp_map,
      ← Category.assoc (L₀.map _), ← L₀.map_comp, aF.counit_naturality, L₀.map_comp,
      Category.assoc, conjugateEquiv_counit, ← Category.assoc (L₀.map _)]
    dsimp only [Functor.comp_obj]
    rw [γ.inv.naturality, Category.assoc]
  have hR : (T₀ ⋙ F₂).map ((conjugateEquiv (aF.comp aL) (aT.comp aF₁) s₁.hom).app (P₂.obj M) ≫
        R.map ((conjugateEquiv (aF₁.comp aL₂) (aT₂.comp aF₂) s₂.hom).app M) ≫
          (conjugateEquiv (aT.comp aT₂) aT₀ ρ.inv).app (G₂.obj M)) ≫
          (aT₀.comp aF₂).counit.app M =
      F₂.map (ρ.inv.app _) ≫ s₂.hom.app _ ≫
        L₂.map (s₁.hom.app _ ≫ (aF.comp aL).counit.app (P₂.obj M)) ≫ aL₂.counit.app M := by
    rw [Adjunction.comp_counit_app, Functor.comp_map, ← Category.assoc, ← F₂.map_comp,
      T₀.map_comp, T₀.map_comp, Category.assoc, Category.assoc, conjugateEquiv_counit,
      ← Category.assoc (T₀.map (R.map _))]
    dsimp only [Functor.comp_obj]
    rw [ρ.inv.naturality, ← Category.assoc (T₀.map _)]
    dsimp only [Functor.comp_obj]
    rw [← Category.assoc (T₀.map _), ρ.inv.naturality]
    simp only [Category.assoc]
    rw [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_map,
      ← Category.assoc (T₂.map (T.map (R.map _))), ← T₂.map_comp, aT.counit_naturality]
    have h₂ := conjugateEquiv_counit (aF₁.comp aL₂) (aT₂.comp aF₂) s₂.hom M
    have h₃ := s₂.hom.naturality (T.map ((conjugateEquiv (aF.comp aL) (aT.comp aF₁) s₁.hom).app
      (P₂.obj M)) ≫ aT.counit.app (G₁.obj (P₂.obj M)))
    have h₁ := congrArg L₂.map (conjugateEquiv_counit (aF.comp aL) (aT.comp aF₁) s₁.hom (P₂.obj M))
    simp only [Functor.comp_map, Adjunction.comp_counit_app, Functor.map_comp, Category.assoc,
      Functor.comp_obj] at h₁ h₂ h₃ ⊢
    rw [h₂, reassoc_of% h₃, reassoc_of% h₁]
  rw [hL, hR, hs]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.comp_map,
    Adjunction.comp_counit_app, Functor.map_comp, Functor.comp_obj]

omit aF₁ aF₂ aT aT₂ aT₀ aL aL₂ aL₀ s₁ s₂ s₀ ρ γ in
/-- Two transformations `T₀ ⋙ F₂ ⟶ F ⋙ L₀` agree as soon as they agree at every `G K` after
`L₀` of the counit of `F ⊣ G`. -/
theorem natTrans_ext_of_comp_map_counit {α β : T₀ ⋙ F₂ ⟶ F ⋙ L₀}
    (h : ∀ K : X, α.app (G.obj K) ≫ L₀.map (aF.counit.app K) =
      β.app (G.obj K) ≫ L₀.map (aF.counit.app K)) : α = β := by
  ext M
  have key (η : T₀ ⋙ F₂ ⟶ F ⋙ L₀) : η.app M = (T₀ ⋙ F₂).map (aF.unit.app M) ≫
      η.app (G.obj (F.obj M)) ≫ L₀.map (aF.counit.app (F.obj M)) := by
    rw [← Category.assoc]
    dsimp only [Functor.comp_obj]
    rw [η.naturality, Category.assoc, Functor.comp_map, ← L₀.map_comp]
    simp
  rw [key α, key β, h]

/-- **A pasted square from the composition of its base change maps.** If the base change map
(`Stacks.CategoryTheory.BaseChange.map`) of the outer square `s₀` is `ρ⁻¹` followed by `T₂` of the
one of `s₁`, the one of `s₂` and `G₂` of `γ`, then `s₀` is the pasting
`ρ⁻¹ F₂ ≫ T s₂ ≫ s₁ L₂ ≫ F γ` of `s₁` and `s₂`. -/
theorem squareIso_hom_app_eq_of_baseChangeMap
    (h : ∀ K : X, ρ.inv.app (G.obj K) ≫
        T₂.map (Stacks.CategoryTheory.BaseChange.map aF aF₁ s₁ (Iso.refl _) K) ≫
        Stacks.CategoryTheory.BaseChange.map aF₁ aF₂ s₂ (Iso.refl _) (L.obj K) ≫
        G₂.map (γ.hom.app K) =
      Stacks.CategoryTheory.BaseChange.map aF aF₂ s₀ (Iso.refl _) K) (M : D₀) :
    s₀.hom.app M = F₂.map (ρ.inv.app M) ≫ s₂.hom.app (T.obj M) ≫ L₂.map (s₁.hom.app M) ≫
      γ.hom.app (F.obj M) := by
  let π : T₀ ⋙ F₂ ⟶ F ⋙ L₀ := Functor.whiskerRight ρ.inv F₂ ≫ Functor.whiskerLeft T s₂.hom ≫
    Functor.whiskerRight s₁.hom L₂ ≫ Functor.whiskerLeft F γ.hom
  suffices hπ : s₀.hom = π from NatTrans.congr_app hπ M
  refine natTrans_ext_of_comp_map_counit aF (fun K => ?_)
  have hK := congrArg (aF₂.homEquiv _ _).symm (h K)
  rw [Stacks.CategoryTheory.BaseChange.homEquiv_symm_map, aF₂.homEquiv_naturality_left_symm,
    aF₂.homEquiv_naturality_left_symm, aF₂.homEquiv_naturality_right_symm,
    Stacks.CategoryTheory.BaseChange.homEquiv_symm_map] at hK
  have h₁ := Stacks.CategoryTheory.BaseChange.homEquiv_symm_map aF aF₁ s₁ (Iso.refl _) K
  rw [Adjunction.homEquiv_counit] at h₁
  have h₂ := s₂.hom.naturality (Stacks.CategoryTheory.BaseChange.map aF aF₁ s₁ (Iso.refl _) K)
  have h₃ := γ.hom.naturality (aF.counit.app K)
  simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp, Functor.comp_map,
    Functor.comp_obj, Functor.id_obj, Category.assoc] at hK h₁ h₂ h₃
  rw [← hK]
  simp only [π, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Functor.comp_obj]
  rw [reassoc_of% h₂, ← L₂.map_comp_assoc, h₁, L₂.map_comp_assoc, h₃]

/-- **The conjugate of a pasted square from the composition of base change maps**:
`conjugateIsoEquiv_pasting`, with the pasting of the squares read off the composition of their base
change maps (`squareIso_hom_app_eq_of_baseChangeMap`). -/
theorem conjugateIsoEquiv_pasting_of_baseChangeMap
    (h : ∀ K : X, ρ.inv.app (G.obj K) ≫
        T₂.map (Stacks.CategoryTheory.BaseChange.map aF aF₁ s₁ (Iso.refl _) K) ≫
        Stacks.CategoryTheory.BaseChange.map aF₁ aF₂ s₂ (Iso.refl _) (L.obj K) ≫
        G₂.map (γ.hom.app K) =
      Stacks.CategoryTheory.BaseChange.map aF aF₂ s₀ (Iso.refl _) K) (M : X₂) :
    G.map ((conjugateEquiv (aL.comp aL₂) aL₀ γ.inv).app M) ≫
        (conjugateIsoEquiv (aF.comp aL₀) (aT₀.comp aF₂) s₀).hom.app M =
      (conjugateIsoEquiv (aF.comp aL) (aT.comp aF₁) s₁).hom.app (P₂.obj M) ≫
        R.map ((conjugateIsoEquiv (aF₁.comp aL₂) (aT₂.comp aF₂) s₂).hom.app M) ≫
        (conjugateEquiv (aT.comp aT₂) aT₀ ρ.inv).app (G₂.obj M) :=
  conjugateIsoEquiv_pasting aF aF₁ aF₂ aT aT₂ aT₀ aL aL₂ aL₀ s₁ s₂ s₀ ρ γ
    (squareIso_hom_app_eq_of_baseChangeMap aF aF₁ aF₂ s₁ s₂ s₀ ρ γ h) M

/-- `conjugateIsoEquiv_pasting_of_baseChangeMap` as an equality of natural transformations. -/
theorem conjugateIsoEquiv_pasting_of_baseChangeMap_natTrans
    (h : ∀ K : X, ρ.inv.app (G.obj K) ≫
        T₂.map (Stacks.CategoryTheory.BaseChange.map aF aF₁ s₁ (Iso.refl _) K) ≫
        Stacks.CategoryTheory.BaseChange.map aF₁ aF₂ s₂ (Iso.refl _) (L.obj K) ≫
        G₂.map (γ.hom.app K) =
      Stacks.CategoryTheory.BaseChange.map aF aF₂ s₀ (Iso.refl _) K) :
    Functor.whiskerRight (conjugateEquiv (aL.comp aL₂) aL₀ γ.inv) G ≫
        (conjugateIsoEquiv (aF.comp aL₀) (aT₀.comp aF₂) s₀).hom =
      Functor.whiskerLeft P₂ (conjugateIsoEquiv (aF.comp aL) (aT.comp aF₁) s₁).hom ≫
        Functor.whiskerRight (conjugateIsoEquiv (aF₁.comp aL₂) (aT₂.comp aF₂) s₂).hom R ≫
        Functor.whiskerLeft G₂ (conjugateEquiv (aT.comp aT₂) aT₀ ρ.inv) := by
  ext M
  exact conjugateIsoEquiv_pasting_of_baseChangeMap aF aF₁ aF₂ aT aT₂ aT₀ aL aL₂ aL₀ s₁ s₂ s₀ ρ γ h M

end CategoryTheory
