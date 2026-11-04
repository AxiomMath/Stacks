module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Pulling back a twist relation along a base change

Let `I_Y : C₀ ⥤ 𝒴` and `I_Z : C₁ ⥤ 𝒵` be two functors, `G : C₀ ⥤ C₁`, `F ⊣ R` an adjunction
`F : 𝒴 ⥤ 𝒵`, and `c : I_Y ⋙ F ≅ G ⋙ I_Z`. Let `τ_Y : I_Y ⟶ I_Y ⋙ D_Y` and `τ_Z : I_Z ⟶ I_Z ⋙ D_Z`
be two "twists", compatible with the base change maps `β_L = η ≫ R(c_L) : I_Y L ⟶ R I_Z G L`
through an identification `ν : D_Z ⋙ R ≅ R ⋙ D_Y`. If a morphism `u₀ : I_Y L' ⟶ I_Y L` carries the
twist of `L` to the twist of `L'` followed by an endomorphism `b` of `L'`, then its base change
`c⁻¹ ≫ F u₀ ≫ c : I_Z G L' ⟶ I_Z G L` carries the twist of `G L` to that of `G L'` followed by
`G b`.

This is the formal part of the computation of the Frobenius twist of a sheaf pulled back from the
base field (the twists being the Frobenius twists over `k̄`, `G` the inverse image along a
morphism over `k`, and `F` the inverse image along its base change to `k̄`).

## Main results

* `CategoryTheory.Adjunction.twist_relation_of_baseChange`: a twist relation pulls back along a
  base change.
* `CategoryTheory.Adjunction.twist_relation_conj`: a twist relation transports along isomorphisms
  of the objects.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C₀ C₁ 𝒴 𝒵 : Type*} [Category C₀] [Category C₁] [Category 𝒴] [Category 𝒵]
  (IY : C₀ ⥤ 𝒴) (IZ : C₁ ⥤ 𝒵) (G : C₀ ⥤ C₁) {F : 𝒴 ⥤ 𝒵} {R : 𝒵 ⥤ 𝒴} (A : F ⊣ R)
  (c : IY ⋙ F ≅ G ⋙ IZ) (DY : 𝒴 ⥤ 𝒴) (DZ : 𝒵 ⥤ 𝒵) (ν : DZ ⋙ R ≅ R ⋙ DY)
  (τY : IY ⟶ IY ⋙ DY) (τZ : IZ ⟶ IZ ⋙ DZ)

/-- The base change maps `η ≫ R c` are natural: `g` is the base change of `f`. -/
private theorem unit_comp_map_comp_eq {L M : C₀} (f : IY.obj L ⟶ IY.obj M)
    (g : IZ.obj (G.obj L) ⟶ IZ.obj (G.obj M)) (hfg : c.hom.app L ≫ g = F.map f ≫ c.hom.app M) :
    (A.unit.app (IY.obj L) ≫ R.map (c.hom.app L)) ≫ R.map g =
      f ≫ A.unit.app (IY.obj M) ≫ R.map (c.hom.app M) := by
  rw [Category.assoc, ← R.map_comp, hfg, R.map_comp, ← Category.assoc, ← Functor.comp_map,
    ← A.unit.naturality, Functor.id_map, Category.assoc]

/-- **A twist relation pulls back along a base change.** -/
theorem twist_relation_of_baseChange
    (hPB : ∀ L, (A.unit.app (IY.obj L) ≫ R.map (c.hom.app L)) ≫ R.map (τZ.app (G.obj L)) ≫
        ν.hom.app (IZ.obj (G.obj L)) =
          τY.app L ≫ DY.map (A.unit.app (IY.obj L) ≫ R.map (c.hom.app L)))
    {L L' : C₀} (u₀ : IY.obj L' ⟶ IY.obj L) (b : L' ⟶ L')
    (h₀ : u₀ ≫ τY.app L = τY.app L' ≫ DY.map (IY.map b) ≫ DY.map u₀) :
    (c.inv.app L' ≫ F.map u₀ ≫ c.hom.app L) ≫ τZ.app (G.obj L) =
      τZ.app (G.obj L') ≫ DZ.map (IZ.map (G.map b)) ≫
        DZ.map (c.inv.app L' ≫ F.map u₀ ≫ c.hom.app L) := by
  have hβu := unit_comp_map_comp_eq IY IZ G A c u₀ (c.inv.app L' ≫ F.map u₀ ≫ c.hom.app L) (by simp)
  have hβb := unit_comp_map_comp_eq IY IZ G A c (IY.map b) (IZ.map (G.map b))
    (c.hom.naturality b).symm
  generalize c.inv.app L' ≫ F.map u₀ ≫ c.hom.app L = u at hβu ⊢
  have hν := ν.hom.naturality (IZ.map (G.map b) ≫ u)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hν
  have hDβb := congrArg DY.map hβb
  have hDβu := congrArg DY.map hβu
  have hPB' := hPB L'
  have hPBL := hPB L
  simp only [Functor.map_comp, Category.assoc] at hβu hν hDβb hDβu hPB' hPBL ⊢
  rw [← cancel_epi (c.hom.app L')]
  apply (A.homEquiv _ _).injective
  rw [← cancel_mono (ν.hom.app (IZ.obj (G.obj L))), Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hβu, hPBL, reassoc_of% h₀, hν, reassoc_of% hPB', reassoc_of% hDβb, hDβu]

omit [Category C₀] [Category 𝒴] in
/-- **A twist relation transports along isomorphisms of the objects.** If `w : I K₂' ⟶ I K₂` is an
isomorphism carrying the twist of `K₂` to that of `K₂'` followed by `b`, and `a : K₁ ≅ K₂`,
`a' : K₁' ≅ K₂'` with `b₁ ≫ a' = a' ≫ b`, then `I a ≫ w⁻¹ ≫ I a'⁻¹ : I K₁ ⟶ I K₁'` carries the
twist of `K₁` to that of `K₁'` followed by `b₁`. -/
theorem twist_relation_conj {K₁ K₂ K₁' K₂' : C₁} (a : K₁ ≅ K₂) (a' : K₁' ≅ K₂')
    (w : IZ.obj K₂' ⟶ IZ.obj K₂) [IsIso w] (b : K₂' ⟶ K₂') (b₁ : K₁' ⟶ K₁')
    (hb : b₁ ≫ a'.hom = a'.hom ≫ b)
    (h : w ≫ τZ.app K₂ = τZ.app K₂' ≫ DZ.map (IZ.map b) ≫ DZ.map w) :
    τZ.app K₁ ≫ DZ.map (IZ.map a.hom ≫ inv w ≫ IZ.map a'.inv) =
      (IZ.map a.hom ≫ inv w ≫ IZ.map a'.inv) ≫ τZ.app K₁' ≫ DZ.map (IZ.map b₁) := by
  have n₁ := τZ.naturality a.hom
  have n₂ := τZ.naturality a'.inv
  have hb' : a'.inv ≫ b₁ = b ≫ a'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h' : inv w ≫ τZ.app K₂' ≫ DZ.map (IZ.map b) = τZ.app K₂ ≫ DZ.map (inv w) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, h]
    simp only [Category.assoc, ← DZ.map_comp, IsIso.hom_inv_id, Category.comp_id]
  dsimp only [Functor.comp_map] at n₁ n₂
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% n₁, reassoc_of% n₂, ← DZ.map_comp (IZ.map a'.inv) (IZ.map b₁),
    ← IZ.map_comp, hb', IZ.map_comp, DZ.map_comp, reassoc_of% h']

end CategoryTheory.Adjunction
