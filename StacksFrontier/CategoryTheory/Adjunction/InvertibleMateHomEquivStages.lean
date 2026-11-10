module

public import StacksFrontier.CategoryTheory.Adjunction.InvertibleMateHomEquiv

/-!
# Homomorphisms out of a base-changed left adjoint, along a tower of base changes

Let `ℓ ⊣ r` be an adjunction with `ℓ : C ⥤ D`, and let `e : r ⋙ G ⟶ H ⋙ r'` be a comparison
for functors `G : C ⥤ E`, `H : D ⥤ F`, `r' : F ⥤ E`. Then a morphism `x : H(ℓ A) ⟶ H K` gives the
morphism `G(η_A) ≫ e_{ℓ A} ≫ r' x ≫ e_K⁻¹ : G A ⟶ G(r K)`. When `ℓ'` is a left adjoint of `r'`
and the mate of `e` is invertible at `A`, this is the bijection
`CategoryTheory.Adjunction.homEquivOfIsIsoMate` followed by `e_K⁻¹`
(`CategoryTheory.Adjunction.stageMateEquiv`).

The construction is compatible with composing base changes: for a second comparison
`e' : r' ⋙ G' ⟶ H' ⋙ r''` and a comparison `e₂ : r ⋙ G₂ ⟶ H₂ ⋙ r''` which is the pasting of `e`
and `e'` read through isomorphisms `G' ∘ G ≅ G₂`, `H' ∘ H ≅ H₂`, carrying a morphism along `H'`
and then applying the construction for `e₂` is applying the construction for `e` and then carrying
the result along `G'`.

## Main definitions

* `stageMateHom`: The morphism `G(η_A) ≫ e_{ℓ A} ≫ r' x ≫ e_K⁻¹` attached to `x`.
* `stageMateEquiv`: The bijection `Hom(H(ℓ A), H K) ≃ Hom(G A, G(r K))` given by `stageMateHom`.

## Main results

* `stageMateHom_bijective`: `stageMateHom` is bijective when the mate of `e` is invertible at `A`.
* `stageMateHom_comp`: `stageMateHom` is compatible with composing base changes.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

section Single

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄} [Category.{v₁} C]
  [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {ℓ : C ⥤ D} {r : D ⥤ C} (adj : ℓ ⊣ r) {r' : F ⥤ E}
  {G : C ⥤ E} {H : D ⥤ F} (e : TwoSquare r H G r')

/-- The morphism `G(η_A) ≫ e_{ℓ A} ≫ r' x ≫ e_K⁻¹ : G A ⟶ G(r K)` attached to a morphism
`x : H(ℓ A) ⟶ H K`. -/
def stageMateHom (A : C) (K : D) [IsIso (e.app K)] (x : H.obj (ℓ.obj A) ⟶ H.obj K) :
    G.obj A ⟶ G.obj (r.obj K) :=
  G.map (adj.unit.app A) ≫ e.app (ℓ.obj A) ≫ r'.map x ≫ inv (e.app K)

/-- **`CategoryTheory.Adjunction.homEquivOfIsIsoMate` through the unit**: the bijection sends `x`
to `G(η_A) ≫ e_{ℓ A} ≫ r' x`. -/
theorem homEquivOfIsIsoMate_eq {ℓ' : E ⥤ F} (adj' : ℓ' ⊣ r') (A : C)
    [IsIso (((mateEquiv adj adj').symm e).app A)] (Y : F) (x : H.obj (ℓ.obj A) ⟶ Y) :
    homEquivOfIsIsoMate adj adj' e A Y x = G.map (adj.unit.app A) ≫ e.app (ℓ.obj A) ≫ r'.map x := by
  rw [homEquivOfIsIsoMate_apply, adj'.homEquiv_naturality_right, adj'.homEquiv_unit,
    ← Category.assoc]
  exact congrArg (· ≫ r'.map x) (unit_mateEquiv_symm adj adj' e A).symm

/-- **The bijection `Hom(H(ℓ A), H K) ≃ Hom(G A, G(r K))`** when the mate of `e` is invertible at
`A` and `e` is invertible at `K`; it is `CategoryTheory.Adjunction.stageMateHom`. -/
def stageMateEquiv {ℓ' : E ⥤ F} (adj' : ℓ' ⊣ r') (A : C)
    [IsIso (((mateEquiv adj adj').symm e).app A)] (K : D) [IsIso (e.app K)] :
    (H.obj (ℓ.obj A) ⟶ H.obj K) ≃ (G.obj A ⟶ G.obj (r.obj K)) :=
  (homEquivOfIsIsoMate adj adj' e A (H.obj K)).trans
    { toFun := fun y => y ≫ inv (e.app K)
      invFun := fun z => z ≫ e.app K
      left_inv := fun y => by simp
      right_inv := fun z => by simp }

/-- `CategoryTheory.Adjunction.stageMateEquiv` sends `x` to `stageMateHom adj e A K x`. -/
theorem stageMateEquiv_apply {ℓ' : E ⥤ F} (adj' : ℓ' ⊣ r') (A : C)
    [IsIso (((mateEquiv adj adj').symm e).app A)] (K : D) [IsIso (e.app K)]
    (x : H.obj (ℓ.obj A) ⟶ H.obj K) :
    stageMateEquiv adj e adj' A K x = stageMateHom adj e A K x := by
  simp only [stageMateEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, homEquivOfIsIsoMate_eq,
    stageMateHom, Category.assoc]

/-- The map `x ↦ G(η_A) ≫ e_{ℓ A} ≫ r' x ≫ e_K⁻¹` is bijective when `ℓ'` is a left adjoint of
`r'`, the mate of `e` is invertible at `A` and `e` is invertible at `K`. -/
theorem stageMateHom_bijective {ℓ' : E ⥤ F} (adj' : ℓ' ⊣ r') (A : C)
    [IsIso (((mateEquiv adj adj').symm e).app A)] (K : D) [IsIso (e.app K)] :
    Function.Bijective (stageMateHom adj e A K) := by
  have h := (stageMateEquiv adj e adj' A K).bijective
  rwa [show ⇑(stageMateEquiv adj e adj' A K) = stageMateHom adj e A K from
    funext (stageMateEquiv_apply adj e adj' A K)] at h

end Single

section Tower

variable {C₀ : Type u₁} {D₀ : Type u₂} {C₁ : Type u₃} {D₁ : Type u₄} {C₂ : Type u₅}
  {D₂ : Type u₆} [Category.{v₁} C₀] [Category.{v₂} D₀] [Category.{v₃} C₁] [Category.{v₄} D₁]
  [Category.{v₅} C₂] [Category.{v₆} D₂]
  {ℓ₀ : C₀ ⥤ D₀} {r₀ : D₀ ⥤ C₀} (adj₀ : ℓ₀ ⊣ r₀) {r₁ : D₁ ⥤ C₁} {r₂ : D₂ ⥤ C₂}
  {G₁ : C₀ ⥤ C₁} {H₁ : D₀ ⥤ D₁} {G' : C₁ ⥤ C₂} {H' : D₁ ⥤ D₂} {G₂ : C₀ ⥤ C₂} {H₂ : D₀ ⥤ D₂}
  (e₁ : TwoSquare r₀ H₁ G₁ r₁) (e' : TwoSquare r₁ H' G' r₂) (e₂ : TwoSquare r₀ H₂ G₂ r₂)
  (cG : ∀ X : C₀, G'.obj (G₁.obj X) ≅ G₂.obj X) (cH : ∀ Z : D₀, H'.obj (H₁.obj Z) ≅ H₂.obj Z)

/-- **`CategoryTheory.Adjunction.stageMateHom` is compatible with composing base changes.** If
`e₂` is the pasting of `e₁` and `e'` read through the isomorphisms `cG : G' ∘ G₁ ≅ G₂` (natural)
and `cH : H' ∘ H₁ ≅ H₂`, then carrying `x : H₁(ℓ₀ A) ⟶ H₁ K` along `H'` and applying the
construction for `e₂` is applying the construction for `e₁` and carrying the result along `G'`. -/
theorem stageMateHom_comp (A : C₀) (K : D₀) [IsIso (e₁.app K)] [IsIso (e₂.app K)]
    (hcG : ∀ (X Y : C₀) (φ : X ⟶ Y), G'.map (G₁.map φ) ≫ (cG Y).hom = (cG X).hom ≫ G₂.map φ)
    (hpaste : ∀ Z : D₀, e₂.app Z =
      (cG (r₀.obj Z)).inv ≫ G'.map (e₁.app Z) ≫ e'.app (H₁.obj Z) ≫ r₂.map (cH Z).hom)
    (x : H₁.obj (ℓ₀.obj A) ⟶ H₁.obj K) :
    stageMateHom adj₀ e₂ A K ((cH (ℓ₀.obj A)).inv ≫ H'.map x ≫ (cH K).hom) =
      (cG A).inv ≫ G'.map (stageMateHom adj₀ e₁ A K x) ≫ (cG (r₀.obj K)).hom := by
  rw [← cancel_mono (e₂.app K)]
  simp only [stageMateHom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hpaste (ℓ₀.obj A), hpaste K]
  simp only [Category.assoc, Functor.map_comp, Functor.map_inv, IsIso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_map_assoc]
  have h₁ : G₂.map (adj₀.unit.app A) ≫ (cG (r₀.obj (ℓ₀.obj A))).inv =
      (cG A).inv ≫ G'.map (G₁.map (adj₀.unit.app A)) := by
    rw [Iso.comp_inv_eq]
    exact (Iso.inv_hom_id_assoc (cG A) _).symm.trans
      ((congrArg ((cG A).inv ≫ ·) (hcG A (r₀.obj (ℓ₀.obj A)) (adj₀.unit.app A)).symm).trans
        (Category.assoc _ _ _).symm)
  have h₂ := e'.naturality x
  simp only [Functor.comp_map] at h₂
  rw [reassoc_of% h₁, ← reassoc_of% h₂]

end Tower

end CategoryTheory.Adjunction
