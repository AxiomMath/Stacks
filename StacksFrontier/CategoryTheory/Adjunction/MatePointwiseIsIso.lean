module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# A transpose of a mate is invertible at an object where the vertical functors are bijective

Consider adjunctions `L ⊣ R` (with `L : C' ⥤ D'`) and `L' ⊣ R'` (with `L' : C ⥤ D`), functors
`H : C' ⥤ C` and `K : D' ⥤ D`, and a natural isomorphism `β : R ⋙ H ⟶ K ⋙ R'`. At an object
`G` of `C'` the composite

`θ : H G ⟶ H (R (L G)) ⟶ R' (K (L G))`

of `H` applied to the unit and of `β` has a transpose `L' (H G) ⟶ K (L G)` along `L' ⊣ R'`, which
is the mate of `β` at `G`. This file shows that the transpose is an isomorphism as soon as `H` and
`K` are bijective on the morphism groups that occur, which is a pointwise form of the fact that the
mate of an isomorphism along two equivalences is an isomorphism.

## Main results

* `CategoryTheory.Adjunction.isIso_homEquiv_symm_map_unit_comp_of_bijective`: the transpose of
  `θ` is an isomorphism.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C' : Type u₁} {D' : Type u₂} {C : Type u₃} {D : Type u₄} [Category.{v₁} C']
  [Category.{v₂} D'] [Category.{v₃} C] [Category.{v₄} D]

/-- Let `L ⊣ R` and `L' ⊣ R'` be adjunctions, `β : R ⋙ H ⟶ K ⋙ R'` a natural isomorphism and `G`
an object of `C'`. Suppose that every object of `D` is isomorphic to `K N'` for some `N'` with
`P N'`, and that for such `N'` the functor `K` is bijective on `L G ⟶ N'` and `H` is bijective on
`G ⟶ R N'`. Then the transpose along `L' ⊣ R'` of `H (η_G) ≫ β (L G) : H G ⟶ R' (K (L G))` is an
isomorphism. -/
theorem isIso_homEquiv_symm_map_unit_comp_of_bijective {L : C' ⥤ D'} {R : D' ⥤ C'}
    (adj : L ⊣ R) {L' : C ⥤ D} {R' : D ⥤ C} (adj' : L' ⊣ R') (H : C' ⥤ C) (K : D' ⥤ D)
    (β : R ⋙ H ⟶ K ⋙ R') [IsIso β] (G : C') (P : D' → Prop)
    (hess : ∀ N : D, ∃ N' : D', P N' ∧ Nonempty (K.obj N' ≅ N))
    (hK : ∀ N' : D', P N' → Function.Bijective (fun χ : L.obj G ⟶ N' => K.map χ))
    (hH : ∀ N' : D', P N' → Function.Bijective (fun χ : G ⟶ R.obj N' => H.map χ)) :
    IsIso ((adj'.homEquiv _ _).symm (H.map (adj.unit.app G) ≫ β.app (L.obj G))) := by
  set θ := H.map (adj.unit.app G) ≫ β.app (L.obj G)
  rw [isIso_iff_coyoneda_map_bijective]
  intro T
  obtain ⟨N', hN', ⟨e⟩⟩ := hess T
  have hred : Function.Bijective (fun ψ : K.obj (L.obj G) ⟶ K.obj N' =>
      (adj'.homEquiv _ _).symm θ ≫ ψ) := by
    have hcomp : (fun χ : L.obj G ⟶ N' => adj'.homEquiv _ _ ((adj'.homEquiv _ _).symm θ ≫
        K.map χ)) = (fun χ' : G ⟶ R.obj N' => H.map χ' ≫ β.app N') ∘
          (fun χ : L.obj G ⟶ N' => adj.homEquiv _ _ χ) := by
      funext χ
      have hβ := β.naturality χ
      simp only [Functor.comp_map] at hβ
      simp only [Function.comp_apply, Adjunction.homEquiv_naturality_right,
        Equiv.apply_symm_apply, θ, Category.assoc, adj.homEquiv_unit, Functor.map_comp, hβ]
    have h₁ : Function.Bijective (fun χ' : G ⟶ R.obj N' => H.map χ' ≫ β.app N') :=
      (((asIso (β.app N')).homToEquiv).bijective.comp (hH N' hN') :)
    have h₂ := h₁.comp (adj.homEquiv G N').bijective
    rw [← hcomp] at h₂
    have h₃ : Function.Bijective (fun ψ : K.obj (L.obj G) ⟶ K.obj N' =>
        adj'.homEquiv _ _ ((adj'.homEquiv _ _).symm θ ≫ ψ)) :=
      (Function.Bijective.of_comp_iff _ (hK N' hN')).1 h₂
    exact (Function.Bijective.of_comp_iff' (adj'.homEquiv _ _).bijective _).1 h₃
  have hT : (fun ψ : K.obj (L.obj G) ⟶ T => (adj'.homEquiv _ _).symm θ ≫ ψ) =
      (fun ψ => ψ ≫ e.hom) ∘ (fun ψ : K.obj (L.obj G) ⟶ K.obj N' =>
        (adj'.homEquiv _ _).symm θ ≫ ψ) ∘ (fun ψ => ψ ≫ e.inv) := by
    funext ψ
    simp
  rw [hT]
  exact e.homToEquiv.bijective.comp (hred.comp e.symm.homToEquiv.bijective)

end CategoryTheory.Adjunction
