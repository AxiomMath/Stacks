module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The image of a mate under the right adjoint

Consider a square of functors whose rows are adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`,
```
      C ⇄ D
    G ↓   ↓ H
      E ⇄ F
```
and a 2-cell `α : R₁ ⋙ G ⟶ H ⋙ R₂` with mate `τ : G ⋙ L₂ ⟶ L₁ ⋙ H`.  This file computes
`R₂(τ_c) : R₂L₂G(c) ⟶ R₂HL₁(c)` from a transformation `π : R₂L₂G ⟶ GR₁L₁` of the monads
`R₂L₂` and `R₁L₁` along `G`: if `α` carries the `R₂L₂`-action on `R₂H(d)` given by the counit
to the `R₁L₁`-action on `R₁(d)` pushed along `G` and `π`, then `R₂(τ_c) = π_c ≫ α_{L₁c}`.

This is the shape in which the comparison of a derived direct image with derived extension of
coefficients is computed in [Stacks, Remark 0GL6]: `L` is extension of coefficients, `R` is
restriction of coefficients, and `π` is a projection formula.

## Main results

* `CategoryTheory.map_mateEquiv_symm_app_eq`: the formula `R₂(τ_c) = π_c ≫ α_{L₁c}`.
* `CategoryTheory.isIso_mateEquiv_symm_app`: hence `τ_c` is invertible as soon as `π_c` and
  `α_{L₁c}` are and `R₂` reflects isomorphisms.

## References

* [Stacks Project, Remark 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
-/

@[expose] public section

namespace CategoryTheory

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare R₁ H G R₂)
  (π : ∀ c : C, R₂.obj (L₂.obj (G.obj c)) ⟶ G.obj (R₁.obj (L₁.obj c)))
  (hπ : ∀ {c c' : C} (f : c ⟶ c'),
    R₂.map (L₂.map (G.map f)) ≫ π c' = π c ≫ G.map (R₁.map (L₁.map f)))
  (hα : ∀ d : D, R₂.map (L₂.map (α.app d)) ≫ R₂.map (adj₂.counit.app (H.obj d)) =
    π (R₁.obj d) ≫ G.map (R₁.map (adj₁.counit.app d)) ≫ α.app d)

include hπ hα in
/-- **The right adjoint of a mate.**  If `α : R₁ ⋙ G ⟶ H ⋙ R₂` carries the counit action of
`R₂L₂` on `R₂H(d)` to the counit action of `R₁L₁` on `R₁(d)` transported along `π`, then the
mate `τ` of `α` satisfies `R₂(τ_c) = π_c ≫ α_{L₁c}`. -/
theorem map_mateEquiv_symm_app_eq (c : C) :
    R₂.map (((mateEquiv adj₁ adj₂).symm α).app c) = π c ≫ α.app (L₁.obj c) := by
  have hτ : ((mateEquiv adj₁ adj₂).symm α).app c =
      L₂.map (G.map (adj₁.unit.app c) ≫ α.app (L₁.obj c)) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) := by
    rw [unit_mateEquiv_symm adj₁ adj₂ α c]
    simp
  rw [hτ, Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc,
    hα (L₁.obj c), reassoc_of% (hπ (adj₁.unit.app c)), ← G.map_comp_assoc, ← R₁.map_comp,
    adj₁.left_triangle_components, R₁.map_id, G.map_id, Category.id_comp]

include hπ hα in
/-- The mate `τ` of `α` is invertible at `c` when `π_c` and `α_{L₁c}` are and the right adjoint
`R₂` reflects isomorphisms. -/
theorem isIso_mateEquiv_symm_app [R₂.ReflectsIsomorphisms] (c : C) [IsIso (π c)]
    [IsIso (α.app (L₁.obj c))] : IsIso (((mateEquiv adj₁ adj₂).symm α).app c) :=
  (isIso_iff_of_reflects_iso _ R₂).mp
    (map_mateEquiv_symm_app_eq adj₁ adj₂ α π hπ hα c ▸ inferInstance)

end CategoryTheory
