module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Bijectivity on hom sets through the mate of a 2-square

For a 2-square `α : G ⋙ L₂ ⟶ L₁ ⋙ H` between two adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, with mate
`β : R₁ ⋙ G ⟶ H ⋙ R₂`, the adjoint transpose of `α_c ≫ H φ` is `G (φ♭) ≫ β_d`. Hence, if `α` is
invertible at `c`, `G` is bijective on `c ⟶ R₁ d` and `β` is invertible at `d`, then `H` is
bijective on `L₁ c ⟶ d`.

This is the form in which "restriction on cohomology is the base change map at the level of
derived direct images" is used to compare cohomology groups along a cartesian square.

## Main results

* `Stacks.Adjunction.homEquiv_app_comp_map_eq`
* `Stacks.Adjunction.map_bijective_of_mateEquiv`

## Implementation notes
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Adjunction

section Mate

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)

/-- For a 2-square `α : G ⋙ L₂ ⟶ L₁ ⋙ H` between two adjunctions, with mate
`β : R₁ ⋙ G ⟶ H ⋙ R₂`, the adjoint transpose of `α_c ≫ H φ` is `G` applied to the adjoint
transpose of `φ`, followed by `β_d`. -/
public theorem homEquiv_app_comp_map_eq {c : C} {d : D} (φ : L₁.obj c ⟶ d) :
    adj₂.homEquiv _ _ (α.natTrans.app c ≫ H.map φ) =
      G.map (adj₁.homEquiv _ _ φ) ≫ (mateEquiv adj₁ adj₂ α).natTrans.app d := by
  have h₁ := (mateEquiv adj₁ adj₂ α).natTrans.naturality φ
  have h₂ := unit_mateEquiv adj₁ adj₂ α c
  simp only [Functor.comp_map] at h₁
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, G.map_comp, Category.assoc, h₁,
    ← Category.assoc, h₂, Category.assoc, ← R₂.map_comp]
  rfl

/-- If a 2-square `α` between two adjunctions is invertible, `G` is bijective on `c ⟶ R₁ d` and
the mate of `α` is invertible at `d`, then `H` is bijective on `L₁ c ⟶ d`. -/
public theorem map_bijective_of_mateEquiv (c : C) (d : D) [IsIso (α.natTrans.app c)]
    (hG : Function.Bijective (G.map : (c ⟶ R₁.obj d) → (G.obj c ⟶ G.obj (R₁.obj d))))
    [IsIso ((mateEquiv adj₁ adj₂ α).natTrans.app d)] :
    Function.Bijective (H.map : (L₁.obj c ⟶ d) → (H.obj (L₁.obj c) ⟶ H.obj d)) := by
  have hpost : Function.Bijective
      (fun ψ : G.obj c ⟶ G.obj (R₁.obj d) ↦ ψ ≫ (mateEquiv adj₁ adj₂ α).natTrans.app d) :=
    ⟨fun _ _ h ↦ (cancel_mono _).1 h,
      fun ψ ↦ ⟨ψ ≫ inv ((mateEquiv adj₁ adj₂ α).natTrans.app d), by simp⟩⟩
  have hpre : Function.Bijective
      (fun ψ : H.obj (L₁.obj c) ⟶ H.obj d ↦ α.natTrans.app c ≫ ψ) :=
    ⟨fun _ _ h ↦ (cancel_epi _).1 h, fun ψ ↦ ⟨inv (α.natTrans.app c) ≫ ψ, by simp⟩⟩
  have key : (adj₂.homEquiv _ _) ∘ (fun ψ ↦ α.natTrans.app c ≫ ψ) ∘
      (H.map : (L₁.obj c ⟶ d) → (H.obj (L₁.obj c) ⟶ H.obj d)) =
      (fun ψ ↦ ψ ≫ (mateEquiv adj₁ adj₂ α).natTrans.app d) ∘ G.map ∘ (adj₁.homEquiv _ _) := by
    funext φ
    exact homEquiv_app_comp_map_eq adj₁ adj₂ α φ
  have h : Function.Bijective ((adj₂.homEquiv _ _) ∘ (fun ψ ↦ α.natTrans.app c ≫ ψ) ∘
      (H.map : (L₁.obj c ⟶ d) → (H.obj (L₁.obj c) ⟶ H.obj d))) := by
    rw [key]
    exact (hpost.comp hG).comp (adj₁.homEquiv c d).bijective
  rw [Function.Bijective.of_comp_iff' (adj₂.homEquiv _ _).bijective] at h
  exact (Function.Bijective.of_comp_iff' hpre _).mp h

end Mate

end Stacks.Adjunction

end
