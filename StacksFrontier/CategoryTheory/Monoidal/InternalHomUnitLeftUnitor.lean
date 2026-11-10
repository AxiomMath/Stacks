module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomEvaluationBijection
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomUnitHomothety

/-!
Morphisms whose whiskering recovers the left unitor.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **A homothety differs from a section with the unit property by an automorphism of the unit
object.** Let `c : A ⊗ K ⟶ K` exhibit `A` as an internal hom from `K` to `K` and let
`a : 𝟙_ C ⟶ A` be a homothety. If `b : 𝟙_ C ⟶ A` is such that `φ ↦ φ ≫ b` is a bijection
`End (𝟙_ C) ⟶ Hom(𝟙_ C, A)`, then `a = u ≫ b` for an automorphism `u` of `𝟙_ C`.

The composition `m` on `A` has `a` as a left unit, so `a ≫ r = b` for
`r = (ρ_ A).inv ≫ (A ◁ b) ≫ m`; writing `a = u ≫ b` and `b ≫ r = v ≫ b` gives `u ≫ v = 𝟙` by
injectivity, and endomorphisms of `𝟙_ C` commute. -/
theorem exists_isIso_comp_eq_of_whiskerRight_comp_eq_leftUnitor {K A : C} (c : A ⊗ K ⟶ K)
    (hc : ∀ Z : C, Function.Bijective fun x : Z ⟶ A => x ▷ K ≫ c)
    {a : 𝟙_ C ⟶ A} (ha : a ▷ K ≫ c = (λ_ K).hom) {b : 𝟙_ C ⟶ A}
    (hb : Function.Bijective fun φ : 𝟙_ C ⟶ 𝟙_ C => φ ≫ b) :
    ∃ u : 𝟙_ C ⟶ 𝟙_ C, IsIso u ∧ u ≫ b = a := by
  obtain ⟨u, hu⟩ := hb.2 a
  dsimp only at hu
  have hm := whiskerRight_comp_internalHomMul c hc ha
  have hab : a ≫ (ρ_ A).inv ≫ A ◁ b ≫ internalHomMul c hc = b := by
    rw [rightUnitor_inv_naturality_assoc, ← unitors_inv_equal, ← whisker_exchange_assoc, hm,
      leftUnitor_naturality, Iso.inv_hom_id_assoc]
  obtain ⟨v, hv⟩ := hb.2 (b ≫ (ρ_ A).inv ≫ A ◁ b ≫ internalHomMul c hc)
  dsimp only at hv
  have huv : u ≫ v = 𝟙 _ := by
    refine hb.1 ?_
    change (u ≫ v) ≫ b = 𝟙 _ ≫ b
    rw [Category.assoc, hv, ← Category.assoc, hu, hab, Category.id_comp]
  exact ⟨u, ⟨v, huv, (comp_comm_tensorUnit v u).trans huv⟩, hu⟩

/-- **Postcomposition with a homothety is bijective exactly when postcomposition with another
section is**, if that section induces a bijection `End (𝟙_ C) ⟶ Hom(𝟙_ C, A)`: the two differ by
an automorphism of `𝟙_ C`
(`CategoryTheory.MonoidalCategory.exists_isIso_comp_eq_of_whiskerRight_comp_eq_leftUnitor`). -/
theorem bijective_comp_iff_of_whiskerRight_comp_eq_leftUnitor {K A : C} (c : A ⊗ K ⟶ K)
    (hc : ∀ Z : C, Function.Bijective fun x : Z ⟶ A => x ▷ K ≫ c)
    {a : 𝟙_ C ⟶ A} (ha : a ▷ K ≫ c = (λ_ K).hom) {b : 𝟙_ C ⟶ A}
    (hb : Function.Bijective fun φ : 𝟙_ C ⟶ 𝟙_ C => φ ≫ b) (Z : C) :
    (Function.Bijective fun φ : Z ⟶ 𝟙_ C => φ ≫ a) ↔
      Function.Bijective fun φ : Z ⟶ 𝟙_ C => φ ≫ b := by
  obtain ⟨u, hu, rfl⟩ := exists_isIso_comp_eq_of_whiskerRight_comp_eq_leftUnitor c hc ha hb
  have e : (fun φ : Z ⟶ 𝟙_ C => φ ≫ u ≫ b) =
      (fun φ : Z ⟶ 𝟙_ C => φ ≫ b) ∘ (fun φ : Z ⟶ 𝟙_ C => φ ≫ u) := by
    funext φ
    simp
  have hu' : Function.Bijective fun φ : Z ⟶ 𝟙_ C => φ ≫ u :=
    ⟨fun φ ψ h => by simpa using congrArg (· ≫ inv u) h,
      fun ψ => ⟨ψ ≫ inv u, by simp⟩⟩
  rw [e, Function.Bijective.of_comp_iff _ hu']

end CategoryTheory.MonoidalCategory

end
