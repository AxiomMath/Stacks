module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Conservative exact right adjoints and generators

Let `F ⊣ G` be an adjunction between pretriangulated categories with `G` exact, and let `E` be a
generator of the target of `G`: an object `K` is zero if and only if every morphism `E⟦n⟧ ⟶ K`
vanishes. Then the following are equivalent: `G K = 0` only for `K = 0`; `G` reflects
isomorphisms; `F E` is a generator of the source of `G`. This is the formal content of
[Stacks, Tag 0E4R].

## Main results

* `CategoryTheory.Pretriangulated.tfae_reflectsIsomorphisms_of_adjunction`
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits

variable {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [G.CommShift ℤ] [G.IsTriangulated]

/-- Morphisms `(F E)⟦n⟧ ⟶ K` correspond to morphisms `E⟦n⟧ ⟶ G K`. -/
def shiftHomEquivOfAdjunction (E : D) (K : C) (n : ℤ) :
    ((F.obj E)⟦n⟧ ⟶ K) ≃ (E⟦n⟧ ⟶ G.obj K) :=
  ((shiftEquiv C n).toAdjunction.homEquiv _ _).trans
    ((adj.homEquiv _ _).trans
      ((Iso.homCongr (Iso.refl E) ((G.commShiftIso (-n)).app K)).trans
        ((shiftEquiv D n).toAdjunction.homEquiv _ _).symm))

include adj in
/-- **[Stacks, Tag 0E4R], formally.** For `F ⊣ G` with `G` exact and `E` a generator of the
target of `G`, the following are equivalent: (1) `G K = 0` if and only if `K = 0`; (2) `G`
reflects isomorphisms; (3) `F E` is a generator of the source of `G`. -/
theorem tfae_reflectsIsomorphisms_of_adjunction (E : D)
    (hE : ∀ K : D, IsZero K ↔ ∀ n : ℤ, Subsingleton (E⟦n⟧ ⟶ K)) :
    List.TFAE [∀ K : C, IsZero (G.obj K) ↔ IsZero K, G.ReflectsIsomorphisms,
      ∀ K : C, IsZero K ↔ ∀ n : ℤ, Subsingleton ((F.obj E)⟦n⟧ ⟶ K)] := by
  tfae_have 1 → 2 := by
    intro h
    refine ⟨fun {A B} φ hφ => ?_⟩
    obtain ⟨Z, g, k, mem⟩ := distinguished_cocone_triangle φ
    have hT := G.map_distinguished _ mem
    have h₃ : IsZero (G.obj Z) :=
      (Triangle.isZero₃_iff_isIso₁ _ hT).2 (hφ : IsIso (G.map φ))
    exact (Triangle.isZero₃_iff_isIso₁ _ mem).1 ((h Z).1 h₃)
  tfae_have 2 → 1 := by
    intro h K
    refine ⟨fun hK => ?_, fun hK => G.map_isZero hK⟩
    have : IsIso (G.map (0 : K ⟶ K)) := by
      rw [G.map_zero]
      exact ⟨⟨0, hK.eq_of_src _ _, hK.eq_of_src _ _⟩⟩
    have : IsIso (0 : K ⟶ K) := isIso_of_reflects_iso _ G
    exact IsZero.of_mono_zero K K
  tfae_have 1 ↔ 3 := by
    have key : ∀ K : C, (∀ n : ℤ, Subsingleton ((F.obj E)⟦n⟧ ⟶ K)) ↔ IsZero (G.obj K) :=
      fun K => (forall_congr' fun n =>
        (shiftHomEquivOfAdjunction adj E K n).subsingleton_congr).trans (hE (G.obj K)).symm
    exact ⟨fun h K => (h K).symm.trans (key K).symm,
      fun h K => (key K).symm.trans (h K).symm⟩
  tfae_finish

end CategoryTheory.Pretriangulated
