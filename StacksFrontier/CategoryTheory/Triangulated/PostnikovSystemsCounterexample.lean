module

public import StacksFrontier.CategoryTheory.Triangulated.PostnikovSystems

/-!
# Uniqueness of morphisms of Postnikov systems: cases (1) and (2)

Cases (1) and (2) of [Stacks, Tag 0FXE] bound the component of a morphism of Postnikov systems on
the totalizations (`CategoryTheory.Triangulated.PostnikovSystem.subsingleton_hom_last`), but not
the whole morphism. This file gives, in any pretriangulated category with a nonzero object, two
Postnikov systems over complexes of length `3` satisfying the hypotheses of both cases and two
different morphisms between them over the same morphism of complexes.

## Main results

* `CategoryTheory.Triangulated.PostnikovSystem.exists_not_subsingleton_hom`: the hypotheses of
  cases (1) and (2) do not determine a morphism of Postnikov systems.

## References

* [Stacks project, Tag 0FXE](https://stacks.math.columbia.edu/tag/0FXE)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-! ### Cases (1) and (2) do not determine the intermediate components

For a nonzero object `B`, the complexes `B ⟶ 0 ⟶ B⟦1⟧ ⟶ 0` and `0 ⟶ B⟦1⟧ ⟶ 0 ⟶ B⟦1⟧⟦1⟧` (written
`X₃ ⟶ X₂ ⟶ X₁ ⟶ X₀`, all differentials zero) carry Postnikov systems with objects
`(Y₀, Y₁, Y₂, Y₃) = (0, B⟦1⟧, B, 0)` and `(Y'₀, Y'₁, Y'₂, Y'₃) = (B⟦1⟧⟦1⟧, B⟦1⟧, 0, 0)`. Both
totalizations vanish, so the hypotheses of cases (1) and (2) hold, yet the zero morphism of
complexes extends both to the zero morphism of Postnikov systems and to the one whose component
`Y₁ ⟶ Y'₁` is the identity of `B⟦1⟧`. -/

section Counterexample

variable (B : D)

/-- The objects `(X₀, X₁, X₂, X₃) = (0, B⟦1⟧, 0, B)` of the first complex. -/
private noncomputable def cexX : Fin 4 → D := ![0, B⟦(1 : ℤ)⟧, 0, B]

/-- The objects `(X'₀, X'₁, X'₂, X'₃) = (B⟦1⟧⟦1⟧, 0, B⟦1⟧, 0)` of the second complex. -/
private noncomputable def cexX' : Fin 4 → D := ![(B⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧, 0, B⟦(1 : ℤ)⟧, 0]

/-- A Postnikov system for `B ⟶ 0 ⟶ B⟦1⟧ ⟶ 0` with objects `(0, B⟦1⟧, B, 0)`. -/
private noncomputable def cexS : PostnikovSystem (cexX B) (fun _ => 0) where
  obj := ![0, B⟦(1 : ℤ)⟧, B, 0]
  π := fun i => match i with
    | ⟨0, _⟩ => 𝟙 _
    | ⟨1, _⟩ => 𝟙 _
    | ⟨2, _⟩ => 0
    | ⟨3, _⟩ => 0
  isIso_π_zero := inferInstanceAs (IsIso (𝟙 (0 : D)))
  p := fun i => match i with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 𝟙 _
  δ := fun i => match i with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 𝟙 _
    | ⟨2, _⟩ => 0
  distinguished := fun i => match i with
    | ⟨0, _⟩ => contractible_distinguished (B⟦(1 : ℤ)⟧)
    | ⟨1, _⟩ => contractible_distinguished₂ B
    | ⟨2, _⟩ => contractible_distinguished₁ B
  p_comp_π := fun i => match i with
    | ⟨0, _⟩ => zero_comp
    | ⟨1, _⟩ => zero_comp
    | ⟨2, _⟩ => comp_zero

/-- A Postnikov system for `0 ⟶ B⟦1⟧ ⟶ 0 ⟶ B⟦1⟧⟦1⟧` with objects `(B⟦1⟧⟦1⟧, B⟦1⟧, 0, 0)`. -/
private noncomputable def cexS' : PostnikovSystem (cexX' B) (fun _ => 0) where
  obj := ![(B⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧, B⟦(1 : ℤ)⟧, 0, 0]
  π := fun i => match i with
    | ⟨0, _⟩ => 𝟙 _
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 0
    | ⟨3, _⟩ => 0
  isIso_π_zero := inferInstanceAs (IsIso (𝟙 ((B⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)))
  p := fun i => match i with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 𝟙 _
    | ⟨2, _⟩ => 𝟙 _
  δ := fun i => match i with
    | ⟨0, _⟩ => 𝟙 _
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 0
  distinguished := fun i => match i with
    | ⟨0, _⟩ => contractible_distinguished₂ (B⟦(1 : ℤ)⟧)
    | ⟨1, _⟩ => contractible_distinguished₁ (B⟦(1 : ℤ)⟧)
    | ⟨2, _⟩ => contractible_distinguished₁ (0 : D)
  p_comp_π := fun i => match i with
    | ⟨0, _⟩ => zero_comp
    | ⟨1, _⟩ => comp_zero
    | ⟨2, _⟩ => comp_zero

/-- The morphism of Postnikov systems `cexS B ⟶ cexS' B` over the zero morphism of complexes
whose component `Y₁ ⟶ Y'₁` is the identity of `B⟦1⟧`, the other components being zero. -/
private noncomputable def cexHom : ∀ i, (cexS B).obj i ⟶ (cexS' B).obj i := fun i => match i with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 𝟙 _
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 0

end Counterexample

/-- Cases (1) and (2) of [Stacks, Tag 0FXE] do not give uniqueness of the whole morphism of
Postnikov systems. In any pretriangulated category with a nonzero object `B` there are complexes
`X₃ ⟶ ⋯ ⟶ X₀` and `X'₃ ⟶ ⋯ ⟶ X'₀`, Postnikov systems `S`, `S'` for them and a morphism of
complexes `f` such that every morphism `Xᵢ⟦i⟧ ⟶ Y'₃⟦3⟧` with `i ≥ 1` is zero (case (1)) and every
morphism `Y₃⟦3⟧ ⟶ X'ⱼ⟦j⟧` with `j < 3` is zero (case (2)), and yet there are two different
morphisms of Postnikov systems `S ⟶ S'` over `f`. Under (1) or (2) the component `Yₙ ⟶ Y'ₙ` on
the totalizations is unique, which is `PostnikovSystem.subsingleton_hom_last`. -/
@[stacks 0FXE "(1), (2): counterexample to uniqueness of the whole morphism of Postnikov systems"]
theorem PostnikovSystem.exists_not_subsingleton_hom (B : D) (hB : ¬ IsZero B) :
    ∃ (X X' : Fin 4 → D) (d : ∀ i : Fin 3, X i.succ ⟶ X i.castSucc)
      (d' : ∀ i : Fin 3, X' i.succ ⟶ X' i.castSucc) (S : PostnikovSystem X d)
      (S' : PostnikovSystem X' d') (f : ∀ i, X i ⟶ X' i),
      (∀ i : Fin 3, d i ≫ f i.castSucc = f i.succ ≫ d' i) ∧
      (∀ i : Fin 4, 0 < (i : ℕ) →
        ∀ u : (X i)⟦((i : ℕ) : ℤ)⟧ ⟶ (S'.obj (Fin.last 3))⟦((3 : ℕ) : ℤ)⟧, u = 0) ∧
      (∀ j : Fin 4, (j : ℕ) < 3 →
        ∀ u : (S.obj (Fin.last 3))⟦((3 : ℕ) : ℤ)⟧ ⟶ (X' j)⟦((j : ℕ) : ℤ)⟧, u = 0) ∧
      ¬ {g : ∀ i, S.obj i ⟶ S'.obj i |
          (∀ i, g i ≫ S'.π i = S.π i ≫ f i) ∧
          (∀ i : Fin 3, S.p i ≫ g i.castSucc = f i.succ ≫ S'.p i) ∧
          (∀ i : Fin 3, S.δ i ≫ (g i.succ)⟦(1 : ℤ)⟧' = g i.castSucc ≫ S'.δ i)}.Subsingleton := by
  refine ⟨cexX B, cexX' B, fun _ => 0, fun _ => 0, cexS B, cexS' B, 0, fun _ => by simp,
    fun _ _ _ => ?_, fun _ _ _ => ?_, fun hs => ?_⟩
  · apply IsZero.eq_of_tgt
    exact Functor.map_isZero _ (isZero_zero D)
  · apply IsZero.eq_of_src
    exact Functor.map_isZero _ (isZero_zero D)
  · have h0 : (0 : ∀ i, (cexS B).obj i ⟶ (cexS' B).obj i) ∈ {g : ∀ i, (cexS B).obj i ⟶
        (cexS' B).obj i |
          (∀ i, g i ≫ (cexS' B).π i = (cexS B).π i ≫ (0 : ∀ i, cexX B i ⟶ cexX' B i) i) ∧
          (∀ i : Fin 3, (cexS B).p i ≫ g i.castSucc =
            (0 : ∀ i, cexX B i ⟶ cexX' B i) i.succ ≫ (cexS' B).p i) ∧
          (∀ i : Fin 3, (cexS B).δ i ≫ (g i.succ)⟦(1 : ℤ)⟧' = g i.castSucc ≫ (cexS' B).δ i)} :=
      ⟨fun _ => by simp, fun _ => by simp, fun _ => by simp⟩
    have h1 : cexHom B ∈ {g : ∀ i, (cexS B).obj i ⟶ (cexS' B).obj i |
          (∀ i, g i ≫ (cexS' B).π i = (cexS B).π i ≫ (0 : ∀ i, cexX B i ⟶ cexX' B i) i) ∧
          (∀ i : Fin 3, (cexS B).p i ≫ g i.castSucc =
            (0 : ∀ i, cexX B i ⟶ cexX' B i) i.succ ≫ (cexS' B).p i) ∧
          (∀ i : Fin 3, (cexS B).δ i ≫ (g i.succ)⟦(1 : ℤ)⟧' = g i.castSucc ≫ (cexS' B).δ i)} := by
      refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
      · match i with
        | ⟨0, _⟩ => exact (zero_comp).trans comp_zero.symm
        | ⟨1, _⟩ => exact (comp_zero).trans comp_zero.symm
        | ⟨2, _⟩ => exact (zero_comp).trans comp_zero.symm
        | ⟨3, _⟩ => exact (zero_comp).trans comp_zero.symm
      · match i with
        | ⟨0, _⟩ => exact (zero_comp).trans zero_comp.symm
        | ⟨1, _⟩ => exact (zero_comp).trans zero_comp.symm
        | ⟨2, _⟩ => exact (comp_zero).trans zero_comp.symm
      · match i with
        | ⟨0, _⟩ => exact (zero_comp).trans zero_comp.symm
        | ⟨1, _⟩ =>
          exact (by simp : 𝟙 (B⟦(1 : ℤ)⟧) ≫ (0 : B ⟶ (0 : D))⟦(1 : ℤ)⟧' = 0).trans comp_zero.symm
        | ⟨2, _⟩ => exact (zero_comp).trans zero_comp.symm
    have h01 : (0 : B⟦(1 : ℤ)⟧ ⟶ B⟦(1 : ℤ)⟧) = 𝟙 _ := congrFun (hs h0 h1) 1
    exact hB (((shiftFunctor D (-1 : ℤ)).map_isZero
      ((IsZero.iff_id_eq_zero _).mpr h01.symm)).of_iso (shiftShiftNeg B (1 : ℤ)).symm)

end CategoryTheory.Triangulated

end
