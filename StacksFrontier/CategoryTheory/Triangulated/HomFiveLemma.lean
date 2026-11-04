module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# The five lemma for maps out of the shifts of an object

Let `C` be a pre-triangulated category, let `φ : T ⟶ T'` be a morphism between distinguished
triangles and let `X` be an object of `C`. If composition with two of the three components of `φ`
is bijective on morphisms out of every shift `X⟦k⟧`, then so is composition with the third.

This is the five lemma for the homological functor `Hom(X, -)`, run on the long exact sequences of
`T` and `T'`; it is stated elementwise, so that it applies to an object `X` which is not assumed
to have any property, and to a morphism of triangles `φ` whose components are not isomorphisms.
It is the form in which a comparison of derived limits is checked against perfect objects: in the
proof of Stacks 0D3F the canonical map `𝒪_X ⊗_R (lim M_n) ⟶ lim (𝒪_X ⊗_R M_n)` is the first
component of a morphism of triangles whose other two components are the comparison
`𝒪_X ⊗_R ∏ M_n ⟶ ∏ 𝒪_X ⊗_R M_n`, and maps out of a perfect object are tested there.

## Main results

* `CategoryTheory.Pretriangulated.bijective_comp_iff_of_source_iso`: bijectivity of composition
  with a morphism is invariant under replacing the source of the test maps by an isomorphic
  object.
* `CategoryTheory.Pretriangulated.bijective_comp_shift_map_iff`: it is invariant under shifting
  both the test object and the morphism.
* `CategoryTheory.Pretriangulated.bijective_comp_hom₃_of_triangle`: the five lemma at the third
  vertex, for a single test object.
* `CategoryTheory.Pretriangulated.bijective_comp_hom₃_of_forall_shift`,
  `CategoryTheory.Pretriangulated.bijective_comp_hom₁_of_forall_shift`: the five lemma at the
  third and first vertices, for all shifts of a test object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Bijectivity of composition with `u` on morphisms out of an object depends on that object only
up to isomorphism. -/
theorem bijective_comp_iff_of_source_iso {Y Y' A B : C} (e : Y ≅ Y') (u : A ⟶ B) :
    Function.Bijective (fun a : Y ⟶ A => a ≫ u) ↔
      Function.Bijective (fun a : Y' ⟶ A => a ≫ u) := by
  let eA : (Y' ⟶ A) ≃ (Y ⟶ A) :=
    ⟨fun a => e.hom ≫ a, fun a => e.inv ≫ a, fun a => by simp, fun a => by simp⟩
  let eB : (Y' ⟶ B) ≃ (Y ⟶ B) :=
    ⟨fun a => e.hom ≫ a, fun a => e.inv ≫ a, fun a => by simp, fun a => by simp⟩
  have hcomp : (fun a : Y ⟶ A => a ≫ u) =
      eB ∘ (fun a : Y' ⟶ A => a ≫ u) ∘ eA.symm := by
    funext a
    simp [eA, eB]
  rw [hcomp, eB.bijective.of_comp_iff', eA.symm.bijective.of_comp_iff]

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Bijectivity of composition with `u` on morphisms out of `Y` is equivalent to bijectivity of
composition with `u⟦n⟧'` on morphisms out of `Y⟦n⟧`, the shift functor being an equivalence. -/
theorem bijective_comp_shift_map_iff {Y A B : C} (u : A ⟶ B) (n : ℤ) :
    Function.Bijective (fun a : Y ⟶ A => a ≫ u) ↔
      Function.Bijective (fun a : Y⟦n⟧ ⟶ A⟦n⟧ => a ≫ u⟦n⟧') := by
  have hmap (Z : C) : Function.Bijective
      ((shiftFunctor C n).map : (Y ⟶ Z) → (Y⟦n⟧ ⟶ Z⟦n⟧)) :=
    ⟨fun _ _ h => (shiftFunctor C n).map_injective h, fun a => (shiftFunctor C n).map_surjective a⟩
  have hcomp : (shiftFunctor C n).map ∘ (fun a : Y ⟶ A => a ≫ u) =
      (fun a : Y⟦n⟧ ⟶ A⟦n⟧ => a ≫ u⟦n⟧') ∘ (shiftFunctor C n).map := by
    funext a
    simp
  rw [← (hmap B).of_comp_iff' (fun a : Y ⟶ A => a ≫ u), hcomp, (hmap A).of_comp_iff]

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- If composition with `u` is bijective on morphisms out of every shift of `X`, then so is
composition with any shift `u⟦n⟧'`. -/
theorem bijective_comp_shift_map_of_forall {X A B : C} {u : A ⟶ B}
    (hu : ∀ k : ℤ, Function.Bijective (fun a : X⟦k⟧ ⟶ A => a ≫ u)) (n k : ℤ) :
    Function.Bijective (fun a : X⟦k⟧ ⟶ A⟦n⟧ => a ≫ u⟦n⟧') :=
  (bijective_comp_iff_of_source_iso ((shiftFunctorAdd' C (k - n) n k (by omega)).app X).symm _).1
    ((bijective_comp_shift_map_iff u n).1 (hu (k - n)))

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Conversely, if composition with a shift `u⟦n⟧'` is bijective on morphisms out of every shift
of `X`, then so is composition with `u`. -/
theorem bijective_comp_of_forall_shift_map {X A B : C} {u : A ⟶ B} (n : ℤ)
    (hu : ∀ k : ℤ, Function.Bijective (fun a : X⟦k⟧ ⟶ A⟦n⟧ => a ≫ u⟦n⟧')) (k : ℤ) :
    Function.Bijective (fun a : X⟦k⟧ ⟶ A => a ≫ u) :=
  (bijective_comp_shift_map_iff u n).2
    ((bijective_comp_iff_of_source_iso ((shiftFunctorAdd' C k n (k + n) rfl).app X) _).1
      (hu (k + n)))

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- An additive map of groups of morphisms which kills only zero is injective. -/
private theorem injective_comp_of_comp_eq_zero {Y A B : C} (u : A ⟶ B)
    (h : ∀ a : Y ⟶ A, a ≫ u = 0 → a = 0) :
    Function.Injective (fun a : Y ⟶ A => a ≫ u) := by
  intro a b hab
  have : (a - b) ≫ u = 0 := by
    simp only [Preadditive.sub_comp]
    exact sub_eq_zero.2 hab
  exact sub_eq_zero.1 (h _ this)

/-- **The five lemma at the third vertex, for maps out of one object.** Let `φ : T ⟶ T'` be a
morphism of distinguished triangles and `Y` an object. Read on the exact sequences
`Hom(Y, T.obj₁) → Hom(Y, T.obj₂) → Hom(Y, T.obj₃) → Hom(Y, T.obj₁⟦1⟧) → Hom(Y, T.obj₂⟦1⟧)`, if
composition with `φ.hom₁` is surjective, with `φ.hom₂` and with `φ.hom₁⟦1⟧'` is bijective and with
`φ.hom₂⟦1⟧'` is injective, then composition with `φ.hom₃` is bijective. -/
theorem bijective_comp_hom₃_of_triangle {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (φ : T ⟶ T') (Y : C)
    (h₁ : Function.Surjective (fun a : Y ⟶ T.obj₁ => a ≫ φ.hom₁))
    (h₂ : Function.Bijective (fun a : Y ⟶ T.obj₂ => a ≫ φ.hom₂))
    (h₄ : Function.Bijective (fun a : Y ⟶ T.obj₁⟦(1 : ℤ)⟧ => a ≫ φ.hom₁⟦(1 : ℤ)⟧'))
    (h₅ : Function.Injective (fun a : Y ⟶ T.obj₂⟦(1 : ℤ)⟧ => a ≫ φ.hom₂⟦(1 : ℤ)⟧')) :
    Function.Bijective (fun a : Y ⟶ T.obj₃ => a ≫ φ.hom₃) := by
  refine ⟨injective_comp_of_comp_eq_zero _ fun c hc => ?_, fun c' => ?_⟩
  · have hc₃ : c ≫ T.mor₃ = 0 := by
      apply h₄.1
      dsimp only
      rw [Category.assoc, φ.comm₃, reassoc_of% hc]
      simp only [zero_comp]
    obtain ⟨b, rfl⟩ := Triangle.coyoneda_exact₃ _ hT c hc₃
    have hb : (b ≫ φ.hom₂) ≫ T'.mor₂ = 0 := by
      rw [Category.assoc, ← φ.comm₂, ← Category.assoc, hc]
    obtain ⟨a', ha'⟩ := Triangle.coyoneda_exact₂ _ hT' _ hb
    obtain ⟨a, rfl⟩ := h₁ a'
    have hab : b = a ≫ T.mor₁ := by
      apply h₂.1
      dsimp only at ha' ⊢
      rw [ha', Category.assoc, Category.assoc, φ.comm₁]
    rw [hab, Category.assoc, comp_distTriang_mor_zero₁₂ _ hT, comp_zero]
  · obtain ⟨d, hd⟩ := h₄.2 (c' ≫ T'.mor₃)
    dsimp only at hd
    have hd₁ : d ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
      apply h₅
      dsimp only
      rw [Category.assoc, ← Functor.map_comp, φ.comm₁, Functor.map_comp, ← Category.assoc, hd,
        Category.assoc, comp_distTriang_mor_zero₃₁ _ hT', comp_zero, zero_comp]
    obtain ⟨c, rfl⟩ := Triangle.coyoneda_exact₁ _ hT d hd₁
    have hdiff : (c' - c ≫ φ.hom₃) ≫ T'.mor₃ = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, ← φ.comm₃, ← hd, Category.assoc, sub_self]
    obtain ⟨b', hb'⟩ := Triangle.coyoneda_exact₃ _ hT' _ hdiff
    obtain ⟨b, rfl⟩ := h₂.2 b'
    refine ⟨c + b ≫ T.mor₂, ?_⟩
    dsimp only at hb' ⊢
    rw [Preadditive.add_comp, Category.assoc, φ.comm₂, ← Category.assoc, ← hb',
      add_sub_cancel]

/-- **The five lemma at the third vertex, for maps out of all shifts of an object.** If
composition with `φ.hom₁` and with `φ.hom₂` is bijective on morphisms out of every shift of `X`,
then so is composition with `φ.hom₃`. -/
theorem bijective_comp_hom₃_of_forall_shift {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (φ : T ⟶ T') (X : C)
    (h₁ : ∀ k : ℤ, Function.Bijective (fun a : X⟦k⟧ ⟶ T.obj₁ => a ≫ φ.hom₁))
    (h₂ : ∀ k : ℤ, Function.Bijective (fun a : X⟦k⟧ ⟶ T.obj₂ => a ≫ φ.hom₂)) (k : ℤ) :
    Function.Bijective (fun a : X⟦k⟧ ⟶ T.obj₃ => a ≫ φ.hom₃) :=
  bijective_comp_hom₃_of_triangle hT hT' φ _ (h₁ k).2 (h₂ k)
    (bijective_comp_shift_map_of_forall h₁ 1 k) (bijective_comp_shift_map_of_forall h₂ 1 k).1

/-- **The five lemma at the first vertex, for maps out of all shifts of an object.** If
composition with `φ.hom₂` and with `φ.hom₃` is bijective on morphisms out of every shift of `X`,
then so is composition with `φ.hom₁`. This is the third-vertex statement for the rotated
morphism of triangles, whose third component is `φ.hom₁⟦1⟧'`. -/
theorem bijective_comp_hom₁_of_forall_shift {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (φ : T ⟶ T') (X : C)
    (h₂ : ∀ k : ℤ, Function.Bijective (fun a : X⟦k⟧ ⟶ T.obj₂ => a ≫ φ.hom₂))
    (h₃ : ∀ k : ℤ, Function.Bijective (fun a : X⟦k⟧ ⟶ T.obj₃ => a ≫ φ.hom₃)) (k : ℤ) :
    Function.Bijective (fun a : X⟦k⟧ ⟶ T.obj₁ => a ≫ φ.hom₁) :=
  bijective_comp_of_forall_shift_map 1
    (bijective_comp_hom₃_of_forall_shift (rot_of_distTriang _ hT) (rot_of_distTriang _ hT')
      ((rotate C).map φ) X h₂ h₃) k

end CategoryTheory.Pretriangulated

end
