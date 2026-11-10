module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Where a natural transformation is invertible

For a natural transformation `α : F ⟶ G` between functors, the objects at which `α` is
invertible are closed under the three operations this file records: passing to a split retract,
forming a finite biproduct, and — when `F` and `G` are exact functors of pretriangulated
categories — completing a distinguished triangle.

## Main results

* `Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_of_splitRetract`: invertibility at
  an object passes to any split retract of it.
* `Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_of_biproduct`: invertibility at
  each summand of a finite biproduct gives invertibility at the biproduct.
* `Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_of_five`: **Stacks 014A** for the
  rotation "first and second invertible give the third", the five lemma for two distinguished
  triangles connected by five morphisms making four squares commute.
* `Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_third_of_distinguished`:
  invertibility at the first two vertices of a distinguished triangle, and at their shifts by
  one, gives invertibility at the third vertex.
* `Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts`:
  invertibility at all shifts of the first and third vertices gives invertibility at all shifts
  of the second.

## Implementation notes

`isIso_of_five` is stated with five independent morphisms rather than with a morphism of
triangles because that is what the application supplies.  A morphism of triangles
`T ⟶ T'` would require its fourth component to be `φ.hom₁⟦1⟧'`, and for the triangles
`F.mapTriangle.obj T` and `G.mapTriangle.obj T` the fourth component that naturality of `α`
produces is instead `α` at the *shifted* object, conjugated by the two `commShiftIso`s.  That is
not `(α.app T.obj₁)⟦1⟧'` unless `α` is compatible with the shift, which is not assumed here.  So
Mathlib's `CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃`, which consumes a morphism of
triangles, does not apply and the five-morphism form is proved from the exactness of the Yoneda
sequences of the two triangles.

`isIso_app_middle_of_all_shifts` quantifies over all shifts because the inverse rotation of a
triangle moves its vertices by `-1`: the hypothesis at a single shift is not enough to feed
`isIso_app_third_of_distinguished`, which needs the hypotheses at the shift by one as well.

## References

* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive

namespace Stacks.CategoryTheory.ComponentwiseInvertibility

/-- A natural transformation invertible at an object is invertible at any split retract of it:
the candidate inverse is the retraction conjugated by the inverse at the ambient object. -/
theorem isIso_app_of_splitRetract {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (α : F ⟶ G) {A B : C} (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (hB : IsIso (α.app B)) : IsIso (α.app A) := by
  have := hB
  let g : G.obj A ⟶ F.obj A := G.map i ≫ inv (α.app B) ≫ F.map r
  refine ⟨⟨g, ?_, ?_⟩⟩
  · dsimp [g]
    calc
      α.app A ≫ G.map i ≫ inv (α.app B) ≫ F.map r =
          (α.app A ≫ G.map i) ≫ inv (α.app B) ≫ F.map r := by
            rw [← Category.assoc]
      _ = (F.map i ≫ α.app B) ≫ inv (α.app B) ≫ F.map r := by
            rw [α.naturality i]
      _ = F.map (i ≫ r) := by simp [Functor.map_comp]
      _ = 𝟙 _ := by simp [hir]
  · dsimp [g]
    calc
      (G.map i ≫ inv (α.app B) ≫ F.map r) ≫ α.app A =
          G.map i ≫ inv (α.app B) ≫ (F.map r ≫ α.app A) := by
            simp only [Category.assoc]
      _ = G.map i ≫ inv (α.app B) ≫ (α.app B ≫ G.map r) := by
            rw [α.naturality r]
      _ = G.map (i ≫ r) := by simp [Functor.map_comp]
      _ = 𝟙 _ := by simp [hir]

/-- A natural transformation invertible at each summand of a finite family is invertible at the
biproduct, both functors preserving that biproduct. -/
theorem isIso_app_of_biproduct {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F G : C ⥤ D) [F.Additive] [G.Additive] {ι : Type*} [Finite ι] (X : ι → C)
    [PreservesBiproduct X F] [PreservesBiproduct X G] (α : F ⟶ G)
    (h : ∀ i, IsIso (α.app (X i))) : IsIso (α.app (⨁ X)) := by
  classical
  let e : (⨁ fun i => F.obj (X i)) ≅ ⨁ fun i => G.obj (X i) :=
    biproduct.mapIso fun i => asIso (α.app (X i))
  have hnat : (F.mapBiproduct X).hom ≫ e.hom =
      α.app (⨁ X) ≫ (G.mapBiproduct X).hom := by
    simp only [Functor.mapBiproduct_hom]
    apply biproduct.hom_ext
    intro i
    dsimp only [e, biproduct.mapIso]
    calc
      _ = F.map (biproduct.π X i) ≫ α.app (X i) := by
        rw [Category.assoc, biproduct.map_π, ← Category.assoc, biproduct.lift_π]
        simp
      _ = α.app (⨁ X) ≫ G.map (biproduct.π X i) := α.naturality _
      _ = _ := by simp only [Category.assoc, biproduct.lift_π]
  have : IsIso ((α.app (⨁ X)) ≫ (G.mapBiproduct X).hom) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.mapBiproduct X).hom

/-- **The five lemma in a pretriangulated category.**  Two distinguished triangles connected by
five morphisms whose four consecutive squares commute, with the first, second, fourth and fifth
invertible, have invertible third morphism. -/
@[stacks 014A "the rotation `two of (a, b, c) isomorphisms give the third` in the case `a, b` \
give `c`, in an arbitrary pretriangulated category. The five independent morphisms with four \
commuting squares are a weaker hypothesis than a morphism of triangles, which forces the fourth \
and fifth to be `a⟦1⟧'` and `b⟦1⟧'`; Mathlib's `isIso₃_of_isIso₁₂` consumes a morphism of \
triangles and so does not apply in this form, and the proof here is from the exactness of the \
Yoneda sequences of the two triangles rather than from it. The other two rotations, for data \
that is a morphism of triangles, are Mathlib's `isIso₁_of_isIso₂₃` and `isIso₂_of_isIso₁₃`"]
theorem isIso_of_five {C : Type*} [Category* C] [HasShift C ℤ] [Preadditive C]
    [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T T' : Triangle C) (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (a₁ : T.obj₁ ⟶ T'.obj₁) (a₂ : T.obj₂ ⟶ T'.obj₂) (a₃ : T.obj₃ ⟶ T'.obj₃)
    (a₄ : T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₁⟦(1 : ℤ)⟧)
    (a₅ : T.obj₂⟦(1 : ℤ)⟧ ⟶ T'.obj₂⟦(1 : ℤ)⟧)
    (ha₁ : IsIso a₁) (ha₂ : IsIso a₂) (ha₄ : IsIso a₄) (ha₅ : IsIso a₅)
    (h₁ : T.mor₁ ≫ a₂ = a₁ ≫ T'.mor₁)
    (h₂ : T.mor₂ ≫ a₃ = a₂ ≫ T'.mor₂)
    (h₃ : T.mor₃ ≫ a₄ = a₃ ≫ T'.mor₃)
    (h₄ : T.mor₁⟦(1 : ℤ)⟧' ≫ a₅ = a₄ ≫ T'.mor₁⟦(1 : ℤ)⟧') :
    IsIso a₃ := by
  have := ha₁
  have := ha₂
  have := ha₄
  have := ha₅
  have : Mono a₃ := by
    rw [mono_iff_cancel_zero]
    intro A x hx
    obtain ⟨t, rfl⟩ := T.coyoneda_exact₃ hT x (by
      rw [← cancel_mono a₄, Category.assoc, h₃, ← Category.assoc, hx]
      simp)
    obtain ⟨s, hs⟩ := T'.coyoneda_exact₂ hT' (t ≫ a₂) (by
      rw [Category.assoc, ← h₂, ← Category.assoc]
      exact hx)
    have ht : t = (s ≫ inv a₁) ≫ T.mor₁ := by
      rw [← cancel_mono a₂, Category.assoc, h₁]
      simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hs
    rw [ht, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
  apply isIso_of_yoneda_map_bijective
  intro A
  refine ⟨fun x y h => (cancel_mono a₃).1 h, ?_⟩
  intro y
  let z := y ≫ T'.mor₃ ≫ inv a₄
  obtain ⟨x, hx⟩ := T.coyoneda_exact₁ hT z (by
    rw [← cancel_mono a₅, Category.assoc, h₄]
    dsimp [z]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, zero_comp]
    rw [comp_distTriang_mor_zero₃₁ T' hT', comp_zero])
  have hx' : x ≫ a₃ ≫ T'.mor₃ = y ≫ T'.mor₃ := by
    rw [← h₃, ← Category.assoc, ← hx]
    dsimp [z]
    simp
  obtain ⟨t, ht⟩ := T'.coyoneda_exact₃ hT' (y - x ≫ a₃) (by
    rw [sub_comp, Category.assoc, hx', sub_self])
  refine ⟨x + (t ≫ inv a₂) ≫ T.mor₂, ?_⟩
  change (x + (t ≫ inv a₂) ≫ T.mor₂) ≫ a₃ = y
  rw [add_comp, Category.assoc, h₂]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← ht, add_sub_cancel]

/-- A natural transformation between exact functors, invertible at the first two vertices of a
distinguished triangle and at their shifts by one, is invertible at the third vertex. -/
theorem isIso_app_third_of_distinguished {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsIso (α.app T.obj₁)) (h₂ : IsIso (α.app T.obj₂))
    (h₁' : IsIso (α.app (T.obj₁⟦(1 : ℤ)⟧))) (h₂' : IsIso (α.app (T.obj₂⟦(1 : ℤ)⟧))) :
    IsIso (α.app T.obj₃) := by
  have := h₁
  have := h₂
  have := h₁'
  have := h₂'
  let a (X : C) := (F.commShiftIso (1 : ℤ)).inv.app X ≫
    α.app (X⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app X
  have ha (X : C) (hX : IsIso (α.app (X⟦(1 : ℤ)⟧))) : IsIso (a X) := by
    dsimp only [a]
    infer_instance
  apply isIso_of_five (F.mapTriangle.obj T) (G.mapTriangle.obj T)
    (F.map_distinguished T hT) (G.map_distinguished T hT)
    (α.app T.obj₁) (α.app T.obj₂) (α.app T.obj₃) (a T.obj₁) (a T.obj₂) h₁ h₂
    (ha _ h₁') (ha _ h₂')
  · exact α.naturality T.mor₁
  · exact α.naturality T.mor₂
  · dsimp [a, Functor.mapTriangle]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc, α.naturality T.mor₃, Category.assoc]
  · dsimp [a, Functor.mapTriangle]
    have hf := (F.commShiftIso (1 : ℤ)).inv.naturality T.mor₁
    have hg := (G.commShiftIso (1 : ℤ)).hom.naturality T.mor₁
    dsimp only [Functor.comp_map] at hf hg
    simp only [Category.assoc]
    rw [← Category.assoc, hf]
    simp only [Category.assoc]
    rw [← Category.assoc (F.map (T.mor₁⟦(1 : ℤ)⟧')), α.naturality]
    simp only [Category.assoc]
    rw [hg]

/-- A natural transformation between exact functors, invertible at every shift of the first and
third vertices of a distinguished triangle, is invertible at every shift of the second. -/
theorem isIso_app_middle_of_all_shifts {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧)))
    (h₃ : ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) :
    ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧)) := by
  intro n
  let S := (shiftFunctor (Triangle C) n).obj T
  have hS : S ∈ distTriang C := T.shift_distinguished hT n
  have h' (X : C) (hX : ∀ m : ℤ, IsIso (α.app (X⟦m⟧))) (m : ℤ) :
      IsIso (α.app ((X⟦n⟧)⟦m⟧)) :=
    (α.isIso_app_iff_of_iso ((shiftFunctorAdd C n m).app X)).1 (hX (n + m))
  exact isIso_app_third_of_distinguished F G α S.invRotate (inv_rot_of_distTriang S hS)
    (h' _ h₃ (-1)) (h₁ n)
    ((α.isIso_app_iff_of_iso
      ((shiftFunctorCompIsoId C (-1 : ℤ) 1 (by simp)).app S.obj₃)).2 (h₃ n))
    (h' _ h₁ 1)

end Stacks.CategoryTheory.ComponentwiseInvertibility

end
