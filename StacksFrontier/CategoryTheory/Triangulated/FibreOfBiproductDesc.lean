module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.CategoryTheory.Preadditive.AdditiveFunctorBiprod

/-!
# The fibre of a map out of a biproduct with an invertible component

Let `T = (F ⟶ A ⊞ B ⟶ C ⟶ F⟦1⟧)` be a distinguished triangle whose second morphism is
`biprod.desc a b` with `b : B ⟶ C` an isomorphism. Then the first morphism followed by the first
projection, `F ⟶ A`, is an isomorphism: the fibre of `(a, b)` is `A`, because the component `b`
already absorbs `C`.

This is the triangulated input of Mayer–Vietoris arguments for a square whose two parallel
sides become invertible after a base change: once one side `b` of the map
`A ⊞ B ⟶ C` is invertible, the first vertex of its distinguished triangle is identified with
`A`.

## Main results

* `CategoryTheory.Pretriangulated.isIso_mor₁_comp_biprod_fst_of_isIso`: the composite
  `F ⟶ A ⊞ B ⟶ A` is an isomorphism.
* `CategoryTheory.Pretriangulated.isIso_map_mor₁_comp_biprod_fst_of_isIso`: the same after a
  triangulated functor that inverts the second component `b`.
* `CategoryTheory.Pretriangulated.isIso_map_mor₁_comp_biprod_snd_of_isZero`: dually, a
  triangulated functor killing `A` and `C` sends `F ⟶ A ⊞ B ⟶ B` to an isomorphism.
* `CategoryTheory.Preadditive.isIso_neg`: the negative of an isomorphism is an isomorphism.

## Implementation notes

The second morphism `biprod.desc a b` is a split epimorphism, a section being
`inv b ≫ biprod.inr`, so the third morphism of the triangle vanishes and the first is a
monomorphism. The map `biprod.lift (𝟙 A) (-(a ≫ inv b)) : A ⟶ A ⊞ B` is killed by
`biprod.desc a b`, hence factors through the first morphism; that factorization is a two-sided
inverse of `F ⟶ A`, the identity on the side of `F` following from the monomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/-- The negative of an isomorphism in a preadditive category is an isomorphism, with inverse the
negative of the inverse. -/
public instance CategoryTheory.Preadditive.isIso_neg {C : Type*} [Category C] [Preadditive C]
    {A B : C} (f : A ⟶ B) [IsIso f] : IsIso (-f) :=
  ⟨-inv f, by simp, by simp⟩

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasBinaryBiproducts C]

/-- **The fibre of `(a, b) : A ⊞ B ⟶ C` with `b` invertible is `A`.** If
`F ⟶ A ⊞ B ⟶ C ⟶ F⟦1⟧` is a distinguished triangle whose second morphism is
`biprod.desc a b` with `b` an isomorphism, then its first morphism followed by the first
projection is an isomorphism `F ≅ A`. -/
public theorem isIso_mor₁_comp_biprod_fst_of_isIso {F A B D : C} (α : F ⟶ A ⊞ B)
    (a : A ⟶ D) (b : B ⟶ D) [IsIso b] (δ : D ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk α (biprod.desc a b) δ ∈ distTriang C) :
    IsIso (α ≫ biprod.fst) := by
  set T := Triangle.mk α (biprod.desc a b) δ
  have hδ : δ = 0 := by
    calc δ = (inv b ≫ biprod.inr) ≫ biprod.desc a b ≫ δ := by simp
      _ = 0 := by
        show (inv b ≫ biprod.inr) ≫ T.mor₂ ≫ T.mor₃ = 0
        rw [comp_distTriang_mor_zero₂₃ T hT, Limits.comp_zero]
  have hmono : Mono α := Triangle.mono₁ T hT hδ
  set s : A ⟶ A ⊞ B := biprod.lift (𝟙 A) (-(a ≫ inv b))
  have hs : s ≫ T.mor₂ = 0 := by simp [s, T]
  obtain ⟨t, ht⟩ := Triangle.coyoneda_exact₂ T hT s hs
  change s = t ≫ α at ht
  refine ⟨t, ?_, ?_⟩
  · rw [← cancel_mono α, Category.assoc, Category.assoc, ← ht, Category.id_comp]
    have hfst : (α - α ≫ biprod.fst ≫ s) ≫ biprod.fst = 0 := by simp [s]
    have hsnd : (α - α ≫ biprod.fst ≫ s) ≫ biprod.snd = 0 := by
      have h₀ : α ≫ biprod.desc a b = 0 := comp_distTriang_mor_zero₁₂ T hT
      have h₁ : (α - α ≫ biprod.fst ≫ s) ≫ biprod.desc a b = 0 := by
        rw [Preadditive.sub_comp, h₀, Category.assoc, Category.assoc,
          show s ≫ biprod.desc a b = 0 from hs, Limits.comp_zero, Limits.comp_zero, sub_zero]
      have h₂ : (α - α ≫ biprod.fst ≫ s) ≫ biprod.desc a b =
          ((α - α ≫ biprod.fst ≫ s) ≫ biprod.snd) ≫ b := by
        rw [biprod.desc_eq, Preadditive.comp_add, ← Category.assoc, hfst, Limits.zero_comp,
          zero_add, Category.assoc]
      rw [← cancel_mono b, ← h₂, h₁, Limits.zero_comp]
    have h₃ : α - α ≫ biprod.fst ≫ s = 0 := biprod.hom_ext _ _
      (by rw [hfst, Limits.zero_comp]) (by rw [hsnd, Limits.zero_comp])
    exact (sub_eq_zero.mp h₃).symm
  · rw [← Category.assoc t, ← ht]
    simp [s]

/-- **The fibre of `(a, b)` after a triangulated functor that inverts `b`.** If
`F ⟶ A ⊞ B ⟶ D ⟶ F⟦1⟧` is a distinguished triangle whose second morphism is `biprod.desc a b`,
and a triangulated functor `G` sends `b` to an isomorphism, then `G` sends the first morphism
followed by the first projection to an isomorphism: `G` carries the triangle to a distinguished
triangle of the same shape, to which `isIso_mor₁_comp_biprod_fst_of_isIso` applies. -/
public theorem isIso_map_mor₁_comp_biprod_fst_of_isIso {C' : Type*} [Category C'] [Preadditive C']
    [HasZeroObject C'] [HasShift C' ℤ] [∀ n : ℤ, (shiftFunctor C' n).Additive] [Pretriangulated C']
    [HasBinaryBiproducts C'] (G : C ⥤ C') [G.CommShift ℤ] [G.IsTriangulated] {F A B D : C}
    (α : F ⟶ A ⊞ B) (a : A ⟶ D) (b : B ⟶ D) [IsIso (G.map b)] (δ : D ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk α (biprod.desc a b) δ ∈ distTriang C) :
    IsIso (G.map (α ≫ biprod.fst)) := by
  have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts _
  have hT' : Triangle.mk (G.map α ≫ (G.mapBiprod A B).hom) (biprod.desc (G.map a) (G.map b))
      (G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app F) ∈ distTriang C' := by
    refine isomorphic_distinguished _ (G.map_distinguished _ hT) _
      (Triangle.isoMk _ _ (Iso.refl _) (G.mapBiprod A B).symm (Iso.refl _) ?_ ?_ ?_)
    · dsimp [Functor.mapTriangle]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · dsimp [Functor.mapTriangle]
      apply biprod.hom_ext' <;>
        simp only [Functor.mapBiprod_inv, Category.comp_id, biprod.inl_desc_assoc,
          biprod.inr_desc_assoc, ← G.map_comp, biprod.inl_desc, biprod.inr_desc]
    · dsimp [Functor.mapTriangle]
      simp
  have := isIso_mor₁_comp_biprod_fst_of_isIso _ _ _ _ hT'
  rw [G.map_comp]
  convert this using 1
  rw [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst]

/-- **A triangulated functor killing the outer vertices.** If `F ⟶ A ⊞ B ⟶ D ⟶ F⟦1⟧` is a
distinguished triangle and a triangulated functor `G` kills `A` and `D`, then `G` sends the first
morphism followed by the second projection to an isomorphism: `G` of the first morphism is
invertible because `G D = 0`, and `G` of the projection because `G A = 0`. -/
public theorem isIso_map_mor₁_comp_biprod_snd_of_isZero {C' : Type*} [Category C']
    [Preadditive C'] [HasZeroObject C'] [HasShift C' ℤ] [∀ n : ℤ, (shiftFunctor C' n).Additive]
    [Pretriangulated C'] (G : C ⥤ C') [G.CommShift ℤ] [G.IsTriangulated] {F A B D : C}
    (α : F ⟶ A ⊞ B) (φ : A ⊞ B ⟶ D) (δ : D ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk α φ δ ∈ distTriang C) (hA : IsZero (G.obj A)) (hD : IsZero (G.obj D)) :
    IsIso (G.map (α ≫ biprod.snd)) := by
  have hα : IsIso (G.map α) := (Triangle.isZero₃_iff_isIso₁ _ (G.map_distinguished _ hT)).1 hD
  have := isIso_map_biprod_snd_of_isZero G (B := B) hA
  rw [G.map_comp]
  infer_instance

end CategoryTheory.Pretriangulated
