module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Invertibility in the derived category from triangles with highly connective first vertex

Let `α : F ⟶ G` be a natural transformation between two exact functors from a pretriangulated
category to the derived category `D(A)` of an abelian category.  Suppose that for every integer
`n` the object `X` sits as the middle vertex of a distinguished triangle `Y ⟶ X ⟶ Z ⟶ Y[1]`
with `α` invertible at `Z` and with `F(Y)` and `G(Y)` concentrated in degrees `≥ n + 2`.  Then
`α` is invertible at `X`: in degree `n` the cohomology of `F(X) ⟶ F(Z)` and of `G(X) ⟶ G(Z)` is
an isomorphism.

The natural transformation `α` is not required to commute with the shift.

## Main results

* `Stacks.DerivedCategoryTruncation.isIso_homologyMap_mor₂_of_isZero`: the second arrow of a
  distinguished triangle is invertible in degree `n` when the first vertex has no cohomology in
  degrees `n` and `n + 1`.
* `Stacks.DerivedCategoryTruncation.isIso_app_of_triangles_isGE`: `α` is invertible at `X` when
  every degree admits such a triangle.

## References

* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.DerivedCategoryTruncation

open DerivedCategory

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- The second arrow of a distinguished triangle of `D(A)` is invertible in cohomological degree
`n` when the first vertex has vanishing cohomology in degrees `n` and `n + 1`. -/
theorem isIso_homologyMap_mor₂_of_isZero (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang _) (n : ℤ)
    (h₀ : IsZero ((homologyFunctor A n).obj T.obj₁))
    (h₁ : IsZero ((homologyFunctor A (n + 1)).obj T.obj₁)) :
    IsIso ((homologyFunctor A n).map T.mor₂) := by
  have : Mono ((homologyFunctor A n).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT n).2 (h₀.eq_of_src _ _)
  have : Epi ((homologyFunctor A n).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) rfl).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

variable {C : Type*} [Category* C] [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (F G : C ⥤ DerivedCategory A) [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] (α : F ⟶ G)

/-- **Invertibility from triangles whose first vertex is highly connective.**  If for every `n`
the object `X` is the middle vertex of a distinguished triangle `Y ⟶ X ⟶ Z ⟶ Y[1]` with `α`
invertible at `Z` and with `F(Y)`, `G(Y)` in degrees `≥ n + 2`, then `α` is invertible at `X`. -/
theorem isIso_app_of_triangles_isGE (X : C)
    (h : ∀ n : ℤ, ∃ (Y Z : C) (u : Y ⟶ X) (v : X ⟶ Z) (w : Z ⟶ Y⟦(1 : ℤ)⟧),
      Triangle.mk u v w ∈ distTriang C ∧ IsIso (α.app Z) ∧ (F.obj Y).IsGE (n + 2) ∧
        (G.obj Y).IsGE (n + 2)) :
    IsIso (α.app X) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  obtain ⟨Y, Z, u, v, w, hT, hZ, hFY, hGY⟩ := h n
  have hF := isIso_homologyMap_mor₂_of_isZero _ (F.map_distinguished _ hT) n
    ((DerivedCategory.isGE_iff _ _).1 hFY n (by omega))
    ((DerivedCategory.isGE_iff _ _).1 hFY (n + 1) (by omega))
  have hG := isIso_homologyMap_mor₂_of_isZero _ (G.map_distinguished _ hT) n
    ((DerivedCategory.isGE_iff _ _).1 hGY n (by omega))
    ((DerivedCategory.isGE_iff _ _).1 hGY (n + 1) (by omega))
  change IsIso ((homologyFunctor A n).map (F.map v)) at hF
  change IsIso ((homologyFunctor A n).map (G.map v)) at hG
  have hsq : (homologyFunctor A n).map (α.app X) ≫ (homologyFunctor A n).map (G.map v) =
      (homologyFunctor A n).map (F.map v) ≫ (homologyFunctor A n).map (α.app Z) := by
    rw [← Functor.map_comp, ← Functor.map_comp, α.naturality]
  have : IsIso ((homologyFunctor A n).map (α.app X) ≫ (homologyFunctor A n).map (G.map v)) := by
    rw [hsq]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((homologyFunctor A n).map (G.map v))

end Stacks.DerivedCategoryTruncation

end
