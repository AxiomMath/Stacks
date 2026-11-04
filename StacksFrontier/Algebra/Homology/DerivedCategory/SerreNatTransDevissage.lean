module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds

/-!
# Invertibility of a natural transformation on `D_P`, read off single objects

Let `P` be a property of objects of an abelian category `A` containing the zero objects, and let
`τ : F₁ ⟶ F₂` be a natural transformation between triangulated functors
`D(A) ⥤ D(B)`. Suppose that each `Fₖ` carries an object `E` of `D_P(A)` with `H^j(E) = 0` to an
object with `H^j(Fₖ E) = 0`, degree by degree. If `τ` is invertible on every object `M[-i]` with
`M` in `P`, then it is invertible on every object of `D_P(A)`, bounded or not.

Fix a degree `i`. The truncation `E ⟶ τ_{≥ i}E` and the inclusion `τ_{≤ i}τ_{≥ i}E ⟶ τ_{≥ i}E`
are carried by both functors to morphisms invertible on `H^i`, because the third vertex of the
image of the relevant truncation triangle has no cohomology in the two degrees adjacent to `i`.
The object `τ_{≤ i}τ_{≥ i}E` is `H^i(E)` placed in degree `i`, where `τ` is invertible by
assumption, and naturality of `τ` transports this to `H^i(τ_E)`.

## Main results

* `DerivedCategory.isIso_app_of_derivedCategoryB`: the dévissage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace DerivedCategory

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- A triangulated functor which preserves the vanishing of each cohomology object on `D_P(A)`
carries the truncation `E ⟶ τ_{≥ i}E` of an object of `D_P(A)` to a morphism invertible on
`H^i`. -/
theorem isIso_homologyFunctor_map_map_truncGEπ_app (P : ObjectProperty A)
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ E : DerivedCategory A, DerivedCategoryB.derivedCategoryB P E → ∀ j : ℤ,
      IsZero ((homologyFunctor A j).obj E) → IsZero ((homologyFunctor B j).obj (F.obj E)))
    (E : DerivedCategory A) (hE : DerivedCategoryB.derivedCategoryB P E) (i : ℤ) :
    IsIso ((homologyFunctor B i).map (F.map ((TStructure.t.truncGEπ i).app E))) := by
  let T := F.mapTriangle.obj ((TStructure.t.triangleLEGE (i - 1) i (by omega)).obj E)
  have hT : T ∈ distTriang (DerivedCategory B) :=
    F.map_distinguished _ (TStructure.t.triangleLEGE_distinguished (i - 1) i (by omega) E)
  have hP : DerivedCategoryB.derivedCategoryB P ((TStructure.t.truncLE (i - 1)).obj E) :=
    fun j => Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj P E hE
      (i - 1) j
  have hLE : T.obj₁.IsLE (i - 1) := by
    rw [isLE_iff]
    intro j hj
    exact hF _ hP j (isZero_of_isLE _ (i - 1) j hj)
  exact isIso_homologyMap_mor₂_of_isLE₁ T hT i (i - 1) hLE (by omega)

/-- A triangulated functor which preserves the vanishing of each cohomology object on `D_P(A)`
carries the inclusion `τ_{≤ i}E ⟶ E` of an object of `D_P(A)` to a morphism invertible on
`H^i`. -/
theorem isIso_homologyFunctor_map_map_truncLEι_app (P : ObjectProperty A)
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ E : DerivedCategory A, DerivedCategoryB.derivedCategoryB P E → ∀ j : ℤ,
      IsZero ((homologyFunctor A j).obj E) → IsZero ((homologyFunctor B j).obj (F.obj E)))
    (E : DerivedCategory A) (hE : DerivedCategoryB.derivedCategoryB P E) (i : ℤ) :
    IsIso ((homologyFunctor B i).map (F.map ((TStructure.t.truncLEι i).app E))) := by
  let T := F.mapTriangle.obj ((TStructure.t.triangleLEGE i (i + 1) rfl).obj E)
  have hT : T ∈ distTriang (DerivedCategory B) :=
    F.map_distinguished _ (TStructure.t.triangleLEGE_distinguished i (i + 1) rfl E)
  have hP : DerivedCategoryB.derivedCategoryB P ((TStructure.t.truncGE (i + 1)).obj E) :=
    fun j => Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj P E hE
      (i + 1) j
  have hGE : T.obj₃.IsGE (i + 1) := by
    rw [isGE_iff]
    intro j hj
    exact hF _ hP j (isZero_of_isGE _ (i + 1) j hj)
  exact isIso_homologyMap_mor₁_of_isGE₃ T hT i (i + 1) hGE (by omega)

/-- **Dévissage of a natural transformation on `D_P(A)`.** Let `τ : F₁ ⟶ F₂` be a natural
transformation between triangulated functors `D(A) ⥤ D(B)`, each of which preserves the vanishing
of every cohomology object on `D_P(A)`. If `τ` is invertible on `M[-i]` for every `M` in `P` and
every `i`, then it is invertible on every object of `D_P(A)`. -/
theorem isIso_app_of_derivedCategoryB (P : ObjectProperty A)
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    {F₁ F₂ : DerivedCategory A ⥤ DerivedCategory B} [F₁.CommShift ℤ] [F₁.IsTriangulated]
    [F₂.CommShift ℤ] [F₂.IsTriangulated] (τ : F₁ ⟶ F₂)
    (h₁ : ∀ E : DerivedCategory A, DerivedCategoryB.derivedCategoryB P E → ∀ j : ℤ,
      IsZero ((homologyFunctor A j).obj E) → IsZero ((homologyFunctor B j).obj (F₁.obj E)))
    (h₂ : ∀ E : DerivedCategory A, DerivedCategoryB.derivedCategoryB P E → ∀ j : ℤ,
      IsZero ((homologyFunctor A j).obj E) → IsZero ((homologyFunctor B j).obj (F₂.obj E)))
    (hs : ∀ (M : A) (i : ℤ), P M → IsIso (τ.app ((singleFunctor A i).obj M)))
    (E : DerivedCategory A) (hE : DerivedCategoryB.derivedCategoryB P E) :
    IsIso (τ.app E) := by
  rw [isIso_iff]
  intro i
  let E₁ := (TStructure.t.truncGE i).obj E
  have hE₁ : DerivedCategoryB.derivedCategoryB P E₁ := fun j =>
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj P E hE i j
  let E₂ := (TStructure.t.truncLE i).obj E₁
  have : E₂.IsGE i := inferInstanceAs (((TStructure.t.truncLE i).obj E₁).IsGE i)
  have : E₂.IsLE i := inferInstanceAs (((TStructure.t.truncLE i).obj E₁).IsLE i)
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE E₂ i
  have hM : P M := P.prop_of_iso ((homologyFunctor A i).mapIso e ≪≫
    (singleFunctorCompHomologyFunctorIso A i).app M)
    (Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj P E₁ hE₁ i i)
  have hτ₂ : IsIso (τ.app E₂) :=
    have := hs M i hM
    IsIso.of_isIso_fac_right (τ.naturality e.hom).symm
  let π : E ⟶ E₁ := (TStructure.t.truncGEπ i).app E
  let ι : E₂ ⟶ E₁ := (TStructure.t.truncLEι i).app E₁
  have hπ₁ := isIso_homologyFunctor_map_map_truncGEπ_app P F₁ h₁ E hE i
  have hπ₂ := isIso_homologyFunctor_map_map_truncGEπ_app P F₂ h₂ E hE i
  have hι₁ := isIso_homologyFunctor_map_map_truncLEι_app P F₁ h₁ E₁ hE₁ i
  have hι₂ := isIso_homologyFunctor_map_map_truncLEι_app P F₂ h₂ E₁ hE₁ i
  have hτ₁ : IsIso ((homologyFunctor B i).map (τ.app E₁)) := by
    have h := congrArg (homologyFunctor B i).map (τ.naturality ι)
    simp only [Functor.map_comp] at h
    exact IsIso.of_isIso_fac_left h
  have h := congrArg (homologyFunctor B i).map (τ.naturality π)
  simp only [Functor.map_comp] at h
  exact IsIso.of_isIso_fac_right h.symm

end DerivedCategory
