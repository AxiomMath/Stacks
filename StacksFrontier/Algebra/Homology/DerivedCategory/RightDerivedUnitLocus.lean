module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness

/-!
# The locus where a right derived functor is computed by its underived functor

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, let `RF` be a right derived
functor of `F` on the unbounded derived categories, with unit
`α : K(F) ⋙ Q_ℬ ⟶ Q_𝒜 ⋙ RF`, and assume that every cochain complex of `𝒜` has a K-injective
resolution. This file describes the locus of `K(𝒜)` where `α` is invertible.

## Main results

* `Stacks.RightDerivedUnitLocus.isIso_app_quotient_iff_quasiIso_map`: at a complex `K` with a
  K-injective resolution `t : K ⟶ L`, the unit is invertible exactly when `F` carries `t` to a
  quasi-isomorphism.
* `Stacks.RightDerivedUnitLocus.isIso_app_obj₁_of_distinguished`,
  `Stacks.RightDerivedUnitLocus.isIso_app_obj₂_of_distinguished`: the locus satisfies two out of
  three on the distinguished triangles of `K(𝒜)`.

## References

* [Stacks Project, Tag 0CSR](https://stacks.math.columbia.edu/tag/0CSR)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.RightDerivedUnitLocus

section Unit

variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- The unit is invertible at a complex `K` exactly when `F` carries a K-injective resolution
`t : K ⟶ L` of it to a quasi-isomorphism. -/
theorem isIso_app_quotient_iff_quasiIso_map
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    {K L : CochainComplex A ℤ} (t : K ⟶ L) [QuasiIso t] (hL : L.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ↔
      QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map t) := by
  have hαL : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hA).2
      DerivedCategory.Qh RF α L hL
  have hQt : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map t)) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff t).2
        ((HomologicalComplex.mem_quasiIso_iff t).2 inferInstance))
  have hRt : IsIso ((DerivedCategory.Qh ⋙ RF).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map t)) := by
    rw [Functor.comp_map]
    infer_instance
  have key : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ↔
      IsIso ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map t)) := by
    rw [← isIso_comp_right_iff _ ((DerivedCategory.Qh ⋙ RF).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map t)),
      ← α.naturality ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map t),
      isIso_comp_right_iff]
  rw [key, Functor.comp_map, DerivedCategory.isIso_Qh_map_iff]
  change HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map t)) ↔ _
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]

/-- Two out of three for the locus where the unit of `RF` is invertible, on the vertices of a
distinguished triangle of `K(𝒜)`. -/
private theorem isIso_app_two_out_of_three
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (T : Triangle (HomotopyCategory A (ComplexShape.up ℤ))) (hT : T ∈ distTriang _) :
    (IsIso (α.app T.obj₂) → IsIso (α.app T.obj₃) → IsIso (α.app T.obj₁)) ∧
      (IsIso (α.app T.obj₁) → IsIso (α.app T.obj₃) → IsIso (α.app T.obj₂)) := by
  let := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor hA
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) RF α
  let F' := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let G' := DerivedCategory.Qh ⋙ RF
  let φ := Triangle.homMk (F'.mapTriangle.obj T) (G'.mapTriangle.obj T)
    (α.app T.obj₁) (α.app T.obj₂) (α.app T.obj₃) (α.naturality T.mor₁) (α.naturality T.mor₂) (by
      change (F'.map T.mor₃ ≫ (F'.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
          (α.app T.obj₁)⟦(1 : ℤ)⟧' =
        α.app T.obj₃ ≫ (G'.map T.mor₃ ≫ (G'.commShiftIso (1 : ℤ)).hom.app T.obj₁)
      rw [Category.assoc, NatTrans.shift_app_comm α (1 : ℤ) T.obj₁, ← Category.assoc,
        ← Category.assoc, α.naturality T.mor₃])
  exact ⟨isIso₁_of_isIso₂₃ φ (F'.map_distinguished T hT) (G'.map_distinguished T hT),
    fun h₁ h₃ => isIso₂_of_isIso₁₃ φ (F'.map_distinguished T hT) (G'.map_distinguished T hT) h₁ h₃⟩

/-- If the unit of `RF` is invertible at the second and third vertices of a distinguished triangle
of `K(𝒜)`, it is invertible at the first. -/
theorem isIso_app_obj₁_of_distinguished
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (T : Triangle (HomotopyCategory A (ComplexShape.up ℤ))) (hT : T ∈ distTriang _)
    (h₂ : IsIso (α.app T.obj₂)) (h₃ : IsIso (α.app T.obj₃)) :
    IsIso (α.app T.obj₁) :=
  (isIso_app_two_out_of_three F RF α hA T hT).1 h₂ h₃

/-- If the unit of `RF` is invertible at the first and third vertices of a distinguished triangle
of `K(𝒜)`, it is invertible at the second. -/
theorem isIso_app_obj₂_of_distinguished
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (T : Triangle (HomotopyCategory A (ComplexShape.up ℤ))) (hT : T ∈ distTriang _)
    (h₁ : IsIso (α.app T.obj₁)) (h₃ : IsIso (α.app T.obj₃)) :
    IsIso (α.app T.obj₂) :=
  (isIso_app_two_out_of_three F RF α hA T hT).2 h₁ h₃

end Unit


end Stacks.RightDerivedUnitLocus

end
