module

public import StacksFrontier.Homology.KFlat.FilteredColimitShifts
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility

/-!
# Invertibility of a natural transformation from its value on shifts of the ring

A natural transformation `α : F ⟶ G` between exact functors out of a triangulated category `C` is
invertible everywhere as soon as both functors commute with direct sums, `C` is reached from
`D(R)` by an essentially surjective exact functor `Ψ` commuting with direct sums, and `α` is
invertible at every shift of `Ψ(R)`. This is [Stacks, Tag 09PB] applied to the property of `K`
that `α` is invertible at every shift of `Ψ K`.

## Main results

* `Stacks.EtaleCohomology.ProjectionFormulaConstant.isIso_app_of_isColimit`: a natural
  transformation invertible at the terms of a diagram is invertible at a colimit preserved by
  both functors.
* `Stacks.EtaleCohomology.ProjectionFormulaConstant.isIso_app_of_coproducts_of_unitShifts`: a
  natural transformation of exact functors commuting with direct sums which is invertible at
  every shift of `Ψ(R)`, for `Ψ : D(R) ⥤ C` essentially surjective, exact and commuting with
  direct sums, is invertible.

## References

* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u v

namespace Stacks.EtaleCohomology.ProjectionFormulaConstant

open Stacks.CategoryTheory.ComponentwiseInvertibility

/-- A natural transformation which is invertible at every term of a diagram is invertible at a
colimit of the diagram preserved by its source and its target. -/
theorem isIso_app_of_isColimit {J C D : Type*} [Category* J] [Category* C] [Category* D]
    (F G : C ⥤ D) (α : F ⟶ G) {K : J ⥤ C} (c : Cocone K) (hc : IsColimit c)
    [PreservesColimit K F] [PreservesColimit K G] (h : ∀ j, IsIso (α.app (K.obj j))) :
    IsIso (α.app c.pt) := by
  have hF := isColimitOfPreserves F hc
  have hG := isColimitOfPreserves G hc
  have : ∀ j, IsIso ((Functor.whiskerLeft K α).app j) := h
  have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
  have he : α.app c.pt = (hF.coconePointsIsoOfNatIso hG (asIso (Functor.whiskerLeft K α))).hom :=
    hF.hom_ext fun j => by
      rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
      exact α.naturality (c.ι.app j)
  rw [he]
  infer_instance

-- `CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts` is stated for the
-- standard model of `D(R)`.
attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [Ring R] [Small.{v} R]
  {C D : Type*} [Category* C] [Category* D]
  [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (α : F ⟶ G)

/-- Let `α : F ⟶ G` be a natural transformation of exact functors which commute with direct sums,
and `Ψ : D(R) ⥤ C` an essentially surjective exact functor commuting with direct sums. If `α` is
invertible at every shift of `Ψ(R)`, then it is invertible everywhere. -/
theorem isIso_app_of_coproducts_of_unitShifts
    (Ψ : DerivedCategory (ModuleCat.{v} R) ⥤ C) [Ψ.CommShift ℤ] [Ψ.IsTriangulated] [Ψ.EssSurj]
    [∀ I : Type v, PreservesColimitsOfShape (Discrete I) Ψ]
    [∀ I : Type v, PreservesColimitsOfShape (Discrete I) F]
    [∀ I : Type v, PreservesColimitsOfShape (Discrete I) G]
    (hbase : ∀ n : ℤ, IsIso (α.app ((Ψ.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
      (ModuleCat.of R (Shrink.{v} R))))⟦n⟧)))
    (K : C) : IsIso (α.app K) := by
  have e : (Ψ.obj (Ψ.objPreimage K))⟦(0 : ℤ)⟧ ≅ K :=
    (shiftFunctorZero C ℤ).app _ ≪≫ Ψ.objObjPreimageIso K
  refine (α.isIso_app_iff_of_iso e).1
    ((CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts (R := R)).2
      (fun M => ∀ n : ℤ, IsIso (α.app ((Ψ.obj M)⟦n⟧))) ?_ ?_ ?_ _ 0)
  · intro I M _ hM n
    exact isIso_app_of_isColimit F G α _
      (isColimitOfPreserves (Ψ ⋙ shiftFunctor C n) (colimit.isColimit (Discrete.functor M)))
      fun j => hM j.as n
  · intro Δ hΔ
    have hΔ' := Ψ.map_distinguished Δ hΔ
    refine ⟨fun h₁ h₂ n => ?_, fun h₁ h₃ => ?_, fun h₂ h₃ => ?_⟩
    · exact isIso_app_third_of_distinguished F G α _ (Triangle.shift_distinguished _ hΔ' n)
        (h₁ n) (h₂ n)
        ((α.isIso_app_iff_of_iso ((shiftFunctorAdd C n 1).app _)).1 (h₁ (n + 1)))
        ((α.isIso_app_iff_of_iso ((shiftFunctorAdd C n 1).app _)).1 (h₂ (n + 1)))
    · exact isIso_app_middle_of_all_shifts F G α _ hΔ' h₁ h₃
    · exact isIso_app_middle_of_all_shifts F G α _ (inv_rot_of_distTriang _ hΔ')
        (fun n => (α.isIso_app_iff_of_iso ((shiftFunctorAdd C (-1) n).app _)).1 (h₃ (-1 + n))) h₂
  · intro k n
    have e : (Ψ.obj (((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
        (ModuleCat.of R (Shrink.{v} R)))⟦k⟧))⟦n⟧ ≅
        (Ψ.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
          (ModuleCat.of R (Shrink.{v} R))))⟦k + n⟧ :=
      (shiftFunctor C n).mapIso ((Ψ.commShiftIso k).app _) ≪≫
        ((shiftFunctorAdd C k n).app _).symm
    exact (α.isIso_app_iff_of_iso e).2 (hbase (k + n))

end Stacks.EtaleCohomology.ProjectionFormulaConstant
