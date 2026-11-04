module

public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility
public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTrans
public import StacksFrontier.Homology.Devissage.IsoLocusOfNatTrans

/-!
# Invertibility of a natural transformation at all shifts

Let `τ : F ⟶ G` be a natural transformation between exact functors of pre-triangulated categories.
The class of objects at all of whose shifts `τ` is invertible contains the third vertex of every
distinguished triangle whose first two vertices it contains, and, when `F` and `G` preserve direct
sums, every direct sum of shifts of a family of objects it contains. No compatibility of `τ` with
the shift is assumed.

## Main results

* `ComponentwiseInvertibility.isIso_app_third_of_all_shifts_of_isTriangulated`: invertibility at
  all shifts of the first two vertices of a distinguished triangle gives it at all shifts of the
  third.
* `StacksDraft.CompactDevissage.isIso_app_shift_of_colimitsOfShape_shiftClosure`: invertibility at
  all shifts of the members of a family gives it at all shifts of a direct sum of shifts of them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

namespace Stacks.CategoryTheory.ComponentwiseInvertibility

/-- A natural transformation between exact functors, invertible at every shift of the first and
second vertices of a distinguished triangle, is invertible at every shift of the third. -/
theorem isIso_app_third_of_all_shifts_of_isTriangulated {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧)))
    (h₂ : ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) :
    ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧)) := fun n =>
  isIso_app_third_of_distinguished F G α _ (T.shift_distinguished hT n) (h₁ n) (h₂ n)
    ((α.isIso_app_iff_of_iso ((shiftFunctorAdd C n 1).app T.obj₁)).1 (h₁ (n + 1)))
    ((α.isIso_app_iff_of_iso ((shiftFunctorAdd C n 1).app T.obj₂)).1 (h₂ (n + 1)))

end Stacks.CategoryTheory.ComponentwiseInvertibility

namespace StacksDraft.CompactDevissage

open StacksDraft.NatTransDevissage Stacks.CategoryTheory.ComponentwiseInvertibility

universe v v' u u'

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasCoproducts.{v} D]
  {D' : Type u'} [Category.{v'} D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  {F G : D ⥤ D'} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) G]
  (τ : F ⟶ G)

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D']
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated] in
/-- `τ` is invertible at every shift of a direct sum of shifts of a family at all of whose shifts
it is invertible. -/
lemma isIso_app_shift_of_colimitsOfShape_shiftClosure {ι : Type v} (E : ι → D)
    (hτ : ∀ i (n : ℤ), IsIso (τ.app ((E i)⟦n⟧))) (Y : D)
    (hY : (⨆ J : Type v, ((ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) Y) (n : ℤ) :
    IsIso (τ.app (Y⟦n⟧)) := by
  rw [ObjectProperty.prop_iSup_iff] at hY
  obtain ⟨J, ⟨p⟩⟩ := hY
  refine isIso_app_of_isColimit τ (p.diag ⋙ shiftFunctor D n)
    (isColimitOfPreserves (shiftFunctor D n) p.isColimit) fun j => ?_
  obtain ⟨W, m, e, ⟨i⟩⟩ := p.prop_diag_obj j
  exact (τ.isIso_app_iff_of_iso ((shiftFunctor D n).mapIso e ≪≫
    (shiftFunctorAdd D m n).symm.app (E i))).2 (hτ i (m + n))

end StacksDraft.CompactDevissage

end
