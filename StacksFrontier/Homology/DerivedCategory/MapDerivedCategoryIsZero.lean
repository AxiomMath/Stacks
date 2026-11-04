module

public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# A faithful exact functor reflects zero objects of derived categories

For an exact functor `F` between abelian categories which is faithful, `F` read on derived
categories reflects zero objects: the cohomology of `F K` is `F` of the cohomology of `K`, and a
faithful additive functor reflects zero objects. A typical instance is restriction of scalars
along a ring map, which shows that `M ∈ D(A')` vanishes as soon as its restriction to `D(A)`
does.

## Main results

* `StacksDraft.DerivedCategoryHomology.isZero_of_isZero_mapDerivedCategory_obj`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.DerivedCategoryHomology

/-- **A faithful exact functor reflects zero objects of derived categories.** -/
theorem isZero_of_isZero_mapDerivedCategory_obj
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Faithful]
    {K : DerivedCategory C} (h : IsZero (F.mapDerivedCategory.obj K)) : IsZero K := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  have hF : IsZero (F.obj ((DerivedCategory.homologyFunctor C n).obj K)) :=
    ((DerivedCategory.homologyFunctor D n).map_isZero h).of_iso
      ((mapDerivedCategoryHomologyIso F n).app K).symm
  exact (IsZero.iff_id_eq_zero _).2
    (F.map_injective (by rw [F.map_id, F.map_zero]; exact hF.eq_of_src _ _))

end StacksDraft.DerivedCategoryHomology
