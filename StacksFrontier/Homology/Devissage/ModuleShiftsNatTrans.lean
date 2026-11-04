module

public import StacksFrontier.Homology.KFlat.FilteredColimitShifts
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaTriangles
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorCounitDevissage

/-!
# A morphism of exact functors out of `D(R)` invertible on the shifts of `R`

Let `R` be a ring and `F, G : D(R) ⥤ D` two exact functors into a pretriangulated category which
commute with direct sums.  A natural transformation `α : F ⟶ G` which is invertible at every shift
`R[k]` of the regular module is invertible.  This is the dévissage of [Stacks, Tag 09PB]
(`CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts`) applied to the
property "`α` is invertible at every shift of this object": it is closed under direct sums because
`F`, `G` and the shift functors preserve them, it satisfies two-out-of-three in a distinguished
triangle by the five lemma (`isIso_app_shifts_triangle`), and it holds at every `R[k]` by
hypothesis.  No compatibility of `α` with the shift is needed.

## Main results

* `StacksDraft.NatTransDevissage.isIso_app_of_isIso_app_shifts_regular`.

## References

* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.NatTransDevissage

universe u v

/-- **A morphism of exact, direct-sum-preserving functors out of `D(R)` which is invertible at
every shift of `R` is invertible** (the dévissage of [Stacks, Tag 09PB]). -/
theorem isIso_app_of_isIso_app_shifts_regular {R : Type u} [Ring R] [Small.{v} R]
    {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : DerivedCategory (ModuleCat.{v} R) ⥤ D) (hFs : F.CommShift ℤ) (hGs : G.CommShift ℤ)
    (hFt : letI := hFs; F.IsTriangulated) (hGt : letI := hGs; G.IsTriangulated)
    (hF : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) F)
    (hG : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) G) (α : F ⟶ G)
    (h : ∀ k : ℤ, IsIso (α.app (((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
      (ModuleCat.of R (Shrink.{v} R)))⟦k⟧))) (K : DerivedCategory (ModuleCat.{v} R)) :
    IsIso (α.app K) := by
  have key := (CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts
    (R := R)).2 (fun K ↦ ∀ n : ℤ, IsIso (α.app (K⟦n⟧)))
    (fun {I} K _ hK n ↦ by
      have := hF I
      have := hG I
      have hc : IsColimit ((shiftFunctor _ n).mapCocone (colimit.cocone (Discrete.functor K))) :=
        isColimitOfPreserves (shiftFunctor _ n) (colimit.isColimit _)
      exact isIso_app_of_isColimit α (Discrete.functor K ⋙ shiftFunctor _ n) hc
        (fun j ↦ hK j.as n))
    (fun T hT ↦ Stacks.Cohomology.ProjectionFormulaTriangles.isIso_app_shifts_triangle
      F G hFs hGs hFt hGt α T hT)
    (fun k n ↦ isIso_app_of_iso α ((shiftFunctorAdd' _ k n (k + n) rfl).app _) (h (k + n)))
    K 0
  exact isIso_app_of_iso α ((shiftFunctorZero _ ℤ).app K) key

end StacksDraft.NatTransDevissage

end
