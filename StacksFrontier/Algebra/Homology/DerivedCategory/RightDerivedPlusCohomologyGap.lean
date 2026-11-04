module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowComparisonDevissage
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# A cohomology gap survives a right derived functor of bounded amplitude

Let `F : A ⥤ B` be an additive functor between abelian categories, `A` with enough injectives,
whose total right derived functor `RF : D⁺(A) ⥤ D⁺(B)` raises the upper bound of the objects of
an isomorphism-closed class `P` by at most `N`. If the cohomology of `T ∈ D⁺(A)` lies in `P` and
vanishes in all degrees `c < p < a`, with `c + N < a - 1`, then `H^{a-1}(RF(T)) = 0`.

Indeed, in the truncation triangle `τ_{≤ c} T ⟶ T ⟶ τ_{> c} T`, the object `τ_{> c} T` lies in
degrees `≥ a`, hence so does `RF(τ_{> c} T)`, `F` being left exact; while `RF(τ_{≤ c} T)` lies in
degrees `≤ c + N < a - 1`. The long exact cohomology sequence then kills `H^{a-1}(RF(T))`.

## Main results

* `CategoryTheory.Functor.isZero_homology_rightDerivedFunctorPlus_of_gap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

attribute [local instance] commShiftRightDerivedFunctorPlus isTriangulated_rightDerivedFunctorPlus

variable {A B : Type*} [Category A] [Abelian A] [EnoughInjectives A] [Category B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- **A cohomology gap survives a right derived functor of bounded amplitude.** -/
theorem isZero_homology_rightDerivedFunctorPlus_of_gap (P : ObjectProperty A) [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] (N : ℤ)
    (hbound : ∀ (K : DerivedCategory.Plus A) (b : ℤ),
      (∀ q : ℤ, P ((DerivedCategory.Plus.homologyFunctor A q).obj K)) → K.IsLE b →
        (F.rightDerivedFunctorPlus.obj K).IsLE (b + N))
    (T : DerivedCategory.Plus A)
    (hT : ∀ q : ℤ, P ((DerivedCategory.Plus.homologyFunctor A q).obj T))
    (a c : ℤ) (hgap : ∀ p : ℤ, c < p → p < a →
      IsZero ((DerivedCategory.Plus.homologyFunctor A p).obj T))
    (hc : c + N < a - 1) :
    IsZero ((DerivedCategory.Plus.homologyFunctor B (a - 1)).obj
      (F.rightDerivedFunctorPlus.obj T)) := by
  let t := DerivedCategory.Plus.TStructure.t (C := A)
  let Tr := (t.triangleLEGT c).obj T
  have hTr : Tr ∈ distTriang _ := t.triangleLEGT_distinguished c T
  -- the first vertex `τ_{≤ c} T`
  have hL : ∀ q : ℤ, P ((DerivedCategory.Plus.homologyFunctor A q).obj Tr.obj₁) := fun q =>
    DerivedCategory.Plus.prop_homology_truncLE_obj P T c (fun i _ => hT i) q
  have hLLE : Tr.obj₁.IsLE c := t.isLE_truncLE_obj T _ _ le_rfl
  have h₁ : (F.rightDerivedFunctorPlus.obj Tr.obj₁).IsLE (a - 2) := by
    have := hbound _ c hL hLLE
    exact (DerivedCategory.Plus.TStructure.t (C := B)).isLE_of_le _ (c + N) (a - 2) (by omega)
  -- the third vertex `τ_{> c} T` lies in degrees `≥ a`
  have h₃ : Tr.obj₃.IsGE a := by
    rw [DerivedCategory.Plus.isGE_iff]
    intro i hi
    by_cases hic : i ≤ c
    · exact DerivedCategory.Plus.isZero_homology_truncGT_obj T i c hic
    · have := DerivedCategory.Plus.isIso_homologyMap_truncGTπ_app T i c (by omega)
      exact (hgap i (by omega) hi).of_iso
        (asIso ((DerivedCategory.Plus.homologyFunctor A i).map ((t.truncGTπ c).app T))).symm
  have h₃' : (F.rightDerivedFunctorPlus.obj Tr.obj₃).IsGE a :=
    F.isGE_rightDerivedFunctorPlus_obj Tr.obj₃ a
  -- the long exact sequence
  have hiso := DerivedCategory.Plus.isIso_homologyMap_mor₂_of_isLE₁
    (F.rightDerivedFunctorPlus.mapTriangle.obj Tr)
    (F.rightDerivedFunctorPlus.map_distinguished Tr hTr) (a - 1) (a - 2) h₁ (by omega)
  have h0 : IsZero ((DerivedCategory.Plus.homologyFunctor B (a - 1)).obj
      (F.rightDerivedFunctorPlus.obj Tr.obj₃)) :=
    DerivedCategory.Plus.isZero_homology_of_isGE' _ a (a - 1) (by omega)
  exact h0.of_iso (@asIso _ _ _ _ _ hiso)

end CategoryTheory.Functor

end
