module

public import StacksFrontier.RingTheory.LocalCohomology.CechModel.BoundedTerms

/-!
# Triangulated functors on a bounded complex

A triangulated endofunctor of a derived category kills a bounded complex as soon as it kills
each of the complex's terms, placed in every degree. Consequently, if `π : K ⟶ K^n[-n]` is
invertible in degree `n` and the functor kills every other term of `K`, then the functor inverts
`π`.

## Main results

* `Stacks.LocalCohomology.CechFormula.isZero_map_of_bounded` — a triangulated functor killing
  every term of a bounded complex kills the complex.
* `Stacks.LocalCohomology.CechFormula.isIso_map_to_single` — such a functor inverts the
  projection onto the one term it does not kill.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace Stacks.LocalCohomology.CechFormula

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- If `K` vanishes outside a range of `m` consecutive degrees starting at `a`, and the
triangulated functor `F` sends every term of `K`, placed in every degree, to zero, then `F` sends
`K` to zero. -/
theorem isZero_map_of_bounded
    (F : DerivedCategory C ⥤ DerivedCategory C) [F.CommShift ℤ] [F.IsTriangulated]
    (K : CochainComplex C ℤ) (a : ℤ) (m : ℕ)
    (hz : ∀ i, i < a ∨ a + m ≤ i → IsZero (K.X i))
    (ht : ∀ i q, IsZero (F.obj ((DerivedCategory.singleFunctor C q).obj (K.X i)))) :
    IsZero (F.obj (DerivedCategory.Q.obj K)) := by
  let P : ObjectProperty (DerivedCategory C) :=
    ObjectProperty.inverseImage (IsZero (C := DerivedCategory C)) F
  have : P.IsClosedUnderIsomorphisms := ⟨fun e hX => hX.of_iso (F.mapIso e.symm)⟩
  have : P.ContainsZero :=
    ⟨0, isZero_zero _, F.map_isZero (isZero_zero (DerivedCategory C))⟩
  have : P.IsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ =>
    Triangle.isZero₂_of_isZero₁₃ _ (F.map_distinguished _ hT) h₁ h₃
  exact prop_Q_obj_of_bounded_terms P m a K hz ht

/-- Let `π : K ⟶ N[-n]` be invertible in degree `n`, with `K` vanishing outside a range of `m`
consecutive degrees starting at `a`. If the triangulated functor `F` kills every term of `K`
other than the degree-`n` one, placed in every degree, then `F` inverts `π`. -/
theorem isIso_map_to_single
    (F : DerivedCategory C ⥤ DerivedCategory C) [F.CommShift ℤ] [F.IsTriangulated]
    (K : CochainComplex C ℤ) (N : C) (n a : ℤ) (m : ℕ)
    (π : K ⟶ (CochainComplex.singleFunctor C n).obj N) (hπ : IsIso (π.f n))
    (hz : ∀ i, i < a ∨ a + m ≤ i → IsZero (K.X i))
    (ht : ∀ i, i ≠ n → ∀ q,
      IsZero (F.obj ((DerivedCategory.singleFunctor C q).obj (K.X i)))) :
    IsIso (F.map (DerivedCategory.Q.map π)) := by
  have hzero : IsZero ((kernel π).X n) := isZero_kernel_toSingle_X_self π hπ
  have hker : IsZero (F.obj (DerivedCategory.Q.obj (kernel π))) := by
    refine isZero_map_of_bounded F (kernel π) a m (fun i hi => ?_) (fun i q => ?_)
    · obtain rfl | hin := eq_or_ne i n
      · exact hzero
      · have := isIso_kernel_ι_toSingle_f π hπ i hin
        exact (hz i hi).of_iso (asIso ((kernel.ι π).f i))
    · obtain rfl | hin := eq_or_ne i n
      · exact F.map_isZero ((DerivedCategory.singleFunctor C q).map_isZero hzero)
      · have := isIso_kernel_ι_toSingle_f π hπ i hin
        exact (ht i hin q).of_iso (F.mapIso
          ((DerivedCategory.singleFunctor C q).mapIso (asIso ((kernel.ι π).f i))))
  exact (Triangle.isZero₁_iff_isIso₂ _
    (F.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished
      (toSingleKernelShortComplex_shortExact π hπ)))).mp hker

end Stacks.LocalCohomology.CechFormula
