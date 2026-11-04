module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory

/-!
# When an exact functor carries `D⁺_B` into `D⁺_{B'}`

Let `R : D(A) ⥤ D(A')` be an exact functor between derived categories of abelian categories, let
`B'` be a weak Serre subcategory of `A'`, and let `K` be a bounded below object of `D(A)`. If `R`
preserves boundedness below and carries each cohomology object of `K`, placed in degree zero, into
`D⁺_{B'}(A')`, then it carries `K` itself into `D⁺_{B'}(A')`.

This is the formal content of the spectral-sequence step in the descent statements for a flat
morphism of ringed topoi: there `R` is the derived pushforward `Rf_*`, `B'` is a weak Serre
subcategory of modules downstairs, and the hypothesis on the cohomology objects comes from the
unit of the derived adjunction being invertible on the heart. Nothing in the argument uses the
geometry, so it is proved for an arbitrary exact functor.

## The argument

The objects of `D(A)` carried by `R` into `D⁺_{B'}(A')` are the preimage
`(derivedCategoryBPlus B').inverseImage R`. It is a strictly full subcategory, stable under the
shift because `R` commutes with it, and closed under the middle vertex of a distinguished triangle
because `R` is exact — so `CategoryTheory.ObjectProperty.prop_of_isGE_of_isLE` gives the statement
for an object with cohomology in finitely many degrees.

A bounded below object need not have cohomology in finitely many degrees, so the last step is read
on cohomology instead: for a fixed degree `q` the truncation triangle at `q + 1` has `τ^{<q+1}K`
inside a bounded window, hence in the preimage, while `R(τ^{≥q+1}K)` lies in `D^{≥q+1}`, so
`H^q(R(τ^{<q+1}K)) ⟶ H^q(RK)` is invertible.

## Main results

* `WeakSerre.isWeakSerre_of_isWeakSerreClass`: a weak Serre subcategory in the sense of Stacks
  0754 satisfies the five term exactness condition of Stacks 02MO (2).
* `DerivedCategoryB.isBoundedBelow_iff_exists_isGE`: cohomological boundedness below is the
  existence of a bound for the canonical t-structure.
* `DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj`: an object of a weak Serre
  subcategory, placed in degree zero, lies in `D⁺_B`.
* `DerivedCategoryB.derivedCategoryBPlus_inverseImage_isStableUnderShift` and
  `derivedCategoryBPlus_inverseImage_isTriangulatedClosed₂`: the preimage of `D⁺_{B'}` under an
  exact functor is a strictly full triangulated subcategory.
* `DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE`: **the theorem**.

## Implementation notes

`CategoryTheory.ObjectProperty.IsWeakSerreClass` is the closure form of the definition of a weak
Serre subcategory and is the hypothesis the consumers carry, because it is a class; the lemmas of
`StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory` are stated for the five term
exactness form `WeakSerre.IsWeakSerre`. The bridge between the two is proved once here rather than
re-derived at each use.

Only stability under the shift and closure under the middle vertex of a distinguished triangle are
established for the preimage, not `CategoryTheory.ObjectProperty.IsTriangulated`: the remaining
condition, containing a zero object, would need `R` to preserve zero morphisms, and nothing below
uses it.

## References

* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u v' u'

namespace WeakSerre

/-- **A weak Serre subcategory in the sense of Stacks 0754 is one in the sense of Stacks 02MO.**
The closure conditions give the five term exactness condition through
`CategoryTheory.ObjectProperty.prop_obj₂_of_exact`. -/
theorem isWeakSerre_of_isWeakSerreClass {A : Type u} [Category.{v} A] [Abelian A]
    (B : ObjectProperty A) [B.IsWeakSerreClass] : IsWeakSerre B :=
  ⟨inferInstance, B.exists_prop_of_isWeakSerreClass, fun E h₀ h₁ h₃ h₄ ↦
    ObjectProperty.prop_mid_of_exact₄ B.prop_obj₂_of_exact
      E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄⟩

end WeakSerre

namespace DerivedCategoryB

open DerivedCategory ObjectProperty WeakSerre

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- **Cohomological boundedness below is boundedness below for the canonical t-structure.** -/
theorem isBoundedBelow_iff_exists_isGE (K : DerivedCategory A) :
    IsBoundedBelow K ↔ ∃ n : ℤ, K.IsGE n := by
  constructor <;> rintro ⟨n, hn⟩
  · exact ⟨n, (DerivedCategory.isGE_iff K n).2 hn⟩
  · exact ⟨n, (DerivedCategory.isGE_iff K n).1 hn⟩

/-- Cohomological boundedness above is boundedness above for the canonical t-structure. -/
private theorem isBoundedAbove_iff_exists_isLE (K : DerivedCategory A) :
    IsBoundedAbove K ↔ ∃ n : ℤ, K.IsLE n := by
  constructor <;> rintro ⟨n, hn⟩
  · exact ⟨n, (DerivedCategory.isLE_iff K n).2 hn⟩
  · exact ⟨n, (DerivedCategory.isLE_iff K n).1 hn⟩

/-- **An object of a weak Serre subcategory, placed in degree zero, lies in `D⁺_B`.** Its
cohomology is the object itself in degree zero and vanishes elsewhere. -/
theorem derivedCategoryBPlus_singleFunctor_obj (B : ObjectProperty A) (hB : IsWeakSerre B)
    (M : A) (hM : B M) :
    derivedCategoryBPlus B ((singleFunctor A 0).obj M) := by
  refine ⟨⟨0, fun n hn ↦ isZero_of_isGE _ 0 n hn⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst hn
    exact hB.isClosedUnderIsomorphisms.of_iso
      ((singleFunctorCompHomologyFunctorIso A 0).app M).symm hM
  · refine zero_mem_of_isWeakSerre B hB _ ?_
    rcases lt_or_gt_of_ne hn with h | h
    · exact isZero_of_isGE _ 0 n h
    · exact isZero_of_isLE _ 0 n h

section

variable {A' : Type u'} [Category.{v'} A'] [Abelian A'] [HasDerivedCategory A']
  (R : DerivedCategory A ⥤ DerivedCategory A') (B' : ObjectProperty A') (hB' : IsWeakSerre B')

include hB'

/-- The objects carried by `R` into `D⁺_{B'}` form a strictly full subcategory. -/
theorem derivedCategoryBPlus_inverseImage_isClosedUnderIsomorphisms :
    ((derivedCategoryBPlus B').inverseImage R).IsClosedUnderIsomorphisms := by
  have := derivedCategoryBPlus_isClosedUnderIsomorphisms B' hB'
  infer_instance

/-- The objects carried by `R` into `D⁺_{B'}` are stable under the shift, because `R` commutes
with it and `D⁺_{B'}` is stable under it. -/
theorem derivedCategoryBPlus_inverseImage_isStableUnderShift [R.CommShift ℤ] :
    ((derivedCategoryBPlus B').inverseImage R).IsStableUnderShift ℤ := by
  have := derivedCategoryBPlus_isStableUnderShift B' hB'
  refine ⟨fun a ↦ ⟨fun K hK ↦ ?_⟩⟩
  exact (derivedCategoryBPlus_isClosedUnderIsomorphisms B' hB').of_iso
    ((R.commShiftIso a).app K).symm ((derivedCategoryBPlus B').le_shift a _ hK)

/-- The objects carried by `R` into `D⁺_{B'}` contain the middle vertex of a distinguished
triangle whose other two vertices they contain, because `R` is exact and `D⁺_{B'}` is a
triangulated subcategory. -/
theorem derivedCategoryBPlus_inverseImage_isTriangulatedClosed₂ [R.CommShift ℤ]
    [R.IsTriangulated] :
    ((derivedCategoryBPlus B').inverseImage R).IsTriangulatedClosed₂ := by
  have := derivedCategoryBPlus_isClosedUnderIsomorphisms B' hB'
  have := derivedCategoryBPlus_isTriangulated B' hB'
  have := derivedCategoryBPlus_inverseImage_isClosedUnderIsomorphisms R B' hB'
  refine IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ ↦ ?_)
  exact (derivedCategoryBPlus B').ext_of_isTriangulatedClosed₂ (R.mapTriangle.obj T)
    (R.map_distinguished T hT) h₁ h₃

/-- **An exact functor preserving boundedness below carries a bounded below object into
`D⁺_{B'}` as soon as it carries each of its cohomology objects, placed in degree zero, there.**

A fixed degree `q` is enough. Below the bound both sides vanish. Above it, truncate at `q + 1`:
the truncation `τ^{<q+1}K` sits in the window `[a, q]`, so `R` carries it into `D⁺_{B'}` by
`CategoryTheory.ObjectProperty.prop_of_isGE_of_isLE`, and `H^q` of the image of the inclusion
`τ^{<q+1}K ⟶ K` is invertible, because the third vertex of the truncation triangle is carried
into `D^{≥q+1}`. -/
theorem derivedCategoryBPlus_map_obj_of_isGE [R.CommShift ℤ] [R.IsTriangulated]
    (hR : ∀ (L : DerivedCategory A) (m : ℤ), L.IsGE m → (R.obj L).IsGE m)
    (K : DerivedCategory A) (a : ℤ) (hGE : K.IsGE a)
    (hH : ∀ q : ℤ, derivedCategoryBPlus B'
      (R.obj ((singleFunctor A 0).obj ((homologyFunctor A q).obj K)))) :
    derivedCategoryBPlus B' (R.obj K) := by
  have := hGE
  have := derivedCategoryBPlus_inverseImage_isClosedUnderIsomorphisms R B' hB'
  have := derivedCategoryBPlus_inverseImage_isStableUnderShift R B' hB'
  have := derivedCategoryBPlus_inverseImage_isTriangulatedClosed₂ R B' hB'
  have hRK : (R.obj K).IsGE a := hR K a hGE
  refine ⟨⟨a, fun i hi ↦ isZero_of_isGE (R.obj K) a i hi⟩, fun q ↦ ?_⟩
  by_cases haq : a ≤ q
  · have hn : ((q - a).toNat : ℤ) = q - a := Int.toNat_of_nonneg (by omega)
    have hT := TStructure.t.triangleLTGE_distinguished (q + 1) K
    have hU : derivedCategoryBPlus B' (R.obj ((TStructure.t.truncLT (q + 1)).obj K)) := by
      refine ((derivedCategoryBPlus B').inverseImage R).prop_of_isGE_of_isLE a (q - a).toNat _
        inferInstance ?_ fun p hp₁ hp₂ ↦ ?_
      · rw [hn]
        exact TStructure.t.isLE_truncLT_obj K (q + 1) (a + (q - a)) (by omega)
      · have : IsIso ((homologyFunctor A p).map ((TStructure.t.truncLTι (q + 1)).app K)) :=
          isIso_homologyMap_mor₁_of_isGE₃ _ hT p (q + 1) inferInstance (by omega)
        exact (derivedCategoryBPlus_isClosedUnderIsomorphisms B' hB').of_iso
          (R.mapIso ((singleFunctor A 0).mapIso (asIso ((homologyFunctor A p).map
            ((TStructure.t.truncLTι (q + 1)).app K))))).symm (hH p)
    have hV : ((TStructure.t.truncGE (q + 1)).obj K).IsGE (q + 1) := inferInstance
    have hiso : IsIso ((homologyFunctor A' q).map
        (R.map ((TStructure.t.truncLTι (q + 1)).app K))) :=
      isIso_homologyMap_mor₁_of_isGE₃ (R.mapTriangle.obj _) (R.map_distinguished _ hT) q (q + 1)
        (hR _ (q + 1) hV) (by omega)
    exact hB'.isClosedUnderIsomorphisms.of_iso
      (asIso ((homologyFunctor A' q).map (R.map ((TStructure.t.truncLTι (q + 1)).app K))))
      (hU.2 q)
  · exact zero_mem_of_isWeakSerre B' hB' _ (isZero_of_isGE (R.obj K) a q (by omega))

end

/-- `D_B(A)` is a triangulated subcategory of `D(A)` when `B` is a weak Serre subcategory of
`A`, in the form instance search can use. -/
instance isTriangulated_derivedCategoryB {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (B : ObjectProperty A) [B.IsWeakSerreClass] :
    (derivedCategoryB B).IsTriangulated :=
  derivedCategoryB_isTriangulated B (WeakSerre.isWeakSerre_of_isWeakSerreClass B)

/-- `D^b_B(A)` is a triangulated subcategory of `D(A)` when `B` is a weak Serre subcategory of
`A`, in the form instance search can use. -/
instance isTriangulated_derivedCategoryBBounded {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (B : ObjectProperty A) [B.IsWeakSerreClass] :
    (derivedCategoryBBounded B).IsTriangulated :=
  derivedCategoryBBounded_isTriangulated B (WeakSerre.isWeakSerre_of_isWeakSerreClass B)

/-- **Cohomological boundedness is boundedness for the canonical t-structure.** The two
descriptions of `D^b_B(A)` agree: vanishing of `H^n` outside a finite range is the conjunction
of `IsGE` and `IsLE`. -/
theorem derivedCategoryBBounded_eq_bounded_inf {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (B : ObjectProperty A) :
    derivedCategoryBBounded B =
      (DerivedCategory.TStructure.t (C := A)).bounded ⊓
        fun K ↦ ∀ n : ℤ, B ((DerivedCategory.homologyFunctor A n).obj K) := by
  funext K
  exact propext (and_congr_left fun _ ↦ and_congr (isBoundedBelow_iff_exists_isGE K)
    (isBoundedAbove_iff_exists_isLE K))

end DerivedCategoryB

end
