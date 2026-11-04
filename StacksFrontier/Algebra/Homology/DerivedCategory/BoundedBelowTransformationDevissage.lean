module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# Invertibility of a transformation of functors `D⁺(C) ⥤ D⁺(D)` from its cohomology objects

Let `η : H₁ ⟶ H₂` be a shift-compatible natural transformation between triangulated functors
`D⁺(C) ⥤ D⁺(D)`, each of which carries `D^{≥m}` into `D^{≥m}`. If `η` is invertible on every
cohomology object of a bounded below `K`, placed in degree zero, then it is invertible at `K`.

This is `DerivedCategory.Plus.isIso_app_of_bounded_below`, which treats endofunctors of
`D⁺(C)`, for functors between two different bounded below derived categories; the argument is
the same dévissage along the truncation triangles of the canonical t-structure.

## Main results

* `DerivedCategory.Plus.isIso_app_of_bounded_below_of_isGE`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory.Plus

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

/-- **Invertibility on `D⁺(C)`, from invertibility on the cohomology objects**, for a
shift-compatible natural transformation between exact functors `D⁺(C) ⥤ D⁺(D)` which carry
`D^{≥m}` into `D^{≥m}`. -/
theorem isIso_app_of_bounded_below_of_isGE {H₁ H₂ : Plus C ⥤ Plus D} [H₁.CommShift ℤ]
    [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated] (η : H₁ ⟶ H₂)
    [NatTrans.CommShift η ℤ]
    (hH₁ : ∀ (L : Plus C) (m : ℤ), L.IsGE m → (H₁.obj L).IsGE m)
    (hH₂ : ∀ (L : Plus C) (m : ℤ), L.IsGE m → (H₂.obj L).IsGE m)
    (K : Plus C) (a : ℤ) (hGE : K.IsGE a)
    (hH : ∀ q : ℤ, IsIso (η.app ((singleFunctor C 0).obj ((homologyFunctor C q).obj K)))) :
    IsIso (η.app K) := by
  let P : ObjectProperty (Plus C) := fun K ↦ IsIso (η.app K)
  have : P.IsTriangulated :=
    Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated H₁ H₂ η
  have : P.IsClosedUnderIsomorphisms :=
    Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms η
  have := hGE
  rw [isIso_iff]
  intro q
  by_cases haq : a ≤ q
  · have heq : a + ((q - a).toNat : ℤ) = q := by omega
    have hT := TStructure.t.triangleLEGT_distinguished q K
    have hU : IsIso (η.app ((TStructure.t.truncLE q).obj K)) := by
      refine prop_of_isGE_of_isLE P a (q - a).toNat _ inferInstance ?_
        fun p hp₁ hp₂ ↦ ?_
      · rw [heq]
        infer_instance
      · have hiso : IsIso ((homologyFunctor C p).map ((TStructure.t.truncLEι q).app K)) :=
          isIso_homologyMap_truncLEι_app K p q (by omega)
        exact P.prop_of_iso
          ((singleFunctor C 0).mapIso (asIso ((homologyFunctor C p).map
            ((TStructure.t.truncLEι q).app K)))).symm (hH p)
    have hV : ((TStructure.t.truncGT q).obj K).IsGE (q + 1) := inferInstance
    have key : ∀ (H : Plus C ⥤ Plus D) [H.CommShift ℤ] [H.IsTriangulated],
        (∀ (L : Plus C) (m : ℤ), L.IsGE m → (H.obj L).IsGE m) →
        IsIso ((homologyFunctor D q).map (H.map ((TStructure.t.truncLEι q).app K))) :=
      fun H _ _ hH ↦ isIso_homologyMap_mor₁_of_isGE₃ _ (H.map_distinguished _ hT) q (q + 1)
        (hH _ (q + 1) hV) (by omega)
    have := key H₁ hH₁
    have := key H₂ hH₂
    have : IsIso ((homologyFunctor D q).map (H₁.map ((TStructure.t.truncLEι q).app K)) ≫
        (homologyFunctor D q).map (η.app K)) := by
      rw [← Functor.map_comp]
      erw [η.naturality ((TStructure.t.truncLEι q).app K)]
      rw [Functor.map_comp]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((homologyFunctor D q).map (H₁.map ((TStructure.t.truncLEι q).app K))) _
  · have hz₁ := hH₁ K a hGE
    have hz₂ := hH₂ K a hGE
    exact IsZero.isIso (isZero_homology_of_isGE' (H₁.obj K) a q (by omega))
      (isZero_homology_of_isGE' (H₂.obj K) a q (by omega)) _

end DerivedCategory.Plus
