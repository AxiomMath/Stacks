module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection

/-!
# Invertibility of a natural transformation between functors of bounded below derived categories

Let `η : H₁ ⟶ H₂` be a shift-compatible natural transformation between two triangulated functors
`D⁺(C) ⥤ D⁺(D)`, each of which carries `D^{≥m}` into `D^{≥m}`, and let `K` be an object of
`D⁺(C)` bounded below by `a`. If `η` is invertible on each cohomology object of `K`, placed in
degree zero, then it is invertible at `K`.

This is `DerivedCategory.Plus.isIso_app_of_bounded_below` for functors between two different
bounded below derived categories; the argument is the same. The objects at which `η` is
invertible form a strictly full triangulated subcategory of `D⁺(C)`, so `η` is invertible at
every object with cohomology in a finite window by the dévissage
`DerivedCategory.Plus.prop_of_isGE_of_isLE`; and for a fixed degree `q` the truncation
`τ_{≤q}K ⟶ K` is invertible on `H^q` after either functor, because the third vertex of the
truncation triangle lies in `D^{≥q+1}` and both functors keep it there.

It is the passage from sheaves to bounded below complexes for a base change map
`g^{-1}Rf_* ⟶ Rf'_*(g')^{-1}`, as in the proof of [Stacks, Tag 0F09].

## Main results

* `DerivedCategory.Plus.isIso_app_of_isGE_of_isIso_app_single` — the theorem.

## References

* [Stacks Project, Tag 0F09](https://stacks.math.columbia.edu/tag/0F09)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace DerivedCategory.Plus

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory D]
  {H₁ H₂ : Plus C ⥤ Plus D} [H₁.CommShift ℤ] [H₂.CommShift ℤ]
  [H₁.IsTriangulated] [H₂.IsTriangulated] (η : H₁ ⟶ H₂) [NatTrans.CommShift η ℤ]

/-- The objects of `D⁺(C)` at which `η` is invertible. -/
private abbrev isoLocus : ObjectProperty (Plus C) := fun K ↦ IsIso (η.app K)

private instance isoLocus_isTriangulated : (isoLocus η).IsTriangulated :=
  Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated H₁ H₂ η

private instance isoLocus_isClosedUnderIsomorphisms : (isoLocus η).IsClosedUnderIsomorphisms :=
  Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms η

omit [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated]
  [NatTrans.CommShift η ℤ] in
/-- The naturality square of `η` at a morphism `g`, read on cohomology in a fixed degree. -/
private theorem isIso_homologyMap_app_of_isIso {X Y : Plus C} (g : X ⟶ Y) (q : ℤ)
    (h₁ : IsIso ((homologyFunctor D q).map (H₁.map g)))
    (h₂ : IsIso ((homologyFunctor D q).map (H₂.map g)))
    (hX : IsIso ((homologyFunctor D q).map (η.app X))) :
    IsIso ((homologyFunctor D q).map (η.app Y)) := by
  have : IsIso ((homologyFunctor D q).map (H₁.map g ≫ η.app Y)) := by
    rw [η.naturality g, Functor.map_comp]
    infer_instance
  rw [Functor.map_comp] at this
  exact IsIso.of_isIso_comp_left ((homologyFunctor D q).map (H₁.map g)) _

/-- **Invertibility on `D⁺(C)`, from invertibility on the cohomology objects**, for a
shift-compatible natural transformation `θ : F₁ ⟶ F₂` between triangulated functors
`D⁺(C) ⥤ D⁺(D)` each of which carries `D^{≥m}` into `D^{≥m}`: if `K` is bounded below and `θ` is
invertible at every cohomology object of `K` placed in degree zero, then `θ` is invertible at
`K`. -/
theorem isIso_app_of_isGE_of_isIso_app_single {F₁ F₂ : Plus C ⥤ Plus D} [F₁.CommShift ℤ]
    [F₂.CommShift ℤ] [F₁.IsTriangulated] [F₂.IsTriangulated] (θ : F₁ ⟶ F₂)
    [NatTrans.CommShift θ ℤ]
    (hF₁ : ∀ (L : Plus C) (m : ℤ), L.IsGE m → (F₁.obj L).IsGE m)
    (hF₂ : ∀ (L : Plus C) (m : ℤ), L.IsGE m → (F₂.obj L).IsGE m)
    (K : Plus C) (a : ℤ) (hGE : K.IsGE a)
    (hθ : ∀ q : ℤ, IsIso (θ.app ((singleFunctor C 0).obj ((homologyFunctor C q).obj K)))) :
    IsIso (θ.app K) := by
  have := hGE
  rw [isIso_iff]
  intro q
  by_cases haq : a ≤ q
  · have heq : a + ((q - a).toNat : ℤ) = q := by omega
    have hT' := TStructure.t.triangleLEGT_distinguished q K
    have hU : IsIso (θ.app ((TStructure.t.truncLE q).obj K)) := by
      refine prop_of_isGE_of_isLE (isoLocus θ) a (q - a).toNat _ inferInstance ?_
        fun p hp₁ hp₂ ↦ ?_
      · rw [heq]
        infer_instance
      · have hiso : IsIso ((homologyFunctor C p).map ((TStructure.t.truncLEι q).app K)) :=
          isIso_homologyMap_truncLEι_app K p q (by omega)
        exact (isoLocus θ).prop_of_iso
          ((singleFunctor C 0).mapIso (asIso ((homologyFunctor C p).map
            ((TStructure.t.truncLEι q).app K)))).symm (hθ p)
    have hV : ((TStructure.t.truncGT q).obj K).IsGE (q + 1) := inferInstance
    have key : ∀ (F : Plus C ⥤ Plus D) [F.CommShift ℤ] [F.IsTriangulated],
        (∀ (L : Plus C) (m : ℤ), L.IsGE m → (F.obj L).IsGE m) →
        IsIso ((homologyFunctor D q).map (F.map ((TStructure.t.truncLEι q).app K))) :=
      fun F _ _ hF ↦ isIso_homologyMap_mor₁_of_isGE₃ _ (F.map_distinguished _ hT') q (q + 1)
        (hF _ (q + 1) hV) (by omega)
    have := hU
    exact isIso_homologyMap_app_of_isIso θ ((TStructure.t.truncLEι q).app K) q (key F₁ hF₁)
      (key F₂ hF₂) inferInstance
  · have hz₁ := hF₁ K a hGE
    have hz₂ := hF₂ K a hGE
    exact IsZero.isIso (isZero_homology_of_isGE' (F₁.obj K) a q (by omega))
      (isZero_homology_of_isGE' (F₂.obj K) a q (by omega)) _

end DerivedCategory.Plus

end
