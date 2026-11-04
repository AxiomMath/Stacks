module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftDerived

/-!
# Transporting the comparison `D(P) ⥤ D_P(A)` along an exact equivalence

Let `A` be an abelian category and `P` a property of its objects whose full subcategory is abelian
with an exact inclusion `ι : P ⥤ A`.  The derived functor of `ι` has cohomology in `P`, so it
factors through the full subcategory `D_P(A)` of `D(A)` of complexes with cohomology in `P`; this
is the comparison functor `D(P) ⥤ D_P(A)`, of which Stacks 06VT and Stacks 08F1 are instances.

This file proves that whether the comparison is an equivalence is invariant under an equivalence
of abelian categories `E : A ≌ A'` matching `P` with a property `P'` of `A'`: if the comparison
for `P'` is an equivalence, so is the comparison for `P`.

## Main definitions

* `Stacks.DerivedComparison.comparison`: the comparison functor `D(P) ⥤ D_P(A)`.
* `Stacks.DerivedComparison.fullSubcategoryEquivalence`: the equivalence `P ≌ P'` cut out of
  `E`.

## Main results

* `Stacks.DerivedComparison.comparisonSquare`: the comparison functors intertwine the derived
  functors induced by `E` on `D(P)` and on `D_P(A)`.
* `Stacks.DerivedComparison.isEquivalence_comparison_of_equivalence`: the comparison for `P` is
  an equivalence as soon as the one for `P'` is.

## Implementation notes

The comparison functors of the library (`AlgebraicGeometry.Space.quasicoherentDerivedComparison`,
`AlgebraicGeometry.SmallEtale.derivedQcohOnSiteComparison`) are `ObjectProperty.lift` of the
derived inclusion with their own proof that it lands in `D_P(A)`; by proof irrelevance they are
`Stacks.DerivedComparison.comparison` on the nose, so the results here apply to them directly.
The four derived categories are taken at independent models.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategoryB

universe w₁ w₂ w₃ w₄

namespace Stacks.DerivedComparison

variable {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']

section Exact

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderKernels]
  [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts]

/-- The inclusion of a full subcategory closed under finite products is additive. -/
instance additive_ι : P.ι.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inclusion of a full subcategory closed under kernels is left exact. -/
instance preservesFiniteLimits_ι : PreservesFiniteLimits P.ι :=
  have : ∀ ⦃X Y : P.FullSubcategory⦄ (f : X ⟶ Y), PreservesLimit (parallelPair f 0) P.ι :=
    fun {_ _} f => P.preservesKernels_ι f
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- The inclusion of a full subcategory closed under cokernels is right exact. -/
instance preservesFiniteColimits_ι : PreservesFiniteColimits P.ι :=
  have : ∀ ⦃X Y : P.FullSubcategory⦄ (f : X ⟶ Y), PreservesColimit (parallelPair f 0) P.ι :=
    fun {_ _} f => P.preservesCokernels_ι f
  Functor.preservesFiniteColimits_of_preservesCokernels _

end Exact

variable (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts]

section Comparison

variable [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} P.FullSubcategory]

/-- The derived inclusion of `P` has cohomology in `P`: the inclusion is exact, so it commutes with
cohomology. -/
theorem derivedCategoryB_ι_mapDerivedCategory_obj (K : DerivedCategory P.FullSubcategory) :
    derivedCategoryB P (P.ι.mapDerivedCategory.obj K) := fun n =>
  P.prop_of_iso ((P.ι.mapDerivedCategoryHomologyIso n).app K).symm
    (P.prop_ι_obj ((DerivedCategory.homologyFunctor _ n).obj K))

/-- The comparison functor `D(P) ⥤ D_P(A)`: the derived functor of the exact inclusion of `P`,
factored through the complexes with cohomology in `P`. -/
def comparison : DerivedCategory P.FullSubcategory ⥤ (derivedCategoryB P).FullSubcategory :=
  (derivedCategoryB P).lift P.ι.mapDerivedCategory (derivedCategoryB_ι_mapDerivedCategory_obj P)

end Comparison

variable (P' : ObjectProperty A') [P'.IsClosedUnderIsomorphisms] [P'.ContainsZero]
  [P'.IsClosedUnderKernels] [P'.IsClosedUnderCokernels] [P'.IsClosedUnderFiniteProducts]
  (E : A ≌ A') [E.functor.Additive] (h : ∀ X, P' (E.functor.obj X) ↔ P X)

/-- The equivalence `P ≌ P'` cut out of an equivalence `E : A ≌ A'` matching `P` with `P'`. -/
def fullSubcategoryEquivalence : P.FullSubcategory ≌ P'.FullSubcategory :=
  E.congrFullSubcategory (funext fun X => propext (h X))

/-- The equivalence `P ≌ P'` is additive: followed by the faithful additive inclusion of `P'` it
is the additive functor `ι ⋙ E.functor`. -/
instance additive_fullSubcategoryEquivalence_functor :
    (fullSubcategoryEquivalence P P' E h).functor.Additive :=
  have : ((fullSubcategoryEquivalence P P' E h).functor ⋙ P'.ι).Additive :=
    inferInstanceAs (P.ι ⋙ E.functor).Additive
  Functor.additive_of_comp_faithful _ P'.ι

variable [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} P.FullSubcategory]
  [HasDerivedCategory.{w₃} A'] [HasDerivedCategory.{w₄} P'.FullSubcategory]

/-- **The comparison functors intertwine the derived functors of `E`.**  After the fully faithful
inclusion of `D_{P'}(A')` both sides are the derived functor of `ι ⋙ E.functor`. -/
def comparisonSquare :
    comparison P ⋙ (Stacks.UniverseLift.derivedCategoryBEquivalence E P P' h).functor ≅
      (fullSubcategoryEquivalence P P' E h).functor.mapDerivedCategory ⋙ comparison P' :=
  Functor.fullyFaithfulCancelRight (derivedCategoryB P').ι
    (Functor.associator _ _ _ ≪≫
      Stacks.DerivedQCoh.mapDerivedCategoryCompIso P.ι E.functor (P.ι ⋙ E.functor) (Iso.refl _) ≪≫
      (Stacks.DerivedQCoh.mapDerivedCategoryCompIso (fullSubcategoryEquivalence P P' E h).functor
        P'.ι (P.ι ⋙ E.functor) (Iso.refl _)).symm ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftCompιIso _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm)

variable {P P'} in
include h in
/-- **Invariance of the comparison under an exact equivalence.**  If `E : A ≌ A'` matches `P`
with `P'`, and the comparison `D(P') ⥤ D_{P'}(A')` is an equivalence, then so is the comparison
`D(P) ⥤ D_P(A)`. -/
theorem isEquivalence_comparison_of_equivalence [(comparison P').IsEquivalence] :
    (comparison P).IsEquivalence := by
  have : ((fullSubcategoryEquivalence P P' E h).functor.mapDerivedCategory ⋙
      comparison P').IsEquivalence := inferInstance
  have : (comparison P ⋙
      (Stacks.UniverseLift.derivedCategoryBEquivalence E P P' h).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso (comparisonSquare P P' E h).symm
  exact Functor.isEquivalence_of_comp_right (comparison P)
    (Stacks.UniverseLift.derivedCategoryBEquivalence E P P' h).functor

end Stacks.DerivedComparison

end
