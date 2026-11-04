module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ThickeningInvariance
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusCompIsoh
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BoundedBelowComparisonEquivalence

/-!
# Bounded below derived adjunctions precomposed with an exact equivalence

Let `e : D ≌ C` be an equivalence of abelian categories. It is exact in both directions, so it
induces an equivalence `D⁺(D) ≌ D⁺(C)` whose two legs are the degreewise derived functors of
`e.functor` and `e.inverse`. Consequently, for an adjunction `L ⊣ R` with `L : C ⥤ E` exact, if
the derived unit `K ⟶ R(L K)` of `Stacks.ComparingTopologies.derivedPlusAdjunction` is invertible
at every `K` of `D⁺(C)`, then so is the derived unit of the adjunction `e ⋙ L ⊣ R ⋙ e⁻¹` at every
`K` of `D⁺(D)`: the first says that the derived left adjoint is fully faithful, and precomposing a
fully faithful functor with an equivalence keeps it fully faithful.

## Main definitions

* `Stacks.CategoryHomology.mapDerivedCategoryPlusEquivalence`: the equivalence
  `D⁺(D) ≌ D⁺(C)` induced by an equivalence of abelian categories, for any models of the derived
  categories.

## Main results

* `CategoryTheory.Adjunction.isIso_derivedPlusAdjunction_unit_app_comp_equivalence`: invertibility
  of the derived unit of `L ⊣ R` everywhere on `D⁺(C)` gives it for `e ⋙ L ⊣ R ⋙ e⁻¹` everywhere
  on `D⁺(D)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryHomology

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- **An equivalence of abelian categories induces an equivalence of bounded below derived
categories**, with the degreewise derived functors of its two legs. -/
def mapDerivedCategoryPlusEquivalence (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] :
    DerivedCategory.Plus C ≌ DerivedCategory.Plus D :=
  CategoryTheory.Equivalence.mk e.functor.mapDerivedCategoryPlus e.inverse.mapDerivedCategoryPlus
    (Functor.mapDerivedCategoryPlusIdIso.symm ≪≫
      (Functor.mapDerivedCategoryPlusCompIsoh e.unitIso.symm).symm)
    (Functor.mapDerivedCategoryPlusCompIsoh e.counitIso ≪≫ Functor.mapDerivedCategoryPlusIdIso)

/-- The functor of `mapDerivedCategoryPlusEquivalence e` is the degreewise derived functor of
`e.functor`. -/
@[simp]
theorem mapDerivedCategoryPlusEquivalence_functor (e : C ≌ D) [e.functor.Additive]
    [e.inverse.Additive] :
    (mapDerivedCategoryPlusEquivalence e).functor = e.functor.mapDerivedCategoryPlus := rfl

end Stacks.CategoryHomology

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives E]

/-- **The derived unit of an adjunction precomposed with an equivalence.** Let `e : D ≌ C` be an
equivalence of abelian categories and `L ⊣ R` an adjunction with `L : C ⥤ E` exact. If the derived
unit `K ⟶ R(L K)` is invertible at every `K` of `D⁺(C)`, then the derived unit of
`e ⋙ L ⊣ R ⋙ e⁻¹` is invertible at every `K` of `D⁺(D)`: invertibility of the unit everywhere is
full faithfulness of the derived left adjoint, which is preserved by precomposing with the derived
equivalence `Stacks.CategoryHomology.mapDerivedCategoryPlusEquivalence e`. -/
theorem isIso_derivedPlusAdjunction_unit_app_comp_equivalence (e : D ≌ C)
    [e.functor.Additive] [e.inverse.Additive]
    {L : C ⥤ E} {R : E ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
    (h : ∀ K, IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction adj).unit.app K))
    (K : DerivedCategory.Plus D) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
      (e.toAdjunction.comp adj)).unit.app K) := by
  have : IsIso (Stacks.ComparingTopologies.derivedPlusAdjunction adj).unit :=
    NatIso.isIso_of_isIso_app _
  let hL := (Stacks.ComparingTopologies.derivedPlusAdjunction adj).fullyFaithfulLOfIsIsoUnit
  let hE := (Stacks.CategoryHomology.mapDerivedCategoryPlusEquivalence e).fullyFaithfulFunctor
  let h' : (e.functor ⋙ L).mapDerivedCategoryPlus.FullyFaithful :=
    (hE.comp hL).ofIso (Functor.mapDerivedCategoryPlusCompIsoh (Iso.refl (e.functor ⋙ L)))
  have := h'.full
  have := h'.faithful
  infer_instance

end CategoryTheory.Adjunction

end
