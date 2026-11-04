module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.LeftDerivedFunctor

/-!
# The filtered right derived functor

Let `A` and `B` be abelian categories and `T : A ⥤ B` an additive functor. Applying `T`
termwise to a bounded-below complex of filtered injective objects and passing to the
bounded-below filtered derived category of `B` gives one route in the defining diagram of
the filtered right derived functor. If `A` has enough injectives, the comparison functor
`CochainComplex.FilteredDerivedCategory.toPlus` is an equivalence, and composing with a
chosen inverse gives the filtered right derived functor `RT : DF⁺(A) ⥤ DF⁺(B)` together
with the natural isomorphism that makes the diagram commute.

## Main definitions

* `CategoryTheory.FilteredDerived.filteredInjectivePlusMapToDerivedPlus`: the
  injective-complex route in the defining diagram.
* `CategoryTheory.FilteredDerived.filteredRightDerivedFunctor`: the filtered right derived
  functor.
* `CategoryTheory.FilteredDerived.filteredRightDerivedFunctorComparison`: the natural
  isomorphism expressing commutativity of the diagram.

## Implementation notes

The termwise construction is `CategoryTheory.FilteredDerived.mapFiniteFiltered`, the functor
`Fil^f(A) ⥤ Fil^f(B)` induced by `T`; on a left exact functor its filtration step is the
image `T(FᵖA) ⊆ T(A)`. Passing to complexes and to the homotopy category gives an exact
functor `K⁺(Fil^f(A)) ⥤ K⁺(Fil^f(B))`, whose restriction to `K⁺(Iᶠ)` is the bottom arrow of
the defining diagram. Additivity of `T` is all that is used, so in particular the
construction applies to left exact functors.

This is the dual of `CategoryTheory.FilteredDerived.filteredLeftDerivedFunctor` and is
built directly rather than by passing to opposite categories.

## References

* [Stacks Project, Tag 03TD](https://stacks.math.columbia.edu/tag/03TD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe vA vB uA uB

namespace CategoryTheory.FilteredDerived

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]

/-- The lower route in the defining diagram of the filtered right derived functor: apply `T`
termwise to a bounded-below complex of filtered injective objects, then pass to the
bounded-below filtered derived category. -/
@[implicit_reducible, stacks 03TD "filtered_right_derived_functor"]
noncomputable def filteredInjectivePlusMapToDerivedPlus (T : A ⥤ B) [T.Additive] :
    (CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).FullSubcategory ⥤
      (CochainComplex.FilteredDerivedCategory.plus B).FullSubcategory :=
  (CochainComplex.FilteredDerivedCategory.plus B).lift
    ((CochainComplex.FilteredDerivedCategory.filteredInjectivePlus A).ι ⋙
      (mapFiniteFiltered T).mapHomotopyCategory (.up ℤ) ⋙
      CochainComplex.FilteredDerivedCategory.Qh)
    (by
      rintro ⟨X, hX⟩
      obtain ⟨K, ⟨⟨n, hn⟩, -⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
      have hm : CochainComplex.IsStrictlyGE
          (((mapFiniteFiltered T).mapHomologicalComplex (.up ℤ)).obj K) n := by
        rw [CochainComplex.isStrictlyGE_iff] at hn ⊢
        intro i hi
        exact (mapFiniteFiltered T).map_isZero (hn i hi)
      have := hm
      exact CochainComplex.FilteredDerivedCategory.plus_Qh_obj
        (((mapFiniteFiltered T).mapHomologicalComplex (.up ℤ)).obj K) n)

/-- The filtered right derived functor `RT : DF⁺(A) ⥤ DF⁺(B)` of an additive functor
`T : A ⥤ B`, defined when `A` has enough injectives. -/
@[implicit_reducible, stacks 03TD "filtered_right_derived_functor"]
noncomputable def filteredRightDerivedFunctor (T : A ⥤ B) [T.Additive] [EnoughInjectives A] :
    (CochainComplex.FilteredDerivedCategory.plus A).FullSubcategory ⥤
      (CochainComplex.FilteredDerivedCategory.plus B).FullSubcategory :=
  (CochainComplex.FilteredDerivedCategory.toPlus A).inv ⋙
    filteredInjectivePlusMapToDerivedPlus T

/-- The natural isomorphism making the injective-resolution diagram for the filtered right
derived functor commute. -/
@[stacks 03TD "filtered_right_derived_functor"]
noncomputable def filteredRightDerivedFunctorComparison (T : A ⥤ B) [T.Additive]
    [EnoughInjectives A] :
    CochainComplex.FilteredDerivedCategory.toPlus A ⋙ filteredRightDerivedFunctor T ≅
      filteredInjectivePlusMapToDerivedPlus T :=
  Functor.isoWhiskerRight
    (CochainComplex.FilteredDerivedCategory.toPlus A).asEquivalence.unitIso.symm
    (filteredInjectivePlusMapToDerivedPlus T)

end CategoryTheory.FilteredDerived

end
