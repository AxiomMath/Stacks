module

public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.FiberedInSets.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Stack.FiberedInSets
public import StacksFrontier.CategoryTheory.Sites.Stack.SetoidToSets
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category of elements of a sheaf is a stack in sets

Let `(𝒞, J)` be a site and let `P` be a presheaf of sets on `𝒞`. Its category of elements
`𝒮_P = CategoryTheory.PresheafOfCategories.discreteProjection P` is fibred in sets, and the
presheaf of objects that Stacks 0430 attaches to a category fibred in sets is `P`, up to a
`ULift`. So
`𝒮_P` is a stack in sets exactly when `P` is a sheaf, and any category over `𝒞` equivalent to
`𝒮_P` over `𝒞` is then a stack in setoids.

## Main definitions

* `CategoryTheory.PresheafOfCategories.objPresheafIso`: the presheaf of objects of `𝒮_P` is `P`
  composed with `CategoryTheory.uliftFunctor`.

## Main results

* `CategoryTheory.PresheafOfCategories.isStackInSets_discreteProjection`: the category of
  elements of a sheaf is a stack in sets.
* `CategoryTheory.PresheafOfCategories.isStackInSetoids_of_equivalenceOver_discreteProjection`:
  a category over `𝒞` equivalent over `𝒞` to the category of elements of a sheaf is a stack in
  setoids.

## References

* [Stacks Project, Tag 0430](https://stacks.math.columbia.edu/tag/0430)
* [Stacks Project, Tag 0431](https://stacks.math.columbia.edu/tag/0431)
* [Stacks Project, Tag 03YS](https://stacks.math.columbia.edu/tag/03YS)
-/

@[expose] public section

open Opposite

namespace CategoryTheory.PresheafOfCategories

universe vC uC

variable {C : Type uC} [Category.{vC} C]

/-- The category of elements of a presheaf of sets is fibred in sets. -/
@[sga "4 I 6.5" "(iv)⇒(ii), special case",
  sga "6 I 6.6" "partial",
  sga "6 I 8.5" "partial",
  sga "7 VI 1.1(d)" "partial"]
instance isFiberedInSets_discreteProjection (P : Cᵒᵖ ⥤ Type vC) :
    (discreteProjection P).IsFiberedInSets :=
  (Functor.isFiberedInSets_iff _).2
    ⟨(isFiberedInSetoids_discreteProjection P).1, isDiscrete_fiber_discreteProjection P⟩

/-- The category of elements of a presheaf of sets is a fibred category. -/
@[sga "6 I 6.6" "partial", sga "6 I 8.5" "partial"]
instance isFibered_discreteProjection (P : Cᵒᵖ ⥤ Type vC) :
    (discreteProjection P).IsFibered :=
  (Functor.IsFiberedInSets.isFiberedInGroupoids (discreteProjection P)).isFibered

/-- The presheaf of objects of the category of elements of `P` is `P`, up to the `ULift` that
raises `P`'s values to the universe of the objects of the total category. -/
noncomputable def objPresheafIso (P : Cᵒᵖ ⥤ Type vC) :
    (discreteProjection P).objPresheaf ≅ P ⋙ uliftFunctor.{uC, vC} :=
  NatIso.ofComponents
    (fun U ↦ Equiv.toIso ((discreteFiberEquiv P U.unop).trans Equiv.ulift.symm))
    (by
      intro U V f
      ext x
      refine ULift.ext ?_
      exact discreteFiberEquiv_eq_map_of_isHomLift P f.unop x
        (Functor.pullbackFiber (discreteProjection P) x f.unop)
        (Functor.IsPreFibered.pullbackMap x.2 f.unop)
        (Functor.IsPreFibered.pullbackMap.IsCartesian x.2 f.unop).toIsHomLift)

/-- The category of elements of a sheaf of sets on the site `(𝒞, J)` is a stack in sets. -/
@[sga "1 XIII 1.11" "partial", sga "1 XIII 1.2"]
theorem isStackInSets_discreteProjection (P : Cᵒᵖ ⥤ Type vC) (J : GrothendieckTopology C)
    (hP : Presheaf.IsSheaf J P) : (discreteProjection P).IsStackInSets J := by
  rwa [Functor.isStackInSets_iff_isSheaf_objPresheaf,
    Presheaf.isSheaf_of_iso_iff (objPresheafIso P), isSheaf_iff_isSheaf_of_type,
    Presieve.isSheaf_comp_uliftFunctor_iff, ← isSheaf_iff_isSheaf_of_type]

/-- A category over `𝒞` equivalent over `𝒞` to the category of elements of a sheaf of sets on the
site `(𝒞, J)` is a stack in setoids. -/
theorem isStackInSetoids_of_equivalenceOver_discreteProjection
    {𝒳 : BasedCategory.{vC, max uC vC} C} (P : Cᵒᵖ ⥤ Type vC) (J : GrothendieckTopology C)
    (hP : Presheaf.IsSheaf J P)
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.p (discreteProjection P)) :
    𝒳.p.IsStackInSetoids J :=
  (BasedCategory.isStackInSetoids_iff_of_equivalence
    (StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence
      (𝒴 := presheafOfCategories (P ⋙ typeToCat)) e) J).2
    (isStackInSets_discreteProjection P J hP).isStackInSetoids

end CategoryTheory.PresheafOfCategories

end
