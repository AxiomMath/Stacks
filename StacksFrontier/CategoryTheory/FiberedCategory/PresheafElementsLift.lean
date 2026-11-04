module

public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElements
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting an object of the category of elements of a presheaf

Let `P` be a presheaf of sets on `C` and let `𝒮_P` be its category of elements (Stacks 04TM),
which is fibred in sets over `C`. An object of `𝒮_P` over `V` is an element of `P(V)`, by
`CategoryTheory.PresheafOfCategories.discreteFiberEquiv`. This file shows that some object over
`U` has its chosen pullback along `f : V ⟶ U` isomorphic to a given object over `V` if and only
if some `s' ∈ P(U)` restricts to the corresponding element.

## Main results

* `CategoryTheory.PresheafOfCategories.discreteFiberEquiv_eq_of_iso`: isomorphic objects of one
  fibre name the same element of the presheaf.
* `CategoryTheory.PresheafOfCategories.discreteFiberEquiv_pullbackFunctor_obj`: the chosen
  pullback of an object names the restriction of its element.
* `CategoryTheory.PresheafOfCategories.nonempty_iso_pullbackFunctor_obj_iff`: the lifting
  criterion, `(∃ x', f^* x' ≅ x) ↔ (∃ s', P(f)(s') = x)`.

## References

* [Stacks Project, Tag 04TM](https://stacks.math.columbia.edu/tag/04TM)
* [Stacks Project, Tag 02XN](https://stacks.math.columbia.edu/tag/02XN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe vC uC

namespace CategoryTheory.PresheafOfCategories

variable {C : Type uC} [Category.{vC} C] (P : Cᵒᵖ ⥤ Type vC)

/-- Isomorphic objects of the fibre over `V` name the same element of `P(V)`. -/
theorem discreteFiberEquiv_eq_of_iso {V : C} {x y : (discreteProjection P).Fiber V} (e : x ≅ y) :
    discreteFiberEquiv P V x = discreteFiberEquiv P V y := by
  simpa using discreteFiberEquiv_eq_map_of_isHomLift P (𝟙 V) y x e.hom.1 e.hom.2

/-- The chosen pullback along `f : V ⟶ U` of an object `x'` over `U` names the restriction
along `f` of the element named by `x'`. -/
@[sga "6 I 6.6" "partial"]
theorem discreteFiberEquiv_pullbackFunctor_obj {V U : C} (f : V ⟶ U)
    (x' : (discreteProjection P).Fiber U) :
    discreteFiberEquiv P V
        (((discreteProjection P).chosenPullbacks.pullbackFunctor f).obj x') =
      P.map f.op (discreteFiberEquiv P U x') :=
  discreteFiberEquiv_eq_map_of_isHomLift P f x'
    (Functor.pullbackFiber (discreteProjection P) x' f)
    (Functor.IsPreFibered.pullbackMap x'.2 f)
    (Functor.IsPreFibered.pullbackMap.IsCartesian x'.2 f).toIsHomLift

/-- An object `x` of the fibre over `V` is the chosen pullback, up to isomorphism, of an object
over `U` if and only if the element of `P(V)` it names is the restriction along `f` of an element
of `P(U)`. -/
theorem nonempty_iso_pullbackFunctor_obj_iff {V U : C} (f : V ⟶ U)
    (x : (discreteProjection P).Fiber V) :
    (∃ x' : (discreteProjection P).Fiber U,
        Nonempty (((discreteProjection P).chosenPullbacks.pullbackFunctor f).obj x' ≅ x)) ↔
      ∃ s' : P.obj (op U), P.map f.op s' = discreteFiberEquiv P V x := by
  constructor
  · rintro ⟨x', ⟨e⟩⟩
    exact ⟨_, (discreteFiberEquiv_pullbackFunctor_obj P f x').symm.trans
      (discreteFiberEquiv_eq_of_iso P e)⟩
  · rintro ⟨s', hs⟩
    refine ⟨(discreteFiberEquiv P U).symm s', ⟨eqToIso <| (discreteFiberEquiv P V).injective ?_⟩⟩
    rw [discreteFiberEquiv_pullbackFunctor_obj P f, Equiv.apply_symm_apply, hs]

end CategoryTheory.PresheafOfCategories

end
