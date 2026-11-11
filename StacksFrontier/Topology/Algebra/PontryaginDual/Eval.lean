module

public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# The evaluation map into the double Pontryagin dual

For a locally compact topological monoid `A`, every `a : A` gives a continuous character
`χ ↦ χ a` of the Pontryagin dual `PontryaginDual A`, and `a ↦ (χ ↦ χ a)` is a continuous monoid
homomorphism `A →ₜ* PontryaginDual (PontryaginDual A)`. It is natural in `A`.

## Main definitions

* `Stacks.Pontryagin.eval`: the evaluation map `A →ₜ* PontryaginDual (PontryaginDual A)`.

## Main results

* `Stacks.Pontryagin.map_map_comp_eval`: the evaluation map is natural.
* `Stacks.Pontryagin.eval_injective_iff`: the evaluation map is injective exactly when the
  characters of `A` separate its points.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

namespace Stacks.Pontryagin

open PontryaginDual

/-- Evaluation at a point is continuous on the Pontryagin dual. -/
instance instContinuousEvalConst {A : Type*} [Monoid A] [TopologicalSpace A] :
    ContinuousEvalConst (PontryaginDual A) A Circle :=
  inferInstanceAs (ContinuousEvalConst (A →ₜ* Circle) A Circle)

/-- Evaluation is jointly continuous on the Pontryagin dual of a locally compact monoid. -/
instance instContinuousEval {A : Type*} [Monoid A] [TopologicalSpace A] [LocallyCompactSpace A] :
    ContinuousEval (PontryaginDual A) A Circle :=
  inferInstanceAs (ContinuousEval (A →ₜ* Circle) A Circle)

variable {A B : Type*} [Monoid A] [TopologicalSpace A] [LocallyCompactSpace A]
  [Monoid B] [TopologicalSpace B] [LocallyCompactSpace B]

variable (A) in
/-- The evaluation map `A →ₜ* PontryaginDual (PontryaginDual A)`, sending `a` to the character
`χ ↦ χ a` of the Pontryagin dual. -/
def eval : A →ₜ* PontryaginDual (PontryaginDual A) where
  toFun a :=
    { toFun χ := χ a
      map_one' := rfl
      map_mul' _ _ := rfl
      continuous_toFun := continuous_eval_const a }
  map_one' := PontryaginDual.ext fun χ ↦ _root_.map_one χ
  map_mul' a b := PontryaginDual.ext fun χ ↦ _root_.map_mul χ a b
  continuous_toFun := ContinuousMonoidHom.continuous_of_continuous_uncurry _ <|
    continuous_eval.comp continuous_swap

/-- The evaluation map sends `a` to the character `χ ↦ χ a`. -/
@[simp]
theorem eval_apply (a : A) (χ : PontryaginDual A) : eval A a χ = χ a :=
  rfl

/-- The evaluation map is natural: `map (map f) ∘ eval = eval ∘ f`. -/
theorem map_map_comp_eval (f : A →ₜ* B) :
    (map (map f)).comp (eval A) = (eval B).comp f :=
  rfl

/-- The evaluation map is injective exactly when the characters separate the points of `A`. -/
theorem eval_injective_iff :
    Function.Injective (eval A) ↔ ∀ a b : A, a ≠ b → ∃ χ : PontryaginDual A, χ a ≠ χ b := by
  refine ⟨fun h a b hab ↦ ?_, fun h a b hab ↦ ?_⟩
  · by_contra! H
    exact hab (h (PontryaginDual.ext H))
  · by_contra hne
    obtain ⟨χ, hχ⟩ := h a b hne
    exact hχ (congrArg (fun F : PontryaginDual (PontryaginDual A) ↦ F χ) hab)

end Stacks.Pontryagin
