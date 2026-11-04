module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Duals of a pure short exact sequence

Let `C` be an abelian monoidal category in which tensoring on the left is right exact, and let
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence whose three terms have right duals. If the
sequence stays a monomorphism on the left after tensoring on the right with any object, that is
`f ▷ T : X₁ ⊗ T ⟶ X₂ ⊗ T` is a monomorphism for every `T`, then the sequence of right duals and
right adjoint mates

  `0 ⟶ X₃ᘁ ⟶ X₂ᘁ ⟶ X₁ᘁ ⟶ 0`

is short exact. For sheaves of modules the hypothesis holds when `X₃` is flat (Stacks 03EX), so
this is the exactness of the dual of a short exact sequence of finite locally free modules.

The proof reads morphisms out of `Xᘁ`, resp. into `Xᘁ`, through the duality: `g : Xᘁ ⟶ T`
corresponds to `η ≫ X ◁ g : 𝟙 ⟶ X ⊗ T`, and `φ : T ⟶ Xᘁ` to `φ ▷ X ≫ ε : T ⊗ X ⟶ 𝟙`; under
these bijections precomposition with a mate `fᘁ` becomes postcomposition with `f ▷ T`, resp.
precomposition with `T ◁ f`. The epimorphy of `X₂ᘁ ⟶ X₁ᘁ` is then the monomorphy of `f ▷ T`,
and the left exactness is the right exactness of `T ⊗ -`.

## Main definitions

* `CategoryTheory.ShortComplex.rightDual`: the short complex of right duals and right adjoint
  mates of a short complex whose terms have right duals.

## Main results

* `CategoryTheory.coevaluation_comp_whiskerLeft_comp_whiskerRight` and
  `CategoryTheory.whiskerRight_rightAdjointMate_comp_evaluation`: the two compatibilities of the
  duality bijections with mates.
* `CategoryTheory.coevaluation_comp_whiskerLeft_injective`,
  `CategoryTheory.whiskerRight_comp_evaluation_injective` and
  `CategoryTheory.whiskerRight_tensorRightHomEquiv_comp_evaluation`: the bijectivity of the
  duality bijections, in the form used here.
* `CategoryTheory.ShortComplex.ShortExact.rightDual`: **the dual of a short exact sequence which
  stays left exact after tensoring is short exact.**

## References

* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
-/

@[expose] public noncomputable section

namespace CategoryTheory

open MonoidalCategory Limits

variable {C : Type*} [Category C] [MonoidalCategory C]

/-! ### The duality bijections and mates -/

/-- The duality bijection `(X' ⊗ 𝟙 ⟶ T) ≃ (𝟙 ⟶ X ⊗ T)` of an exact pairing, evaluated on a
morphism out of `X'`. -/
theorem tensorLeftHomEquiv_unit_apply {X X' T : C} [ExactPairing X X'] (g : X' ⟶ T) :
    tensorLeftHomEquiv (𝟙_ C) X X' T ((ρ_ X').hom ≫ g) = η_ X X' ≫ X ◁ g := by
  simp only [tensorLeftHomEquiv, Equiv.coe_fn_mk, MonoidalCategory.whiskerLeft_comp]
  rw [unitors_inv_equal, ← rightUnitor_inv_naturality_assoc, rightUnitor_tensor_inv]
  simp

/-- Under the duality bijection `(Xᘁ ⟶ T) ≃ (𝟙 ⟶ X ⊗ T)`, precomposition with the mate `fᘁ` is
postcomposition with `f ▷ T`. -/
theorem coevaluation_comp_whiskerLeft_comp_whiskerRight {X Y T : C} [HasRightDual X]
    [HasRightDual Y] (f : X ⟶ Y) (g : Xᘁ ⟶ T) :
    (η_ X Xᘁ ≫ X ◁ g) ≫ f ▷ T = η_ Y Yᘁ ≫ Y ◁ (fᘁ ≫ g) := by
  rw [Category.assoc, whisker_exchange, ← Category.assoc, ← coevaluation_comp_rightAdjointMate,
    Category.assoc, MonoidalCategory.whiskerLeft_comp]

/-- The duality bijection `(Xᘁ ⟶ T) ≃ (𝟙 ⟶ X ⊗ T)` is injective. -/
theorem coevaluation_comp_whiskerLeft_injective {X T : C} [HasRightDual X] {g g' : Xᘁ ⟶ T}
    (h : η_ X Xᘁ ≫ X ◁ g = η_ X Xᘁ ≫ X ◁ g') : g = g' := by
  rw [← tensorLeftHomEquiv_unit_apply, ← tensorLeftHomEquiv_unit_apply] at h
  simpa using (tensorLeftHomEquiv (𝟙_ C) X Xᘁ T).injective h

/-- Under the duality bijection `(T ⟶ Xᘁ) ≃ (T ⊗ X ⟶ 𝟙)`, postcomposition with the mate `fᘁ` is
precomposition with `T ◁ f`. -/
theorem whiskerRight_rightAdjointMate_comp_evaluation {X Y T : C} [HasRightDual X]
    [HasRightDual Y] (f : X ⟶ Y) (φ : T ⟶ Yᘁ) :
    (φ ≫ fᘁ) ▷ X ≫ ε_ X Xᘁ = T ◁ f ≫ φ ▷ Y ≫ ε_ Y Yᘁ := by
  rw [comp_whiskerRight, Category.assoc, rightAdjointMate_comp_evaluation, ← Category.assoc,
    ← whisker_exchange, Category.assoc]

/-- The duality bijection `(T ⟶ Xᘁ) ≃ (T ⊗ X ⟶ 𝟙)` is injective. -/
theorem whiskerRight_comp_evaluation_injective {X T : C} [HasRightDual X] {φ φ' : T ⟶ Xᘁ}
    (h : φ ▷ X ≫ ε_ X Xᘁ = φ' ▷ X ≫ ε_ X Xᘁ) : φ = φ' := by
  have h' := congrArg (tensorRightHomEquiv T X Xᘁ (𝟙_ C)) h
  rw [tensorRightHomEquiv_whiskerRight_comp_evaluation,
    tensorRightHomEquiv_whiskerRight_comp_evaluation] at h'
  simpa using h'

/-- The duality bijection `(T ⟶ Xᘁ) ≃ (T ⊗ X ⟶ 𝟙)` is surjective: its inverse is read off
`tensorRightHomEquiv`. -/
theorem whiskerRight_tensorRightHomEquiv_comp_evaluation {X T : C} [HasRightDual X]
    (χ : T ⊗ X ⟶ 𝟙_ C) :
    (tensorRightHomEquiv T X Xᘁ (𝟙_ C) χ ≫ (λ_ _).hom) ▷ X ≫ ε_ X Xᘁ = χ := by
  apply (tensorRightHomEquiv T X Xᘁ (𝟙_ C)).injective
  rw [tensorRightHomEquiv_whiskerRight_comp_evaluation]
  simp

/-! ### The dual of a short complex -/

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

/-- The short complex `X₃ᘁ ⟶ X₂ᘁ ⟶ X₁ᘁ` of right duals and right adjoint mates of a short complex
`X₁ ⟶ X₂ ⟶ X₃` whose terms have right duals. -/
abbrev ShortComplex.rightDual (S : ShortComplex C) [HasRightDual S.X₁] [HasRightDual S.X₂]
    [HasRightDual S.X₃] : ShortComplex C :=
  ShortComplex.mk (rightAdjointMate S.g) (rightAdjointMate S.f)
    (by rw [← comp_rightAdjointMate, S.zero]; simp [rightAdjointMate])

end Preadditive

section Abelian

variable [Abelian C] [MonoidalPreadditive C] [∀ T : C, PreservesFiniteColimits (tensorLeft T)]

/-- **The dual of a pure short exact sequence is short exact.** Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be
short exact, with right duals of its three terms, and such that `f ▷ T` is a monomorphism for
every object `T`. Then `0 ⟶ X₃ᘁ ⟶ X₂ᘁ ⟶ X₁ᘁ ⟶ 0` is short exact. -/
theorem ShortComplex.ShortExact.rightDual {S : ShortComplex C} (hS : S.ShortExact)
    [HasRightDual S.X₁] [HasRightDual S.X₂] [HasRightDual S.X₃]
    (hpure : ∀ T : C, Mono (S.f ▷ T)) : S.rightDual.ShortExact := by
  have hT : ∀ T : C, (S.map (tensorLeft T)).Exact ∧ Epi ((tensorLeft T).map S.g) := fun T =>
    (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi (tensorLeft T)).1
      inferInstance S hS
  have hmono : Mono (rightAdjointMate S.g) := by
    refine ⟨fun {T} φ φ' h => ?_⟩
    have hepi : Epi (T ◁ S.g) := (hT T).2
    apply whiskerRight_comp_evaluation_injective
    rw [← cancel_epi (T ◁ S.g), ← whiskerRight_rightAdjointMate_comp_evaluation,
      ← whiskerRight_rightAdjointMate_comp_evaluation, h]
  have hepi : Epi (rightAdjointMate S.f) := by
    refine ⟨fun {T} g g' h => ?_⟩
    have := hpure T
    apply coevaluation_comp_whiskerLeft_injective
    rw [← cancel_mono (S.f ▷ T), coevaluation_comp_whiskerLeft_comp_whiskerRight,
      coevaluation_comp_whiskerLeft_comp_whiskerRight, h]
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  have : Mono S.rightDual.f := hmono
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ fun {T} φ hφ => ?_)
  have hex := (hT T).1
  have hepiT : Epi (S.map (tensorLeft T)).g := (hT T).2
  have hzero : (S.map (tensorLeft T)).f ≫ (φ ▷ S.X₂ ≫ ε_ S.X₂ S.X₂ᘁ) = 0 := by
    show T ◁ S.f ≫ _ = 0
    rw [← whiskerRight_rightAdjointMate_comp_evaluation]
    show (φ ≫ S.rightDual.g) ▷ _ ≫ _ = 0
    rw [hφ, MonoidalPreadditive.zero_whiskerRight, zero_comp]
  let χ := hex.gIsCokernel.desc (CokernelCofork.ofπ _ hzero)
  refine ⟨tensorRightHomEquiv T S.X₃ S.X₃ᘁ (𝟙_ C) χ ≫ (λ_ _).hom, ?_⟩
  apply whiskerRight_comp_evaluation_injective
  show (_ ≫ rightAdjointMate S.g) ▷ S.X₂ ≫ _ = _
  rw [whiskerRight_rightAdjointMate_comp_evaluation,
    whiskerRight_tensorRightHomEquiv_comp_evaluation]
  exact hex.gIsCokernel.fac (CokernelCofork.ofπ _ hzero) WalkingParallelPair.one

end Abelian

end CategoryTheory
