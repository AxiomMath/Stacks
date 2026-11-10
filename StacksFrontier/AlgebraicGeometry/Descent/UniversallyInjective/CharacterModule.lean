module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.CharacterModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTensorShortExact
public import StacksFrontier.Algebra.Module.CharacterModule.Duality
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Universal injectivity and the character-module dual

Taking characters with values in `ℚ / ℤ` is an exact contravariant operation on modules which
also detects injective and surjective linear maps. A linear map of modules over a commutative
ring is universally injective if and only if its map on character modules is a split
surjection, and the resulting splittings can be chosen functorially in the tensor factor.

## Main definitions

* `functorialCharacterModuleSection` is the section obtained from a chosen section by
  postcomposition under the tensor--hom adjunction.

## Main results

* The exactness clause of 08WR is `CharacterModule.dual_exact`, proved in
  `StacksFrontier.Algebra.Module.CharacterModule.Duality`; this module tags it rather than
  restating it.
* `universallyInjective_iff_dual_splitSurjective` characterizes universal injectivity by a
  linear section of the character-module dual.
* `exists_functorialCharacterModuleSplitting` constructs a single such family and records both
  its splitting and naturality equations.

## Implementation notes

All three clauses of 08WR are existing results registered directly rather than restated:
exactness is `CharacterModule.dual_exact`, stated for composable linear maps using
`Function.Exact`, and the reflection assertions for injections and surjections are Mathlib
results. The phrase "split surjection" is expressed by the existence of a linear section whose
composite with the dual map is the identity, so the statement retains the splitting data rather
than merely asserting surjectivity. The character
module `C(M)` is `CharacterModule M` and the map `C(1_P ⊗ f)` is
`CharacterModule.dual (LinearMap.lTensor P f)`; conjugating postcomposition by a chosen
section through `CharacterModule.homEquiv` gives the functorial family, whose naturality is
expressed against the maps induced by `h ⊗ 1`.

## References

* [Stacks Project, Tag 08WR](https://stacks.math.columbia.edu/tag/08WR)
* [Stacks Project, Tag 08WU](https://stacks.math.columbia.edu/tag/08WU)
* [Stacks Project, Tag 08WV](https://stacks.math.columbia.edu/tag/08WV)
-/

@[expose] public section

open scoped TensorProduct

universe u v

section Exactness

add_to_stacks 08WR "exactness" CharacterModule.dual_exact

add_to_stacks 08WR "reflection of injections"
  CharacterModule.dual_surjective_iff_injective

add_to_stacks 08WR "reflection of surjections"
  CharacterModule.dual_injective_iff_surjective

end Exactness

section SplitSurjective

private theorem dual_lTensor_homEquiv
    {R : Type*} [CommRing R]
    {F'' F' G : Type*} [AddCommGroup F''] [AddCommGroup F'] [AddCommGroup G]
    [Module R F''] [Module R F'] [Module R G]
    (a : F'' →ₗ[R] F') (η : G →ₗ[R] CharacterModule F') :
    CharacterModule.dual (LinearMap.lTensor G a) (CharacterModule.homEquiv η) =
      CharacterModule.homEquiv (CharacterModule.dual a ∘ₗ η) := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul g m => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- A module map is universally injective exactly when its character-module dual admits a
linear section. -/
@[stacks 08WU]
theorem universallyInjective_iff_dual_splitSurjective
    {R : Type u} [CommRing R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) :
    UniversallyInjective f ↔
      ∃ s : CharacterModule M →ₗ[R] CharacterModule N,
        (CharacterModule.dual f).comp s = LinearMap.id := by
  refine ⟨fun hf => ?_, fun ⟨s, hs⟩ Q _ _ => ?_⟩
  · obtain ⟨χ, hχ⟩ := CharacterModule.dual_surjective_of_injective _
      ((LinearMap.lTensor_inj_iff_rTensor_inj _ f).mpr (hf _))
      (CharacterModule.homEquiv (LinearMap.id : CharacterModule M →ₗ[R] CharacterModule M))
    refine ⟨CharacterModule.homEquiv.symm χ, CharacterModule.homEquiv.injective ?_⟩
    rwa [← dual_lTensor_homEquiv, LinearEquiv.apply_symm_apply]
  · rw [← LinearMap.lTensor_inj_iff_rTensor_inj, ← CharacterModule.dual_surjective_iff_injective]
    exact dual_lTensor_surjective_of_postcomp f Q fun ξ =>
      ⟨s ∘ₗ ξ, by rw [← LinearMap.comp_assoc, hs, LinearMap.id_comp]⟩

end SplitSurjective

section Functorial

/-- The section on character modules of tensor products induced by postcomposition with `g`
under the tensor--hom adjunction. -/
noncomputable def functorialCharacterModuleSection
    {R : Type u} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : CharacterModule M →ₗ[R] CharacterModule N)
    (P : Type*) [AddCommGroup P] [Module R P] :
    CharacterModule (P ⊗[R] M) →ₗ[R] CharacterModule (P ⊗[R] N) :=
  (CharacterModule.homEquiv (R := R) (A := P) (B := N)).toLinearMap ∘ₗ
    (g.compRight R) ∘ₗ
    (CharacterModule.homEquiv (R := R) (A := P) (B := M)).symm.toLinearMap

/-- A universally injective map admits a section after applying the character
module functor, and the section obtained on `C(P ⊗ -)` by postcomposition is a splitting
functorial in the module `P`. -/
@[stacks 08WV]
theorem exists_functorialCharacterModuleSplitting
    {R : Type u} [CommRing R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : UniversallyInjective f) :
    ∃ g : CharacterModule M →ₗ[R] CharacterModule N,
      CharacterModule.dual f ∘ₗ g = LinearMap.id ∧
      (∀ (P : Type v) [AddCommGroup P] [Module R P],
        CharacterModule.dual (LinearMap.lTensor P f) ∘ₗ
            functorialCharacterModuleSection g P =
          LinearMap.id) ∧
      ∀ (P Q : Type v) [AddCommGroup P] [Module R P]
        [AddCommGroup Q] [Module R Q] (h : P →ₗ[R] Q),
        functorialCharacterModuleSection g P ∘ₗ
            CharacterModule.dual (LinearMap.rTensor M h) =
          CharacterModule.dual (LinearMap.rTensor N h) ∘ₗ
            functorialCharacterModuleSection g Q := by
  obtain ⟨g, hg⟩ := (universallyInjective_iff_dual_splitSurjective f).mp hf
  refine ⟨g, hg, ?_, ?_⟩
  · intro P _ _; ext x y; induction y using TensorProduct.inductionOn with
    | tmul p m =>
      exact congrArg (fun k : CharacterModule M →ₗ[R] CharacterModule M =>
        k (CharacterModule.curry x p) m) hg
    | add y y' hy hy' => rw [map_add, map_add, hy, hy']
  · intro P Q _ _ _ _ h; ext x y; induction y using TensorProduct.inductionOn with
    | tmul p n => rfl
    | add y y' hy hy' => rw [map_add, map_add, hy, hy']

end Functorial
