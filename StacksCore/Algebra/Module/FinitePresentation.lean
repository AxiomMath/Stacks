module

public import Mathlib.Algebra.Module.FinitePresentation
import StacksCore.Tactic.StacksAttribute

/-! # Finitely presented modules -/

@[expose] public section

add_to_stacks 0518 "part 2"  Module.FinitePresentation
add_to_stacks 0583 "part 1"
  instIsLocalizedModuleLinearMapIdLocalizationLocalizedModuleMapOfFinitePresentation
add_to_stacks 0583 "part 1" Module.FinitePresentation.isLocalizedModule_mapExtendScalars
add_to_stacks 0583 "part 2" Module.FinitePresentation.isLocalizedModule_map

variable {R M1 M2 M3 : Type*} [Ring R] [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup M3]
  [Module R M1] [Module R M2] [Module R M3] (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3)
  (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)

/-- `M1` is isomorphic to the kernel of `g` when `f` is injective and `f, g` are exact. -/
private noncomputable def kerEquivOfExact : M1 ≃ₗ[R] LinearMap.ker g :=
  (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.1 hfg).symm)

include hfg hf hg in
@[stacks 0519 "2"]
lemma Module.FinitePresentation.of_exact_fst [Module.FinitePresentation R M1]
    [Module.FinitePresentation R M3] :
    Module.FinitePresentation R M2 := by
  have : Module.FinitePresentation R (LinearMap.ker g) := .of_equiv (kerEquivOfExact f g hfg hf)
  exact Module.finitePresentation_of_ker g hg

include hfg hg in
@[stacks 0519 "4"]
lemma Module.FinitePresentation.of_exact_third [Module.Finite R M1]
    [Module.FinitePresentation R M2] :
    Module.FinitePresentation R M3 := by
  refine Module.finitePresentation_of_surjective g hg ?_
  rw [LinearMap.exact_iff.1 hfg, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map f

include hfg hf hg in
@[stacks 0519 "5"]
lemma Module.Finite.of_exact_left [Module.Finite R M2]
    [Module.FinitePresentation R M3] :
    Module.Finite R M1 := by
  have : Module.Finite R (LinearMap.ker g) := .of_fg (Module.FinitePresentation.fg_ker g hg)
  exact Module.Finite.equiv (kerEquivOfExact f g hfg hf).symm
