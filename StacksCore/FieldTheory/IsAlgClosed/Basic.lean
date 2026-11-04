module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Algebraically closed  -/

@[expose] public section

universe u

open Polynomial AdjoinRoot

add_to_stacks 09GQ "Universe polymorphic version" IsAlgClosed.algebraMap_bijective_of_isIntegral
add_to_stacks 09GR "(4) ⇒ (1), Universe polymorphic version"
  IsAlgClosed.algebraMap_bijective_of_isIntegral
add_to_stacks 09GY isCoprime_iff_aeval_ne_zero_of_isAlgClosed

/-- **Stacks 09GQ** (equivalence between Stacks' definition and mathlib's), **Stacks 09GR**
(condition (4) ⇔ (1)).
A field `K` is algebraically closed iff for every algebraic field extension `L/K` the
structure map `K → L` is surjective, i.e. `K` has no proper algebraic extension. -/
@[stacks 09GQ "Equivalence between Stacks' definition and mathlib's",
  stacks 09GR "(4) ⇔ (1)"]
theorem isAlgClosed_iff_forall_algebraMap_surjective (K : Type u) [Field K] :
    IsAlgClosed K ↔ ∀ (L : Type u) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L],
      (⇑(algebraMap K L)).Surjective := by
  refine ⟨fun _ _ _ ↦ IsAlgClosed.algebraMap_bijective_of_isIntegral.surjective, fun h ↦
    .of_exists_root _ fun p hpm hpi ↦ ?_⟩
  have _ := Fact.mk hpi
  have _ := hpm.finite_adjoinRoot
  obtain ⟨x, hx⟩ := h (AdjoinRoot p) (.root _)
  refine ⟨x, (algebraMap K (AdjoinRoot p)).injective ?_⟩
  rw [map_zero, ← aeval_algebraMap_apply_eq_algebraMap_eval, hx, aeval_eq, mk_self]

/-- **Stacks 09GR**.
For a field `K`, the following are equivalent:
(1) every algebraic field extension `L/K` has surjective structure map `K → L`;
(2) every irreducible polynomial in `K[X]` has degree `1`;
(3) every nonconstant polynomial in `K[X]` has a root in `K`;
(4) `K` is algebraically closed. -/
@[stacks 09GR]
theorem IsAlgClosed.tfae (K : Type u) [Field K] :
    [∀ (L : Type u) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L],
      (⇑(algebraMap K L)).Surjective,
    ∀ p : K[X], Irreducible p → p.degree = 1,
    ∀ p : K[X], p.degree ≠ 0 → ∃ (x : K), p.IsRoot x,
    IsAlgClosed K].TFAE := by
  tfae_have 4 ↔ 1 := isAlgClosed_iff_forall_algebraMap_surjective K
  tfae_have 4 → 2 := fun _ _ ↦ IsAlgClosed.degree_eq_one_of_irreducible K
  tfae_have 3 → 4 := fun h ↦ IsAlgClosed.of_exists_root K fun p hpm hpi ↦ h p fun hp0 ↦ by
    simp [hpm.degree_le_zero_iff_eq_one.mp (by rw [hp0])] at hpi
  tfae_have 2 → 3 := fun h p hp ↦ by
    obtain ⟨f, hfm, hfi, hfp⟩ := exists_monic_irreducible_factor p <| by
      simpa [isUnit_iff_degree_eq_zero]
    obtain ⟨x, hfx⟩ := exists_root_of_degree_eq_one (h _ hfi)
    exact ⟨x, hfx.dvd hfp⟩
  tfae_finish
