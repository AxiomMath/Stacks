module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
## Composition of quotient map and submodule inclusion
-/

@[expose] public section

/-- A set spans the quotient `M ⧸ N` exactly when it spans `M` together with `N`.

`Submodule.map_mkQ_eq_top` says this for a submodule; this is the span-level form, and it is what
turns a statement about generators of a quotient into one about a `⊔` that Nakayama can eat. -/
theorem Submodule.span_image_mkQ_eq_top_iff {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (t : Set M) :
    Submodule.span R (N.mkQ '' t) = ⊤ ↔ N ⊔ Submodule.span R t = ⊤ := by
  rw [← Submodule.map_span, Submodule.map_mkQ_eq_top]

@[simp]
lemma Submodule.subtype_mkQ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) : (Submodule.mkQ p) ∘ₗ p.subtype = 0 := by
  ext; simp only [LinearMap.coe_comp, coe_subtype, Function.comp_apply, mkQ_apply,
    LinearMap.zero_apply, Quotient.mk_eq_zero, SetLike.coe_mem]
