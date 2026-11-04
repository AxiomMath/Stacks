module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Pushout of a short exact sequence

Pushing out the left-hand map in a short exact sequence of objects of an abelian category
produces another short exact sequence with the same cokernel.

## Main results

* `CategoryTheory.exists_shortExact_pushout` constructs the pushout short exact sequence.

## Implementation notes

The statement is given in an arbitrary abelian category. The `IsPushout` assertion records the
universal property of the middle object, while the compatibility with the map to the unchanged
right-hand object identifies the resulting short exact sequence canonically.

## References

* [Stacks Project, Tag 0G9U](https://stacks.math.columbia.edu/tag/0G9U)
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

/-- The pushout of the left-hand map in a short exact sequence is again a short exact sequence,
with the same right-hand object. -/
@[stacks 0G9U]
theorem exists_shortExact_pushout
    {C : Type u} [Category C] [Abelian C]
    {K P M K' : C} {i : K ⟶ P} {p : P ⟶ M}
    (hip : i ≫ p = 0) (h : (ShortComplex.mk i p hip).ShortExact) (a : K ⟶ K') :
    ∃ (E : C) (j : P ⟶ E) (i' : K' ⟶ E) (q : E ⟶ M)
      (hi'q : i' ≫ q = 0),
      IsPushout i a j i' ∧ j ≫ q = p ∧ (ShortComplex.mk i' q hi'q).ShortExact := by
  let E := pushout i a
  let j : P ⟶ E := pushout.inl i a
  let i' : K' ⟶ E := pushout.inr i a
  let q : E ⟶ M := pushout.desc p 0 (by simpa using hip)
  have hi'q : i' ≫ q = 0 := pushout.inr_desc _ _ _
  have hjq : j ≫ q = p := pushout.inl_desc _ _ _
  have := h.epi_g
  have : Epi q := epi_of_epi_fac hjq
  have hq : IsColimit (CokernelCofork.ofπ q hi'q) :=
    CokernelCofork.IsColimit.ofπ' q hi'q (fun {X} f hf ↦ by
      let d := CokernelCofork.IsColimit.desc' h.gIsCokernel (j ≫ f) (by
        rw [← Category.assoc, show i ≫ j = a ≫ i' from pushout.condition]
        simp [hf])
      refine ⟨d.1, pushout.hom_ext ?_ ?_⟩
      · rw [← Category.assoc, hjq]
        exact d.2
      · rw [← Category.assoc, hi'q, zero_comp, hf])
  have := h.mono_f
  exact ⟨E, j, i', q, hi'q, IsPushout.of_hasPushout i a, hjq,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hq)
      (by dsimp [i']; infer_instance) inferInstance⟩

end CategoryTheory
