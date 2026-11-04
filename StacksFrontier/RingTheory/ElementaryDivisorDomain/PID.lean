module

public import Mathlib.Algebra.Module.PID
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.ElementaryDivisorDomain.Bezout

/-!
# Structure of finite modules over a principal ideal domain

Every finite module over a principal ideal domain is the direct sum of a finite-rank free module
and finitely many cyclic modules `R ⧸ (f)` with `f ≠ 0`. This is the classical structure theorem,
the special case of the Bézout-domain splitting in
`StacksFrontier.RingTheory.ElementaryDivisorDomain.Bezout` in which every ideal is principal.

## Main results

* `finite_equiv_free_prod_directSum_quotient_span_singleton`: the structure theorem for finite
  modules over a principal ideal domain.

## Implementation notes

A principal ideal domain is expressed by the `IsDomain` and `IsPrincipalIdealRing` classes. The
finite free summand is represented by finitely supported functions on `Fin r`, while the binary
direct sum is represented by the product of modules.

## References

* [Stacks, Tag 0ASV](https://stacks.math.columbia.edu/tag/0ASV)
-/

@[expose] public section

open scoped DirectSum

universe u v

/-- **Stacks 0ASV**.
Every finite module over a principal ideal domain is isomorphic to the direct sum of a
finite-rank free module and finitely many cyclic modules defined by nonzero elements. -/
@[stacks 0ASV]
theorem finite_equiv_free_prod_directSum_quotient_span_singleton
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (r n : ℕ) (f : Fin n → R),
      (∀ i, f i ≠ 0) ∧
        Nonempty (M ≃ₗ[R] (Fin r →₀ R) × ⨁ i : Fin n, R ⧸ Ideal.span {f i}) := by
  obtain ⟨r, I, inst, p, hp, e, ⟨h⟩⟩ := Module.equiv_free_prod_directSum R M
  let E := @Fintype.equivFin I inst
  refine ⟨r, Fintype.card I, fun i ↦ p (E.symm i) ^ e (E.symm i), ?_, ?_⟩
  · intro i
    exact pow_ne_zero _ (hp (E.symm i)).ne_zero
  · exact ⟨by
      simpa [E, Ideal.submodule_span_eq] using
        h.trans ((LinearEquiv.refl R (Fin r →₀ R)).prodCongr
          (DirectSum.lequivCongrLeft R E))⟩
