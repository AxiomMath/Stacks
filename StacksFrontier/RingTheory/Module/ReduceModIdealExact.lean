module

public import Mathlib.Algebra.Exact
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Reduction modulo an ideal preserves exactness

If `f` and `g` are exact and `g` is surjective, their reductions modulo an ideal `I` are exact.
Surjectivity of `g` is what the proof needs: it makes an element of the middle term killed by `g`
modulo `I` differ from one in the image of `f` by an element of `I • ⊤`.
-/

@[expose] public section

namespace LinearMap

/-- The reductions of `f` and `g` modulo `I` are exact, for `f` and `g` exact with `g`
surjective. -/
theorem reduceModIdeal_exact {R : Type*} [CommRing R] {K L M : Type*} [AddCommGroup K]
    [Module R K] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M] (I : Ideal R)
    (f : K →ₗ[R] L) (g : L →ₗ[R] M) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (LinearMap.reduceModIdeal I f) (LinearMap.reduceModIdeal I g) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ : g y ∈ Submodule.map g (I • (⊤ : Submodule R L)) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]
        exact (Submodule.Quotient.mk_eq_zero _).mp hy
      obtain ⟨x, hx⟩ := (hfg (y - z)).mp (by rw [map_sub, hzy, sub_self])
      exact ⟨Submodule.Quotient.mk x,
        (Submodule.Quotient.eq _).mpr (by simpa [hx] using Submodule.neg_mem _ hz)⟩
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [← hx]
        show Submodule.Quotient.mk (g (f x)) = 0
        rw [hfg.apply_apply_eq_zero x, Submodule.Quotient.mk_zero]

end LinearMap
