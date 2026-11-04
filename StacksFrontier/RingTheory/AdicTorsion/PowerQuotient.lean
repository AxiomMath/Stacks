module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.LinearCombination

/-!
# The torsion of a quotient by a power of a nonzerodivisor

Let `R` be a commutative ring and `t ∈ R` a nonzerodivisor. In `R / (tᵏ⁺¹)` an element killed by
`t` is `tᵏ` times an element, and the same holds coordinatewise in a finite free
`R / (tᵏ⁺¹)`-module. These two statements are the torsion computation behind the short exact
sequences `0 → Fₙ → Fₙ₊₁ → F₁ → 0` of a coherent adic system along a principal ideal, and behind
the freeness of a finite module whose quotients by the powers of a regular parameter are free.

## Main results

* `Stacks.AdicTorsion.exists_eq_pow_smul_of_smul_eq_zero` — in `R / (tᵏ⁺¹)` an element killed by
  `t` is `tᵏ` times an element.
* `Stacks.AdicTorsion.exists_eq_pow_smul_of_smul_eq_zero_of_linearEquiv` — the same for a module
  isomorphic to a finite power of `R / (tᵏ⁺¹)`.

## Implementation notes

The ideal is taken as a variable `J` together with the equation `J = Ideal.span {t ^ (k + 1)}`,
rather than as the span itself: the consumers meet it as the stalk of an ideal sheaf, which is
only *equal* to such a span.
-/

@[expose] public section

universe u

namespace Stacks.AdicTorsion

variable {R : Type u} [CommRing R]

/-- **In `R / (tᵏ⁺¹)` an element killed by the nonzerodivisor `t` is `tᵏ` times an element.**
Lift the element to `a ∈ R`; the hypothesis says `t a = b tᵏ⁺¹` for some `b`, and cancelling one
factor of `t` gives `a = tᵏ b`. -/
theorem exists_eq_pow_smul_of_smul_eq_zero {t : R} (ht : t ∈ nonZeroDivisors R) (k : ℕ)
    {J : Ideal R} (hJ : J = Ideal.span {t ^ (k + 1)}) {c : R ⧸ J} (hc : t • c = 0) :
    ∃ d : R ⧸ J, c = t ^ k • d := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  have hmk (s x : R) : (Submodule.Quotient.mk (s * x) : R ⧸ J) =
      s • (Submodule.Quotient.mk x : R ⧸ J) := rfl
  have hmem : t * a ∈ J := by
    refine (Submodule.Quotient.mk_eq_zero _).mp ?_
    rw [hmk]
    exact hc
  rw [hJ, Ideal.mem_span_singleton'] at hmem
  obtain ⟨b, hb⟩ := hmem
  refine ⟨Submodule.Quotient.mk b, ?_⟩
  have hzero : (a - t ^ k * b) * t = 0 := by linear_combination -hb
  have ha : a = t ^ k * b := sub_eq_zero.mp (ht.2 _ hzero)
  rw [ha, hmk]

/-- **The `t`-torsion of a finite free module over `R / (tᵏ⁺¹)`.** If `M` is isomorphic to
`(R / (tᵏ⁺¹))ʳ` and `t` is a nonzerodivisor of `R`, then an element of `M` killed by `t` is
`tᵏ` times an element: in coordinates this is
`Stacks.AdicTorsion.exists_eq_pow_smul_of_smul_eq_zero`. -/
theorem exists_eq_pow_smul_of_smul_eq_zero_of_linearEquiv {t : R} (ht : t ∈ nonZeroDivisors R)
    (k r : ℕ) {J : Ideal R} (hJ : J = Ideal.span {t ^ (k + 1)}) {M : Type*} [AddCommGroup M]
    [Module R M] (e : M ≃ₗ[R] (Fin r → R ⧸ J)) {m : M} (hm : t • m = 0) :
    ∃ y : M, m = t ^ k • y := by
  classical
  have hsmul : t • e m = 0 := by rw [← LinearEquiv.map_smul, hm, map_zero]
  have hzero : ∀ i : Fin r, t • e m i = 0 := fun i => congrFun hsmul i
  choose d hd using fun i : Fin r => exists_eq_pow_smul_of_smul_eq_zero ht k hJ (hzero i)
  refine ⟨e.symm d, ?_⟩
  calc m = e.symm (e m) := (e.symm_apply_apply m).symm
    _ = e.symm (t ^ k • d) := congrArg e.symm (funext hd)
    _ = t ^ k • e.symm d := map_smul _ _ _

end Stacks.AdicTorsion

end
