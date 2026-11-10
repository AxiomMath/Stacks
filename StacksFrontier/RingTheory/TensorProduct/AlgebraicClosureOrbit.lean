module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.FieldTheory.Normal.AlgClosed

/-!
# The automorphisms of an algebraic closure act transitively on the primes of a base change

Let `k` be a field, `κ/k` an arbitrary field extension and `K/k` an algebraic closure.  The
group `Aut_k(K)` acts on `κ ⊗[k] K` through the second factor, and this file proves that it
acts transitively on the prime ideals.

No separability is assumed of either extension.  That matters: over an imperfect field the
extension `K/k` is not separable, so `Aut_k(K)` does *not* have `k` as its fixed field — the
purely inseparable elements of `K` are fixed by every `k`-automorphism — and therefore
`Algebra.IsInvariant κ (κ ⊗[k] K) (K ≃ₐ[k] K)` is **false**.  The transitivity statement is
nevertheless true, and the proof below does not go through a fixed-field argument.

## Main results

* `Stacks.AlgClosureOrbit.exists_algEquiv_comp_eq` — any two `k`-algebra maps out of an
  algebraic closure of `k` into an algebraically closed field differ by a `k`-automorphism of
  the closure.
* `Stacks.AlgClosureOrbit.exists_algHom_eq_zero_iff` — every prime of `κ ⊗[k] K` is the zero
  set of a `κ`-algebra map into an algebraic closure of `κ`.
* `Stacks.AlgClosureOrbit.exists_algEquiv_comap_eq` — the transitivity statement.

## Implementation notes

The argument is the classical one.  A prime `P` of `κ ⊗[k] K` has quotient integral over the
field `κ`, hence a field, so `P` is the kernel of a `κ`-algebra map `α` into a fixed algebraic
closure `Ω` of `κ`.  Restricting `α` along `Algebra.TensorProduct.includeRight` leaves a
`k`-algebra map `K → Ω`, and two such differ by a `k`-automorphism `σ` of `K` because the image
of an algebraic closure of `k` in `Ω` is independent of the embedding.  Transporting `α` by
`σ` on the second factor then produces the map whose kernel is the second prime.

The statement of the main result is written with `Ideal.comap` along the ring homomorphism
underlying `Algebra.TensorProduct.congr (AlgEquiv.refl) σ`, which is the spelling the
geometric consumers use.

## References

* [Stacks Project, Tag 04KP](https://stacks.math.columbia.edu/tag/04KP)
* [Stacks Project, Tag 0C4Y](https://stacks.math.columbia.edu/tag/0C4Y)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.AlgClosureOrbit

/-- **Any two `k`-algebra maps out of an algebraic closure of `k` into an algebraically closed
field differ by a `k`-automorphism of the closure.**  The image of such a map is the relative
algebraic closure of `k` in the target, hence independent of the map, and the two maps then
differ by the induced automorphism. -/
theorem exists_algEquiv_comp_eq
    (k K Ω : Type*) [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
    [IsAlgClosure k K] [IsAlgClosed Ω] (φ ψ : K →ₐ[k] Ω) :
    ∃ σ : K ≃ₐ[k] K, φ.comp σ.toAlgHom = ψ := by
  have halg : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  have hrange : ψ.range = φ.range := by
    rw [← AlgHom.fieldRange_toSubalgebra, ← AlgHom.fieldRange_toSubalgebra,
      (normal_iff_forall_fieldRange_eq k K Ω).mp inferInstance ψ φ]
  refine ⟨(AlgEquiv.ofInjectiveField ψ).trans
    ((Subalgebra.equivOfEq _ _ hrange).trans (AlgEquiv.ofInjectiveField φ).symm), ?_⟩
  ext b
  change φ ((AlgEquiv.ofInjectiveField φ).symm
    ((Subalgebra.equivOfEq _ _ hrange) (AlgEquiv.ofInjectiveField ψ b))) = ψ b
  have key : ∀ y : φ.range, φ ((AlgEquiv.ofInjectiveField φ).symm y) = (y : Ω) :=
    fun y => congrArg Subtype.val ((AlgEquiv.ofInjectiveField φ).apply_symm_apply y)
  rw [key]
  rfl

variable (k κ K : Type u) [Field k] [Field κ] [Field K] [Algebra k κ] [Algebra k K]

/-- A `κ`-algebra map out of `κ ⊗[k] K` is determined on `c ⊗ₜ d` by its restriction along
`Algebra.TensorProduct.includeRight`. -/
theorem apply_tmul {Ω : Type u} [CommRing Ω] [Algebra k Ω] [Algebra κ Ω]
    [IsScalarTower k κ Ω] (γ : (κ ⊗[k] K) →ₐ[κ] Ω) (c : κ) (d : K) :
    γ (c ⊗ₜ[k] d) = algebraMap κ Ω c *
      ((γ.restrictScalars k).comp Algebra.TensorProduct.includeRight) d := by
  rw [show (c ⊗ₜ[k] d : κ ⊗[k] K) =
        algebraMap κ (κ ⊗[k] K) c * Algebra.TensorProduct.includeRight d by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul],
    map_mul, AlgHom.commutes]
  rfl

/-- **A prime of `κ ⊗[k] K` is the set of elements killed by a `κ`-algebra map into an
algebraically closed field**, when `K` is algebraic over `k`.  The quotient by the prime is a
domain integral over the field `κ`, hence a field, and an algebraic closure of `κ` receives
it. -/
theorem exists_algHom_eq_zero_iff [Algebra.IsAlgebraic k K]
    (Ω : Type u) [Field Ω] [Algebra κ Ω] [IsAlgClosed Ω]
    (P : Ideal (κ ⊗[k] K)) [P.IsPrime] :
    ∃ α : (κ ⊗[k] K) →ₐ[κ] Ω, ∀ x, α x = 0 ↔ x ∈ P := by
  have hint : Algebra.IsIntegral κ (κ ⊗[k] K) := Algebra.IsIntegral.tensorProduct k κ K
  have hintq : Algebra.IsIntegral κ ((κ ⊗[k] K) ⧸ P) :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ κ P) Ideal.Quotient.mk_surjective
  have halgq : Algebra.IsAlgebraic κ ((κ ⊗[k] K) ⧸ P) := Algebra.IsIntegral.isAlgebraic
  have hfield : IsField ((κ ⊗[k] K) ⧸ P) := isField_of_isIntegral_of_isField' (Field.toIsField κ)
  let L : ((κ ⊗[k] K) ⧸ P) →ₐ[κ] Ω := IsAlgClosed.lift
  let _ : Field ((κ ⊗[k] K) ⧸ P) := hfield.toField
  refine ⟨L.comp (Ideal.Quotient.mkₐ κ P), fun x => ?_⟩
  change L (Ideal.Quotient.mk P x) = 0 ↔ x ∈ P
  rw [map_eq_zero_iff L (L : ((κ ⊗[k] K) ⧸ P) →+* Ω).injective]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- **The automorphisms of an algebraic closure act transitively on the primes of the base
change of a field extension along it.**  No separability is assumed: the statement holds for an
arbitrary field extension `κ/k` and the full algebraic closure `K` of `k`, where the
fixed-field argument available for a Galois extension is unavailable. -/
theorem exists_algEquiv_comap_eq [IsAlgClosure k K]
    (P Q : Ideal (κ ⊗[k] K)) [P.IsPrime] [Q.IsPrime] :
    ∃ σ : K ≃ₐ[k] K,
      Ideal.comap (Algebra.TensorProduct.congr (AlgEquiv.refl (R := κ) (A₁ := κ))
        σ).toRingEquiv.toRingHom P = Q := by
  have halg : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  obtain ⟨α, hα⟩ := exists_algHom_eq_zero_iff k κ K (AlgebraicClosure κ) P
  obtain ⟨β, hβ⟩ := exists_algHom_eq_zero_iff k κ K (AlgebraicClosure κ) Q
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comp_eq k K (AlgebraicClosure κ)
    ((α.restrictScalars k).comp Algebra.TensorProduct.includeRight)
    ((β.restrictScalars k).comp Algebra.TensorProduct.includeRight)
  refine ⟨σ, ?_⟩
  have hpt : ∀ x, α ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := κ) (A₁ := κ)) σ) x)
      = β x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      rw [show (Algebra.TensorProduct.congr (AlgEquiv.refl (R := κ) (A₁ := κ)) σ)
            (a ⊗ₜ[k] b) = a ⊗ₜ[k] σ b by simp,
        apply_tmul k κ K α a (σ b), apply_tmul k κ K β a b]
      congr 1
      exact AlgHom.congr_fun hσ b
    | add x y hx hy => simp only [map_add, hx, hy]
  ext x
  rw [Ideal.mem_comap, ← hα, ← hβ]
  change α ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := κ) (A₁ := κ)) σ) x) = 0 ↔ _
  rw [hpt]

end Stacks.AlgClosureOrbit

end
