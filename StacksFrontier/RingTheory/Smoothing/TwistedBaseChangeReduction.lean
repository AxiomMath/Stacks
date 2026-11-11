module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Smoothing.ResolutionReductions
public import StacksFrontier.RingTheory.Smoothing.StrictlyStandardParameterPowers

/-!
# Stacks 07G0: reducing to the base change of `C` to the twisted base

In the proof of Stacks 07FJ, steps (1)–(15) produce: generators `a_1, …, a_t` of `H_{A/k}`, the
algebra `B = A[x_1, …, x_d, z_{ij}]/(x_i^{2N} - Σ_j z_{ij} a_j)` with the enlargement `B → C` of
Stacks 07CE and its retraction `C → B`, the maps `B → Λ` and `C → Λ` of step (14), and the
twisted base `R = k[y_1, …, y_m, t_1, …, t_d]` with `R → Λ` and `k[x_1, …, x_d] → R`,
`x_i ↦ γ_i = π_i t_i` of step (15). Step (16), Stacks 07G0, says that it suffices to resolve
`R → C ⊗_{k[x_1, …, x_d]} R → Λ ⊃ q`.

## Main results

* `Stacks.Smoothing.canBeResolved_of_canBeResolved_twistedBase_tensorProduct`: Stacks 07G0.

## Implementation notes

The base change is handled as `R ⊗_{k[x_1, …, x_d]} C`, as in
`StacksFrontier.RingTheory.Smoothing.ResolutionReductions`. The proof is the one of Stacks: the
`a_j` map into `H_{B/k[x_1, …, x_d]}`
(`Stacks.Smoothing.forall_algebraMap_mem_singularIdeal_parameterPowerAlgebra`), hence into
`H_{C/k[x_1, …, x_d]}` and then into `H_{(R ⊗ C)/R}`, and `H_{T/R} ⊆ H_{T/k}` for every
solution `T`, as `R` is smooth over `k`.

## References

* [Stacks Project, Tag 07G0](https://stacks.math.columbia.edu/tag/07G0)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Smoothing

universe u w

/-- **Stacks 07G0.** Let `k` be a field, `A` a finite type `k`-algebra with
`H_{A/k} = (a_1, …, a_t)`, `A → Λ` a `k`-algebra map and `q ⊂ Λ`. Let
`B = A[x_1, …, x_d, z_{ij}]/(x_i^{2N} - Σ_j z_{ij} a_j)` and let `B → C` be as in Stacks 07CE
(07FP), with `k[x_1, …, x_d]`-algebra retraction `g : C → B`. Let `φ : k[y_1, …, y_m] → Λ`,
`π_1, …, π_d ∈ k[y_1, …, y_m]`, `δ_1, …, δ_d ∈ Λ` and `λ_{ij} ∈ Λ` with
`(π'_i)^{2N} = Σ_j a_j λ_{ij}` for `π'_i = δ_i π_i`; map `B → Λ` by `x_i ↦ π'_i`,
`z_{ij} ↦ λ_{ij}` and `C → Λ` through `g` (step (14)); let `R = k[y_1, …, y_m, t_1, …, t_d]`
map to `Λ` by `φ` and `t_i ↦ δ_i`, and `k[x_1, …, x_d] → R` by `x_i ↦ γ_i = π_i t_i` (step
(15)). Then it suffices to resolve `R → C ⊗_{k[x_1, …, x_d]} R → Λ ⊃ q`, where
`C ⊗_{k[x_1, …, x_d]} R → Λ` is induced by the two maps `C → Λ` and `R → Λ`.

The base change is written `R ⊗_{k[x_1, …, x_d]} C`, the same ring with its two factors swapped,
for which the `R`-algebra structure is Mathlib's canonical one. The structure maps
`k[x_1, …, x_d] → R`, `R → Λ` and `R ⊗_{k[x_1, …, x_d]} C → Λ` are arbitrary instances pinned
down by `hR`, `hRΛ` and `hTΛ` to the maps of steps (14)–(15). The further properties of the `π_i`
and `δ_i` chosen in steps (10)–(13) are not needed for this step. -/
@[stacks 07G0]
theorem canBeResolved_of_canBeResolved_twistedBase_tensorProduct {k : Type u} {A : Type u}
    {Λ : Type w} {C : Type u} [Field k] [CommRing A] [CommRing Λ] [CommRing C] [Algebra k A]
    [Algebra k Λ] [Algebra A Λ] [IsScalarTower k A Λ] [Algebra.FiniteType k A] {t d N m : ℕ}
    (a : Fin t → A) (ha : Ideal.span (Set.range a) = singularIdeal k A)
    [Algebra (MvPolynomial (Fin d) k) C] [Algebra (parameterPowerAlgebra A d N a) C]
    [IsScalarTower (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) C]
    [Algebra.FinitePresentation (MvPolynomial (Fin d) k) C]
    (g : C →ₐ[MvPolynomial (Fin d) k] parameterPowerAlgebra A d N a)
    (hg : g.comp (IsScalarTower.toAlgHom (MvPolynomial (Fin d) k)
        (parameterPowerAlgebra A d N a) C) =
      AlgHom.id (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a))
    (hC : ∀ b : parameterPowerAlgebra A d N a,
      RingHom.IsLocalCompleteIntersection
          (algebraMap (MvPolynomial (Fin d) k) (Localization.Away b)) →
      (letI : Algebra (Localization.Away b)
          (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b)) :=
        (Localization.awayMap (algebraMap (parameterPowerAlgebra A d N a) C) b).toAlgebra
      Algebra.Smooth (Localization.Away b)
        (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b))))
    (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (π : Fin d → MvPolynomial (Fin m) k) (δ : Fin d → Λ)
    (lam : Fin d → Fin t → Λ)
    (hrel : ∀ i, (δ i * φ (π i)) ^ (2 * N) = ∑ j, algebraMap A Λ (a j) * lam i j)
    [Algebra (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k)]
    (hR : algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) =
      (twistedBaseHom π).toRingHom)
    [Algebra (MvPolynomial (Fin m ⊕ Fin d) k) Λ]
    (hRΛ : algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ = (twistedBaseToTarget φ δ).toRingHom)
    [Algebra (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ]
    [IsScalarTower (MvPolynomial (Fin m ⊕ Fin d) k)
      (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ]
    (hTΛ : ∀ (r : MvPolynomial (Fin m ⊕ Fin d) k) (c : C),
      algebraMap (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ (r ⊗ₜ c) =
        twistedBaseToTarget φ δ r *
          improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel g c)
    (q : Ideal Λ)
    (h : CanBeResolved (MvPolynomial (Fin m ⊕ Fin d) k)
      (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ q) :
    CanBeResolved k A Λ q := by
  have : IsScalarTower k (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [hR]
      exact ((twistedBaseHom π).commutes x).symm
  have : IsScalarTower k (MvPolynomial (Fin m ⊕ Fin d) k) Λ :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [hRΛ]
      exact ((twistedBaseToTarget φ δ).commutes x).symm
  have : Algebra.Smooth k (MvPolynomial (Fin m ⊕ Fin d) k) := ⟨inferInstance, inferInstance⟩
  have : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra k C := ((algebraMap (MvPolynomial (Fin d) k) C).comp
    (algebraMap k (MvPolynomial (Fin d) k))).toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin d) k) C :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := MvPolynomial (Fin d) k) (A := C) fun x => rfl
  let : Algebra A C := ((algebraMap (parameterPowerAlgebra A d N a) C).comp
    (algebraMap A (parameterPowerAlgebra A d N a))).toAlgebra
  have : IsScalarTower A (parameterPowerAlgebra A d N a) C :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := parameterPowerAlgebra A d N a) (A := C)
      fun x => rfl
  have : IsScalarTower k A C := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change algebraMap (MvPolynomial (Fin d) k) C (algebraMap k (MvPolynomial (Fin d) k) x) =
      algebraMap (parameterPowerAlgebra A d N a) C
        (algebraMap A (parameterPowerAlgebra A d N a) (algebraMap k A x))
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) C,
      ← IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k)
        (parameterPowerAlgebra A d N a),
      ← IsScalarTower.algebraMap_apply k A (parameterPowerAlgebra A d N a)]
  have hAΛ : ∀ x : A,
      algebraMap (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ
          (Algebra.TensorProduct.includeRight (algebraMap A C x)) = algebraMap A Λ x := by
    intro x
    rw [Algebra.TensorProduct.includeRight_apply, hTΛ, map_one, one_mul,
      improvedAlgebraToTarget_apply]
    change parameterPowerAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel
      (g (algebraMap (parameterPowerAlgebra A d N a) C
        (algebraMap A (parameterPowerAlgebra A d N a) x))) = _
    rw [show g (algebraMap (parameterPowerAlgebra A d N a) C
        (algebraMap A (parameterPowerAlgebra A d N a) x)) =
          algebraMap A (parameterPowerAlgebra A d N a) x from AlgHom.congr_fun hg _]
    exact (parameterPowerAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel).commutes x
  have hmem : ∀ j, a j ∈ singularIdeal k A := fun j => ha ▸ Ideal.subset_span ⟨j, rfl⟩
  exact canBeResolved_of_canBeResolved_tensorProduct (R := MvPolynomial (Fin m ⊕ Fin d) k)
    (C := C) q ha hAΛ (forall_algebraMap_mem_singularIdeal_parameterPowerAlgebra k A d N a hmem)
    hC h

end Stacks.Smoothing

end
