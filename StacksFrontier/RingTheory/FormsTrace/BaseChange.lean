module

public import StacksFrontier.RingTheory.FormsTrace.Nice

/-!
# Trace maps on forms and base change

Let

```
B₁ → B₂
↑     ↑
R₁ → R₂
```

be a pushout of commutative rings with `B₁` finite projective over `R₁`. The trace of `B₂/R₂`
is the base change of the trace of `B₁/R₁`, and if `h ∈ R₁` is such that `h^N` kills `Ω_{B₁/R₁}`
and the image of `h` is a nonzerodivisor on the forms of `R₂`, then any two families with
property (1) of Stacks, Lemma 0FLB on the two sides are compatible with the pull-back of forms:
`Θ₂(g^*η) = f^*Θ₁(η)`. This is how the trace maps of the universal charts are compared with each
other and transported to arbitrary finite syntomic algebras in the proof of Lemma 0FLB.

## Main results

* `Stacks.FormsTrace.kaehlerMap_comp`, `Stacks.FormsTrace.formsMap_formsMap`: functoriality of
  the pull-back of forms.
* `Stacks.FormsTrace.trace_algebraMap_of_isPushout`: `Trace_{B₂/R₂}(g b) = f(Trace_{B₁/R₁}(b))`.
* `Stacks.FormsTrace.IsFormsTrace.formsMap_comm_of_isPushout`: `Θ₂(g^*η) = f^*Θ₁(η)`.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
-/

@[expose] public noncomputable section

open scoped TensorProduct
open KaehlerDifferential

universe u

namespace Stacks.FormsTrace

section Functoriality

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Algebra A C] [IsScalarTower A B C]

/-- Functoriality of the map on absolute Kähler differentials. -/
theorem kaehlerMap_comp (ω : Ω[A⁄ℤ]) :
    KaehlerDifferential.map ℤ ℤ B C (KaehlerDifferential.map ℤ ℤ A B ω) =
      KaehlerDifferential.map ℤ ℤ A C ω := by
  have hω : ω ∈ Submodule.span A (Set.range (D ℤ A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    simp only [KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add]
  | smul a x _ hx =>
    rw [map_smul (KaehlerDifferential.map ℤ ℤ A C), ← hx,
      map_smul (KaehlerDifferential.map ℤ ℤ A B),
      ← algebraMap_smul B a (KaehlerDifferential.map ℤ ℤ A B x), map_smul, algebraMap_smul]

/-- **Functoriality of the pull-back of forms**: `g^* f^* = (g f)^*`. -/
theorem formsMap_formsMap (p : ℕ) (ω : ⋀[A]^p Ω[A⁄ℤ]) :
    formsMap B C p (formsMap A B p ω) = formsMap A C p ω :=
  (ExteriorAlgebra.powMapₛₗ_eq_comp (φ := algebraMap A B) (ψ := algebraMap B C)
    (χ := algebraMap A C) p (Stacks.DeRham.kaehlerMapₛₗ A B) (Stacks.DeRham.kaehlerMapₛₗ B C)
    (Stacks.DeRham.kaehlerMapₛₗ A C) (fun a => IsScalarTower.algebraMap_apply A B C a)
    (fun ω => (kaehlerMap_comp ω).symm) ω).symm

end Functoriality

variable {R₁ B₁ R₂ B₂ : Type u} [CommRing R₁] [CommRing B₁] [CommRing R₂] [CommRing B₂]
  [Algebra R₁ B₁] [Algebra R₁ R₂] [Algebra R₂ B₂] [Algebra B₁ B₂] [Algebra R₁ B₂]
  [IsScalarTower R₁ R₂ B₂] [IsScalarTower R₁ B₁ B₂] [Algebra.IsPushout R₁ B₁ R₂ B₂]

/-- **The trace commutes with base change** along a pushout:
`Trace_{B₂/R₂}(g b) = f(Trace_{B₁/R₁}(b))`. -/
theorem trace_algebraMap_of_isPushout [Module.Finite R₁ B₁] [Module.Projective R₁ B₁]
    [Module.Finite R₂ B₂] [Module.Projective R₂ B₂] (b : B₁) :
    trace R₂ B₂ (algebraMap B₁ B₂ b) = algebraMap R₁ R₂ (trace R₁ B₁ b) := by
  have hbc : IsBaseChange R₂ (IsScalarTower.toAlgHom R₁ B₁ B₂).toLinearMap :=
    (Algebra.IsPushout.symm (inferInstance : Algebra.IsPushout R₁ B₁ R₂ B₂)).out
  let e : R₂ ⊗[R₁] B₁ ≃ₗ[R₂] B₂ := hbc.equiv
  have hconj : Algebra.lmul R₂ B₂ (algebraMap B₁ B₂ b) =
      e.toLinearMap ∘ₗ ((Algebra.lmul R₁ B₁ b).baseChange R₂ ∘ₗ
        e.symm.toLinearMap) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨t, rfl⟩ := e.surjective x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      simp only [LinearMap.baseChange_tmul, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', e,
        hbc.equiv_tmul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', map_mul,
        mul_smul_comm]
    | add s t hs ht => simp only [map_add, hs, ht]
  rw [trace, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hconj,
    Stacks.Discriminant.finiteProjectiveTrace_conj,
    Stacks.Discriminant.finiteProjectiveTrace_baseChange]
  rfl

omit [Algebra.IsPushout R₁ B₁ R₂ B₂] in
/-- The pull-back of forms around a commutative square: `g^* f^* = f'^* f''^*`. -/
theorem formsMap_formsMap_square (p : ℕ) (ω : ⋀[R₁]^p Ω[R₁⁄ℤ]) :
    formsMap B₁ B₂ p (formsMap R₁ B₁ p ω) = formsMap R₂ B₂ p (formsMap R₁ R₂ p ω) := by
  rw [formsMap_formsMap, formsMap_formsMap]

/-- The pull-back of forms carries the span of pulled back forms into the span of pulled back
forms. -/
theorem formsMap_mem_pulledBackSpan_of_mem {p : ℕ} {x : ⋀[B₁]^p Ω[B₁⁄ℤ]}
    (hx : x ∈ pulledBackSpan R₁ B₁ p) [Module.Finite R₁ B₁] [Module.Projective R₁ B₁]
    [Module.Finite R₂ B₂] [Module.Projective R₂ B₂]
    {Θ₂ : ∀ p : ℕ, ⋀[B₂]^p Ω[B₂⁄ℤ] →ₗ[R₂] ⋀[R₂]^p Ω[R₂⁄ℤ]} (hΘ₂ : IsFormsTrace R₂ B₂ Θ₂)
    {Θ₁ : ∀ p : ℕ, ⋀[B₁]^p Ω[B₁⁄ℤ] →ₗ[R₁] ⋀[R₁]^p Ω[R₁⁄ℤ]} (hΘ₁ : IsFormsTrace R₁ B₁ Θ₁) :
    Θ₂ p (formsMap B₁ B₂ p x) = formsMap R₁ R₂ p (Θ₁ p x) := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  simp only [map_finsuppSum]
  refine Finsupp.sum_congr fun ω _ => ?_
  rw [map_smulₛₗ, formsMap_formsMap_square (R₂ := R₂), hΘ₂, hΘ₁, map_smulₛₗ,
    trace_algebraMap_of_isPushout (R₁ := R₁)]

/-- **Trace maps on forms are compatible with base change** (proof of Stacks, Lemma 0FLB): if
`h^N` kills `Ω_{B₁/R₁}` and the image of `h` in `R₂` is a nonzerodivisor on the forms of `R₂`,
then `Θ₂(g^*η) = f^*Θ₁(η)` for any two families with property (1). -/
theorem IsFormsTrace.formsMap_comm_of_isPushout [Module.Finite R₁ B₁] [Module.Projective R₁ B₁]
    [Module.Finite R₂ B₂] [Module.Projective R₂ B₂] {h : R₁} {N : ℕ}
    (hN : ∀ x : Ω[B₁⁄R₁], h ^ N • x = 0)
    (hreg : ∀ p, IsSMulRegular (⋀[R₂]^p Ω[R₂⁄ℤ]) (algebraMap R₁ R₂ h))
    {Θ₁ : ∀ p : ℕ, ⋀[B₁]^p Ω[B₁⁄ℤ] →ₗ[R₁] ⋀[R₁]^p Ω[R₁⁄ℤ]} (hΘ₁ : IsFormsTrace R₁ B₁ Θ₁)
    {Θ₂ : ∀ p : ℕ, ⋀[B₂]^p Ω[B₂⁄ℤ] →ₗ[R₂] ⋀[R₂]^p Ω[R₂⁄ℤ]} (hΘ₂ : IsFormsTrace R₂ B₂ Θ₂)
    (p : ℕ) (η : ⋀[B₁]^p Ω[B₁⁄ℤ]) :
    Θ₂ p (formsMap B₁ B₂ p η) = formsMap R₁ R₂ p (Θ₁ p η) := by
  have key := formsMap_mem_pulledBackSpan_of_mem (pow_smul_mem_pulledBackSpan hN p η) hΘ₂ hΘ₁
  set c : R₁ := (h ^ N) ^ p
  have e1 : formsMap B₁ B₂ p (c • η) = algebraMap R₁ R₂ c • formsMap B₁ B₂ p η := by
    rw [← algebraMap_smul B₁ c η, map_smulₛₗ, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R₁ R₂ B₂, algebraMap_smul]
  rw [e1, map_smul, map_smul, map_smulₛₗ] at key
  exact ((hreg p).pow (N * p)) (by rw [pow_mul, ← map_pow, ← map_pow]; exact key)

end Stacks.FormsTrace

end
