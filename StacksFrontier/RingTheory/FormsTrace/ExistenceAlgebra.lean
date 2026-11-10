module

public import StacksFrontier.RingTheory.FormsTrace.Defs
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElement
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.DedekindComparison
public import StacksFrontier.RingTheory.TateMap.DetNL

/-!
# Trace maps on forms from a twisted map and a trace-valued map

Let `A → B` be a finite projective ring map. Suppose given `B`-linear maps

`c^p : Ω^p_B → ⋀^p_B(B ⊗_A Ω_A) ⊗_B L`

into the twist by a `B`-module `L`, carrying the image of every pulled back form `ω` to
`ω ⊗ δ` for a fixed `δ ∈ L`, and a `B`-linear map `u : L → Hom_A(B, A)` carrying `δ` to
`Trace_{B/A}`. Then the composite of `c^p`, of `id ⊗ u`, of
`⋀^p_B(B ⊗_A Ω_A) ≅ B ⊗_A Ω^p_A` and of evaluation `(b ⊗ ω) ⊗ φ ↦ φ(b) ω` satisfies condition
(1) of Stacks, Lemma 0FLB.

## Main definitions

* `Stacks.FormsTrace.dualContract`: evaluation `Hom_A(B, A) ⊗_B (B ⊗_A N) → N`.
* `Stacks.FormsTrace.detNLToTate`: the identification of `NaiveCotangent.detNL` with
  `Stacks.TateMap.detNL`.

## Main results

* `Stacks.FormsTrace.formsMap_eq_map_mapBaseChange`: the pull-back of forms factors through
  `⋀^p_B(B ⊗_A Ω_A)`.
* `Stacks.FormsTrace.exists_isFormsTrace_of_twisted`: given `c^p` and `u` as above, some maps
  `Θ^p : Ω^p_B → Ω^p_A` satisfy condition (1) of Stacks, Lemma 0FLB.
* `Stacks.FormsTrace.selfFactorizationDualEquiv_finiteFlatTraceElement_eq_trace`: under
  `ω_{B/A} = Hom_A(B, A)` the trace element of a finite flat algebra is `Trace_{B/A}`.
* `Stacks.FormsTrace.detNLToTate_deltaNL`: `Stacks.FormsTrace.detNLToTate` carries `δ(NL_{B/A})`
  to `δ(NL_{B/A})`.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v

namespace Stacks.FormsTrace

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- **The pull-back of forms factors through the base-changed forms**: `Ω^p_A → Ω^p_B` is
`ω ↦ 1 ⊗ ω` into `⋀^p_B(B ⊗_A Ω_A)` followed by `⋀^p` of `B ⊗_A Ω_A → Ω_B`. -/
theorem formsMap_eq_map_mapBaseChange (p : ℕ) (ω : ⋀[A]^p Ω[A⁄ℤ]) :
    formsMap A B p ω = exteriorPower.map p (KaehlerDifferential.mapBaseChange ℤ A B)
      (ExteriorAlgebra.exteriorPowerBaseChangeMap A B Ω[A⁄ℤ] p ω) := by
  have hω : ω ∈ (⊤ : Submodule A (⋀[A]^p Ω[A⁄ℤ])) := Submodule.mem_top
  rw [← exteriorPower.ιMulti_span A p Ω[A⁄ℤ]] at hω
  induction hω using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [ExteriorAlgebra.powMapₛₗ_ιMulti, ExteriorAlgebra.exteriorPowerBaseChangeMap_ιMulti,
      exteriorPower.map_apply_ιMulti]
    refine congrArg (exteriorPower.ιMulti B p) (funext fun i ↦ ?_)
    change KaehlerDifferential.map ℤ ℤ A B (v i) = _
    rw [Function.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smulₛₗ, map_smul (ExteriorAlgebra.exteriorPowerBaseChangeMap A B Ω[A⁄ℤ] p) a x,
      ← algebraMap_smul B a, map_smul, hx]

attribute [local instance] Stacks.Discriminant.algebraDualModule

/-- The two actions of `A` on `Hom_A(B, A)`, directly and through `B` acting on the source, are
compatible. -/
theorem isScalarTower_dual : IsScalarTower A B (Module.Dual A B) where
  smul_assoc a b φ := by
    ext x
    change φ ((a • b) * x) = a • φ (b * x)
    rw [smul_mul_assoc, map_smul]

attribute [local instance] isScalarTower_dual

variable {A B}

/-- **Evaluation of base-changed forms against `Hom_A(B, A)`**:
`(b ⊗ ω) ⊗ φ ↦ φ(b) ω`, read as `Hom_A(B, A) ⊗_B (B ⊗_A N) → N`. -/
def dualContract (N : Type v) [AddCommGroup N] [Module A N] :
    Module.Dual A B ⊗[B] (B ⊗[A] N) →ₗ[A] N :=
  (TensorProduct.lid A N).toLinearMap ∘ₗ
    (LinearMap.rTensor N (LinearMap.applyₗ (R := A) (1 : B))) ∘ₗ
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A B B (Module.Dual A B)
      N).toLinearMap.restrictScalars A)

/-- `Stacks.FormsTrace.dualContract` on pure tensors: `φ ⊗ (b ⊗ n) ↦ φ(b) n`. -/
theorem dualContract_tmul (N : Type v) [AddCommGroup N] [Module A N] (φ : Module.Dual A B)
    (b : B) (n : N) : dualContract N (φ ⊗ₜ (b ⊗ₜ n)) = φ b • n := by
  simp [dualContract]

variable (A B) in
/-- **Condition (1) of Lemma 0FLB from a twisted map and a trace-valued map.** Let `A → B` be
finite projective, `L` a `B`-module with an element `δ`, `c^p : Ω^p_B → ⋀^p_B(B ⊗_A Ω_A) ⊗_B L`
`B`-linear maps carrying the image `⋀^p(B ⊗_A Ω_A → Ω_B)(ω)` of every `ω` to `ω ⊗ δ`, and
`u : L → Hom_A(B, A)` a `B`-linear map (for `(b · φ)(x) = φ(bx)`) carrying `δ` to
`Trace_{B/A}`. The elements `ω` are parametrized by surjections `E p : P p → ⋀^p_B(B ⊗_A Ω_A)`.
Then some maps
`Θ^p : Ω^p_B → Ω^p_A` satisfy condition (1) of Lemma 0FLB:
`Θ^p(η)` is `∑ φ_k(b_k) ω_k` if `c^p(η) ↦ ∑ (b_k ⊗ ω_k) ⊗ φ_k` under `id ⊗ u` and
`⋀^p_B(B ⊗_A Ω_A) ≅ B ⊗_A Ω^p_A`. -/
theorem exists_isFormsTrace_of_twisted [Module.Finite A B] [Module.Projective A B]
    {L : Type v} [AddCommGroup L] [Module B L]
    (c : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[B] (⋀[B]^p (B ⊗[A] Ω[A⁄ℤ])) ⊗[B] L) (δ : L)
    {P : ℕ → Type v} (E : ∀ p : ℕ, P p → ⋀[B]^p (B ⊗[A] Ω[A⁄ℤ]))
    (hE : ∀ p : ℕ, Function.Surjective (E p))
    (hc : ∀ (p : ℕ) (ζ : P p),
      c p (exteriorPower.map p (KaehlerDifferential.mapBaseChange ℤ A B) (E p ζ)) = E p ζ ⊗ₜ δ)
    (u : L →ₗ[B] Module.Dual A B) (hu : u δ = trace A B) :
    ∃ Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ], IsFormsTrace A B Θ := by
  let Φ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[B]
      Module.Dual A B ⊗[B] (B ⊗[A] ⋀[A]^p Ω[A⁄ℤ]) := fun p ↦
    (TensorProduct.comm B _ _).toLinearMap ∘ₗ
      LinearMap.rTensor (Module.Dual A B)
        (ExteriorAlgebra.exteriorPowerBaseChange A B Ω[A⁄ℤ] p).symm.toLinearMap ∘ₗ
      u.lTensor _ ∘ₗ c p
  refine ⟨fun p ↦ dualContract (⋀[A]^p Ω[A⁄ℤ]) ∘ₗ (Φ p).restrictScalars A, ?_⟩
  intro p b ω
  have h1 : (ExteriorAlgebra.exteriorPowerBaseChange A B Ω[A⁄ℤ] p).symm
      (ExteriorAlgebra.exteriorPowerBaseChangeMap A B Ω[A⁄ℤ] p ω) = 1 ⊗ₜ ω := by
    rw [LinearEquiv.symm_apply_eq, ExteriorAlgebra.exteriorPowerBaseChange_tmul, one_smul]
  have h2 : Φ p (formsMap A B p ω) = trace A B ⊗ₜ (1 ⊗ₜ ω) := by
    obtain ⟨ζ, hζ⟩ := hE p (ExteriorAlgebra.exteriorPowerBaseChangeMap A B Ω[A⁄ℤ] p ω)
    rw [formsMap_eq_map_mapBaseChange, ← hζ]
    simp only [Φ, LinearMap.coe_comp, Function.comp_apply, hc,
      LinearMap.lTensor_tmul, hu, LinearMap.rTensor_tmul, LinearEquiv.coe_coe]
    rw [hζ]
    simp only [h1, TensorProduct.comm_tmul]
  change dualContract (⋀[A]^p Ω[A⁄ℤ]) (Φ p (b • formsMap A B p ω)) = _
  rw [map_smul, h2, TensorProduct.smul_tmul', dualContract_tmul]
  change trace A B (b * 1) • ω = _
  rw [mul_one]

section SelfDual

variable (A B)

/-- Under `ω_{B/A} = Hom_A(B, A)` for the factorization of `A → B` through itself
(`Stacks.Discriminant.selfFactorizationDualEquiv`), the trace element `Trace_{B/A} ⊗ 1` of a
finite flat algebra (Tag 0BT8) is `Trace_{B/A}`. -/
theorem selfFactorizationDualEquiv_finiteFlatTraceElement_eq_trace [IsNoetherianRing A]
    [Module.Finite A B] [Module.Projective A B] :
    Stacks.Discriminant.selfFactorizationDualEquiv
      (Stacks.Discriminant.finiteFlatTraceElement A B) = trace A B := by
  change TensorProduct.lid B (Module.Dual A B)
    ((TensorProduct.comm B (Module.Dual A B) B) (trace A B ⊗ₜ (1 : B))) = trace A B
  simp

/-- The determinant `NaiveCotangent.detNL` of `NL_{B/A}` is `Stacks.TateMap.detNL`: both are the
value of the determinant functor at `NL_{B/A}`. -/
def detNLToTate [Algebra.Syntomic A B] :
    NaiveCotangent.detNL A B →ₗ[B] Stacks.TateMap.detNL A B :=
  LinearMap.id

/-- `Stacks.FormsTrace.detNLToTate` carries `δ(NL_{B/A})` to `δ(NL_{B/A})`. -/
theorem detNLToTate_deltaNL [Algebra.Syntomic A B] [Algebra.QuasiFinite A B] :
    detNLToTate A B (NaiveCotangent.deltaNL A B) = Stacks.TateMap.deltaNL A B :=
  rfl

end SelfDual

end Stacks.FormsTrace

end
