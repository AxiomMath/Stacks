module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# An endomorphism and its adjoint for a nondegenerate pairing have the same trace

Let `G` be a free module of finite rank over `ℤ/N`, `e` a left-nondegenerate pairing on `G` with
values in `ℤ/N`, and `σ, τ` endomorphisms of `G` with `e(σa, σb) = c e(a, b)` and `σ τ = c`, for a
unit `c` of `ℤ/N`. Then `τ` is the adjoint of `σ` (`e(σa, b) = e(a, τb)`) and `Tr σ = Tr τ`
(`Stacks.Picard.trace_eq_of_pairing`). For a twisted Frobenius `φ = Ψ⁻¹ F^f` of a curve, with
`σ = φ^*`, `τ = Ψ^*` on `Pic[ℓⁿ]`, `c = q` and `e` the Weil pairing, this is the step
`Tr(φ^*) = Tr(Ψ^*)` of the proof of Weil's theorem (Tag 03U1) through the zeta function.
-/

@[expose] public noncomputable section

namespace Stacks.Picard

variable {N : ℕ} [NeZero N] {G : Type*} [AddCommGroup G] [Module (ZMod N) G]
  [Module.Free (ZMod N) G] [Module.Finite (ZMod N) G]

/-- **The trace of an endomorphism equals that of its adjoint for a nondegenerate pairing.** -/
theorem trace_eq_of_pairing (σ τ : G →ₗ[ZMod N] G) (c : ZMod N) (hc : IsUnit c)
    (e : G →+ G →+ ZMod N) (he : ∀ a, (∀ b, e a b = 0) → a = 0)
    (hσ : ∀ a b, e (σ a) (σ b) = c * e a b) (hστ : ∀ a, σ (τ a) = c • a) :
    LinearMap.trace (ZMod N) G σ = LinearMap.trace (ZMod N) G τ := by
  classical
  rcases subsingleton_or_nontrivial (ZMod N) with _ | _
  · exact Subsingleton.elim _ _
  -- `e` is bilinear over `ℤ/N`
  have hlin : ∀ (a : G) (t : ZMod N) (b : G), e a (t • b) = t * e a b := fun a t b =>
    ((e a).toZModLinearMap N).map_smul t b
  have hlin' : ∀ (t : ZMod N) (a b : G), e (t • a) b = t * e a b := fun t a b =>
    congrArg (fun f : G →+ ZMod N => f b) ((e.toZModLinearMap N).map_smul t a)
  -- the map to the dual
  let Φ : G →ₗ[ZMod N] Module.Dual (ZMod N) G :=
    { toFun := fun a => (e a).toZModLinearMap N
      map_add' := fun a a' => LinearMap.ext fun b => by simp
      map_smul' := fun t a => LinearMap.ext fun b => by simp [hlin'] }
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := ZMod N) (M := G)
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  have : Finite G := Module.finite_of_finite (ZMod N)
  have : Finite (Module.Dual (ZMod N) G) := Finite.of_equiv _ b.dualBasis.equivFun.toEquiv.symm
  have hΦbij : Function.Bijective Φ := by
    refine Function.Injective.bijective_of_nat_card_le ?_
      (Nat.card_congr (b.dualBasis.equivFun.toEquiv.trans b.equivFun.toEquiv.symm)).le
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun a ha => he a fun b => congrArg (fun f : Module.Dual (ZMod N) G => f b) ha
  let Φe := LinearEquiv.ofBijective Φ hΦbij
  -- `τ` is the adjoint of `σ`
  have hadj : ∀ a b, e (σ a) b = e a (τ b) := fun a b => by
    obtain ⟨u, rfl⟩ := hc
    exact (Units.mul_right_inj u).1 (by rw [← hσ a (τ b), hστ, hlin])
  have hconj : Φe.conj σ = Module.Dual.transpose τ := by
    refine LinearMap.ext fun f => LinearMap.ext fun b => ?_
    obtain ⟨a, rfl⟩ := hΦbij.2 f
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show Φe.symm (Φ a) = a from Φe.symm_apply_apply a]
    exact hadj a b
  rw [← LinearMap.trace_conj' σ Φe, hconj, LinearMap.trace_transpose']

end Stacks.Picard
