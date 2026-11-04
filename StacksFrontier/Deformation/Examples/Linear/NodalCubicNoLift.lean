module

public import Mathlib.LinearAlgebra.Isomorphisms
public import StacksFrontier.Deformation.Examples.Linear.NodalCubicRightLift

/-!
# `M` does not lift: the negative half of the refutation

Seventeenth layer of the instantiation of `Deformation.FlatModuleLiftBaseChangeStatement`, and
the mathematical heart of it:

**`M = P/(x)` has no `A'`-flat `P'`-module lift.**

Layer sixteen produced the lift on the `Q'` side, so this is the half that makes the biconditional
of Stacks 0DZ2 fail. It is the step that
`StacksFrontier.Deformation.Examples.Linear.NodalArtinSchreierLift` listed as *not* checked — "the
assembly of Nakayama with `eq_bot_of_flat_quotient_of_isNilpotent` into the statement that *every*
lift of `M` is an `ξ` as above" — and it is mathematics, not bookkeeping.

## The two steps

**The scalar step is pure ring theory and carries no modules at all.** If `ξ ∈ A' = NC[t]/t³`
reduces to `0` in `NC` and satisfies the relation `ξ² = t·ξ + t²·Y` of `P'`, then writing
`ξ = t·a + t²·b` in the basis `1, t, t²` (`exists_cst_add_tau`, with the constant coefficient
`redA ξ = 0`) the relation becomes `a·a = a + Y` by `twisted_lift_iff` — the Artin–Schreier
equation for `Y`, which `not_isASSol_ncY` says has no solution over the nodal cubic. That is
`Deformation.Examples.ArtinSchreier.not_twisted_scalar`.

**The module step produces such a `ξ` from any lift.** Let `M'` be an `A'`-flat `P'`-module with
`P ⊗_{P'} M' ≅ M`. The step is stated below in terms of a bare function `f : M' → NC` with three
properties — additive, `f (p • y) = p̄ · f y`, surjective, and killed exactly on `t·M'` — because
that is all the proof uses, and because stating it that way keeps every tensor product and every
`Module P' M` instance out of it. (The instance diamond recorded in
`Deformation.Examples.ArtinSchreier.qRedComparison` is the reason that matters: the hypotheses
here are ones the caller can discharge in whatever instance path its own goal happens to carry.)
Then:

* `M'` is **cyclic over `A'`**. Pick `m₀` with `f m₀ = 1`. For any `y`, choose `a` with
  `redA a = f y`; then `f (y − a·m₀) = 0`, so `y − a·m₀ ∈ t·M'`. Iterating three times and using
  `t³ = 0` writes `y = (a₀ + t·a₁ + t²·a₂)·m₀` outright — Nakayama, done by hand, which at
  nilpotence index three is three substitutions rather than a limit argument.
* `M' ≅ A'/J` for `J = {a : a·m₀ = 0}`, and `J ⊆ ker(A' → NC) = (t)` because `a·m₀ = 0` forces
  `redA a = f (a·m₀) = 0`. So `J` is nilpotent, `A'/J` is `A'`-flat, and
  `eq_bot_of_flat_quotient_of_isNilpotent` gives `J = ⊥`: **`M'` is free of rank one over `A'`**.
* Hence `x · m₀ = ξ · m₀` for a unique `ξ ∈ A'`. It reduces to `0` because `x` dies in
  `M = P/(x)`, and it satisfies `ξ² = t·ξ + t²·Y` because `x` does, by `pRelation` and
  injectivity. The scalar step finishes it.

## Main results

* `Deformation.Examples.ArtinSchreier.not_twisted_scalar`: the scalar step.
* `Deformation.Examples.ArtinSchreier.not_flat_lift_of_reduction`: **no `A'`-flat `P'`-module has
  a reduction map onto `M`**, i.e. `M` has no `A'`-flat `P'`-module lift.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### The scalar step -/

/-- **No scalar solves the lifting relation.** If `ξ ∈ A' = NC[t]/t³` reduces to zero in `NC` and
satisfies the defining relation `ξ² = t·ξ + t²·Y` of `P'`, then `Y` is an Artin–Schreier value of
the nodal cubic, which `not_isASSol_ncY` forbids.

Writing `ξ = t·a + t²·b` — possible because `redA ξ = 0` kills the constant coefficient in the
basis `1, t, t²` — the relation becomes `a·a = a + Y` by `twisted_lift_iff`, and in
characteristic two that is `a² + a = Y`. -/
theorem not_twisted_scalar (ξ : ABase) (hred : redA ξ = 0)
    (hrel : ξ * ξ = tau NC * ξ + tau NC * tau NC * cst NC ncY) : False := by
  obtain ⟨a, b, c, hξ⟩ := exists_cst_add_tau (R := NC) ξ
  have ha : a = 0 := by
    have h := congrArg redA hξ
    rw [hred] at h
    simpa using h.symm
  subst ha
  rw [map_zero, zero_add] at hξ
  subst hξ
  have hb : b * b = b + ncY := (twisted_lift_iff b c ncY).1 hrel
  refine not_isASSol_ncY ⟨b, ?_⟩
  change b * b + b = ncY
  linear_combination hb + b * two_eq_zero_nc

/-! ### The module step -/

/-- **`M = P/(x)` has no `A'`-flat `P'`-module lift.**

The hypotheses are the reduction map of a putative lift, in the weakest form the proof uses: a
bare function `f : M' → NC` which is additive, semilinear over `P' → NC`, surjective, and killed
exactly on `t·M'`. A lift `M'` with `P ⊗_{P'} M' ≅ M` supplies such an `f` as
`m ↦ e (1 ⊗ m)`.

The proof is Nakayama by hand at nilpotence index three, then
`eq_bot_of_flat_quotient_of_isNilpotent`, then `not_twisted_scalar`. -/
theorem not_flat_lift_of_reduction {M' : Type u} [AddCommGroup M'] [Module PBase M']
    [Module ABase M'] [IsScalarTower ABase PBase M'] [Module.Flat ABase M']
    (f : M' → NC)
    (hadd : ∀ y z : M', f (y + z) = f y + f z)
    (hsmul : ∀ (p : PBase) (y : M'), f (p • y) = pBaseToNC p * f y)
    (hsurj : Function.Surjective f)
    (hkerf : ∀ y : M', f y = 0 → ∃ w : M', y = tauP • w) :
    False := by
  -- `f` is semilinear over `A' → NC` too
  have hA2 : ∀ (a : ABase) (y : M'), (algebraMap ABase PBase a) • y = a • y := fun a y =>
    IsScalarTower.algebraMap_smul PBase a y
  have hsmulA : ∀ (a : ABase) (y : M'), f (a • y) = redA a * f y := by
    intro a y
    rw [← hA2, hsmul, pBaseToNC_algebraMap]
  have hzero : f 0 = 0 := map_zero (AddMonoidHom.mk' f hadd)
  have hsub : ∀ y z : M', f (y - z) = f y - f z := map_sub (AddMonoidHom.mk' f hadd)
  obtain ⟨m₀, hm₀⟩ := hsurj 1
  have hfa : ∀ a : ABase, f (a • m₀) = redA a := fun a => by rw [hsmulA, hm₀, mul_one]
  -- one Nakayama step
  have hstep : ∀ y : M', ∃ (a : ABase) (w : M'), y = a • m₀ + (tau NC) • w := by
    intro y
    obtain ⟨a, ha⟩ := redA_surjective (f y)
    have h0 : f (y - a • m₀) = 0 := by
      rw [hsub, hfa, ha, sub_self]
    obtain ⟨w, hw⟩ := hkerf _ h0
    refine ⟨a, w, ?_⟩
    have h2 : y - a • m₀ = (tau NC) • w := hw.trans (by rw [tauP]; exact hA2 _ w)
    exact sub_eq_iff_eq_add'.1 h2
  -- three steps and `t³ = 0` make `M'` cyclic over `A'`
  have hgen : ∀ y : M', ∃ a : ABase, y = a • m₀ := by
    intro y
    obtain ⟨a₀, w₁, h₁⟩ := hstep y
    obtain ⟨a₁, w₂, h₂⟩ := hstep w₁
    obtain ⟨a₂, w₃, h₃⟩ := hstep w₂
    have e3 : (tau NC) • w₂ = (tau NC * a₂) • m₀ + (tau NC * tau NC) • w₃ := by
      rw [h₃, smul_add, smul_smul, smul_smul]
    have e2 : (tau NC) • ((tau NC) • w₂) = (tau NC * (tau NC * a₂)) • m₀ := by
      rw [e3, smul_add, smul_smul, smul_smul, tau_cube', zero_smul, add_zero]
    have e1 : (tau NC) • w₁ = (tau NC * a₁) • m₀ + (tau NC * (tau NC * a₂)) • m₀ := by
      rw [h₂, smul_add, smul_smul, e2]
    refine ⟨a₀ + tau NC * a₁ + tau NC * (tau NC * a₂), ?_⟩
    rw [h₁, e1, add_smul, add_smul, add_assoc]
  -- `M'` is `A'/J` for an ideal `J` inside `(t)`
  set ψ : ABase →ₗ[ABase] M' := LinearMap.toSpanSingleton ABase M' m₀ with hψdef
  have hψapp : ∀ a : ABase, ψ a = a • m₀ := fun a => rfl
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨a, ha⟩ := hgen y
    exact ⟨a, (hψapp a).trans ha.symm⟩
  have hJle : (LinearMap.ker ψ : Ideal ABase) ≤ RingHom.ker redA := by
    intro a ha
    rw [LinearMap.mem_ker, hψapp] at ha
    rw [RingHom.mem_ker, ← hfa, ha, hzero]
  have hnil : IsNilpotent (LinearMap.ker ψ : Ideal ABase) := by
    obtain ⟨n, hn⟩ := isNilpotent_ker_redA
    refine ⟨n, le_antisymm ?_ bot_le⟩
    calc (LinearMap.ker ψ : Ideal ABase) ^ n ≤ (RingHom.ker redA) ^ n :=
          pow_le_pow_left' hJle n
      _ = ⊥ := hn
  have hflatq : Module.Flat ABase (ABase ⧸ (LinearMap.ker ψ : Ideal ABase)) :=
    Module.Flat.of_linearEquiv (ψ.quotKerEquivOfSurjective hψsurj)
  have hJbot : (LinearMap.ker ψ : Ideal ABase) = ⊥ :=
    eq_bot_of_flat_quotient_of_isNilpotent _ hnil hflatq
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot]
    exact hJbot
  -- the action of `x` on `M'` is a scalar
  obtain ⟨ξ, hξ⟩ := hψsurj ((AdjoinRoot.root pPoly) • m₀)
  rw [hψapp] at hξ
  -- that scalar reduces to zero
  have hred : redA ξ = 0 := by
    rw [← hfa, hξ, hsmul, pBaseToNC_root, zero_mul]
  -- and it satisfies the relation of `P'`
  have hcomm : ∀ (a : ABase) (p : PBase) (y : M'), a • (p • y) = p • (a • y) := by
    intro a p y
    rw [← hA2 a (p • y), smul_smul, mul_comm, ← smul_smul, hA2 a y]
  have hrel : ξ * ξ = tau NC * ξ + tau NC * tau NC * cst NC ncY := by
    refine hψinj ?_
    rw [hψapp, hψapp]
    have hstep1 : (algebraMap ABase PBase (tau NC) * AdjoinRoot.root pPoly) • m₀
        = (tau NC * ξ) • m₀ := by
      rw [← smul_smul, hA2, ← hξ, smul_smul]
    calc (ξ * ξ) • m₀ = ξ • (ξ • m₀) := (smul_smul ξ ξ m₀).symm
      _ = ξ • ((AdjoinRoot.root pPoly) • m₀) := by rw [hξ]
      _ = (AdjoinRoot.root pPoly) • (ξ • m₀) := hcomm _ _ _
      _ = (AdjoinRoot.root pPoly) • ((AdjoinRoot.root pPoly) • m₀) := by rw [hξ]
      _ = (AdjoinRoot.root pPoly * AdjoinRoot.root pPoly) • m₀ := smul_smul _ _ _
      _ = (algebraMap ABase PBase (tau NC) * AdjoinRoot.root pPoly
            + algebraMap ABase PBase (tau NC * tau NC * cst NC ncY)) • m₀ := by rw [pRelation]
      _ = (algebraMap ABase PBase (tau NC) * AdjoinRoot.root pPoly) • m₀
            + (algebraMap ABase PBase (tau NC * tau NC * cst NC ncY)) • m₀ := add_smul _ _ _
      _ = (tau NC * ξ) • m₀ + (tau NC * tau NC * cst NC ncY) • m₀ := by
            rw [hstep1, hA2]
      _ = (tau NC * ξ + tau NC * tau NC * cst NC ncY) • m₀ := (add_smul _ _ _).symm
  exact not_twisted_scalar ξ hred hrel

end Deformation.Examples.ArtinSchreier

end
