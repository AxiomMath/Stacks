module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AdicCompletionLimitComparison
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence

/-!
# Nakayama's lemma for the cohomology of a sheaf over a local base

Let `A` be a local ring with maximal ideal `𝔪`, let `X` be a scheme over `Spec A` and let `𝒢` be
an `𝒪_X`-module. If `H ᵖ(X, 𝒢)` is a finite `A`-module, if `H ᵖ(X, 𝒢 / 𝔪 ⁿ 𝒢)` vanishes for one
`n > c`, and if the kernel of `H ᵖ(X, 𝒢) → H ᵖ(X, 𝒢 / 𝔪 ⁿ 𝒢)` lies in `𝔪 ⁿ⁻ᶜ H ᵖ(X, 𝒢)` — the
bound of [Stacks, Tag 02OB] clause (1) — then `H ᵖ(X, 𝒢) = 0`.

This is the last paragraph of the source's proof of clause (1) of [Stacks, Tag 0D2M]: there the
vanishing of every term of the tower makes the `𝔪`-adic completion of `H ᵖ(X, ℱ ⊗ ℒ ^⊗ d)` zero,
the module is finite over `A`, and Nakayama's lemma concludes. Both clauses of
[Stacks, Tag 0D2M] are
`Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_and_surjective_fiberTwist`.

## Main results

* `Stacks.Cohomology.FormalFunctions.subsingleton_cohomologyOverBase_of_subsingleton_tower`:
  over a local base, a cohomology module that is finite over `A` and whose `n`-th adic-quotient
  cohomology vanishes for one `n` exceeding the bound of [Stacks, Tag 02OB] is itself zero.

## Implementation notes

Cohomology is `Stacks.Cohomology.FormalFunctions.cohomologyOverBase`, `H ᵖ(X, -)` as an
`A`-module through the structure morphism, and the tower `n ↦ H ᵖ(X, 𝒢 / 𝔪 ⁿ 𝒢)` together with
the maps to it from `H ᵖ(X, 𝒢)` is `adicCohomologyTower` and `adicCohomologyProj` for the ideal
sheaf `𝔪 · 𝒪_X`. Vanishing of a cohomology module is `Subsingleton` of its carrier.

Only one exponent `n` is used, and the lemma is stated for an arbitrary `n > c` rather than for
the whole tower: `n - c ≥ 1` is exactly what puts `𝔪 ⁿ⁻ᶜ` inside `𝔪`. The lemma needs no
Noetherian hypothesis — its finiteness hypothesis already supplies the finite generation that
Nakayama's lemma consumes — and asks of `A` only that it be local, through `𝔪 ⊆ Jac(0)`.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Ample Stacks.AlgebraicGeometry.HyperplaneTwistSequence

/-- **Nakayama's lemma for the cohomology of a sheaf over a local base.**

Let `A` be a local ring with maximal ideal `𝔪`, let `X` be a scheme over `Spec A` and let `𝒢` be
an `𝒪_X`-module. Suppose `H ᵖ(X, 𝒢)` is a finite `A`-module, that `H ᵖ(X, 𝒢 / 𝔪 ⁿ 𝒢)` vanishes
for one `n` with `n > c`, and that the kernel of `H ᵖ(X, 𝒢) → H ᵖ(X, 𝒢 / 𝔪 ⁿ 𝒢)` is contained in
`𝔪 ⁿ⁻ᶜ H ᵖ(X, 𝒢)` — the bound of [Stacks, Tag 02OB] clause (1). Then `H ᵖ(X, 𝒢) = 0`.

Vanishing of the target makes that kernel everything, so `H ᵖ(X, 𝒢) = 𝔪 ⁿ⁻ᶜ H ᵖ(X, 𝒢)` and
`n - c ≥ 1` puts the right-hand side inside `𝔪 H ᵖ(X, 𝒢)`; Nakayama's lemma
([Stacks, Tag 00DV] clause (2)) applies because `𝔪` lies in the Jacobson radical of a local
ring. -/
public theorem subsingleton_cohomologyOverBase_of_subsingleton_tower
    (A : Type u) [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (G : X.Modules) (p c n : ℕ) (hn : c < n)
    (hfinite : Module.Finite A (cohomologyOverBase A f p G))
    (hquot : Subsingleton (adicCohomologyTower A f (IsLocalRing.maximalIdeal A) G p n))
    (hker : LinearMap.ker (adicCohomologyProj A f (IsLocalRing.maximalIdeal A) G p n) ≤
      IsLocalRing.maximalIdeal A ^ (n - c) •
        (⊤ : Submodule A (cohomologyOverBase A f p G))) :
    Subsingleton (cohomologyOverBase A f p G) := by
  have hpow : IsLocalRing.maximalIdeal A ^ (n - c) ≤ IsLocalRing.maximalIdeal A := by
    calc IsLocalRing.maximalIdeal A ^ (n - c)
        ≤ IsLocalRing.maximalIdeal A ^ 1 := Ideal.pow_le_pow_right (by omega)
      _ = IsLocalRing.maximalIdeal A := pow_one _
  have hle : (⊤ : Submodule A (cohomologyOverBase A f p G)) ≤
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A (cohomologyOverBase A f p G)) :=
    le_trans (fun x _ => hker (LinearMap.mem_ker.2 (@Subsingleton.elim _ hquot _ 0)))
      (Submodule.smul_mono_left hpow)
  have hbot : (⊤ : Submodule A (cohomologyOverBase A f p G)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfinite.fg_top hle
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hzero : ∀ x : cohomologyOverBase A f p G, x = 0 := fun x => by
    rw [← Submodule.mem_bot A, ← hbot]; exact Submodule.mem_top
  exact ⟨fun x y => by rw [hzero x, hzero y]⟩

end Stacks.Cohomology.FormalFunctions

end
