module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapClosedPointProZero
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapIdealPowerSubmodule

/-!
# Part (5) of Stacks 0EFY: the limit comparison for `I^{m₀}M` at the `m₀` part (1) produces

In Situation [Stacks, Tag 0EFU] with `A` local and `T = {𝔪}`, part (5) of [Stacks, Tag 0EFY]
asserts that

`Hˢ_𝔪(I^{m₀}M) ⟶ lim_n Hˢ_𝔪(I^{m₀}M/IⁿM)`

is an isomorphism, for the integer `m₀` part (1) of the same lemma produces — not for an
unspecified one, and in particular not at `m₀ = 0`, where the assertion collapses to part (4)
read in degree `s`.

The route is the stability of the situation under `M ↦ IᵏM`
(`Stacks.Algebraization.BootstrapSituation.idealPowerSubmodule`). Applied to that situation, the
two assertions of [Stacks, Tag 0EFX] at the closed point hold for the module `IᵏM`, and
`Stacks.LocalCohomology.isIso_limitLift_localCohomologyAdicCone_of_stableImage` turns them into
invertibility of the limit comparison in degree `s`. That gives the assertion **for every `k`**;
the main statement then exhibits one integer `m₀` which witnesses part (1) and part (5)
simultaneously, part (1) being
`Stacks.LocalCohomology.exists_forall_injective_localCohomologyAdicProjection_of_proZero` fed by
the pro-zero assertion of [Stacks, Tag 0EFX] at the closed point.

## The inverse system, and why it is the source's

For the module `IᵏM` the tower of adic quotients has `n`-th term `IᵏM/Iⁿ(IᵏM)`, and
`Iⁿ(IᵏM) = I^{n+k}M` inside `M` (`Stacks.Algebraization.map_subtype_pow_smul_top`). So the
tower is the source's system `{IᵏM/IⁿM}_{n ≥ k}` read along the cofinal shift `n ↦ n + k`, and
the two limits agree. The same reading is used for part (3) at `T = {𝔪}`,
`Stacks.LocalCohomology.isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology_smul`.

## Main results

* `Stacks.Algebraization.isIso_limitLift_localCohomologyAdicCone_idealPowerSubmodule_closedPoint`
  — the comparison `Hˢ_𝔪(IᵏM) ⟶ lim Hˢ_𝔪(IᵏM/Iⁿ⁺ᵏM)` is an isomorphism, for every `k`.
* `exists_forall_injective_and_isIso_limitLift_localCohomologyAdicCone_closedPoint`, in the
  namespace `Stacks.Algebraization` — **parts (1) and (5) of [Stacks, Tag 0EFY] at `T = {𝔪}`,
  at one and the same `m₀`.**

## Implementation notes

The statements are in the set-indexed model of local cohomology, which is the model both
assertions of [Stacks, Tag 0EFX] and the engines of Tag 0EFY's parts are stated in; the
coreflection-model readings of parts (1), (4) and (6) live in
`StacksFrontier/AlgebraicGeometry/Algebraization/BootstrapCanonicalAdicLimit.lean`.

The source's `T` is an arbitrary specialization-stable subset of `V(I)`; `T = {𝔪}` over a local
ring is one such. The complete [Stacks, Tag 0EFY], at a general specialization-stable `T` and with
one `m₀` for all seven parts, is
`Stacks.Algebraization.exists_bound_adicLocalCohomologyComparisons`.

## References

* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (S : BootstrapSituation.{u, u, u})

/-- **The limit comparison in degree `s` for the submodule `IᵏM`, for every `k`.** In Situation
[Stacks, Tag 0EFU] with `A` local and `T = {𝔪}`,

`Hˢ_𝔪(IᵏM) ⟶ lim_n Hˢ_𝔪(IᵏM/Iⁿ(IᵏM))`

is an isomorphism; the `n`-th term of that tower is `IᵏM/I^{n+k}M`
(`Stacks.Algebraization.map_subtype_pow_smul_top`).

Nothing beyond the situation is assumed. The proof applies
`Stacks.LocalCohomology.isIso_limitLift_localCohomologyAdicCone_of_stableImage` to the situation
`Stacks.Algebraization.BootstrapSituation.idealPowerSubmodule`, whose module is `IᵏM`; the two
inputs are the pro-zero assertion of [Stacks, Tag 0EFX] in degree `s` and its stable-image
assertion in degree `s + 1`, both available at this locus for every situation. -/
public theorem isIso_limitLift_localCohomologyAdicCone_idealPowerSubmodule_closedPoint
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) (k : ℕ) :
    IsIso (limit.lift
      (localCohomologyAdicTower.{u, u} S.A S.T S.I S.s
        (ModuleCat.of S.A ↥(S.I ^ k • (⊤ : Submodule S.A S.M))))
      (localCohomologyAdicCone.{u, u} S.A S.T S.I S.s
        (ModuleCat.of S.A ↥(S.I ^ k • (⊤ : Submodule S.A S.M))))) := by
  have : IsLocalRing (S.idealPowerSubmodule k).A := ‹IsLocalRing S.A›
  have hT' : (S.idealPowerSubmodule k).T = {closedPoint (S.idealPowerSubmodule k).A} := hT
  have hpro : IsProZeroIdealPowerCohomology.{u, u} S.T S.I
      (ModuleCat.of S.A ↥(S.I ^ k • (⊤ : Submodule S.A S.M))) S.s := fun m =>
    exists_map_idealPowerTower_eq_zero_closedPoint (S.idealPowerSubmodule k) hT'
      (S.idealPowerSubmodule k).s le_rfl m
  have hstab : HasStableImageIdealPowerCohomology.{u, u} S.T S.I
      (ModuleCat.of S.A ↥(S.I ^ k • (⊤ : Submodule S.A S.M))) (S.s + 1) 0 :=
    hasStableImageIdealPowerCohomology_closedPoint (S.idealPowerSubmodule k) hT'
  exact isIso_limitLift_localCohomologyAdicCone_of_stableImage.{u, u} S.T S.I
    (ModuleCat.of S.A ↥(S.I ^ k • (⊤ : Submodule S.A S.M))) S.s hpro hstab

/-- **Parts (1) and (5) of [Stacks, Tag 0EFY] at `T = {𝔪}`, at one and the same `m₀`.** In
Situation [Stacks, Tag 0EFU] with `A` local and `T = {𝔪}`, there is an integer `m₀` such that

* `Hⁱ_𝔪(M) ⟶ Hⁱ_𝔪(M/IⁿM)` is injective for every `i ≤ s` and every `n ≥ m₀` — part (1); and
* `Hˢ_𝔪(I^{m₀}M) ⟶ lim_n Hˢ_𝔪(I^{m₀}M/IⁿM)` is an isomorphism — part (5), **at that `m₀`**.

The second item is the statement of part (5) read for the module `I^{m₀}M`: the `n`-th term of
its tower of adic quotients is `I^{m₀}M/I^{n+m₀}M`
(`Stacks.Algebraization.map_subtype_pow_smul_top`), so the tower is the source's system
`{I^{m₀}M/IⁿM}_{n ≥ m₀}` along the cofinal shift `n ↦ n + m₀` and the limits agree.

Nothing beyond the situation is assumed; in particular `A` need not be `I`-adically complete.
Part (1) comes from the pro-zero assertion of [Stacks, Tag 0EFX] at this locus through
`Stacks.LocalCohomology.exists_forall_injective_localCohomologyAdicProjection_of_proZero`, and
part (5) holds at that `m₀` because
`isIso_limitLift_localCohomologyAdicCone_idealPowerSubmodule_closedPoint` proves it for every
exponent, the situation being stable under `M ↦ IᵏM`.

The source's `T` is an arbitrary specialization-stable subset of `V(I)`, and the general case
rests on [Stacks, Tag 0EFX] for that `T`, which is proved in
`StacksFrontier/AlgebraicGeometry/Algebraization/BootstrapUniformStableImage.lean`; parts (1), (3)
and (5) at a general locus, at one and the same `m₀`, are
`Stacks.Algebraization.exists_forall_injective_and_isMittagLeffler_and_isIso_limitLift`, and all
seven parts there are `Stacks.Algebraization.exists_bound_adicLocalCohomologyComparisons`. -/
public theorem exists_forall_injective_and_isIso_limitLift_localCohomologyAdicCone_closedPoint
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) :
    ∃ m₀ : ℕ,
      (∀ i ≤ S.s, ∀ n : ℕ, m₀ ≤ n →
        Function.Injective ((localCohomologyAdicCone.{u, u} S.A S.T S.I i
          (ModuleCat.of S.A S.M)).π.app (op n)).hom) ∧
      IsIso (limit.lift
        (localCohomologyAdicTower.{u, u} S.A S.T S.I S.s
          (ModuleCat.of S.A ↥(S.I ^ m₀ • (⊤ : Submodule S.A S.M))))
        (localCohomologyAdicCone.{u, u} S.A S.T S.I S.s
          (ModuleCat.of S.A ↥(S.I ^ m₀ • (⊤ : Submodule S.A S.M))))) := by
  obtain ⟨m₀, hm₀⟩ := exists_forall_injective_localCohomologyAdicProjection_of_proZero.{u, u}
    S.T S.I (ModuleCat.of S.A S.M) S.s
    fun i hi => exists_map_idealPowerTower_eq_zero_closedPoint S hT i hi 0
  exact ⟨m₀, hm₀,
    isIso_limitLift_localCohomologyAdicCone_idealPowerSubmodule_closedPoint S hT m₀⟩

end Stacks.Algebraization

end
