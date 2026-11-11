module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapAdicProjectionInjectivity
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletionUnitDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationLocalCohomologyLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdeal

/-!
# The canonical comparison `Hⁱ_𝔪(M) ⟶ lim Hⁱ_𝔪(M/IⁿM)` in the bootstrap situation

In Situation [Stacks, Tag 0EFU] with `A` local and `T = {𝔪}`, the **canonical** map

`Hⁱ_𝔪(M) ⟶ lim_n Hⁱ_𝔪(M/IⁿM)`

— the limit comparison of the cone whose legs are the canonical maps `Hⁱ_𝔪(M) ⟶ Hⁱ_𝔪(M/IⁿM)` —
is an isomorphism for `i ≤ s`, with no completeness assumption on `A`. Consequently those
canonical maps are injective from some index on, uniformly in `i ≤ s`.

This is the isomorphism assertion of [Stacks, Tag 0EFR] read at the canonical comparison rather
than at `Stacks.Algebraization.localCohomologyToAdicQuotientLimit`, and it is part (1) and part
(4) of [Stacks, Tag 0EFY] at `T = {𝔪}`.

The distinction matters, and three results combine to remove it.

* `Stacks.Algebraization.isIso_homology_localCohomologyToCompletedLocalCohomology_closedPoint`
  is the first display of the proof of [Stacks, Tag 0EFR] over an arbitrary Noetherian local
  ring; cancelling the shrinking isomorphism off it reads it at the derived `I`-adic completion
  unit itself, which is `isIso_homology_completedLocalCohomologyUnit_closedPoint` below.
* `Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite`
  presents `RΓ_𝔪(M)^∧` as a derived limit of the tower `n ↦ RΓ_𝔪(M/IⁿM)` **with its canonical
  projections**, for a finite module over a Noetherian ring. That is part (1) of
  [Stacks, Tag 0EEW] pinned to those projections.
* `Stacks.Algebraization.isIso_localCohomologyAdicQuotientToLimit` turns the two into
  invertibility of the canonical comparison, Tag 0DXJ at the canonical projections supplying the
  second leg.

## Main results

* `Stacks.Algebraization.isIso_homology_completedLocalCohomologyUnit_closedPoint` — the first
  display of [Stacks, Tag 0EFR] at the completion unit, over an arbitrary Noetherian local ring.
* `Stacks.Algebraization.isIso_localCohomologyAdicQuotientToLimit_closedPoint` — the canonical
  comparison `Hⁱ_𝔪(M) ⟶ lim Hⁱ_𝔪(M/IⁿM)` is an isomorphism for `i ≤ s`.
* `Stacks.Algebraization.exists_forall_injective_localCohomologyAdicQuotientMap_closedPoint` —
  the canonical maps `Hⁱ_𝔪(M) ⟶ Hⁱ_𝔪(M/IⁿM)` are injective for `n ≫ 0`, uniformly in `i ≤ s`.

## Implementation notes

The two main statements are parts (1) and (4) of [Stacks, Tag 0EFY] at `T = {𝔪}`. They carry no
attribute: the complete Tag 0EFY, at a general specialization-stable `T`, is
`Stacks.Algebraization.exists_bound_adicLocalCohomologyComparisons`. Neither registers
[Stacks, Tag 0EFR], which has two assertions and is registered in
`StacksFrontier/AlgebraicGeometry/Algebraization/CompletionUnitDescent.lean`;
`isIso_homology_completedLocalCohomologyUnit_closedPoint` is a step of its proof and so carries
no attribute at all.

The hypothesis `S.I ≠ ⊤` of
`Stacks.Algebraization.zeroLocus_maximalIdeal_inter` is not assumed: it follows from
`S.T = {𝔪}` and `S.T ⊆ V(S.I)`, which put the closed point in `V(S.I)`.

## References

* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

variable (S : BootstrapSituation.{u, u, u})

/-- In the bootstrap situation with `A` local and `T = {𝔪}` the ideal `I` is proper: the closed
point lies in `T ⊆ V(I)`. -/
public theorem ne_top_of_eq_closedPoint [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) :
    S.I ≠ ⊤ := by
  have hmem : closedPoint S.A ∈ PrimeSpectrum.zeroLocus (S.I : Set S.A) :=
    S.subset_adicLocus (by rw [hT]; exact rfl)
  intro htop
  rw [PrimeSpectrum.mem_zeroLocus, htop] at hmem
  exact (closedPoint S.A).asIdeal.ne_top_iff_one.mp (closedPoint S.A).2.ne_top
    (hmem (Submodule.mem_top (x := (1 : S.A))))

/-- **The first display of the proof of [Stacks, Tag 0EFR], at the completion unit, over an
arbitrary Noetherian local ring.** In the bootstrap situation with `A` local and `T = {𝔪}`, the
derived `I`-adic completion unit `RΓ_𝔪(M) ⟶ RΓ_𝔪(M)^∧` is an isomorphism on cohomology in
degrees `i ≤ s`.

This is
`Stacks.Algebraization.isIso_homology_localCohomologyToCompletedLocalCohomology_closedPoint`
with the shrinking identification — an isomorphism — cancelled off. No completeness assumption on
`A` enters, the descent of the first display along `A → A^∧` having already been carried out in
`StacksFrontier/AlgebraicGeometry/Algebraization/CompletionUnitDescent.lean`. -/
public theorem isIso_homology_completedLocalCohomologyUnit_closedPoint
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) (i : ℤ) (hi : i ≤ S.s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i).map
      (Dualizing.completedLocalCohomologyUnit S.A S.I (maximalIdeal S.A)
        S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
        (ModuleCat.of S.A S.M))) := by
  have h := isIso_homology_localCohomologyToCompletedLocalCohomology_closedPoint S hT i hi
  rw [localCohomologyToCompletedLocalCohomology_eq_unit_comp,
    Functor.map_comp] at h
  have := h
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i).map
      (completedLocalCohomologyShrinkIso S.A S.I (maximalIdeal S.A) (maximalIdeal S.A)
        S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
        (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) rfl).hom)

/-- **The canonical comparison `Hⁱ_𝔪(M) ⟶ lim Hⁱ_𝔪(M/IⁿM)` is an isomorphism for `i ≤ s`.** In
Situation [Stacks, Tag 0EFU] with `A` local and `T = {𝔪}`, with nothing assumed beyond the
situation — in particular `A` need not be `I`-adically complete.

The map is `Stacks.Algebraization.localCohomologyAdicQuotientToLimit`, the limit comparison of
the cone whose `n`-th leg is `Hⁱ_𝔪` of the quotient map `M ⟶ M/IⁿM`. This is the isomorphism
assertion of [Stacks, Tag 0EFR] read at that map, which is what a consumer reasoning about the
individual projections needs; `Stacks.Algebraization.localCohomologyToAdicQuotientLimit`, the
arrow Tag 0EFR is registered on, is instead built from an unpinned derived-limit witness.

This is also **part (4) of [Stacks, Tag 0EFY]** at `T = {𝔪}`, in the wider range `i ≤ s` that
contains that part's range `i < s`. It improves
`Stacks.Algebraization.isIso_localCohomologyToAdicQuotientLimit_of_isAdicComplete`
(`StacksFrontier/AlgebraicGeometry/Algebraization/BootstrapLocalCohomologyLimit.lean`) in two ways:
the `I`-adic completeness of `A` is not assumed, and the arrow is the canonical comparison.
The source's `T` is an arbitrary specialization-stable subset of `V(I)`; `T = {𝔪}` over a local
ring is one such. The complete [Stacks, Tag 0EFY], at a general specialization-stable `T` and with
one `m₀` for all seven parts, is
`Stacks.Algebraization.exists_bound_adicLocalCohomologyComparisons`. -/
public theorem isIso_localCohomologyAdicQuotientToLimit_closedPoint
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) (i : ℤ) (hi : i ≤ S.s) :
    IsIso (localCohomologyAdicQuotientToLimit S.A S.I (maximalIdeal S.A)
      (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) i) :=
  isIso_localCohomologyAdicQuotientToLimit S.A S.I (maximalIdeal S.A)
    (ModuleCat.of S.A S.M) (zeroLocus_maximalIdeal_inter (ne_top_of_eq_closedPoint S hT)) i
    (isIso_homology_completedLocalCohomologyUnit_closedPoint S hT i hi)

/-- **Part (6) of [Stacks, Tag 0EFY] at `T = {𝔪}`.** In Situation [Stacks, Tag 0EFU] with `A`
local and `T = {𝔪}`, the canonical map `Hˢ_𝔪(M) ⟶ lim Hˢ_𝔪(M/IⁿM)` is injective, and every
element of `I^{m₀}` carries an element of the limit into its image — that is, the cokernel is
killed by `I^{m₀}`, for every `m₀` whatsoever.

The part is immediate from `isIso_localCohomologyAdicQuotientToLimit_closedPoint` read in degree
exactly `s`, which is inside the range `i ≤ s` of that theorem: the comparison is then an
isomorphism, hence injective and surjective, so the cokernel is zero and `m₀` plays no role. The
source asserts the two halves separately because at a general specialization-stable `T` the
comparison in the top degree `s` need not be surjective; what makes the top degree accessible
here is that `T = {𝔪}` puts it inside the range of [Stacks, Tag 0EFR]. -/
public theorem injective_and_smul_mem_range_localCohomologyAdicQuotientToLimit_closedPoint
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) (m₀ : ℕ) :
    Function.Injective (localCohomologyAdicQuotientToLimit S.A S.I (maximalIdeal S.A)
        (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) S.s).hom ∧
      ∀ a ∈ S.I ^ m₀, ∀ y, ∃ x, (localCohomologyAdicQuotientToLimit S.A S.I (maximalIdeal S.A)
        (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) S.s).hom x = a • y := by
  have := isIso_localCohomologyAdicQuotientToLimit_closedPoint S hT S.s le_rfl
  have hbij := ConcreteCategory.bijective_of_isIso
    (localCohomologyAdicQuotientToLimit S.A S.I (maximalIdeal S.A)
      (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) S.s)
  exact ⟨hbij.1, fun a _ y => hbij.2 (a • y)⟩

/-- **Part (1) of [Stacks, Tag 0EFY] at `T = {𝔪}`, with nothing assumed beyond Situation
[Stacks, Tag 0EFU].** There is an integer `m₀` such that the canonical map
`Hⁱ_𝔪(M) ⟶ Hⁱ_𝔪(M/IⁿM)` is injective for every `i ≤ s` and every `n ≥ m₀`.

The kernels of the canonical maps form a descending chain in the Artinian module `Hⁱ_𝔪(M)` whose
intersection is the kernel of the canonical comparison to the limit, and that comparison is
injective by `isIso_localCohomologyAdicQuotientToLimit_closedPoint`; so the chain reaches `0`.
The pinned derived-limit presentation that argument consumes is
`Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite`.

This improves
`exists_forall_injective_homology_localCohomologyAdicQuotientMap_of_eq_closedPoint` of
`StacksFrontier/AlgebraicGeometry/Algebraization/BootstrapAdicProjectionInjectivity.lean` by
dropping both its `[IsAdicComplete]` instance and its `hproj` hypothesis.

The source's `T` is an arbitrary specialization-stable subset of `V(I)`; `T = {𝔪}` over a local
ring is one such. The complete [Stacks, Tag 0EFY], at a general specialization-stable `T` and with
one `m₀` for all seven parts, is
`Stacks.Algebraization.exists_bound_adicLocalCohomologyComparisons`. -/
public theorem exists_forall_injective_localCohomologyAdicQuotientMap_closedPoint
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) :
    ∃ m₀ : ℕ, ∀ i : ℤ, i ≤ S.s → ∀ n : ℕ, m₀ ≤ n →
      Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i).map
        (Dualizing.localCohomologyAdicQuotientMap S.A S.I (maximalIdeal S.A)
          (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) n)).hom :=
  Stacks.LocalCohomology.exists_forall_injective_homology_localCohomologyAdicQuotientMap
    S.A S.I (ModuleCat.of S.A S.M) S.s _ _
    (Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite
      S.A S.I (maximalIdeal S.A) S.I.fg_of_isNoetherianRing
      (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M))
    (Dualizing.completedLocalCohomologyUnit S.A S.I (maximalIdeal S.A)
      S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M))
    (Dualizing.completedLocalCohomologyUnit_comp_projection S.A S.I (maximalIdeal S.A)
      S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M))
    (isIso_homology_completedLocalCohomologyUnit_closedPoint S hT)

end Stacks.Algebraization

end
