module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimitCone
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimitLocal

/-!
# Essential constancy at the closed point of a local bootstrap situation

In the bootstrap situation of [Stacks, Tag 0EFU] with `A` local and `T = {𝔪}`, the canonical cone
`Hⁱ_𝔪(M) → {Hⁱ_𝔪(M/IⁿM)}` is a limit cone for every `i ≤ s` ([Stacks, Tag 0EFR]), and so the
system is essentially constant with value `Hⁱ_𝔪(M)`: the terms are Artinian, hence the system is
Mittag-Leffler and the projections are eventually injective.

The complete case is `Stacks.Algebraization.nonempty_isLimit_cone_of_isAdicComplete`; the general
local case descends from the `I`-adic completion by
`Stacks.Algebraization.nonempty_isLimit_cone_of_eq_closedPoint_of_complete`.

## Main results

* `Stacks.Algebraization.nonempty_isLimit_cone_of_eq_closedPoint` — Stacks 0EFR in cone form.
* `Stacks.Algebraization.exists_isEssentiallyConstantWith_of_eq_closedPoint` — the essential
  constancy at the closed point, in every degree `i ≤ s`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u w

namespace Stacks.Algebraization

/-- **Stacks Tag 0EFR, in cone form.** In the bootstrap situation with `A` local and `T = {𝔪}`,
for `i ≤ s` the maps `Hⁱ_𝔪(M) → Hⁱ_𝔪(M/IⁿM)` exhibit `Hⁱ_𝔪(M)` as `lim Hⁱ_𝔪(M/IⁿM)`. -/
theorem nonempty_isLimit_cone_of_eq_closedPoint (S : BootstrapSituation.{u, u, w})
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) (i : ℤ) (hi : i ≤ S.s) :
    Nonempty (IsLimit (Stacks.LocalCohomology.Bootstrap.cone.{u, u} S i)) :=
  nonempty_isLimit_cone_of_eq_closedPoint_of_complete
    (fun S' _ _ hT' i hi ↦ nonempty_isLimit_cone_of_isAdicComplete S' hT' i hi) S hT i hi

/-- **Essential constancy at the closed point.** In the bootstrap situation with `A` local and
`T = {𝔪}`, for every `i ≤ s` the system `{Hⁱ_𝔪(M/IⁿM)}` is essentially constant with value
`Hⁱ_𝔪(M)`. In negative degrees every module vanishes; otherwise the limit identification of
Stacks 0EFR and the Artinianness of local cohomology at `𝔪` of finite modules give it. -/
theorem exists_isEssentiallyConstantWith_of_eq_closedPoint (S : BootstrapSituation.{u, u, w})
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) (i : ℤ) (hi : i ≤ S.s) :
    ∃ (j : ℕᵒᵖ) (σ : (Stacks.LocalCohomology.Bootstrap.tower.{u, u} S i).obj j ⟶
        (Stacks.LocalCohomology.Bootstrap.cone.{u, u} S i).pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith
        (Stacks.LocalCohomology.Bootstrap.tower.{u, u} S i)
        (Stacks.LocalCohomology.Bootstrap.cone.{u, u} S i) j σ := by
  obtain ⟨hlim⟩ := nonempty_isLimit_cone_of_eq_closedPoint S hT i hi
  exact Stacks.LocalCohomology.Bootstrap.isEssentiallyConstantWith_of_eq_closedPoint_of_isLimit
    S i hT hlim

end Stacks.Algebraization
