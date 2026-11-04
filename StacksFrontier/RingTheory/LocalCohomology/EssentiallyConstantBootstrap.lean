module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapUniformPrimes
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantFromProZero
public import StacksFrontier.RingTheory.LocalCohomology.LocalDualityTransfer.PerPrime

/-!
# Theorem 0EIE: essential constancy of the local cohomology of the adic quotients

In Situation [Stacks, Tag 0EFU] (`Stacks.Algebraization.BootstrapSituation`), for every `i ≤ s`
the inverse system `{H^i_T(M/IⁿM)}_{n ≥ 0}` is essentially constant with value `H^i_T(M)`; in
particular it is Mittag-Leffler, `H^i_T(M)` is annihilated by a power of `I`, and
`H^i_T(M) = lim H^i_T(M/IⁿM)` ([Stacks, Tag 0EIE]).

## Proof

The source deduces the theorem from Lemma [Stacks, Tag 0EFX] — the inverse systems
`{H^i_T(IⁿM)}` are pro-zero for `i ≤ s`, and the stable images in degree `s + 1` inject into
`H^{s+1}_T(I^{m₀}M)` — applied to `M` and to an auxiliary module `Q`:
`Stacks.LocalCohomology.Bootstrap.exists_isEssentiallyConstantWith_of_proZero`.

Lemma 0EFX is `Stacks.Algebraization.proZero_and_eventually_injective_of_perPrimeDualityTransfer`:
per prime `𝔮 ∈ T` the assertions hold by Stacks 0EFR at the closed point of `A_𝔮` (in cone form,
`Stacks.Algebraization.nonempty_isLimit_cone_of_isAdicComplete` and its descent), they are made
uniform in `𝔮` by local duality natural in the module
(`Stacks.LocalCohomology.LocalDualityTransfer.perPrimeDualityTransfer`) together with the
stabilization of kernels in the finite modules `Extʲ_A(IⁿM, ω)`, and they are globalized by
Stacks 0EF9 and 0EFA.

The three consequences follow from essential constancy:
`Stacks.LocalCohomology.Bootstrap.isMittagLeffler`, `exists_pow_smul_eq_zero` and `isLimit`.

## Main results

* `Stacks.LocalCohomology.Bootstrap.essentiallyConstant_and_consequences` — Stacks 0EIE.

## Implementation notes

The module of the situation is taken in the universe of its ring (`BootstrapSituation.{u, u, w}`),
the universe in which the local duality and completion results this rests on are available.

## References

* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.LocalCohomology.Bootstrap

open Stacks.Algebraization

/-- **Stacks Project, Tag 0EIE.** In Situation 0EFU, for `i ≤ s` the inverse system
`{H^i_T(M/IⁿM)}_{n ≥ 0}` is essentially constant with value `H^i_T(M)` (with respect to the cone
of the maps `H^i_T(M) → H^i_T(M/IⁿM)` induced by the quotient maps). In particular it is
Mittag-Leffler, `H^i_T(M)` is annihilated by a power of `I`, and the canonical maps exhibit
`H^i_T(M)` as `lim H^i_T(M/IⁿM)`. -/
@[stacks 0EIE]
theorem essentiallyConstant_and_consequences (S : BootstrapSituation.{u, u, w}) (i : ℤ)
    (hi : i ≤ S.s) :
    (∃ (j : ℕᵒᵖ) (σ : (tower.{u, u} S i).obj j ⟶ (cone.{u, u} S i).pt),
        EssentiallyConstantPro.IsEssentiallyConstantWith (tower.{u, u} S i) (cone.{u, u} S i)
          j σ) ∧
      IsMittagLefflerCategorical (tower.{u, u} S i) ∧
      (∃ n : ℕ, ∀ a ∈ S.I ^ n,
        ∀ x : (localCohomologyWithSupportInModuleFunctor.{u, u} S.A S.T i).obj
          (ModuleCat.of S.A S.M), a • x = 0) ∧
      Nonempty (IsLimit (cone.{u, u} S i)) := by
  have hX := proZero_and_eventually_injective_of_perPrimeDualityTransfer.{u, w}
    (fun B _ _ ω hω ↦ LocalDualityTransfer.perPrimeDualityTransfer ω hω)
  obtain ⟨j, σ, h⟩ := exists_isEssentiallyConstantWith_of_proZero hX.1 hX.2 S i hi
  exact ⟨⟨j, σ, h⟩, isMittagLeffler S i hi h, exists_pow_smul_eq_zero S i hi h,
    ⟨isLimit S i hi h⟩⟩

end Stacks.LocalCohomology.Bootstrap
