module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteGabberCenterLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenterLimitGermDeathUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.StrictlyLocalOpensVanishingBound

/-!
# Stacks 0DC6 and Gabber's theorem on cohomological dimension

The Zariski–Riemann proof of Travaux de Gabber, Exposé XVIII-A, Corollary 1.2 (the last remark of
§2 there) is complete: germ death in the limit of the proper models
(`AlgebraicGeometry.Scheme.ZariskiRiemann.centerLimitGermDeath`) gives germ death at valuation rings, at the centres of small rank and
pointwise on the proper models, and with the cofilteredness of the refinements, the stalk
cocycle and the Leray step, Corollary 1.2 (`FractionFieldVanishingBound n` for every `n`). This
file draws the consequences: Theorem 1.1 of the exposé, the vanishing above `d_V` of Stacks 0DC6,
and Stacks 0DC6 itself, for all four types of base, with no hypothesis beyond the source's.

## Main results

All names are in the namespace `AlgebraicGeometry`.

* `Scheme.ZariskiRiemann.fractionFieldVanishingBound`: Exposé XVIII-A, Corollary 1.2.
* `Scheme.ZariskiRiemann.isTorsionVanishingBound_opens_spec`: Exposé XVIII-A, Theorem 1.1.
* `Scheme.LocallyFiniteTypeEtale.gabberVanishing`: the vanishing above `d_V` of Stacks 0DC6.
* `Scheme.LocallyFiniteTypeEtale.etaleVanishingAboveBound_of_isUnboundedDescentEtaleBase`: the
  same bound on the members of the coverings in `Cov_V`.
* `Scheme.LocallyFiniteTypeEtale.localSerre`: **Stacks 0DC6**, all four types.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Theorem 1.1, Corollary 1.2 and the last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Cohomology.CohomologicalDescent

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

/-- **Exposé XVIII-A, Corollary 1.2** (Gabber): for every `n`, the fraction field of a strictly
henselian Noetherian local domain of dimension `e ≥ 1` in which `n` is invertible has
`cd_n ≤ 2e - 1`. Germ death in the limit of the proper models gives germ death at valuation
rings, at the centres of small rank and pointwise on the proper models; the cofilteredness of the
refinements, the stalk cocycle and the Leray step are proved. -/
theorem fractionFieldVanishingBound (n : ℕ) : FractionFieldVanishingBound.{u} n :=
  fractionFieldVanishingBound_of_pointwiseGermDeath (fun B _ _ => refinementsCofiltered B)
    (fun _ _ _ _ _ => lerayKilling)
    (pointwiseGermDeath_of_centeredGermDeath
      (centeredGermDeath_of_valuationGermDeath_of_stable
        (valuationGermDeath_of_centerLimitGermDeath centerLimitGermDeath n)
        deadAtStableUnderRefinement))

/-- **Exposé XVIII-A, Theorem 1.1** (Gabber), for coefficients killed by `n`. Let `A` be a
strictly henselian Noetherian local ring of dimension `d` with `n` invertible in `A`, and `U` any
open of `Spec A`. Then `cd_n(U) ≤ 2d - 1` (read in `ℕ`, so `0` when `d = 0`). -/
theorem isTorsionVanishingBound_opens_spec {n : ℕ} (A : Type u) [CommRing A] [IsNoetherianRing A]
    [StrictlyHenselianLocalRing A] {d : ℕ} (hd : ringKrullDim A = d) (hn : IsUnit (n : A))
    (U : (Spec (.of A)).Opens) :
    IsTorsionVanishingBound U.toScheme n ((2 * d - 1 : ℕ) : WithBot ℕ∞) :=
  isTorsionVanishingBound_opens_spec_of_fractionFieldVanishingBound
    (fractionFieldVanishingBound n) A hd hn U

end AlgebraicGeometry.Scheme.ZariskiRiemann

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

open ZariskiRiemann

variable {S : Scheme.{u}}

/-- **The vanishing above `d_V` of Stacks 0DC6** (Gabber's theorem on cohomological dimension, as
the source uses it). For every base `S` of Stacks 0DC6 and every `n` invertible on `S`,
`GabberVanishing S n`. -/
theorem gabberVanishing (hS : IsUnboundedDescentEtaleBase S) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) : GabberVanishing S n :=
  gabberVanishing_of_centerLimitGermDeath' hS hn centerLimitGermDeath

/-- **The vanishing above `d_V` on the members of the coverings in `Cov_V`.** For every base `S`
of Stacks 0DC6 and every `n` invertible on `S`, `EtaleVanishingAboveBound S n`. -/
theorem etaleVanishingAboveBound_of_isUnboundedDescentEtaleBase
    (hS : IsUnboundedDescentEtaleBase S) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) :
    EtaleVanishingAboveBound S n :=
  have : IsLocallyNoetherian S := hS.isLocallyNoetherian_and_nonempty_and_ne_top.1
  etaleVanishingAboveBound_of_gabberVanishing (gabberVanishing hS hn)

/-- **Stacks 0DC6.** Let `S` be the spectrum of a finite field, of a separably closed field, of a
strictly henselian Noetherian local ring, or of a henselian Noetherian local ring with finite
residue field, and let `Λ` be a finite ring whose order is invertible on `S`. On the ringed site
`(C, Λ)` of schemes locally of finite type over `S`, the family `A_U` of all sheaves of
`Λ`-modules satisfies conditions (1), (2), (3) of Stacks 0DC1, with `B` the quasi-compact
objects, `d_V = 1 + 2 dim(S) + sup_{v ∈ V} (trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{V, v})` and `Cov_V`
the étale coverings of `V` by quasi-compact objects. -/
@[stacks 0DC6 "all four types"]
theorem localSerre (Λ : Type u) [CommRing Λ] [Finite Λ]
    (hS : IsUnboundedDescentEtaleBase S) (hn : IsUnit (Nat.card Λ : Γ(S, ⊤))) :
    (∀ U, (allModules S Λ U).IsWeakSerreClass) ∧
      IsStableUnderRestriction (ringedSite S Λ) (allModules S Λ) ∧
      IsLocalOnCoverings (ringedSite S Λ) (allModules S Λ) ∧
      ∃ b : LocalCohomologicalBound (ringedSite S Λ) (allModules S Λ),
        b.B = {V | IsQuasiCompact ((liftedEquiv S).inverse.obj V)} ∧
        (∀ V hV, ∃ d : ℕ, b.degreeBound V hV = d ∧
          ((liftedEquiv S).inverse.obj V).obj.hom.etaleCohomologyBound = d) ∧
        ∀ V hV (𝒰 : PreZeroHypercover.{u + 1} V),
          (b.coverings V hV).cov 𝒰 ↔ IsQuasiCompactEtaleCovering 𝒰 :=
  localSerre_of_gabberVanishing Λ hS (gabberVanishing hS hn)

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
