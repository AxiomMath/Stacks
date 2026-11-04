module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteGabberLocalReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.PuncturedSpectrumOfFractionField

/-!
# Stacks 0DC6 reduced to Corollary 1.2 of Gabber's theorem

Travaux de Gabber, Exposé XVIII-A, Lemma 2.1 (the punctured bound,
`AlgebraicGeometry.Scheme.PuncturedSpectrumVanishingBound`) follows from Corollary 1.2 there
(`AlgebraicGeometry.Scheme.FractionFieldVanishingBound`) by induction on the dimension
(`AlgebraicGeometry.Scheme.puncturedSpectrumVanishingBound_of_fractionFieldVanishingBound`).
So the reduction of Stacks 0DC6 to the two local bounds
(`Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_puncturedSpectrum_of_fractionField`)
needs Corollary 1.2 alone: for every base `S` of Stacks 0DC6 and every `n` invertible on `S`,
`FractionFieldVanishingBound n` gives `GabberVanishing S n`.

## Main results

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_fractionFieldVanishingBound`:
  `GabberVanishing S n` from Corollary 1.2, for every base of Stacks 0DC6.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Corollary 1.2 and Lemma 2.1, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Cohomology.CohomologicalDescent

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

/-- **The vanishing above `d_V` of Stacks 0DC6 from Corollary 1.2 of Gabber's theorem.** For
every base `S` of Stacks 0DC6 and every `n` invertible on `S`, Travaux de Gabber, Exposé XVIII-A,
Corollary 1.2 (`FractionFieldVanishingBound n`) gives `GabberVanishing S n`: it implies the
punctured bound of Lemma 2.1 by induction on the dimension. -/
theorem gabberVanishing_of_fractionFieldVanishingBound {S : Scheme.{u}}
    (hS : IsUnboundedDescentEtaleBase S) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    (h : FractionFieldVanishingBound.{u} n) : GabberVanishing S n :=
  gabberVanishing_of_puncturedSpectrum_of_fractionField hS hn
    (puncturedSpectrumVanishingBound_of_fractionFieldVanishingBound h) h

/-- **Stacks 0DC6 from Corollary 1.2 of Gabber's theorem.** For every base `S` of Stacks
0DC6 and every finite ring `Λ` whose order is invertible on `S`, Travaux de Gabber, Exposé XVIII-A,
Corollary 1.2 (`FractionFieldVanishingBound |Λ|`) gives the conditions (1), (2), (3) of Stacks 0DC1
for the family of all sheaves of `Λ`-modules on the slices of the ringed site of schemes locally of
finite type over `S`, with `B` the quasi-compact objects, `d_V` the bound of the example and `Cov_V`
the étale coverings by quasi-compact objects. Corollary 1.2 is proved
(`AlgebraicGeometry.Scheme.ZariskiRiemann.fractionFieldVanishingBound`), and Stacks 0DC6 is
`localSerre`. -/
theorem localSerre_of_fractionFieldVanishingBound (Λ : Type u) [CommRing Λ] [Finite Λ]
    {S : Scheme.{u}} (hS : IsUnboundedDescentEtaleBase S) (hn : IsUnit (Nat.card Λ : Γ(S, ⊤)))
    (h : FractionFieldVanishingBound.{u} (Nat.card Λ)) :
    (∀ U, (allModules S Λ U).IsWeakSerreClass) ∧
      IsStableUnderRestriction (ringedSite S Λ) (allModules S Λ) ∧
      IsLocalOnCoverings (ringedSite S Λ) (allModules S Λ) ∧
      ∃ b : LocalCohomologicalBound (ringedSite S Λ) (allModules S Λ),
        b.B = {V | IsQuasiCompact ((liftedEquiv S).inverse.obj V)} ∧
        (∀ V hV, ∃ d : ℕ, b.degreeBound V hV = d ∧
          ((liftedEquiv S).inverse.obj V).obj.hom.etaleCohomologyBound = d) ∧
        ∀ V hV (𝒰 : PreZeroHypercover.{u + 1} V),
          (b.coverings V hV).cov 𝒰 ↔ IsQuasiCompactEtaleCovering 𝒰 :=
  localSerre_of_gabberVanishing Λ hS (gabberVanishing_of_fractionFieldVanishingBound hS hn h)

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
