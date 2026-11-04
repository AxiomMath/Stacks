module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteGabberFractionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.GermKillingSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.GermKillingOfPointwise
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannLerayKilling
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ProperModelRefinementsCofiltered
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ValuationGermDeath

/-!
# Stacks 0DC6 from Gabber's Zariski–Riemann argument

The vanishing above `d_V` of Stacks 0DC6, `GabberVanishing S n`, for every base `S` of 0DC6 and
every `n` invertible on `S`, from the three inputs of Gabber's Zariski–Riemann proof of Travaux
de Gabber, Exposé XVIII-A, Corollary 1.2 (the last remark of §2 there):

* `AlgebraicGeometry.Scheme.ZariskiRiemann.GermKilling n`: germs of `R^q j_* F` on the closed
  fibre of a proper model die on a refinement away from the points of small transcendence degree;
* `AlgebraicGeometry.Scheme.ZariskiRiemann.RefinementsCofiltered B`: two refinements of a proper
  model have a common refinement;
* `AlgebraicGeometry.Scheme.ZariskiRiemann.LerayKilling B`: the Leray spectral sequence of
  `j : Spec (Frac B) ⟶ Y`, in the colimit over the proper models `Y`.

Corollary 1.2 then gives Lemma 2.1 by induction on the dimension
(`AlgebraicGeometry.Scheme.puncturedSpectrumVanishingBound_of_fractionFieldVanishingBound`), and so
`GabberVanishing S n`.

## Main results

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_zariskiRiemann`
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_pointwiseGermDeath`: the
  same with the Leray step proved (`AlgebraicGeometry.Scheme.ZariskiRiemann.lerayKilling`) and germ
  killing in its pointwise form (`AlgebraicGeometry.Scheme.ZariskiRiemann.PointwiseGermDeath`).
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_centeredGermDeath`: the
  same with cofilteredness proved (`AlgebraicGeometry.Scheme.ZariskiRiemann.refinementsCofiltered`)
  and germ killing at the centres of valuations
  (`AlgebraicGeometry.Scheme.ZariskiRiemann.CenteredGermDeath`).

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

open ZariskiRiemann in
/-- **The vanishing above `d_V` of Stacks 0DC6 from Gabber's Zariski–Riemann argument.** For
every base `S` of Stacks 0DC6 and every `n` invertible on `S`, germ killing on the proper models,
cofilteredness of their refinements and the Leray step give `GabberVanishing S n`. -/
theorem gabberVanishing_of_zariskiRiemann {S : Scheme.{u}}
    (hS : IsUnboundedDescentEtaleBase S) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    (hgerm : GermKilling.{u} n)
    (hcof : ∀ (B : Type u) [CommRing B] [IsDomain B], RefinementsCofiltered B)
    (hL : ∀ (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
      [StrictlyHenselianLocalRing B], LerayKilling B) :
    GabberVanishing S n :=
  gabberVanishing_of_fractionFieldVanishingBound hS hn
    (fractionFieldVanishingBound_of_zariskiRiemannKilling
      (zariskiRiemannKilling_of_germKilling hcof hgerm) hL)

open ZariskiRiemann in
/-- **The vanishing above `d_V` of Stacks 0DC6 from pointwise germ death.** For every base `S` of
Stacks 0DC6 and every `n` invertible on `S`, pointwise germ death on the proper models and
cofilteredness of their refinements give `GabberVanishing S n`; the Leray step is
`AlgebraicGeometry.Scheme.ZariskiRiemann.lerayKilling`. -/
theorem gabberVanishing_of_pointwiseGermDeath {S : Scheme.{u}}
    (hS : IsUnboundedDescentEtaleBase S) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    (hgerm : PointwiseGermDeath.{u} n)
    (hcof : ∀ (B : Type u) [CommRing B] [IsDomain B], RefinementsCofiltered B) :
    GabberVanishing S n :=
  gabberVanishing_of_fractionFieldVanishingBound hS hn
    (fractionFieldVanishingBound_of_pointwiseGermDeath hcof (fun _ _ _ _ _ => lerayKilling)
      hgerm)

open ZariskiRiemann in
/-- **The vanishing above `d_V` of Stacks 0DC6 from germ killing at the centres of
valuations.** For every base `S` of Stacks 0DC6 and every `n` invertible on `S`,
`AlgebraicGeometry.Scheme.ZariskiRiemann.CenteredGermDeath n` gives `GabberVanishing S n`; the
Leray step and the cofilteredness of the proper models are proved. -/
theorem gabberVanishing_of_centeredGermDeath {S : Scheme.{u}}
    (hS : IsUnboundedDescentEtaleBase S) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    (h : CenteredGermDeath.{u} n) : GabberVanishing S n :=
  gabberVanishing_of_pointwiseGermDeath hS hn (pointwiseGermDeath_of_centeredGermDeath h)
    fun B _ _ => refinementsCofiltered B

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
