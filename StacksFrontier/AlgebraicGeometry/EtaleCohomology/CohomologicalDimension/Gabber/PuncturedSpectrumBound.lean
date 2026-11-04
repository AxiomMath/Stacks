module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBound
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs

/-!
# The vanishing bound on the punctured spectrum of a strictly local ring

Travaux de Gabber, Exposé XVIII-A, Theorem 1.1 (Lemma 2.1 there): for a strictly henselian
Noetherian local ring `A` of dimension `d ≥ 1` and an integer `n` invertible in `A`, the punctured
spectrum `U = Spec A ∖ {𝔪}` has `H^q(U, 𝓕) = 0` for every abelian sheaf `𝓕` on `U_ét` killed by
`n` and every `q > 2d - 1`. This file only *states* that bound, as the proposition
`AlgebraicGeometry.Scheme.PuncturedSpectrumVanishingBound n`; it is the local input from which
Exposé XVIII-A, Lemma 2.2 (`AlgebraicGeometry.Scheme.LocalToGlobalVanishingBound`) is deduced by
dévissage.

## Main definitions

* `AlgebraicGeometry.Scheme.PuncturedSpectrumVanishingBound`: the bound `2d - 1` for the
  punctured spectra (`Stacks.puncturedSpectrum`) of strictly henselian Noetherian local rings of
  dimension `d ≥ 1`.

## References

* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Theorem 1.1 and Lemma 2.1, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **Exposé XVIII-A, Theorem 1.1 / Lemma 2.1, for coefficients killed by `n`.** For every
strictly henselian Noetherian local ring `A` of dimension `d ≥ 1` in which `n` is invertible,
the punctured spectrum `Spec A ∖ {𝔪}` has étale cohomology with coefficients killed by `n`
vanishing in degrees above `2d - 1`. -/
def PuncturedSpectrumVanishingBound (n : ℕ) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [StrictlyHenselianLocalRing A] (d : ℕ),
    ringKrullDim A = d → 0 < d → IsUnit (n : A) →
      IsTorsionVanishingBound (Stacks.puncturedSpectrum A).toScheme n ((2 * d - 1 : ℕ) : WithBot ℕ∞)

end AlgebraicGeometry.Scheme

end
