module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.LocalSectionsAtPointProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.PuncturedStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteGabberReduction

/-!
# Stacks 0DC6 reduced to Gabber's two local bounds

Travaux de Gabber, Exposé XVIII-A, Lemma 2.2
(`AlgebraicGeometry.Scheme.LocalToGlobalVanishingBound`) follows from the local bound of
Theorem 1.1 / Lemma 2.1 there
(`AlgebraicGeometry.Scheme.PuncturedSpectrumVanishingBound`: the punctured spectrum of a
strictly henselian Noetherian local ring of dimension `d ≥ 1` has `cd_n ≤ 2d - 1`), by the
dévissage of `AlgebraicGeometry.Scheme.localToGlobalVanishingBound_of_localInputs`: its punctured
input is `puncturedStalkVanishing_of_puncturedSpectrumVanishingBound` and its local-sections input
is `localSectionsAtPoint`, which holds outright.

Hence, for every base `S` of Stacks 0DC6 and every `n` invertible on `S`, the vanishing
`GabberVanishing S n` follows from Theorem 1.1 and Corollary 1.2 of Exposé XVIII-A
(`PuncturedSpectrumVanishingBound n` and `FractionFieldVanishingBound n`), the two statements of
Gabber's theorem that remain unproved in this library.

## Main results

* `AlgebraicGeometry.Scheme.localToGlobalVanishingBound_of_puncturedSpectrumVanishingBound`:
  Lemma 2.2 from Theorem 1.1.
* `Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_puncturedSpectrum_of_fractionField`:
  `GabberVanishing S n` from Theorem 1.1 and Corollary 1.2, for every base of Stacks 0DC6.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **Travaux de Gabber, Exposé XVIII-A, Lemma 2.2, from Theorem 1.1**, for coefficients killed by
`n`: the bound `2d - 1` on the punctured spectra of strictly henselian Noetherian local rings
gives, on every Noetherian scheme `X` on which `n` is invertible, the bound
`sup_x (c(x) + 2 dim 𝒪_{X,x})` from bounds `c(x)` for the residue fields. -/
theorem localToGlobalVanishingBound_of_puncturedSpectrumVanishingBound {n : ℕ}
    (h : PuncturedSpectrumVanishingBound.{u} n) : LocalToGlobalVanishingBound.{u} n :=
  localToGlobalVanishingBound_of_localInputs
    (puncturedStalkVanishing_of_puncturedSpectrumVanishingBound h) (localSectionsAtPoint n)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

/-- **The vanishing above `d_V` of Stacks 0DC6 from Gabber's two local bounds.** For every base
`S` of Stacks 0DC6 and every `n` invertible on `S`, Travaux de Gabber, Exposé XVIII-A,
Theorem 1.1 (`PuncturedSpectrumVanishingBound n`) and Corollary 1.2
(`FractionFieldVanishingBound n`) give `GabberVanishing S n`. -/
theorem gabberVanishing_of_puncturedSpectrum_of_fractionField {S : Scheme.{u}}
    (hS : IsUnboundedDescentEtaleBase S) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    (h₁ : PuncturedSpectrumVanishingBound.{u} n) (h₃ : FractionFieldVanishingBound.{u} n) :
    GabberVanishing S n :=
  gabberVanishing_of_localToGlobal_of_fractionField hS hn
    (localToGlobalVanishingBound_of_puncturedSpectrumVanishingBound h₁) h₃

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
