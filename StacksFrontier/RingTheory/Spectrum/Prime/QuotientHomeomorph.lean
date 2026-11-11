module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCore.Tactic.StacksAttribute

/-!
# `Spec (R ⧸ I)` is homeomorphic to `V(I)`

The quotient map `R → R ⧸ I` induces, via `PrimeSpectrum.comap`, a homeomorphism
`Spec (R ⧸ I) ≃ₜ V(I)` whose inverse sends `𝔭` to `𝔭 / I` (Stacks 00E5).
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- **Stacks 00E5**: the quotient map `R → R ⧸ I` induces, via `PrimeSpectrum.comap`, a
homeomorphism `Spec (R ⧸ I) ≃ₜ V(I)`. The forward map is `comap (Ideal.Quotient.mk I)`
(`Ideal.coe_primeSpectrumQuotientHomeomorphZeroLocus_apply`), and the inverse sends `𝔭` to
`𝔭 / I = 𝔭.map (Ideal.Quotient.mk I)`
(`Ideal.primeSpectrumQuotientHomeomorphZeroLocus_symm_apply`).

The underlying bijection is Mathlib's `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`; it is a
homeomorphism because `comap (Ideal.Quotient.mk I)` is an embedding
(`PrimeSpectrum.isEmbedding_comap_of_surjective`). -/
@[stacks 00E5]
noncomputable def primeSpectrumQuotientHomeomorphZeroLocus :
    PrimeSpectrum (R ⧸ I) ≃ₜ PrimeSpectrum.zeroLocus (R := R) I :=
  I.primeSpectrumQuotientOrderIsoZeroLocus.toEquiv.toHomeomorphOfIsInducing <| by
    refine (Topology.IsEmbedding.subtypeVal.of_comp_iff.mp ?_).isInducing
    exact PrimeSpectrum.isEmbedding_comap_of_surjective _ (Quotient.mk I) Quotient.mk_surjective

/-- **Stacks 00E5**, the forward map: the homeomorphism `Spec (R ⧸ I) ≃ₜ V(I)` is induced by the
quotient map `R → R ⧸ I` via the functoriality of `Spec`. -/
@[stacks 00E5 "the map is `comap` of the quotient map", simp]
theorem coe_primeSpectrumQuotientHomeomorphZeroLocus_apply (p : PrimeSpectrum (R ⧸ I)) :
    (I.primeSpectrumQuotientHomeomorphZeroLocus p : PrimeSpectrum R) =
      PrimeSpectrum.comap (Quotient.mk I) p :=
  rfl

/-- **Stacks 00E5**, the inverse: the inverse of `Spec (R ⧸ I) ≃ₜ V(I)` sends `𝔭 ⊇ I` to
`𝔭 / I`, the image of `𝔭` in `R ⧸ I`. -/
@[stacks 00E5 "the inverse is `𝔭 ↦ 𝔭 / I`", simp]
theorem primeSpectrumQuotientHomeomorphZeroLocus_symm_apply
    (p : PrimeSpectrum.zeroLocus (R := R) I) :
    (I.primeSpectrumQuotientHomeomorphZeroLocus.symm p).asIdeal =
      p.1.asIdeal.map (Quotient.mk I) := by
  obtain ⟨⟨p, _⟩, _⟩ := p
  rfl

end Ideal

end
