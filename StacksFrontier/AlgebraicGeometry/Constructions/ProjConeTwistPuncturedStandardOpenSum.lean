module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedGlobalMap
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedPushforward

/-!
# The summands of the standard-open decomposition of the functions on the punctured cone

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}` and let `U ⊆ L` be the punctured cone.
Over a standard open `D₊(f)` of a positive-degree homogeneous element,
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSectionsEquivTwistSections` writes

  `Γ(D₊(f), (π|_U)_* 𝒪_U) = ⨁_{m ∈ ℤ} Γ(D₊(f), 𝒪_P(m))`,

which is the footnote computation of [Stacks, Tag 0EKG] over one standard open. This file
identifies the `m`-th summand of that decomposition with the local degreewise inclusion
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistApp`, so that the decomposition becomes
a statement about the morphism of sheaves of `𝒪_P`-modules glued in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjConeTwistPuncturedGlobalMap.lean`.

It is the punctured analogue of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjConeTwistStandardOpenSum.lean`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSectionsRingEquiv_symm_of`: the
  `m`-th summand of the ring isomorphism
  `Γ(D₊(f), (π|_U)_* 𝒪_U) ≃+* ⨁_{m ∈ ℤ} (A[1/f])_m`, read backwards.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSectionsEquivTwistSections_symm_of`:
  **the `m`-th summand of the standard-open decomposition
  `Γ(D₊(f), (π|_U)_* 𝒪_U) = ⨁_{m ∈ ℤ} Γ(D₊(f), 𝒪_P(m))` is the local degreewise inclusion.**

## Implementation notes

The proof is the nonnegative one with the chart `D₊(ψ f)` of `L` replaced by the chart
`D₊(σ f · ψ f)` of `U`, and the transport along `π⁻¹(D₊(f)) = D₊(ψ f)` replaced by the
restriction `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedChartRestrict` along the open
immersion of `U`. That restriction is itself an `eqToHom`, by
`Stacks.AlgebraicGeometry.ProjConeTwist.openUInL_ι_appLE_eq_eqToHom`, which is what makes the two
descriptions of the summand agree on the nose.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open DirectSum
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A}

/-- **The `m`-th summand of the ring isomorphism
`Γ(D₊(f), (π|_U)_* 𝒪_U) ≃+* ⨁_{m ∈ ℤ} (A[1/f])_m`.** Read backwards, a degree-`m` element `y` of
`(B[1/σ f · ψ f])₀` placed in the `m`-th summand is `y` itself, read as a function on
`D₊(σ f · ψ f)` through the identification of [Stacks, Tag 01M6] and restricted to the chart of
`U` over `D₊(f)`. -/
@[stacks 0EKG "the inverse of the standard-open direct-sum decomposition of the functions on the \
punctured cone carries the m-th summand to the inclusion of a degree-m fraction, for every \
integer m"]
theorem puncturedConeAlgebraSectionsRingEquiv_symm_of (m : ℤ) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (y : puncturedGrading 𝒜 d hf m) :
    (puncturedConeAlgebraSectionsRingEquiv 𝒜 d hf hd).symm
        (DirectSum.of (fun k : ℤ => ↥(puncturedGrading 𝒜 d hf k)) m y) =
      (eqToHom (puncturedConeAlgebra_sections_basicOpen 𝒜 d hf hd).symm).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom
          (y : HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f))) := by
  let := gradedRingPuncturedGrading 𝒜 d hf
  have h0 : (DirectSum.decomposeRingEquiv (puncturedGrading 𝒜 d hf)).symm
      (DirectSum.of (fun k : ℤ => ↥(puncturedGrading 𝒜 d hf k)) m y) =
      (y : HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f)) :=
    DirectSum.decompose_symm_of _ y
  change (eqToIso (puncturedConeAlgebra_sections_basicOpen 𝒜 d hf
          hd)).commRingCatIsoToRingEquiv.symm
      ((AlgebraicGeometry.Proj.basicOpenIsoAway (grading 𝒜) (sigmaMulPsi 𝒜 f)
          (sigmaMulPsi_mem_grading 𝒜 d hf) hd).commRingCatIsoToRingEquiv
        ((DirectSum.decomposeRingEquiv (puncturedGrading 𝒜 d hf)).symm
          (DirectSum.of (fun k : ℤ => ↥(puncturedGrading 𝒜 d hf k)) m y))) = _
  rw [h0]
  rfl

/-- **The `m`-th summand of the standard-open decomposition
`Γ(D₊(f), (π|_U)_* 𝒪_U) = ⨁_{m ∈ ℤ} Γ(D₊(f), 𝒪_P(m))` is the local degreewise inclusion
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistApp`.** This identifies the footnote
computation of [Stacks, Tag 0EKG] over one standard open with the local datum the morphism
`𝒪_P(m) ⟶ (π|_U)_* 𝒪_U` of sheaves of `𝒪_P`-modules is glued from. -/
@[stacks 0EKG "the m-th summand of the standard-open direct-sum decomposition of the functions \
on the punctured cone is the local degreewise inclusion of the sections of O_P(m), for the \
truncation cone and every integer m"]
theorem puncturedConeAlgebraSectionsEquivTwistSections_symm_of (m : ℤ) (d : ℕ) (hf : f ∈ 𝒜 d)
    (hd : 0 < d)
    (s : (ProjectiveSpectrum.Proj.twistingSheaf 𝒜 m).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (puncturedConeAlgebraSectionsEquivTwistSections 𝒜 d hf hd).symm (DirectSum.of _ m s) =
      (puncturedConeTwistApp 𝒜 m d hf hd).hom s := by
  have hstep1 : (puncturedConeAlgebraSectionsEquivTwistSections 𝒜 d hf hd).symm
        (DirectSum.of _ m s) =
      (puncturedConeAlgebraSectionsRingEquiv 𝒜 d hf hd).symm
        (DirectSum.of (fun k : ℤ => ↥(puncturedGrading 𝒜 d hf k)) m
          ((puncturedGradingEquivSectionsTwist 𝒜 d hf hd m).symm s)) :=
    congrArg (puncturedConeAlgebraSectionsRingEquiv 𝒜 d hf hd).symm
      (DFinsupp.mapRange_single
        (hf := fun i => (puncturedGradingEquivSectionsTwist 𝒜 d hf hd i).symm.map_zero))
  rw [hstep1, puncturedConeAlgebraSectionsRingEquiv_symm_of, puncturedConeTwistApp_apply,
    openUInL_ι_appLE_eq_eqToHom]
  rfl

end Stacks.AlgebraicGeometry.ProjConeTwist

end
