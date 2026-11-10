module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistGlobalMap

/-!
# The degreewise inclusion is the `m`-th summand of the standard-open decomposition

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}`. Over a standard open `D₊(f)` of a
positive-degree homogeneous element, the inclusion of the `m`-th summand of the direct sum
`Γ(D₊(f), π_* 𝒪_L) = ⨁_{m ≥ 0} Γ(D₊(f), 𝒪_P(m))` of
`Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebraSectionsEquivTwistSections` is the degreewise
inclusion `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebraSectionsRingEquiv_symm_of`: the inverse of
  the standard-open ring isomorphism `(π_* 𝒪_L)(D₊(f)) ≃+* ⨁_{m ≥ 0} (A[1/f])_m` carries the
  `m`-th summand to the inclusion of a degree-`m` fraction, read as a function on `D₊(ψ f)`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebraSectionsEquivTwistSections_symm_of`: the
  `m`-th summand of the standard-open decomposition of `Γ(D₊(f), π_* 𝒪_L)` is the degreewise
  inclusion `coneTwistApp`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
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

/-- The inverse of the ring isomorphism `(π_* 𝒪_L)(D₊(f)) ≃+* ⨁_{m ≥ 0} (A[1/f])_m` sends a
degree-`m` element `y` of `(B[1/ψ f])₀`, placed in the `m`-th summand, to `y` read as a function
on `D₊(ψ f)` by `AlgebraicGeometry.Proj.awayToSection` and transported along
`π⁻¹(D₊(f)) = D₊(ψ f)`. -/
@[stacks 0EKG "the inverse of the standard-open direct-sum decomposition of the functions on \
the cone carries the m-th summand to the inclusion of a degree-m fraction"]
theorem coneAlgebraSectionsRingEquiv_symm_of (m d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (y : awayGrading 𝒜 d hf m) :
    (coneAlgebraSectionsRingEquiv 𝒜 d hf hd).symm
        (DirectSum.of (fun k : ℕ => ↥(awayGrading 𝒜 d hf k)) m y) =
      (eqToHom (coneAlgebra_sections_basicOpen 𝒜 d hf hd).symm).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom
          (y : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f))) := by
  let := gradedRingAwayGrading 𝒜 d hf
  have h0 : (DirectSum.decomposeRingEquiv (awayGrading 𝒜 d hf)).symm
      (DirectSum.of (fun k : ℕ => ↥(awayGrading 𝒜 d hf k)) m y) =
      (y : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)) :=
    DirectSum.decompose_symm_of _ y
  change (eqToIso (coneAlgebra_sections_basicOpen 𝒜 d hf hd)).commRingCatIsoToRingEquiv.symm
      ((AlgebraicGeometry.Proj.basicOpenIsoAway (grading 𝒜) (psi 𝒜 f)
          ((psi 𝒜).map_mem hf) hd).commRingCatIsoToRingEquiv
        ((DirectSum.decomposeRingEquiv (awayGrading 𝒜 d hf)).symm
          (DirectSum.of (fun k : ℕ => ↥(awayGrading 𝒜 d hf k)) m y))) = _
  rw [h0]
  rfl

/-- The inclusion of the `m`-th summand of the standard-open decomposition
`Γ(D₊(f), π_* 𝒪_L) = ⨁_{m ≥ 0} Γ(D₊(f), 𝒪_P(m))` is the degreewise inclusion
`Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp`. -/
@[stacks 0EKG "the m-th summand of the standard-open direct-sum decomposition of the functions \
on the cone is the local degreewise inclusion of the sections of O_P(m), for the truncation cone"]
theorem coneAlgebraSectionsEquivTwistSections_symm_of (m d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : (ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (coneAlgebraSectionsEquivTwistSections 𝒜 d hf hd).symm (DirectSum.of _ m s) =
      (coneTwistApp 𝒜 m d hf hd).hom s := by
  have hs : (coneAlgebraSectionsEquivTwistSections 𝒜 d hf hd).symm
        (DirectSum.of _ m s) =
      (coneAlgebraSectionsRingEquiv 𝒜 d hf hd).symm
        (DirectSum.of (fun k : ℕ => ↥(awayGrading 𝒜 d hf k)) m
          ((awayGradingEquivSectionsTwist 𝒜 d hf hd m).symm s)) :=
    congrArg (coneAlgebraSectionsRingEquiv 𝒜 d hf hd).symm
      (DFinsupp.mapRange_single
        (hf := fun i => (awayGradingEquivSectionsTwist 𝒜 d hf hd i).symm.map_zero))
  have hmap : (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
        (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op =
      eqToHom (coneAlgebra_sections_basicOpen 𝒜 d hf hd).symm := by
    rw [eqToHom_op, eqToHom_map]
    rfl
  rw [hs, coneAlgebraSectionsRingEquiv_symm_of, coneTwistApp_apply, ← hmap]
  rfl

end Stacks.AlgebraicGeometry.ProjConeTwist

end
