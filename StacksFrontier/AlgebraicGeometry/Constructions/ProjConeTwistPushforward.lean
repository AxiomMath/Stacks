module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPresentation
public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalizationGraded

/-!
# The direct image of the structure sheaf of the cone over a standard open

Let `A = ⨁_{d ≥ 0} A_d` be a graded ring, `P = Proj A`, and let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}`. For `f ∈ A_d` homogeneous of positive
degree, `π⁻¹(D₊(f)) = D₊(ψ f)`, so the sections of `π_* 𝒪_L` over the standard open `D₊(f)` are the
degree-zero part `(B[1/ψ f])₀` of a localization of `B`, and that ring is the direct sum over
`m ≥ 0` of the degree-`m` parts of `A[1/f]`. This is the identification
`π_* 𝒪_L = ⨁_{m ≥ 0} 𝒪_P(m)` over one standard open of `P`, with the summands written as the
homogeneous parts of `A[1/f]` rather than as sections of twisting sheaves.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebra_sections_basicOpen`: the sections of
  `π_* 𝒪_L` over `D₊(f)` are the functions on `D₊(ψ f)`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebraSectionsRingEquiv`: those sections are the
  direct sum over `m ≥ 0` of the degree-`m` parts of `A[1/f]`, as a ring isomorphism.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum Opposite
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {f : A}

/-- The sections of `π_* 𝒪_L` over a standard open `D₊(f)` are the functions on `D₊(ψ f)`. -/
theorem coneAlgebra_sections_basicOpen (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (coneAlgebra (truncationConeData 𝒜)).right.obj.obj
        (op (Proj.basicOpen 𝒜 f)) =
      Γ(AlgebraicGeometry.Proj (grading 𝒜), Proj.basicOpen (grading 𝒜) (psi 𝒜 f)) :=
  congrArg (fun U => Γ(AlgebraicGeometry.Proj (grading 𝒜), U))
    (pi_preimage_basicOpen 𝒜 f d hf hd)

/-- The sections of the direct image of the structure sheaf of the cone over a standard open
`D₊(f)` of `P = Proj A` are the direct sum, over the nonnegative degrees, of the homogeneous parts
of the localization `A[1/f]`: `(π_* 𝒪_L)(D₊(f)) ≃+* ⨁_{m ≥ 0} (A[1/f])_m`. -/
@[stacks 0EKG "the footnote computation π_* O_L = ⨁_{m ≥ 0} O_P(m), over one standard open \
D₊(f) of P and for the truncation algebra, with the summands written as the homogeneous parts \
of A[1/f]"]
def coneAlgebraSectionsRingEquiv (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (coneAlgebra (truncationConeData 𝒜)).right.obj.obj (op (Proj.basicOpen 𝒜 f)) ≃+*
      (⨁ m : ℕ, ↥(awayGrading 𝒜 d hf m)) :=
  letI := gradedRingAwayGrading 𝒜 d hf
  ((eqToIso (coneAlgebra_sections_basicOpen 𝒜 d hf hd)).commRingCatIsoToRingEquiv.trans
      (Proj.basicOpenIsoAway (grading 𝒜) (psi 𝒜 f)
        ((psi 𝒜).map_mem hf) hd).commRingCatIsoToRingEquiv.symm).trans
    (DirectSum.decomposeRingEquiv (awayGrading 𝒜 d hf))

end Stacks.AlgebraicGeometry.ProjConeTwist

end
