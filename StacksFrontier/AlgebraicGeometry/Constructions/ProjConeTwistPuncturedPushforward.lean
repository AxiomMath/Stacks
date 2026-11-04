module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPushforward
public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalizationPunctured

/-!
# The direct image of the structure sheaf of the punctured cone over a standard open

Let `A = ⨁_{d ≥ 0} A_d` be a graded ring, `P = Proj A`, and let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}`. Let `U ⊆ L` be the part of the cone
lying over `Spec A ∖ V(A₊)`, the punctured cone. For `f ∈ A_d` homogeneous of positive degree
the part of `U` lying over the standard open `D₊(f)` of `P` is the standard open `D₊(σ f · ψ f)`
of `L`, so the sections of `(π|_U)_* 𝒪_U` over `D₊(f)` are the degree-zero part
`(B[1/σ f · ψ f])₀` of a localization of `B`, and that ring is the whole localization `A[1/f]` —
equivalently the direct sum over *all* integers `m` of the degree-`m` parts of `A[1/f]`. This is
the identification `(π|_U)_* 𝒪_U = ⨁_{m ∈ ℤ} 𝒪_P(m)` over one standard open of `P`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebra_sections_basicOpen`: the sections of
  `(π|_U)_* 𝒪_U` over `D₊(f)` are the functions on `D₊(σ f · ψ f)`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSectionsEquivAway`: those sections
  are the localization `A[1/f]`, as a ring isomorphism.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSectionsRingEquiv`: those sections
  are the direct sum over all `m ∈ ℤ` of the degree-`m` parts of `A[1/f]`, as a ring isomorphism.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSectionsEquivTwistSections` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebraSectionsEquivTwistSections`: the same for the
  punctured cone and for the cone, with the summands written as the sections of the twisting
  sheaves over `D₊(f)` rather than as homogeneous parts of `A[1/f]`.

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

/-- The sections of `(π|_U)_* 𝒪_U` over a standard open `D₊(f)` are the functions on the
standard open `D₊(σ f · ψ f)` of `L`. -/
theorem puncturedConeAlgebra_sections_basicOpen (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (puncturedConeAlgebra (truncationConeData 𝒜)).right.obj.obj
        (op (Proj.basicOpen 𝒜 f)) =
      Γ(AlgebraicGeometry.Proj (grading 𝒜),
        Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f)) := by
  have hopen : (openUInL 𝒜).ι ''ᵁ (((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ Proj.basicOpen 𝒜 f) =
      Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f) := by
    rw [Scheme.Hom.comp_preimage, pi_preimage_basicOpen 𝒜 f d hf hd,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      openUInL_inf_basicOpen 𝒜 f d hf hd, sigmaMulPsi]
  exact congrArg (fun U => Γ(AlgebraicGeometry.Proj (grading 𝒜), U)) hopen

/-- The sections of the direct image of the structure sheaf of the punctured cone over a standard
open `D₊(f)` of `P = Proj A` are the localization of `A` at `f`:
`((π|_U)_* 𝒪_U)(D₊(f)) ≃+* A[1/f]`. -/
@[stacks 0EKG "the sections of the direct image of the structure sheaf of the punctured cone \
over a standard open D₊(f) of P are the localization A[1/f]"]
def puncturedConeAlgebraSectionsEquivAway (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (puncturedConeAlgebra (truncationConeData 𝒜)).right.obj.obj
        (op (Proj.basicOpen 𝒜 f)) ≃+*
      Localization.Away f :=
  ((eqToIso (puncturedConeAlgebra_sections_basicOpen 𝒜 d hf hd)).commRingCatIsoToRingEquiv.trans
      (Proj.basicOpenIsoAway (grading 𝒜) (sigmaMulPsi 𝒜 f)
        (sigmaMulPsi_mem_grading 𝒜 d hf) hd).commRingCatIsoToRingEquiv.symm).trans
    (puncturedRingEquiv 𝒜 d hf)

/-- The sections of the direct image of the structure sheaf of the punctured cone over a standard
open `D₊(f)` of `P = Proj A` are the direct sum, over *all* integer degrees, of the homogeneous
parts of the localization `A[1/f]`: `((π|_U)_* 𝒪_U)(D₊(f)) ≃+* ⨁_{m ∈ ℤ} (A[1/f])_m`. -/
@[stacks 0EKG "the footnote computation (π|_U)_* O_U = ⨁_{m ∈ ℤ} O_P(m), over one standard open \
D₊(f) of P and for the truncation algebra, with the summands written as the homogeneous parts \
of A[1/f]"]
def puncturedConeAlgebraSectionsRingEquiv (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (puncturedConeAlgebra (truncationConeData 𝒜)).right.obj.obj
        (op (Proj.basicOpen 𝒜 f)) ≃+*
      (⨁ m : ℤ, ↥(puncturedGrading 𝒜 d hf m)) :=
  letI := gradedRingPuncturedGrading 𝒜 d hf
  ((eqToIso (puncturedConeAlgebra_sections_basicOpen 𝒜 d hf hd)).commRingCatIsoToRingEquiv.trans
      (Proj.basicOpenIsoAway (grading 𝒜) (sigmaMulPsi 𝒜 f)
        (sigmaMulPsi_mem_grading 𝒜 d hf) hd).commRingCatIsoToRingEquiv.symm).trans
    (DirectSum.decomposeRingEquiv (puncturedGrading 𝒜 d hf))

/-- The sections of the direct image of the structure sheaf of the punctured cone over a standard
open `D₊(f)` of `P = Proj A` are the direct sum of the sections of the twisting sheaves over
`D₊(f)`: `((π|_U)_* 𝒪_U)(D₊(f)) ≃+ ⨁_{m ∈ ℤ} Γ(D₊(f), 𝒪_P(m))`. -/
@[stacks 0EKG "the footnote computation (π|_U)_* O_U = ⨁_{m ∈ ℤ} O_P(m), over one standard open \
D₊(f) of P and for the truncation algebra, with the summands written as the sections of the \
twisting sheaves"]
def puncturedConeAlgebraSectionsEquivTwistSections (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (puncturedConeAlgebra (truncationConeData 𝒜)).right.obj.obj
        (op (Proj.basicOpen 𝒜 f)) ≃+
      (⨁ m : ℤ, ↥((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 m).val.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)))) :=
  (puncturedConeAlgebraSectionsRingEquiv 𝒜 d hf hd).toAddEquiv.trans
    (puncturedDirectSumEquivSectionsTwist 𝒜 d hf hd)

/-- The sections of the direct image of the structure sheaf of the cone over a standard open
`D₊(f)` of `P = Proj A` are the direct sum of the sections of the nonnegative twisting sheaves
over `D₊(f)`: `(π_* 𝒪_L)(D₊(f)) ≃+ ⨁_{m ≥ 0} Γ(D₊(f), 𝒪_P(m))`. -/
@[stacks 0EKG "the footnote computation π_* O_L = ⨁_{m ≥ 0} O_P(m), over one standard open \
D₊(f) of P and for the truncation algebra, with the summands written as the sections of the \
twisting sheaves"]
def coneAlgebraSectionsEquivTwistSections (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (coneAlgebra (truncationConeData 𝒜)).right.obj.obj
        (op (Proj.basicOpen 𝒜 f)) ≃+
      (⨁ m : ℕ, ↥((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ)).val.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)))) :=
  (coneAlgebraSectionsRingEquiv 𝒜 d hf hd).toAddEquiv.trans
    (awayDirectSumEquivSectionsTwist 𝒜 d hf hd)

end Stacks.AlgebraicGeometry.ProjConeTwist

end
