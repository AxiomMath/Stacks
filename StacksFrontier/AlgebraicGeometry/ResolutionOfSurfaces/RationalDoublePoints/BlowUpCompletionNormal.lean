module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpCompletedLocalRings
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Completion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowersExtra

/-!
# Normality of the blowup of the completion of a rational surface singularity

Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two defining a rational singularity
whose completion `A^` along `𝔪` is again a normal domain. Then `A^` is itself a local normal
Nagata domain of dimension two: locality and Noetherianness of the completion are Mathlib's, the
Nagata property holds because `A^` is a complete Noetherian local ring, the dimension is
unchanged by completion, and normality is the hypothesis. Consequently the blowup of `Spec(A^)`
in the maximal ideal of `A^` is normal as soon as `A^` defines a rational singularity, and the
completion of the local ring of the blowup of `Spec(A)` in `𝔪` at a closed point is a normal
domain.

## Main definitions

* `AlgebraicGeometry.BlowUpMaximalIdealIsNormal`: the statement of [Stacks, Tag 0B4Z], that for
  a local normal Nagata domain of dimension two defining a rational singularity, the blowup of
  its spectrum in the maximal ideal is a normal scheme.

## Main results

* `AlgebraicGeometry.isNormal_blowUp_maximalIdeal_adicCompletion`: the blowup of `Spec(A^)` in
  the maximal ideal of `A^` is normal, granted [Stacks, Tag 0B4Z] and the rational singularity
  of `A^`.
* `AlgebraicGeometry.isNormal_blowUp_maximalIdeal_adicCompletion_of_isIntegrallyClosed`: the same
  conclusion from integral closedness of the affine blowup algebras `A^[𝔪^/a]`.
* `isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal_of_rationalSingularity`: the
  completion of the local ring of the blowup of `Spec(A)` in `𝔪` at a closed point is a normal
  domain, granted [Stacks, Tag 0B4Z] and the rational singularity of `A^`.

## Implementation notes

[Stacks, Tag 0B4Z] enters as the hypothesis `BlowUpMaximalIdealIsNormal`, quantified over all
rings satisfying its hypotheses. That `A^` defines a rational singularity, clause (1) of
[Stacks, Tag 0BG7], is also a hypothesis. The hypothesis `_hrat` that `A` defines a rational
singularity is not used in the proof.

## References

* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
* [Stacks Project, Tag 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z)
* [Stacks Project, Tag 0B4Y](https://stacks.math.columbia.edu/tag/0B4Y)
* [Stacks Project, Tag 0C3V](https://stacks.math.columbia.edu/tag/0C3V)
* [Stacks Project, Tag 07NV](https://stacks.math.columbia.edu/tag/07NV)
-/


@[expose] public noncomputable section

open IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### The statement of Tag 0B4Z -/

/-- The statement of [Stacks, Tag 0B4Z]: for every local normal Nagata domain `B` of dimension
two which defines a rational singularity, the blowup of `Spec(B)` in the maximal ideal is a
normal scheme. -/
public def BlowUpMaximalIdealIsNormal : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNormalDomain B], IsNagataRing B →
    ringKrullDim B = 2 → DefinesRationalSingularity B →
      IsNormal (blowUp (maximalIdealSheaf B))

/-! ### The blowup of the completion in the maximal ideal of the completion -/

/-- Let `A` be a two-dimensional Noetherian local ring whose completion `A^` along the maximal
ideal is a normal domain defining a rational singularity. Granted [Stacks, Tag 0B4Z], the blowup
of `Spec(A^)` in the maximal ideal of `A^` is normal. -/
public theorem isNormal_blowUp_maximalIdeal_adicCompletion
    (h0B4Z : BlowUpMaximalIdealIsNormal.{u}) (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hdim : ringKrullDim A = 2)
    (hcompletion : IsNormalDomain (AdicCompletion (maximalIdeal A) A))
    (hrat : DefinesRationalSingularity (AdicCompletion (maximalIdeal A) A)) :
    IsNormal (blowUp (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A))) := by
  have : IsNormalDomain (AdicCompletion (maximalIdeal A) A) := hcompletion
  exact h0B4Z _ IsLocalRing.isNagataRing_adicCompletion_maximalIdeal
    (IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal.trans hdim) hrat

/-- Let `A` be a Noetherian local ring whose completion `A^` along the maximal ideal is a normal
domain. If each affine blowup algebra `A^[𝔪^/a]` of the maximal ideal `𝔪^` of `A^` is integrally
closed, then the blowup of `Spec(A^)` in `𝔪^` is normal. -/
public theorem isNormal_blowUp_maximalIdeal_adicCompletion_of_isIntegrallyClosed
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hcompletion : IsNormalDomain (AdicCompletion (maximalIdeal A) A))
    (hcharts : ∀ a ∈ Ideal.map
        (Scheme.ΓSpecIso (.of (AdicCompletion (maximalIdeal A) A))).inv.hom
          (maximalIdeal (AdicCompletion (maximalIdeal A) A)),
      IsIntegrallyClosed (affineBlowupAlgebra
        (Ideal.map (Scheme.ΓSpecIso (.of (AdicCompletion (maximalIdeal A) A))).inv.hom
          (maximalIdeal (AdicCompletion (maximalIdeal A) A))) a (Localization.Away a))) :
    IsNormal (blowUp (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A))) := by
  have : IsNormalDomain (AdicCompletion (maximalIdeal A) A) := hcompletion
  exact (isNormal_blowUp_maximalIdeal_iff_isIntegrallyClosed
    (AdicCompletion (maximalIdeal A) A)).2 hcharts

/-! ### Normality of the completed local rings of the blowup -/

/-- Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two which defines a rational
singularity and whose completion `A^` along `𝔪` is normal. Granted [Stacks, Tag 0B4Z] and that
`A^` defines a rational singularity, the completion of the local ring of the blowup of `Spec(A)`
in `𝔪` at a closed point is a normal domain. -/
public theorem isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal_of_rationalSingularity
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] (hnagata : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (_hrat : DefinesRationalSingularity A)
    (hcompletion : IsNormalDomain (AdicCompletion (maximalIdeal A) A))
    (h0B4Z : BlowUpMaximalIdealIsNormal.{u})
    (hratCompletion : DefinesRationalSingularity (AdicCompletion (maximalIdeal A) A))
    (x : blowUp (maximalIdealSheaf A))
    (hx : IsClosed ({x} : Set (blowUp (maximalIdealSheaf A)))) :
    IsNormalDomain (AdicCompletion
      (maximalIdeal ((blowUp (maximalIdealSheaf A)).presheaf.stalk x))
      ((blowUp (maximalIdealSheaf A)).presheaf.stalk x)) := by
  have : IsNoetherianRing A := hnagata.isNoetherianRing
  exact isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal A
    (isNormal_blowUp_maximalIdeal_adicCompletion h0B4Z A hdim hcompletion hratCompletion) x hx

end AlgebraicGeometry

end
