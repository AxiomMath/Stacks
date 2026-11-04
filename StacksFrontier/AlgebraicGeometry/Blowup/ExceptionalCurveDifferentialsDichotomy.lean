module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowup
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceFormsDichotomy
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpSingularPoints
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality

/-!
# The twist dichotomy for the blowup of a regular local surface in its closed point

Let `(A, 𝔪, κ)` be a regular local ring of dimension two, let `b : X ⟶ S = Spec A` be the
blowing up of `S` in `𝔪` and let `E` be its exceptional divisor. For a morphism `q : S ⟶ S₀` and
`r` the generic rank of the relative differentials,

`Ω^r_X ≅ (b^*Ω^r_S)(E)` or `Ω^r_X ≅ b^*Ω^r_S`,

where `Ω^r = (⋀^r Ω)^{∨∨}`. This is the dichotomy used in the inductive step of
[Stacks, Tag 0B4T], with every hypothesis about the blowup itself discharged: the twist exponent
of [Stacks, Tag 0B3T] is at most `min s r` with `s` the rank of `Ω_{E/κ}`, and `Ω_{E/κ}` is
invertible because `E` is the projective line over `κ`.

## Main results

* `Stacks.Blowup.isIntegral_blowUp_residuePoint`,
  `Stacks.Blowup.isRegular_blowUp_residuePoint` and
  `Stacks.Blowup.topologicalKrullDim_blowUp_residuePoint_le_two`: the blowup of a regular local
  surface in its closed point is integral and regular of dimension two ([Stacks, Tag 0AGR]),
  on the presentation `Stacks.Blowup.blowUp`.
* `Stacks.Blowup.nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_residuePoint`:
  **the dichotomy.**

## Implementation notes

[Stacks, Tag 0AGR] is proved in the library for `AlgebraicGeometry.blowUp`, the presentation of
the blowup through a chosen Rees datum, while the dichotomy is phrased for
`Stacks.Blowup.blowUp`, the presentation through the explicit Rees datum. The two are isomorphic
over the base by `Stacks.Blowup.blowUpIso`; integrality transports by
`AlgebraicGeometry.IsIntegral.of_isIso`, regularity by `AlgebraicGeometry.isRegular_of_iso` (the
blowup being locally Noetherian, as it is proper over a Noetherian base), and the dimension by
`IsHomeomorph.topologicalKrullDim_eq`. The centre is written as the closed point
`Spec κ ⟶ Spec A`, whose ideal sheaf is `𝔪` by
`AlgebraicGeometry.ker_residuePoint_eq_ofIdealTop_map`.

The hypotheses that remain are those of the ambient tower, not of the blowup: the coherence of
the two modules of differentials over `S₀`, and a nonempty open on which both have rank `r`.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Scheme.Modules Stacks.SheafOfModules

universe u

namespace Stacks.Blowup

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)

include hdim in
/-- **The blowup of a regular local surface in its closed point is integral**, on the
presentation `Stacks.Blowup.blowUp`: part of [Stacks, Tag 0AGR], transported along
`Stacks.Blowup.blowUpIso`. -/
theorem isIntegral_blowUp_residuePoint :
    IsIntegral (Stacks.Blowup.blowUp (residuePoint A).ker) := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  rw [AlgebraicGeometry.ker_residuePoint_eq_ofIdealTop_map]
  have := AlgebraicGeometry.isIntegral_blowUp_maximalIdeal A hdim
  exact IsIntegral.of_isIso (blowUpIso _).inv

/-- The blowup of a regular local surface in its closed point is locally Noetherian, being
proper over a Noetherian base. -/
theorem isLocallyNoetherian_blowUp_residuePoint :
    IsLocallyNoetherian (Stacks.Blowup.blowUp (residuePoint A).ker) :=
  LocallyOfFiniteType.isLocallyNoetherian (Stacks.Blowup.blowUpToBase (residuePoint A).ker)

include hdim in
/-- **The blowup of a regular local surface in its closed point is regular**, on the
presentation `Stacks.Blowup.blowUp`: the regularity half of [Stacks, Tag 0AGR], transported
along `Stacks.Blowup.blowUpIso`. -/
theorem isRegular_blowUp_residuePoint :
    AlgebraicGeometry.IsRegular (Stacks.Blowup.blowUp (residuePoint A).ker) := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have hiso := isLocallyNoetherian_blowUp_residuePoint A
  rw [AlgebraicGeometry.ker_residuePoint_eq_ofIdealTop_map] at hiso ⊢
  exact AlgebraicGeometry.isRegular_of_iso (blowUpIso _)
    (AlgebraicGeometry.isRegular_blowUp_maximalIdeal A hdim)

include hdim in
/-- **The blowup of a regular local surface in its closed point has dimension two**, on the
presentation `Stacks.Blowup.blowUp`: the blowup is a modification of `Spec A`, and the two
presentations are homeomorphic. -/
theorem topologicalKrullDim_blowUp_residuePoint_le_two :
    topologicalKrullDim (Stacks.Blowup.blowUp (residuePoint A).ker) ≤ 2 := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  rw [AlgebraicGeometry.ker_residuePoint_eq_ofIdealTop_map,
    IsHomeomorph.topologicalKrullDim_eq _
      (blowUpIso (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom
          (IsLocalRing.maximalIdeal A)))).hom.homeomorph.isHomeomorph]
  exact AlgebraicGeometry.topologicalKrullDim_blowUp_maximalIdeal_le_two A hdim

include hdim in
/-- **The dichotomy of [Stacks, Tag 0B4T] for the blowup of a regular local surface in its closed
point.** Let `(A, 𝔪, κ)` be a regular local ring of dimension two, let `b : X ⟶ S = Spec A` be
the blowing up of `S` in `𝔪` with exceptional divisor `E`, and let `q : S ⟶ S₀`. Suppose
`b^*Ω_{S/S₀}` and `Ω_{X/S₀}` are coherent and both of rank `r` on a nonempty open. Then

`Ω^r_X ≅ (b^*Ω^r_S)(E)` or `Ω^r_X ≅ b^*Ω^r_S`,

where `Ω^r` abbreviates `(⋀^r Ω)^{∨∨}`.

`X` is integral and regular of dimension two and `E` is integral by [Stacks, Tag 0AGR] and part
(1) of [Stacks, Tag 0AGQ], `Ω_{X/S} ≅ i_*Ω_{E/κ}` is [Stacks, Tag 0B4L], and `Ω_{E/κ}` is
invertible because `E` is the projective line over `κ`; the bound `k ≤ min 1 r` of
[Stacks, Tag 0B3T] then leaves only the two alternatives. -/
theorem nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_residuePoint
    {S₀ : Scheme.{u}} (q : Spec (.of A) ⟶ S₀) (r : ℕ)
    [((Scheme.Modules.pullback (Stacks.Blowup.blowUpToBase (residuePoint A).ker)).obj
        (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase (residuePoint A).ker ≫ q)).IsCoherent]
    (U : (Stacks.Blowup.blowUp (residuePoint A).ker).Opens)
    (hU : ∃ x : Stacks.Blowup.blowUp (residuePoint A).ker, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (Stacks.Blowup.blowUpToBase (residuePoint A).ker)).obj
        (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase (residuePoint A).ker ≫ q)).over U) r] :
    Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(Stacks.Blowup.blowUp (residuePoint A).ker).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _
                (Stacks.Blowup.blowUp (residuePoint A).ker).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (Stacks.Blowup.blowUp (residuePoint A).ker).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf'
            (Stacks.Blowup.exceptionalIdeal (residuePoint A).ker))).obj
        (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (Stacks.Blowup.blowUpToBase (residuePoint A).ker)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ))) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase (residuePoint A).ker ≫ q)) (r : ℤ))) ∨
    Nonempty
      (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (Stacks.Blowup.blowUpToBase (residuePoint A).ker)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ)) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.blowUpToBase (residuePoint A).ker ≫ q)) (r : ℤ))) := by
  have := isIntegral_blowUp_residuePoint A hdim
  have : IsIntegral (Stacks.Blowup.exceptionalIdeal (residuePoint A).ker).subscheme :=
    isIntegral_exceptionalDivisor_residuePoint A hdim
  exact Stacks.BlowupFormsDichotomy.nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower
    (residuePoint A) q (isRegular_blowUp_residuePoint A hdim)
    (topologicalKrullDim_blowUp_residuePoint_le_two A hdim)
    (isFiniteLocallyFreeOfRank_one_relativeDifferentials_exceptionalToCentre A hdim) r U hU

end Stacks.Blowup

end
