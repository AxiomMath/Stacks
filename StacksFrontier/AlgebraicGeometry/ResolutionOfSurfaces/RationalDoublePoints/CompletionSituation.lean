module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowupStillGood
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.Situation
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Completion
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein
import StacksFrontier.RingTheory.AdicCompletion.Flat
import StacksFrontier.RingTheory.Dualizing.Complex
import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift
import StacksFrontier.RingTheory.Dualizing.TrivialDuality
import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Ext

/-!
# The completion of a rational double point is a rational double point

Let `(A, 𝔪, κ)` be as in Situation [Stacks, Tag 0BGC]. The source resolves `Spec A` by passing
to the completion `A^`, where the termination statement of Section 54.12 is available
([Stacks, Tag 0BG2] and [Stacks, Tag 0BG3] want a complete base). This file checks that `A^` is
again in Situation 0BGC: it is a complete Noetherian local ring, hence Nagata; it has the
dimension of `A`; it defines a rational singularity by clause (1) of [Stacks, Tag 0BG7]; it is
a normal domain by hypothesis; its own completion is itself; it is Gorenstein because
`A ⟶ A^` is flat and local with closed fibre a field ([Stacks, Tag 0BJL]); and it is not
regular because regularity can be read off the completion ([Stacks, Tag 07NY]).

## Main definitions

* `AlgebraicGeometry.RationalDoublePointSituation.completion`: Situation 0BGC for `A^`.

## Main results

* `AlgebraicGeometry.isAdicComplete_maximalIdeal_adicCompletion`: the completion of a Noetherian
  local ring is complete, so (Mathlib's `AdicCompletion.ofAlgEquiv`) it is its own completion.

## References

* [Stacks Project, Tag 0BGC](https://stacks.math.columbia.edu/tag/0BGC)
* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
* [Stacks Project, Tag 07NY](https://stacks.math.columbia.edu/tag/07NY)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The completion of a Noetherian local ring is complete for its own maximal ideal. -/
theorem isAdicComplete_maximalIdeal_adicCompletion (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal A) A))
      (AdicCompletion (maximalIdeal A) A) :=
  AdicCompletion.isAdicComplete_of_fg (maximalIdeal A).fg_of_isNoetherianRing

namespace RationalDoublePointSituation

/-- The rational double point situation whose ring is the `𝔪`-adic completion `A^` of the ring
`A` of `S`. -/
def completion (S : RationalDoublePointSituation.{u}) : RationalDoublePointSituation.{u} where
  A := AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A
  normalDomain := S.completion_normalDomain
  nagata := IsLocalRing.isNagataRing_adicCompletion_maximalIdeal
  dimension_two :=
    (_root_.ringKrullDim_adicCompletion_maximalIdeal (A := S.A)).symm.trans S.dimension_two
  definesRationalSingularity :=
    letI := S.completion_normalDomain
    (definesRationalSingularity_adicCompletion_and_isNormalDomain_stalk_blowUp S.A S.nagata
      S.dimension_two S.definesRationalSingularity).1
  completion_normalDomain := by
    letI := S.completion_normalDomain
    letI := isAdicComplete_maximalIdeal_adicCompletion S.A
    let e := (AdicCompletion.ofAlgEquiv
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))).toRingEquiv
    have : IsDomain (AdicCompletion
        (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))
        (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A)) :=
      e.toMulEquiv.isDomain_iff.mp inferInstance
    exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩
  gorenstein := by
    let B := AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A
    let I := (IsLocalRing.maximalIdeal S.A).map (algebraMap S.A B)
    have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap S.A B)).ne
    have : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have : IsLocalRing (B ⧸ I) :=
      IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
    have hres : Dualizing.IsGorensteinLocalRing (B ⧸ I) := by
      have heq : I = IsLocalRing.maximalIdeal B := by
        dsimp [I, B]
        exact (AdicCompletion.maximalIdeal_eq_map :
          IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) = _).symm
      let e : (B ⧸ I) ≃+* IsLocalRing.ResidueField B := Ideal.quotEquivOfEq heq
      exact Dualizing.isGorensteinLocalRing_of_ringEquiv e
        (Dualizing.IsRegularLocalRing.isGorensteinLocalRing (IsLocalRing.ResidueField B))
    exact (Dualizing.isGorensteinLocalRing_iff_of_flat S.A B).mpr ⟨S.gorenstein, hres⟩
  not_isRegularLocalRing := fun h =>
    S.not_isRegularLocalRing (isRegularLocalRing_iff_adicCompletion_maximalIdeal.mpr h)

/-- The ring of `S.completion` is the `𝔪`-adic completion of the ring of `S`. -/
@[simp]
theorem completion_A (S : RationalDoublePointSituation.{u}) :
    S.completion.A = AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A :=
  rfl

/-- The ring of `AlgebraicGeometry.RationalDoublePointSituation.completion` is complete. -/
instance isAdicComplete_completion (S : RationalDoublePointSituation.{u}) :
    IsAdicComplete (IsLocalRing.maximalIdeal S.completion.A) S.completion.A :=
  isAdicComplete_maximalIdeal_adicCompletion S.A

end RationalDoublePointSituation

end AlgebraicGeometry

end
