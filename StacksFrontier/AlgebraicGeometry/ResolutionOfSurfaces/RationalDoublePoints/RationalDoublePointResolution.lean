module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageBlowUp

/-!
# Resolution of rational double points

This file assembles [Stacks, Tag 0BGE]: a local normal Nagata domain `A` of dimension two which
defines a rational singularity, whose completion is normal, and which is Gorenstein, is resolved
by a finite sequence of blowups in singular closed points, each intervening scheme being normal
with finitely many singular points of the same type.

The first member of the sequence is `Spec A`
(`AlgebraicGeometry.isRationalDoublePointStage_spec`). Blowing up a singular point of a stage
gives a stage, and decreases the multiset of completion classes of the singular points
(`AlgebraicGeometry.IsRationalDoublePointStage.blowUp_of_mem_singularLocus`), for the relation
`AlgebraicGeometry.blowUpSingularRel` whose well-foundedness is the termination argument of the
source.

## Main results

* `AlgebraicGeometry.isRationalDoublePointStage_spec`: `Spec A` is a stage.
* `AlgebraicGeometry.exists_singularPointBlowupChain_isRegular_of_levels`: the resolution, from a
  levelled descent in the sense of `AlgebraicGeometry.acc_completionClass_of_levels`.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **The first member of the sequence of Tag 0BGE is a stage.** For `A` as in
[Stacks, Tag 0BGE], `Spec A` is a locally Noetherian normal scheme of dimension two whose
singular locus is at most the closed point, the local ring there being `A`, which is then the
ring of a Situation [Stacks, Tag 0BGC]. -/
theorem isRationalDoublePointStage_spec (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNormalDomain A] (hnagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrational : DefinesRationalSingularity A)
    (hcompletion : IsNormalDomain (AdicCompletion (maximalIdeal A) A))
    (hgorenstein : letI : IsNoetherianRing A := hnagata.isNoetherianRing
      Dualizing.IsGorensteinLocalRing A) :
    IsRationalDoublePointStage (Spec (.of A)) := by
  have : IsNoetherianRing A := hnagata.isNoetherianRing
  obtain ⟨hnorm, hfin, -, hrdp⟩ := isNormal_and_finite_singularLocus_and_exists_situation A
    hnagata hdim hrational hcompletion hgorenstein
  refine ⟨isLocallyNoetherian_Spec.mpr inferInstance, hnorm, ?_, hfin, hrdp⟩
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := A)).trans hdim |>.le

/-- **Tag 0BGE from a levelled descent.** Granted the hypotheses of
`AlgebraicGeometry.acc_completionClass_of_levels`, a ring `A` as in [Stacks, Tag 0BGE] is
resolved by a finite sequence of blowups in singular closed points whose members are stages. -/
theorem exists_singularPointBlowupChain_isRegular_of_levels
    (Inv : ℕ → ∀ (R : Type u) [CommRing R] [IsLocalRing R], R → Prop)
    (hiso : ∀ (n : ℕ) (R R' : Type u) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
      (e : R ≃+* R') (x : R), Inv n R x → Inv n R' (e x))
    (hcompl : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R),
      Inv n R x → Inv n (AdicCompletion (maximalIdeal R) R) (algebraMap _ _ x))
    (hmem : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] (x : R),
      Inv n R x → x ∈ maximalIdeal R)
    (hstep : ∀ (n : ℕ) (S : RationalDoublePointSituation.{u}) (x : S.A), Inv n S.A x →
      ∀ z ∈ singularLocus (blowUp (maximalIdealSheaf S.A)),
        (∃ S' : RationalDoublePointSituation.{u},
            Nonempty (S'.A ≃+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk z) ∧
            (singularLocus (blowUp (maximalIdealSheaf S'.A)) = ∅ ∨
              ∃ i < n, ∃ y : S'.A, Inv i S'.A y)) ∨
          (Function.Surjective ((Ideal.Quotient.mk (maximalIdeal
              ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z))).comp
                (maximalIdealBlowUpStalkHom S.A z)) ∧
            Ideal.map (maximalIdealBlowUpStalkHom S.A z) (maximalIdeal S.A) =
              Ideal.span {maximalIdealBlowUpStalkHom S.A z x} ∧
            Inv n ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z)
              (maximalIdealBlowUpStalkHom S.A z x)))
    (hall : ∀ S : RationalDoublePointSituation.{u},
      singularLocus (blowUp (maximalIdealSheaf S.A)) = ∅ ∨ ∃ (n : ℕ) (x : S.A), Inv n S.A x)
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] (hnagata : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hrational : DefinesRationalSingularity A)
    (hcompletion : IsNormalDomain (AdicCompletion (maximalIdeal A) A))
    (hgorenstein : letI : IsNoetherianRing A := hnagata.isNoetherianRing
      Dualizing.IsGorensteinLocalRing A) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
      SingularPointBlowupChain IsRationalDoublePointStage (Spec (.of A)) Y f ∧ IsRegular Y :=
  exists_singularPointBlowupChain_isRegular_of_forall_acc
    (acc_completionClass_of_levels Inv hiso hcompl hmem hstep hall) _
    (isRationalDoublePointStage_spec A hnagata hdim hrational hcompletion hgorenstein)

end AlgebraicGeometry

end
