module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.RationalDoublePointLevelStep

/-!
# Stacks Tag 0BGE: resolution of rational double points

Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two which defines a rational
singularity, whose completion is normal, and which is Gorenstein. Then there is a finite sequence
of blowups in singular closed points `Xₙ → ⋯ → X₁ → X₀ = Spec(A)` with `Xₙ` regular, each `Xᵢ`
being normal with finitely many singular points of the same type, that is, whose local rings are
as in Situation [Stacks, Tag 0BGC].

## Main results

* `AlgebraicGeometry.exists_singularPointBlowupChain_isRegular_of_definesRationalSingularity`:
  the resolution of a rational double point by a finite sequence of blowups in singular closed
  points.
* `AlgebraicGeometry.exists_singularPointBlowupChain_isNormal_isRegular`: the same, for a
  Noetherian `A`, with only the normality of the stages recorded.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0BGC](https://stacks.math.columbia.edu/tag/0BGC)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two which defines a rational
singularity, whose completion is normal, and which is Gorenstein. Then there exists a finite
sequence of blowups in singular closed points `Xₙ → Xₙ₋₁ → ⋯ → X₁ → X₀ = Spec(A)` such that `Xₙ`
is regular and such that each scheme `Xᵢ` of the sequence is normal with finitely many singular
points of the same type: the local ring at each singular point is again the ring of a Situation
[Stacks, Tag 0BGC]. -/
@[stacks 0BGE]
theorem exists_singularPointBlowupChain_isRegular_of_definesRationalSingularity
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] (hnagata : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hrational : DefinesRationalSingularity A)
    (hcompletion : IsNormalDomain (AdicCompletion (maximalIdeal A) A))
    (hgorenstein : letI : IsNoetherianRing A := hnagata.isNoetherianRing
      Dualizing.IsGorensteinLocalRing A) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
      SingularPointBlowupChain (fun W => IsNormal W ∧ (singularLocus W).Finite ∧
          ∀ w ∈ singularLocus W, ∃ S : RationalDoublePointSituation.{u},
            Nonempty (S.A ≃+* W.presheaf.stalk w))
        (Spec (.of A)) Y f ∧ IsRegular Y := by
  obtain ⟨Y, f, hchain, hreg⟩ := exists_singularPointBlowupChain_isRegular_of_levels
    rationalDoublePointLevel (fun n _ _ _ _ _ _ e x h => rationalDoublePointLevel_ringEquiv n e x h)
    (fun n R _ _ _ x h => rationalDoublePointLevel_adicCompletion n R x h)
    (fun n _ _ _ x h => mem_maximalIdeal_of_rationalDoublePointLevel n x h)
    (fun n S x hx z hz => S.step_rationalDoublePointLevel n x hx z hz)
    (fun S => S.exists_rationalDoublePointLevel) A hnagata hdim hrational hcompletion hgorenstein
  exact ⟨Y, f, hchain.mono fun W hW => ⟨hW.2.1, hW.2.2.2⟩, hreg⟩

/-- Let `A` be a Noetherian local normal Nagata domain of dimension two which defines a rational
singularity, whose completion is normal, and which is Gorenstein. Then there exists a finite
sequence of blowups in singular closed points `Y → ⋯ → Spec(A)` with `Y` regular and every stage
normal. -/
theorem exists_singularPointBlowupChain_isNormal_isRegular (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A] (hnagata : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hrational : DefinesRationalSingularity A)
    (hcompletion : IsNormalDomain (AdicCompletion (maximalIdeal A) A))
    (hgorenstein : Dualizing.IsGorensteinLocalRing A) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
      SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsRegular Y := by
  obtain ⟨Y, f, hchain, hreg⟩ :=
    exists_singularPointBlowupChain_isRegular_of_definesRationalSingularity A hnagata hdim
      hrational hcompletion hgorenstein
  exact ⟨Y, f, hchain.mono fun W hW => hW.1, hreg⟩

end AlgebraicGeometry

end
