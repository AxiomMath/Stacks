module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.LocalModel

/-!
# The top higher direct image of the twists of degree above `-n - 1`

For a commutative ring `R` and `n = m + 1 ≥ 1`, `Hⁿ(ℙⁿ_R, 𝒪(d)) = 0` for every `d ≥ -n`: by
Serre's computation it is the dual of the degree `-n - 1 - d < 0` part of `R[T₀, …, Tₙ]`, which
is zero. Consequently, on the projective bundle `π : 𝐏(E) ⟶ S` of a finite locally free module
of constant rank `n + 1`, `Rⁿ π_* 𝒪_{𝐏(E)}(d) = 0` for `d ≥ -n`.

## Main results

* `isZero_Hgroup_twistingSheaf_top`: `Hⁿ(ℙⁿ_R, 𝒪(d)) = 0` for `d ≥ -n`.
* `isZero_rightDerivedPlus_pushforward_twist_top`: `Rⁿ π_* 𝒪_{𝐏(E)}(d) = 0` for `d ≥ -n` on a
  projective bundle of constant rank `n + 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

/-- **`Hⁿ(ℙⁿ_R, 𝒪(d)) = 0` for `d ≥ -n`**, `n = m + 1 ≥ 1`, on the homogeneous-spectrum model. -/
public theorem isZero_Hgroup_twistingSheaf_top (R : Type u) [CommRing R] (m : ℕ) (d : ℤ)
    (hd : -((m + 1 : ℕ) : ℤ) ≤ d) :
    IsZero (Hgroup (AlgebraicGeometry.Proj
        (Stacks.ProjectiveCohomology.polyGrading R (m + 1))).ringCatSheaf ⊤ (m + 1)
      (twistingSheaf (Stacks.ProjectiveCohomology.polyGrading R (m + 1)) d)) := by
  have hbot : Stacks.ProjectiveSpace.Cohomology.twistChart R (m + 1) (-d - (((m + 1 : ℕ) : ℤ) + 1))
      (∅ : Set (Fin (m + 1 + 1))) = ⊥ :=
    Stacks.ProjectiveSpace.Cohomology.twistChart_eq_bot_of_neg (R := R) (m + 1)
      (by push_cast at hd ⊢; omega)
  have h0 : IsZero (Stacks.ProjectiveSpace.Cohomology.twistCohomology R (m + 1) d (m + 1)) := by
    refine ((Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology R m d).degreeTop).isZero_iff.mpr
      ?_
    rw [ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun f g => LinearMap.ext fun x => ?_⟩
    have hx : x = 0 := by
      have hmem : (x : (Fin (m + 1 + 1) → ℤ) →₀ R) ∈ (⊥ : Submodule R _) := hbot ▸ x.2
      exact Subtype.ext ((Submodule.mem_bot R).mp hmem)
    rw [hx, map_zero, map_zero]
  have h1 : IsZero (((Stacks.Cohomology.sectionsFunctor
      (AlgebraicGeometry.Proj (Stacks.ProjectiveCohomology.polyGrading R (m + 1))) ⊤).rightDerived
        (m + 1)).obj (twistingSheaf (Stacks.ProjectiveCohomology.polyGrading R (m + 1)) d)) := by
    have hs : Subsingleton
        (Stacks.ProjectiveSpace.Cohomology.twistCohomology R (m + 1) d (m + 1)) :=
      ModuleCat.subsingleton_of_isZero h0
    rw [ModuleCat.isZero_iff_subsingleton]
    exact hs
  exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    (Stacks.ProjectiveSpace.Cohomology.projRingSheaf R (m + 1)) ⊤ (m + 1)
    (twistingSheaf (Stacks.ProjectiveCohomology.polyGrading R (m + 1)) d)).mp h1

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)

/-- **`Rⁿ π_* 𝒪_{𝐏(E)}(d) = 0` for `d ≥ -n`**, for `E` finite locally free of constant rank
`n + 1` with `n ≥ 1`. -/
public theorem isZero_rightDerivedPlus_pushforward_twist_top {n : ℕ} (hn : 1 ≤ n)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
    (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) (d : ℤ)
    (hd : -(n : ℤ) ≤ d) :
    IsZero (((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
      (n : ℤ)).obj (D.algebra.piece d)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact isZero_rightDerivedPlus_pushforward_twist_of_poly E hqc (m + 1) hfree D d (m + 1)
    fun R => isZero_Hgroup_twistingSheaf_top R m d hd

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
