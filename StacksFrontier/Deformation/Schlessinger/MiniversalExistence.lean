module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Formal.VersalObject.MinimalExistence
public import StacksFrontier.Deformation.Schlessinger.VersalExistence
public import StacksFrontier.Deformation.VersalObject.MinimalVersalOrbitBijection

/-!
# Schlessinger's conditions give a minimal versal object with orbitwise bijective differential

Stacks 06IX is the equivalence, for a predeformation category `𝓕` over `𝒞_Λ`, of

1. `𝓕` has a minimal versal formal object with bijective differential,
2. `𝓕` has a minimal versal formal object whose differential is bijective on
   `Der_Λ(k, k)`-orbits, and
3. `𝓕` satisfies Schlessinger's conditions (S1) and (S2) and has a finite-dimensional tangent
   space.

This file proves the implication (3) implies (2).

## Main results

* `Deformation.exists_minimalVersal_hasBijectiveDifferentialOnDerivationOrbits`: a
  predeformation category satisfying (S1) and (S2) with finite-dimensional tangent space has a
  minimal versal formal object whose differential is bijective on derivation orbits.

## References

* [Stacks Project, Tag 06IX](https://stacks.math.columbia.edu/tag/06IX)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w uF vF

/-- A predeformation category satisfying Schlessinger's conditions (S1) and (S2) whose tangent
space is finite dimensional has a minimal versal formal object whose differential is bijective
on `Der_Λ(k, k)`-orbits. -/
@[stacks 06IX "(3) implies (2)", sga "7 VI 1.11" "(i)", sga "7 VI 1.20" "special case"]
public theorem exists_minimalVersal_hasBijectiveDifferentialOnDerivationOrbits
    (Λ : Type u) (k : Type w) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hpre : IsPredeformationCategory.{u, v, w} 𝓕.p)
    (hS1 : SchlessingerConditionS1 𝓕.p)
    (hS2 : SchlessingerConditionS2 𝓕.p)
    (hfin :
      letI : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨hpre⟩
      letI : Fact (SchlessingerConditionS2
          (Functor.Elements.π (isomorphismClasses 𝓕 hpre.cofibered))) :=
        ⟨schlessingerConditionS2_of_isIsomorphismClasses 𝓕 hpre.cofibered hS2 (Or.inl hpre)⟩
      FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k
        (isomorphismClasses 𝓕 hpre.cofibered))) :
    ∃ ξ : FormalObject 𝓕.p,
      IsMinimalVersal hpre.cofibered ξ ∧
        HasBijectiveDifferentialOnDerivationOrbits.{u, v, w} 𝓕.p hpre ξ := by
  obtain ⟨ξ, hξ⟩ := exists_minimalVersalFormalObject hpre
    (exists_versalFormalObject Λ k 𝓕 hpre hS1 hS2 hfin)
  exact ⟨ξ, hξ, minimalVersal_hasBijectiveDifferentialOnDerivationOrbits 𝓕.p hpre hS2 ξ hξ⟩

end Deformation

end
