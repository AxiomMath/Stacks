module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence

/-!
# The algebraization situation of Stacks 0EIL is inhabited, and its conditions are not vacuous

Every theorem of Stacks chapter 52's algebraization package is stated for a variable
`S : Stacks.Algebraization.AlgebraizationSituation`, and until this file nothing in either Lean
tree exhibited one: the whole development was conditional on an unconstructed ambient structure.
This file supplies a witness and checks that the four conditions of Stacks 0EIL are satisfiable,
that the completeness hypothesis of the last of them is satisfiable, and that the containment
hypothesis buried in condition (3) is not automatic.

The witness is `A = ℤ` with `I = ⊥ ⊆ 𝔞 = ⊤`, so `X = Spec ℤ`, `Y = X`, `Z = ∅` and `U = X`. The
ring is Noetherian and `⊥`-adically complete, and `Y` is nonempty, which is what makes the last
statement below a genuine refutation rather than an artefact of an empty space.

## Main results

* `Stacks.Algebraization.intWitness` — the witness.
* `Stacks.Algebraization.conditions_of_completion` — each of conditions (3), (4), (5) and (6) of
  Stacks 0EIL holds for the completion of an arbitrary coherent module, so none of the four
  predicates is empty.
* `Stacks.Algebraization.not_closedLocus_subset_bot` — the containment
  `U ∩ Y ⊆ V` required of the neighbourhood `V` in condition (3) fails at `V = ⊥`, so that
  hypothesis is restrictive rather than automatic.

## References

* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 0EIL](https://stacks.math.columbia.edu/tag/0EIL)
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry
namespace Stacks.Algebraization

/-- Q3: the ambient structure is exhibited. `A = ℤ`, `I = ⊥ ≤ 𝔞 = ⊤`, so `U = X`. -/
public def intWitness : AlgebraizationSituation.{0} where
  A := ℤ
  I := ⊥
  a := ⊤
  I_le_a := bot_le

/-- Q4: the completeness hypothesis of
`Stacks.Algebraization.isRestrictionOfCompletion_of_extendsToX` holds at this intWitness, by
Mathlib's instance `IsAdicComplete.bot`. -/
example : IsAdicComplete intWitness.I intWitness.A :=
  inferInstanceAs (IsAdicComplete (⊥ : Ideal ℤ) ℤ)

/-- Q1/Q2: each condition is inhabited — the completion of any coherent module satisfies it. -/
public theorem conditions_of_completion (S : AlgebraizationSituation.{0})
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf) :
    IsCompletionNearClosed S
        ((completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).obj G) ∧
      IsCompletionOfRestriction S
        ((completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).obj G) ∧
      IsRestrictionOfCompletion S
        ((completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).obj G) ∧
      ExtendsToX S ((completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).obj G) := by
  have h2 := (isCompletion_iff_ofRestriction S _).1 (Functor.obj_mem_essImage _ G)
  have h5 := (isCompletionOfRestriction_iff_isRestrictionOfCompletion S _).1 h2
  exact ⟨(isCompletion_iff_nearClosed S _).1 (Functor.obj_mem_essImage _ G), h2, h5,
    extendsToX_of_isRestrictionOfCompletion S _ h5⟩

/-- Q5: the `∀`/`⊆` hypothesis of `IsCompletionNearClosed` is REFUTABLE at a degenerate
instance: at `V = ⊥` the required containment fails, because the closed locus of the witness is
all of `U`. -/
public theorem not_closedLocus_subset_bot :
    ¬ ((intWitness.U.ι.base ⁻¹' Set.range intWitness.Yι.base) ⊆
      ((⊥ : intWitness.U.toScheme.Opens) : Set intWitness.U.toScheme)) := by
  have hU : (intWitness.U : Set intWitness.X) = Set.univ := by
    change (PrimeSpectrum.zeroLocus ((⊤ : Ideal ℤ) : Set ℤ))ᶜ = Set.univ
    simp
  have hns : ¬ Subsingleton (ℤ ⧸ (⊥ : Ideal ℤ)) := by
    rw [Ideal.Quotient.subsingleton_iff]
    simp
  have hnt : Nontrivial (ℤ ⧸ (⊥ : Ideal ℤ)) := not_subsingleton_iff_nontrivial.1 hns
  obtain ⟨y⟩ := (inferInstance : Nonempty (PrimeSpectrum (ℤ ⧸ (⊥ : Ideal ℤ))))
  have hx : intWitness.Yι.base y ∈ (intWitness.U : Set intWitness.X) := hU ▸ Set.mem_univ _
  intro hsub
  have hmem : (⟨intWitness.Yι.base y, hx⟩ : intWitness.U.toScheme) ∈
      intWitness.U.ι.base ⁻¹' Set.range intWitness.Yι.base := ⟨y, rfl⟩
  have hbad := hsub hmem
  simp only [TopologicalSpace.Opens.coe_bot] at hbad
  exact hbad

end Stacks.Algebraization
end
