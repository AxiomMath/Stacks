module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.ZeroNotInvertible
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Tautological
public import StacksFrontier.AlgebraicGeometry.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialDividedPowers

/-!
# The projective bundle of a module of rank zero

A finite locally free module `ℰ` of rank zero is zero, so the tautological surjection
`π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)` exhibits the twist of its projective bundle as a quotient of zero. An
invertible module which is zero lives on the empty scheme, so `𝐏(ℰ)` is empty and all its Chow
groups vanish. This is the case `r = 0` of the projective space bundle formula
[Stacks, Tag 02TX], whose source `⨁_{i = 0}^{r - 1} A_{k + i}(X)` is then the empty sum.

## Main results

* `Stacks.Chow.isZero_of_isFiniteLocallyFreeOfRank_zero` — a module finite locally free of rank
  zero is a zero object.
* `Stacks.Chow.isEmpty_bundle_of_rank_zero` — its projective bundle is empty.
* `Stacks.Chow.subsingleton_chowGroup_of_isEmpty` — the Chow groups of an empty scheme vanish.
* `Stacks.Chow.subsingleton_chowGroup_bundle_of_rank_zero` — **Stacks 02TX in rank zero**: the
  Chow groups of the projective bundle of a module of rank zero vanish.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TV](https://stacks.math.columbia.edu/tag/02TV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (E : X.Modules)

/-- **A module finite locally free of rank zero is zero.** Locally it is free on the empty index
type, and vanishing of a module is local. -/
theorem isZero_of_isFiniteLocallyFreeOfRank_zero
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0] : IsZero E := by
  choose U hU e using (AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_iff E 0).mpr
    ‹_›
  refine Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.isZero_of_isZero_restrict U
    (top_unique fun x _ ↦ Opens.mem_iSup.2 ⟨x, hU x⟩) E fun x ↦ ?_
  exact (SheafOfModules.isZero_free_of_isEmpty _).of_iso (e x).some

/-- **The projective bundle of a module of rank zero is empty.** The tautological map
`π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)` is an epimorphism out of a zero object, so the twist is zero; being also
invertible, it lives on the empty scheme. -/
theorem isEmpty_bundle_of_rank_zero
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0] :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
    IsEmpty (bundle E) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have hpull : IsZero ((Scheme.Modules.pullback
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (Stacks.SymGraded.schemeSheafGradedAlgebra E (bundlePieces E))).toBase).obj E) :=
    Functor.map_isZero _ (isZero_of_isFiniteLocallyFreeOfRank_zero E)
  have := Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E (bundlePieces E)
  have htwist : IsZero (Stacks.ProjectiveBundleSplitting.tautologicalTwist E (bundlePieces E)) :=
    hpull.of_epi (Stacks.ProjectiveBundleSplitting.tautologicalMap E (bundlePieces E))
  exact Stacks.AlgebraicGeometry.ProjRepresentsF1.isEmpty_of_isZero_of_isInvertible _ _
    (isInvertible_bundleTwist E) htwist

/-- **The Chow groups of an empty scheme vanish**: it has no points, so its only cycle is zero. -/
theorem subsingleton_chowGroup_of_isEmpty (C : ChowSituation.{u}) {P : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] [IsEmpty P] (k : ℤ) :
    Subsingleton (chowGroup C sP k) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  obtain ⟨d, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  congr 1
  exact Subtype.ext (Function.locallyFinsuppWithin.ext fun w ↦ isEmptyElim w)

/-- **Stacks 02TX in rank zero.** For a module `ℰ` finite locally free of rank zero, the Chow
groups of its projective bundle vanish in every degree, so the map
`⨁_{i = 0}^{-1} A_{k + i}(X) = 0 ⟶ A_{k - 1}(𝐏(ℰ))` of the projective space bundle formula is an
isomorphism. -/
theorem subsingleton_chowGroup_bundle_of_rank_zero (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0] (k : ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
    Subsingleton (chowGroup C (bundleProj E ≫ sX) k) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
  have := isEmpty_bundle_of_rank_zero E
  exact subsingleton_chowGroup_of_isEmpty C _ k

end Stacks.Chow

end
