module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.ReductionDegree
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegrees.DegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegrees.VeroneseTransport

/-!
# Part (5) of Tag 0B5R: `M_n ⟶ Γ(Proj S, M(n)~)` is an isomorphism in all large degrees

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring which is Noetherian, and let `M = ⨁_{n ∈ ℤ} 𝒨 n` be a
finite graded `S`-module, `X = Proj S`. Then the canonical maps

`𝒨 n ⟶ Γ(X, M(n)~)`

of Equation 01MR are bijective in all sufficiently large degrees. This is part (5) of
[Stacks, Tag 0B5R]: the tag's `N' = ⨁_{n ≥ k} H⁰(X, M(n)~)` and the canonical map `M → N'` of
part (4) is Equation 01MR, whose degree-`n` component on `M_n` is exactly
`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections`, by
`Stacks.AlgebraicGeometry.ProjCoherentII.globalSectionsModuleMap_hom_component`.

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegrees`
  `.exists_bijective_degreeNToGlobalSections_of_isNoetherian`: for `S` Noetherian and `M` finite,
  the maps `𝒨 n ⟶ Γ(X, M(n)~)` are bijective in all sufficiently large degrees.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open Stacks.AlgebraicGeometry.ProjShiftedSections (degreeNToGlobalSections)
open Stacks.GradedModule (shiftedGrading addSubgroupGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjLargeDegrees

universe u

/-- For `S` a Noetherian graded ring and `M` a finite graded `S`-module, the canonical map
`M_n → Γ(Proj S, M(n)~)` of Equation 01MR is an isomorphism in all sufficiently large degrees.
This is part (5) of [Stacks, Tag 0B5R]. -/
theorem exists_bijective_degreeNToGlobalSections_of_isNoetherian
    {S M : Type u} {σ τ : Type u} [CommRing S] [IsNoetherianRing S]
    [AddCommGroup M] [Module S M] [Module.Finite S M]
    [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
    [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
    [SetLike.GradedSMul 𝒮 𝒨] :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
      Function.Bijective (degreeNToGlobalSections 𝒮 𝒨 n) := by
  classical
  obtain ⟨r, f, deg, d, hdeg, hfdeg, hgen, hdpos, hLd, hveronese, -, -⟩ :=
    ProjCoherentII.exists_reductionDegree 𝒮
  have : IsNoetherianRing (𝒮 0) := ProjCoherentII.isNoetherianRing_gradeZero 𝒮
  let := Stacks.Veronese.veroneseGradingGradedRing 𝒮 d hdpos
  have : IsNoetherianRing (Stacks.Veronese.veroneseGrading 𝒮 d 0) :=
    Stacks.Veronese.isNoetherianRing_veroneseGrading_zero 𝒮 d
  obtain ⟨nv, yv, hyv, hyvgen⟩ :=
    Stacks.Veronese.exists_finite_degreeOne_generators_veroneseSubring 𝒮 d f deg hdeg hfdeg hgen
      hveronese
  have hstep : ∀ q : Fin d, ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m →
      Function.Bijective (degreeNToGlobalSections 𝒮 𝒨 ((d : ℤ) * m + ((q : ℕ) : ℤ))) := by
    intro q
    let := Stacks.Veronese.veroneseModuleGradingDecomposition 𝒮
      (shiftedGrading (addSubgroupGrading 𝒨) ((q : ℕ) : ℤ)) d hdpos
    have : Module.Finite (Stacks.Veronese.veroneseSubring 𝒮 d)
        (Stacks.Veronese.veroneseSubmodule 𝒮
          (shiftedGrading (addSubgroupGrading 𝒨) ((q : ℕ) : ℤ)) d) :=
      Stacks.Veronese.finite_veroneseSubmodule_of_lcm_dvd 𝒮 hdeg hfdeg hgen hdpos hLd
        (shiftedGrading (addSubgroupGrading 𝒨) ((q : ℕ) : ℤ))
    obtain ⟨m₀, hm₀⟩ := exists_bijective_degreeNToGlobalSections_degreeOne
      (Stacks.Veronese.veroneseGrading 𝒮 d)
      (Stacks.Veronese.veroneseModuleGrading 𝒮
        (shiftedGrading (addSubgroupGrading 𝒨) ((q : ℕ) : ℤ)) d) yv hyv hyvgen
    refine ⟨m₀, fun m hm => ?_⟩
    rw [mul_comm (d : ℤ) m]
    exact bijective_degreeNToGlobalSections_addSubgroupGrading 𝒮 𝒨 _ <|
      bijective_degreeNToGlobalSections_shiftedGrading 𝒮 (addSubgroupGrading 𝒨) _ (m * d) <|
        bijective_degreeNToGlobalSections_of_veronese 𝒮 _ d hdpos m (hm₀ m hm)
  choose m₀ hm₀ using hstep
  set B : ℕ := Finset.univ.sup (fun q : Fin d => (m₀ q).toNat)
  refine ⟨(d : ℤ) * ((B : ℤ) + 1) + (d : ℤ), fun n hn => ?_⟩
  obtain ⟨p, hp⟩ : ∃ p : Fin d × ℤ, Stacks.GradedModule.intEquivResidue d hdpos p = n :=
    ⟨(Stacks.GradedModule.intEquivResidue d hdpos).symm n, Equiv.apply_symm_apply _ _⟩
  rw [Stacks.GradedModule.intEquivResidue_apply] at hp
  have hq : ((p.1 : ℕ) : ℤ) < (d : ℤ) := by exact_mod_cast p.1.2
  have hBq : m₀ p.1 ≤ (B : ℤ) := (Int.self_le_toNat _).trans <| by
    exact_mod_cast Finset.le_sup (f := fun q : Fin d => (m₀ q).toNat) (Finset.mem_univ p.1)
  have hmB : (B : ℤ) < p.2 := by
    by_contra! hle
    nlinarith [mul_le_mul_of_nonneg_left hle (Int.natCast_nonneg d)]
  rw [← hp]
  exact hm₀ p.1 p.2 (by omega)

end Stacks.AlgebraicGeometry.ProjLargeDegrees

end
