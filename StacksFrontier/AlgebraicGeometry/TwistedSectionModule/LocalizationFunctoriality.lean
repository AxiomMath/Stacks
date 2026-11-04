module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingGradedHom
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.DivisionFunctoriality

/-!
# Stacks Tag 0B5L's comparison map is natural in the twisted module

Stacks Tag 0B5I asks its comparison `M̃ ⟶ f_* ℱ` to be a natural transformation in `ℱ`, and Stacks
Tag 01QJ repeats that for the transposed morphism. On a standard open the comparison is Tag 0B5L's
map `Γ_*(X, ℱ, L)_{(s)} ⟶ Γ(X_s, ℱ)`, which is `Stacks.TwistedSections.localizationLiftOfDegree`,
and this file proves **that map is natural in `ℱ`**: the square

`Γ_*(X, ℱ, L)_{(s)} ⟶ Γ_*(X, ℱ', L)_{(s)}` over `N ⟶ N'`

commutes as soon as the two families of divisions are compatible on numerators, which is what
`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/DivisionFunctoriality.lean` supplies.

The vertical map on the sources is the covariance of the degree-zero localization in the graded
module, `Stacks.SheafOfModules.degreeZeroLocalizationMap`, applied to
`Stacks.TwistedSections.twistModuleLinearMap`.

## Main results

* `Stacks.TwistedSections.localizationLift_mapDegreeZeroLocalization`: **the naturality square
  for `localizationLiftOfDegree`**, from compatibility of the division families on numerators.
* `Stacks.TwistedSections.localizationLiftOfMonoidal_mapDegreeZeroLocalization`: the same for the
  map produced by a monoidal functor — on a scheme, for restriction to an open inside the
  nonvanishing locus, which is Tag 0B5L's map itself.

## Implementation notes

Both proofs reduce a general element of the degree-zero localization to a single fraction with
`Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree`, whose numerator has
degree `n * d`, and then cross once to the `d * n` spelling the divisions are indexed at; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/LocalizationComparison.lean` for why the two
orders of that product cannot both be used.

## What is not done

**This is not yet Tag 0B5I's naturality square.** That square's vertical map on the sources is
`(tildeFunctor L).map φ` read on the sections over `D₊(p)`, transported along
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`. Nothing
in the library identifies that transported map with
`Stacks.SheafOfModules.degreeZeroLocalizationMap` applied to
`Stacks.TwistedSections.twistModuleLinearMap`, so the square below is about the localizations
themselves and not yet about the sections of `M̃`.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections sectionRing HasTrivialSelfBraiding)
open scoped Stacks.GradedLocalization

universe v₂ u₂ w v u

namespace Stacks.TwistedSections

section Abstract

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] {F F' L : C}
  [(MonoidalCategory.tensorRight L).Additive] [BraidedCategory C] [HasTrivialSelfBraiding L]
  {N : Type w} [AddCommGroup N] {N' : Type w} [AddCommGroup N']

/-- **The comparison map of Stacks Tag 0B5L is natural in the twisted module.** If the two
families of divisions agree on numerators up to `ψ`, then the two ways round the square — divide
in `ℱ'` after pushing the fraction forward, or push the division forward — agree. -/
theorem localizationLift_mapDegreeZeroLocalization {d : ℕ} (s : powSections L d)
    (D : (n : ℕ) → twistSections F L (d * n) →+ N) (hD : IsPowerInvariantOfDegree s D)
    (D' : (n : ℕ) → twistSections F' L (d * n) →+ N') (hD' : IsPowerInvariantOfDegree s D')
    (φ : F ⟶ F') (ψ : N →+ N')
    (hcompat : ∀ (n : ℕ) (t : twistSections F L (d * n)),
      D' n (twistSectionsMap φ (d * n) t) = ψ (D n t))
    (z : sectionAtNonvanishingOpenOfDegree F L s) :
    localizationLiftOfDegree s D' hD'
        (Stacks.SheafOfModules.degreeZeroLocalizationMap (sectionGrading L)
          (moduleGrading F L) (moduleGrading F' L) (twistModuleLinearMap (L := L) φ)
          (twistModuleHom_mem_moduleGrading (L := L) φ) (homogeneousSectionOfDegree s) z) =
      ψ (localizationLiftOfDegree s D hD z) := by
  obtain ⟨n, x, hx, hz⟩ :=
    Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree
      (sectionGrading L) (moduleGrading F L) (homogeneousSectionOfDegree_mem s) z
  obtain ⟨t, rfl⟩ := mem_moduleGrading_natCast_iff.mp hx
  set t' : twistSections F L (d * n) := twistCongr (Nat.mul_comm n d) t with ht'
  have hof : DirectSum.of (twistSections F L) (d * n) t' =
      DirectSum.of (twistSections F L) (n * d) t := of_twistCongr _ t
  rw [hof.symm] at hz
  have hmap : ((Stacks.SheafOfModules.degreeZeroLocalizationMap (sectionGrading L)
        (moduleGrading F L) (moduleGrading F' L) (twistModuleLinearMap (L := L) φ)
        (twistModuleHom_mem_moduleGrading (L := L) φ) (homogeneousSectionOfDegree s) z :
        GradedModuleDegreeZeroLocalization (sectionGrading L) (moduleGrading F' L)
          (homogeneousSectionOfDegree s)) :
      LocalizedModule.Away (homogeneousSectionOfDegree s) (twistModule F' L)) =
      LocalizedModule.mk (S := Submonoid.powers (homogeneousSectionOfDegree s))
        (DirectSum.of (twistSections F' L) (d * n) (twistSectionsMap φ (d * n) t'))
        ⟨homogeneousSectionOfDegree s ^ n, ⟨n, rfl⟩⟩ := by
    refine (Stacks.SheafOfModules.degreeZeroLocalizationMap_coe (sectionGrading L)
      (moduleGrading F L) (moduleGrading F' L) (twistModuleLinearMap (L := L) φ)
      (twistModuleHom_mem_moduleGrading (L := L) φ) (homogeneousSectionOfDegree s) z).trans ?_
    rw [hz, LocalizedModule.map_mk]
    congr 1
    exact twistModuleHom_of (L := L) φ (d * n) t'
  rw [localizationLiftOfDegree_fraction s D' hD' _ n _ hmap,
    localizationLiftOfDegree_fraction s D hD z n t' hz, hcompat]

end Abstract

section Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [Preadditive D]
  (G : C ⥤ D) [G.Monoidal] [G.Additive] {F F' L : C}
  [(MonoidalCategory.tensorRight L).Additive] [HasTrivialSelfBraiding L]
  [(MonoidalCategory.tensorRight (G.obj L)).Additive]

/-- **Stacks Tag 0B5L's comparison map, as produced by a monoidal functor, is natural in the
twisted module.** On a scheme, with `G` the restriction to an open inside the nonvanishing locus
of `s`, this is the naturality in `ℱ` of Tag 0B5L's own map. -/
theorem localizationLiftOfMonoidal_mapDegreeZeroLocalization {d : ℕ} (s : powSections L d)
    [IsIso (mapPowSections G s)] (φ : F ⟶ F')
    (z : sectionAtNonvanishingOpenOfDegree F L s) :
    localizationLiftOfMonoidal G (F := F') s
        (Stacks.SheafOfModules.degreeZeroLocalizationMap (sectionGrading L)
          (moduleGrading F L) (moduleGrading F' L) (twistModuleLinearMap (L := L) φ)
          (twistModuleHom_mem_moduleGrading (L := L) φ) (homogeneousSectionOfDegree s) z) =
      twistSectionsMap (G.map φ) 0 (localizationLiftOfMonoidal G (F := F) s z) :=
  localizationLift_mapDegreeZeroLocalization s (monoidalDivision G s)
    (isPowerInvariant_monoidalDivision G s) (monoidalDivision G s)
    (isPowerInvariant_monoidalDivision G s) φ
    (twistSectionsHom (G.map φ) 0) (monoidalDivision_twistSectionsMap G s φ) z

end Monoidal

end Stacks.TwistedSections

end
