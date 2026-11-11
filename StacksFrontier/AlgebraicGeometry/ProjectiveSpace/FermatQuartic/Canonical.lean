module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HypersurfaceCanonicalSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.RingedSpaceTrace
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.SmoothDualizingModule
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HypersurfaceDifferentials

/-!
# The canonical sheaf of the Fermat quartic is trivial

Let `k` be a field and `X = V(x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴) ⊆ 𝐏³_k` the Fermat quartic. If `X` is
smooth of relative dimension two over `k` and its conormal sheaf in `𝐏³_k` is `i^*𝒪(-4)`, then

`ω_X = ⋀² Ω_{X/k} ≅ 𝒪_X`.

The first identification is part (7) of [Stacks, Tag 0FVV] (for `X` proper over `k`), the
second the adjunction formula for a smooth hypersurface of degree four in `𝐏³`
(`Stacks.ProjectiveSpace.exteriorPowerRelativeDifferentialsIsoUnitOfConormalIso`). The conormal
sheaf is `i^*𝒪(-4)` by `AlgebraicGeometry.conormalSheafZeroSchemeIso`
(`AlgebraicGeometry.FermatQuartic.nonempty_conormalSheaf_iso_pullback_twistingSheafModule`);
smoothness of relative dimension two and properness are instance arguments here.

## Main results

* `AlgebraicGeometry.FermatQuartic.nonempty_conormalSheaf_iso_pullback_twistingSheafModule`:
  `𝒞_{X/𝐏³} ≅ i^*𝒪(-4)`.
* `AlgebraicGeometry.FermatQuartic.nonempty_exteriorPower_relativeDifferentials_iso_unit_of_smooth`
  and `AlgebraicGeometry.FermatQuartic.nonempty_dualizingModule_iso_unit_of_smooth`: the two
  statements below with the conormal sheaf discharged.
* `AlgebraicGeometry.FermatQuartic`
  `.nonempty_exteriorPower_relativeDifferentials_iso_unit_of_conormalIso`: `⋀² Ω_{X/k} ≅ 𝒪_X`.
* `AlgebraicGeometry.FermatQuartic.nonempty_dualizingModule_iso_unit_of_conormalIso`: `ω_X ≅ 𝒪_X`.
* The primed variants take the conormal sheaf in the spelling `Stacks.Conormal.conormalSheaf`.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheafModule degreeSection)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.FermatQuartic

variable (k : Type u) [Field k]

/-- **The Fermat quartic has trivial `⋀² Ω`.** If `X ⟶ Spec k` is smooth of relative dimension
two and the conormal sheaf of `X ⊆ 𝐏³_k` is `i^*𝒪(-4)`, then `⋀² Ω_{X/k} ≅ 𝒪_X`. -/
theorem nonempty_exteriorPower_relativeDifferentials_iso_unit_of_conormalIso
    [hsm : SmoothOfRelativeDimension 2 (toSpec k)]
    (e : (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf (toProjectiveSpace k) :
        (fermatQuartic k).Modules) ≅
      (Scheme.Modules.pullback (toProjectiveSpace k)).obj
        (twistingSheafModule (polyGrading k 3) (-4))) :
    Nonempty (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (toSpec k)) 2 ≅
      SheafOfModules.unit (fermatQuartic k).ringCatSheaf) := by
  have : SmoothOfRelativeDimension (1 + 1) (toProjectiveSpace k ≫ projToSpecCoeff k (1 + 2)) :=
    hsm
  exact ⟨Stacks.ProjectiveSpace.exteriorPowerRelativeDifferentialsIsoUnitOfConormalIso
    (m := 1) (toProjectiveSpace k)
    (e ≪≫ (Scheme.Modules.pullback (toProjectiveSpace k)).mapIso
      (eqToIso (congrArg (twistingSheafModule (polyGrading k 3)) (by norm_num))))⟩

/-- `nonempty_exteriorPower_relativeDifferentials_iso_unit_of_conormalIso` with the conormal
sheaf in the spelling `Stacks.Conormal.conormalSheaf`. -/
theorem nonempty_exteriorPower_relativeDifferentials_iso_unit_of_conormalIso'
    [SmoothOfRelativeDimension 2 (toSpec k)]
    (e : Stacks.Conormal.conormalSheaf (toProjectiveSpace k) ≅
      (Scheme.Modules.pullback (toProjectiveSpace k)).obj
        (twistingSheafModule (polyGrading k 3) (-4))) :
    Nonempty (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (toSpec k)) 2 ≅
      SheafOfModules.unit (fermatQuartic k).ringCatSheaf) :=
  nonempty_exteriorPower_relativeDifferentials_iso_unit_of_conormalIso k
    (Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso _ ≪≫ e)

/-- **The dualizing module of the Fermat quartic is trivial.** If `X ⟶ Spec k` is proper and
smooth of relative dimension two and the conormal sheaf of `X ⊆ 𝐏³_k` is `i^*𝒪(-4)`, then
`ω_X ≅ ⋀² Ω_{X/k} ≅ 𝒪_X`, by part (7) of [Stacks, Tag 0FVV]. -/
theorem nonempty_dualizingModule_iso_unit_of_conormalIso [IsProper (toSpec k)]
    [SmoothOfRelativeDimension 2 (toSpec k)]
    (e : (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf (toProjectiveSpace k) :
        (fermatQuartic k).Modules) ≅
      (Scheme.Modules.pullback (toProjectiveSpace k)).obj
        (twistingSheafModule (polyGrading k 3) (-4))) :
    Nonempty (Stacks.Duality.dualizingModule (toSpec k) ≅
      SheafOfModules.unit (fermatQuartic k).ringCatSheaf) := by
  obtain ⟨e₁⟩ :=
    (Stacks.Duality.nonempty_relativeDualizingComplex_iso_and_relativeDualizingModule_iso_of_smooth
      (toSpec k) 2).2
  obtain ⟨e₂⟩ := nonempty_exteriorPower_relativeDifferentials_iso_unit_of_conormalIso k e
  exact ⟨e₁ ≪≫ e₂⟩

/-- `nonempty_dualizingModule_iso_unit_of_conormalIso` with the conormal sheaf in the spelling
`Stacks.Conormal.conormalSheaf`. -/
theorem nonempty_dualizingModule_iso_unit_of_conormalIso' [IsProper (toSpec k)]
    [SmoothOfRelativeDimension 2 (toSpec k)]
    (e : Stacks.Conormal.conormalSheaf (toProjectiveSpace k) ≅
      (Scheme.Modules.pullback (toProjectiveSpace k)).obj
        (twistingSheafModule (polyGrading k 3) (-4))) :
    Nonempty (Stacks.Duality.dualizingModule (toSpec k) ≅
      SheafOfModules.unit (fermatQuartic k).ringCatSheaf) :=
  nonempty_dualizingModule_iso_unit_of_conormalIso k
    (Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso _ ≪≫ e)

/-- **The conormal sheaf of the Fermat quartic in `𝐏³_k` is `i^*𝒪(-4)`**: the quartic is a
nonzero section of `𝒪(4)` on the integral scheme `𝐏³_k`, hence regular, and the conormal sheaf of
the zero scheme of a regular section of `𝒪(4)` is `i^*𝒪(-4)`
(`AlgebraicGeometry.conormalSheafZeroSchemeIso`). -/
theorem nonempty_conormalSheaf_iso_pullback_twistingSheafModule :
    Nonempty ((Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf (toProjectiveSpace k) :
        (fermatQuartic k).Modules) ≅
      (Scheme.Modules.pullback (toProjectiveSpace k)).obj
        (twistingSheafModule (polyGrading k 3) (-4))) := by
  have hgen := MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (3 + 1)) k
  have ht := Stacks.PresheafOfModules.sectionOfTop_val_top
    (twistingSheafModule (polyGrading k 3) ((4 : ℕ) : ℤ)).val
    (degreeSection (polyGrading k 3) 4 (fermatPolynomial k))
  obtain ⟨s, hs, hJ⟩ : ∃ s : (twistingSheafModule (polyGrading k 3) ((4 : ℕ) : ℤ)).sections,
      s.eval (op ⊤) ≠ 0 ∧ degreeSection (polyGrading k 3) 4 (fermatPolynomial k) = s.eval (op ⊤) :=
    ⟨_, ht ▸ Stacks.ProjectiveSpace.Cohomology.degreeSection_ne_zero k 3 4 _
      (fermatPolynomial_ne_zero k), ht.symm⟩
  have key : ∀ t : Γ(twistingSheafModule (polyGrading k 3) ((4 : ℕ) : ℤ), ⊤),
      t = s.eval (op ⊤) →
      Nonempty ((Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf
          (zeroScheme (Proj (polyGrading k 3)) (twistingSheafModule (polyGrading k 3) ((4 : ℕ) : ℤ))
            t).subschemeι : (zeroScheme (Proj (polyGrading k 3))
              (twistingSheafModule (polyGrading k 3) ((4 : ℕ) : ℤ)) t).subscheme.Modules) ≅
        (Scheme.Modules.pullback (zeroScheme (Proj (polyGrading k 3))
          (twistingSheafModule (polyGrading k 3) ((4 : ℕ) : ℤ)) t).subschemeι).obj
            (twistingSheafModule (polyGrading k 3) (-4))) := by
    rintro t rfl
    exact ⟨conormalSheafZeroSchemeIso _ _ s _
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistNegTensorIsoUnit (polyGrading k 3) hgen
          ((4 : ℕ) : ℤ))
        (isRegularSection_of_eval_top_ne_zero _ s hs) ≪≫
      (Scheme.Modules.pullback _).mapIso
        (eqToIso (congrArg (twistingSheafModule (polyGrading k 3)) (by norm_num)))⟩
  exact key _ hJ

/-- **The Fermat quartic has trivial `⋀² Ω`**, if it is smooth of relative dimension two over
`k`: `nonempty_exteriorPower_relativeDifferentials_iso_unit_of_conormalIso` with the conormal
sheaf of `nonempty_conormalSheaf_iso_pullback_twistingSheafModule`. -/
theorem nonempty_exteriorPower_relativeDifferentials_iso_unit_of_smooth
    [SmoothOfRelativeDimension 2 (toSpec k)] :
    Nonempty (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (toSpec k)) 2 ≅
      SheafOfModules.unit (fermatQuartic k).ringCatSheaf) :=
  (nonempty_conormalSheaf_iso_pullback_twistingSheafModule k).elim
    (nonempty_exteriorPower_relativeDifferentials_iso_unit_of_conormalIso k)

/-- **The dualizing module of the Fermat quartic is trivial**, if it is proper and smooth of
relative dimension two over `k`: `nonempty_dualizingModule_iso_unit_of_conormalIso` with the
conormal sheaf of `nonempty_conormalSheaf_iso_pullback_twistingSheafModule`. -/
theorem nonempty_dualizingModule_iso_unit_of_smooth [IsProper (toSpec k)]
    [SmoothOfRelativeDimension 2 (toSpec k)] :
    Nonempty (Stacks.Duality.dualizingModule (toSpec k) ≅
      SheafOfModules.unit (fermatQuartic k).ringCatSheaf) :=
  (nonempty_conormalSheaf_iso_pullback_twistingSheafModule k).elim
    (nonempty_dualizingModule_iso_unit_of_conormalIso k)

end AlgebraicGeometry.FermatQuartic

end
