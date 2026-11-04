module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.ChartCechSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.NeighbourhoodRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.ZeroSchemeLocalCohomologyTorsion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeRestriction

/-!
# Sections of the powers of an ample module are complete along the zero scheme of a section

Let `k` be a field, `X` a proper scheme over `k`, `L` an ample invertible `𝒪_X`-module, `s` a
global section of `L`, and `Y = Z(s)` with infinitesimal neighbourhoods `Y_n`. Assume

`depth(𝒪_{X, x}) + dim({x}‾) > 1`

at every point `x ∉ Y`. [Stacks, Tag 0EL2] (with [Stacks, Tag 0EL1] for `V = X`) says that
`Γ(V, 𝓕) → lim Γ(Y_n, 𝓕|_{Y_n})` is then an isomorphism, for every open `V ⊇ Y` and every
coherent `𝓕` satisfying the same bound. This file proves it in the shape that condition (2) of
[Stacks, Tag 0EJZ] consumes, namely for the powers of an ample invertible module: the base's
`Stacks.FundamentalGroup.AmplePowerSectionsCompleteFromDepth`, as the theorem
`Stacks.Algebraization.amplePowerSectionsCompleteFromDepth`.

## The proof

The proof is the source's: pass to the section ring and use Faltings' annihilator theorem. It is
organised as follows; the declarations named in this section without a namespace live in
`Stacks.Algebraization.SectionRingCone`.

* Pass to a power `L' = L^{⊗ e}` that has degree-one sections `t_j` with affine nonvanishing
  loci covering `X` (`exists_degreeOne_affine_cover`), and replace `s` by `s^e`. The zero scheme
  of `s^e` is `Y^e` (`zeroScheme_sectionPowTensorPow`), so the two infinitesimal towers are
  cofinal (`isInfinitesimalSectionsComplete_subschemeι_iff_of_pow_le`).
* In the section ring `A` of `L'`, with `f = s^e ∈ A₁` and `I = (t_j)`, the depth hypothesis off
  `Y` together with Faltings' theorem kills `H¹_I(A)` and `H²_I(A)` by a power of `f`
  (`exists_pow_smul_localCohomologyModule_sectionRing_eq_zero`).
* The charts `X_{t_j}` identify `Γ(X, L'^{⊗ m})` and `Γ(X, L'^{⊗ m} / Y^{n+1})` with the
  degree-`m` Čech cocycles of `A` and of `A / f^{n+1} A`. The degreewise theorem on formal
  functions then gives completeness
  (`isIdealPowerQuotientSectionsComplete_natTensorPow_of_localCohomology_torsion`).
* An open `V ⊇ Y` is handled by
  `Stacks.Algebraization.SectionRingCone.sectionsCompleteAmplePowers_neighborhood`. The points
  outside `V` are closed and have depth at least two, so sections extend across them.

## Main results

* `Stacks.Algebraization.SectionRingCone.isInfinitesimalSectionsComplete_tensorPowModule_of_cover`
  — completeness of every power of an ample module with a degree-one affine cover, along the
  zero scheme of a degree-one section, from the depth bound off it.
* `Stacks.Algebraization.SectionRingCone.sectionsCompleteAmplePowers_zeroScheme_of_depth` —
  condition (2) of [Stacks, Tag 0EJZ] for `Y ⊆ X`.
* `Stacks.Algebraization.amplePowerSectionsCompleteFromDepth` — the base's
  `Stacks.FundamentalGroup.AmplePowerSectionsCompleteFromDepth`, proved.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EL2](https://stacks.math.columbia.edu/tag/0EL2)
* [Stacks Project, Tag 0EJZ](https://stacks.math.columbia.edu/tag/0EJZ)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen)

universe u

namespace Stacks.Algebraization.SectionRingCone

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- **Completeness of the powers of an ample module with degree-one charts.** Let `X` be proper
over a field `k` and `M` an ample invertible module with degree-one sections `t_j` whose
nonvanishing loci are affine and cover `X`. Let `σ` be a global section of `M`. If
`depth(𝒪_{X, x}) + dim({x}‾) > 1` at every point where `σ` does not vanish, then for every
`m ≥ 0` the global sections of `M^{⊗ m}` are the inverse limit of their restrictions to the
infinitesimal neighbourhoods of the zero scheme of `σ`.

Faltings' theorem kills the low local cohomology of the section ring by a power of `σ`, and the
chart bridge turns that into completeness of the ideal-power quotients. -/
theorem isInfinitesimalSectionsComplete_tensorPowModule_of_cover
    (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (hM : Stacks.Ample.IsAmple X M)
    (σ : Γ(M, ⊤)) {r : ℕ} (t : Fin r → powSections M 1)
    (haff : ∀ j, IsAffineOpen (nvOpen M (t j))) (hcov : ⨆ j, nvOpen M (t j) = ⊤)
    (hdepth : ∀ x : X, x ∈ nvOpen M (degreeOneSection M σ) →
      enatToEInt (Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) +
        krullDimToEInt (dimClosureAt X x) > ((1 : ℤ) : EInt))
    (m : ℕ) :
    IsInfinitesimalSectionsComplete (zeroScheme X M σ).subschemeι
      (Stacks.Ample.tensorPowModule X M (m : ℤ)) := by
  have : IsNoetherianRing (sectionRing M) := isNoetherianRing_sectionRing M k g hM
  have hI : (Ideal.span (Set.range fun j => DirectSum.of (powSections M) 1 (t j))).FG :=
    Submodule.fg_span (Set.finite_range _)
  obtain ⟨c, hc⟩ := exists_pow_smul_localCohomologyModule_sectionRing_eq_zero k g M hM
    (degreeOneSection M σ) hdepth t hcov hI
  have : (Stacks.TensorPowers.natTensorPow M m).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  have hQ := isIdealPowerQuotientSectionsComplete_natTensorPow_of_localCohomology_torsion M hM σ
    t hcov haff hI ⟨c, hc 1 (by norm_num)⟩ ⟨c, hc 2 le_rfl⟩ m
  exact (isInfinitesimalSectionsComplete_iff_quotientSections _ (zeroScheme X M σ)
    (Scheme.IdealSheafData.ker_subschemeι _) (Stacks.TensorPowers.natTensorPow M m)).mpr hQ

/-- **Condition (2) of [Stacks, Tag 0EJZ] for the zero scheme of an ample section.** Let `k` be
a field, `X` proper over `k`, `L` an ample invertible module and `s ∈ Γ(X, L)`. If
`depth(𝒪_{X, x}) + dim({x}‾) > 1` at every point `x ∉ Z(s)`, then some ample invertible module
has all of its nonnegative powers complete along `Z(s)`. The module is a power `L^{⊗ e}` with
degree-one affine charts, and completeness along `Z(s^e) = Z(s)^e` transfers to `Z(s)` by
cofinality. -/
theorem sectionsCompleteAmplePowers_zeroScheme_of_depth
    (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) (s : Γ(L, ⊤))
    (hdepth : Stacks.FundamentalGroup.DepthAddDimGtOneOutsideSupport X (zeroScheme X L s)) :
    Stacks.FundamentalGroup.SectionsCompleteAmplePowers (zeroScheme X L s).subschemeι := by
  have hLs : Stacks.Ample.IsAmple X L :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mp hL
  obtain ⟨e, r, t, he, hLe, haff, hcov⟩ := exists_degreeOne_affine_cover L hLs
  have hsupp := support_zeroScheme_sectionPowTensorPow L s he
  have hdepthe : ∀ x : X, x ∈ nvOpen (Stacks.Ample.tensorPowModule X L (e : ℤ))
      (degreeOneSection _ (sectionPowTensorPow L s e)) →
      enatToEInt (Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) +
        krullDimToEInt (dimClosureAt X x) > ((1 : ℤ) : EInt) := by
    intro x hx
    have hs : (nvOpen (Stacks.Ample.tensorPowModule X L (e : ℤ))
        (degreeOneSection _ (sectionPowTensorPow L s e)) : Set X) =
        Stacks.Ample.nonvanishingLocus _ (sectionPowTensorPow L s e) := by
      rw [Stacks.AmpleFiniteAvoidance.coe_nvOpen, nvLocus_degreeOneSection]
    have hx' : x ∉ ((zeroScheme X (Stacks.Ample.tensorPowModule X L (e : ℤ))
        (sectionPowTensorPow L s e)).support : Set X) :=
      notMem_support_zeroScheme_of_notMem_asHomogeneousIdeal _ hLe (sectionPowTensorPow L s e)
        (degreeOneSection _ (sectionPowTensorPow L s e)) hs x
        ((mem_nvOpen_iff_notMem_asHomogeneousIdeal _ hLe one_pos _ x).mp hx)
    rw [hsupp] at hx'
    exact hdepth x hx'
  have hJ : ∀ m : ℕ, IsInfinitesimalSectionsComplete (zeroScheme X L s).subschemeι
      (Stacks.Ample.tensorPowModule X (Stacks.Ample.tensorPowModule X L (e : ℤ)) (m : ℤ)) :=
    fun m => (isInfinitesimalSectionsComplete_subschemeι_iff_of_pow_le he
      (zeroScheme_sectionPowTensorPow L s e).ge (zeroScheme_sectionPowTensorPow_le L s he) _).mp
      (isInfinitesimalSectionsComplete_tensorPowModule_of_cover k g _ hLe
        (sectionPowTensorPow L s e) t haff hcov hdepthe m)
  have hLeinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (Stacks.Ample.tensorPowModule X L (e : ℤ)) :=
    Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible
  refine ⟨Stacks.Ample.tensorPowModule X L (e : ℤ), hLeinv,
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X _).mpr hLe, 0, fun m _ => ?_⟩
  exact isInfinitesimalSectionsComplete_of_iso _
    (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X _ (m : ℤ)).symm (hJ m)

end Stacks.Algebraization.SectionRingCone

namespace Stacks.Algebraization

/-- **[Stacks, Tag 0EL2], in the shape condition (2) of [Stacks, Tag 0EJZ] consumes it.** The
base's `Stacks.FundamentalGroup.AmplePowerSectionsCompleteFromDepth` holds. For `X` proper over a
field, `L` ample invertible and `s ∈ Γ(X, L)` with `depth(𝒪_{X, x}) + dim({x}‾) > 1` off `Z(s)`:
some ample invertible module has all of its large powers complete along `Z(s) ⊆ X`, and also
along `Z(s) ⊆ V` for every open `V ⊇ Z(s)`. -/
public theorem amplePowerSectionsCompleteFromDepth :
    Stacks.FundamentalGroup.AmplePowerSectionsCompleteFromDepth.{u} := by
  intro k _ X g _ L _ hL s hdepth
  have hX := SectionRingCone.sectionsCompleteAmplePowers_zeroScheme_of_depth k g L hL s hdepth
  exact ⟨hX, fun W =>
    SectionRingCone.sectionsCompleteAmplePowers_neighborhood L k g hL s hdepth W hX⟩

end Stacks.Algebraization

end
