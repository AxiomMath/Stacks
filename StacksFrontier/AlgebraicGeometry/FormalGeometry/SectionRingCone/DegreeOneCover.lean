module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.Ample
public import StacksFrontier.AlgebraicGeometry.AmplePositivePower.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemePower
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerThickenings

/-!
# A power of an ample module with degree-one charts, and the power of a section

Let `X` be a scheme and `L` an ample invertible `𝒪_X`-module. The affine nonvanishing loci `X_b`
of homogeneous sections `b` of the section ring `Γ_*(X, L)` cover `X`, but in general the `b` live
in different degrees and `L` itself may have no sections at all. Passing to a power
`L' = L^{⊗ e}` puts finitely many such sections in **degree one** of `Γ_*(X, L')`. That is the
shape in which the section ring of `L'` and its localizations at the chart elements are easiest
to handle: on `X_t` with `t` of degree one, `t` trivializes `L'`.

A section `s` of `L` gives the section `s^e` of `L'`, and the zero scheme of `s^e` is cut out by
the `e`-th power of the ideal of the zero scheme of `s`. The two closed subschemes therefore have
the same support and cofinal towers of infinitesimal neighbourhoods; see
`StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.ZeroSchemePowerCofinality`.

## Main definitions

* `Stacks.Algebraization.SectionRingCone.degreeOneSection` — a global section of an invertible
  module `M`, read as a degree-one element of the section ring `Γ_*(X, M)`.
* `Stacks.Algebraization.SectionRingCone.sectionPowTensorPow` — the `e`-th power `s^e` of a global
  section `s` of `L`, as a global section of `Stacks.Ample.tensorPowModule X L e`.

## Main results

* `Stacks.Algebraization.SectionRingCone.exists_degreeOne_affine_cover` — for `L` ample there are
  `e ≥ 1` and finitely many degree-one elements `t j` of the section ring of `L^{⊗ e}` whose
  nonvanishing loci are affine and cover `X`; `L^{⊗ e}` is again ample.
* `Stacks.Algebraization.SectionRingCone.zeroScheme_sectionPowTensorPow` — `Z(s^e) = Z(s)^e`.
* `Stacks.Algebraization.SectionRingCone.zeroScheme_sectionPowTensorPow_le` and
  `Stacks.Algebraization.SectionRingCone.support_zeroScheme_sectionPowTensorPow` — `Z(s^e)` lies
  between `Z(s)^e` and `Z(s)`, with the same support, for `e ≥ 1`.

## Implementation notes

The power `L'` is spelled `Stacks.Ample.tensorPowModule X L e`, the family `Stacks.Ample.IsAmple`
is stated over; its invertibility is an instance and its ampleness is
`Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple`. The power `s^e` is the sectionwise
power `Stacks.SheafOfModules.Invertible.sectionPow'`, for which `Z(s^e) = Z(s)^e` is proved as
`AlgebraicGeometry.zeroScheme_sectionPow'_degreeOne`, carried to `tensorPowModule` along
`Stacks.PowerFamilyBridge.tensorPowerModuleIso`.

A degree-one element of `Γ_*(X, M)` is a morphism `𝟙 ⟶ 𝟙 ⊗ M` (the first natural tensor power is
`𝟙 ⊗ M` on the nose); `degreeOneSection` composes the honest section with the inverse left unitor
and reads it through `Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv`, so that its
nonvanishing locus is that of the section it came from.

## References

* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample
open Stacks.AmpleFiniteAvoidance (nvLocus nvOpen coe_nvOpen)
open Stacks.GradedSections (powSections)

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

namespace Stacks.Algebraization.SectionRingCone

variable {X : Scheme.{u}}

/-! ### Degree-one elements of the section ring -/

section DegreeOne

variable (M : X.Modules)

/-- **A global section of `M` read as a degree-one element of `Γ_*(X, M)`.** The first natural
tensor power of `M` is `𝟙 ⊗ M`; the section is moved there by the inverse left unitor and read as
a morphism out of the unit through the carrier comparison. -/
def degreeOneSection (σ : Γ(M, ⊤)) : powSections M 1 :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (𝟙_ X.Modules ⊗ M)).symm
    ((λ_ M).inv.app ⊤ σ)

/-- The honest global section attached to `degreeOneSection σ` is `σ`, moved by the inverse left
unitor. -/
theorem globalSection_degreeOneSection (σ : Γ(M, ⊤)) :
    Stacks.SectionProduct.globalSection X (𝟙_ X.Modules ⊗ M) (degreeOneSection M σ) =
      (λ_ M).inv.app ⊤ σ :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (𝟙_ X.Modules ⊗ M)).apply_symm_apply
    _

/-- **The nonvanishing locus of `degreeOneSection σ` is that of `σ`.** -/
theorem nvLocus_degreeOneSection (σ : Γ(M, ⊤)) :
    nvLocus M (degreeOneSection M σ) = nonvanishingLocus M σ := by
  change nonvanishingLocus (𝟙_ X.Modules ⊗ M)
      (Stacks.SectionProduct.globalSection X (𝟙_ X.Modules ⊗ M) (degreeOneSection M σ)) = _
  rw [globalSection_degreeOneSection]
  exact nonvanishingLocus_congr (λ_ M).symm σ

end DegreeOne

/-! ### The degree-one affine cover of a power -/

variable (L : X.Modules) [IsInvertibleModule X L]

/-- **An ample invertible module has a power with a finite degree-one affine cover.** For `L`
ample there are `e ≥ 1`, a finite family `t j` of degree-one elements of the section ring of
`L' = L^{⊗ e}` whose nonvanishing loci `X_{t j}` are affine and cover `X`, and `L'` is again ample.

Ampleness, together with quasi-compactness, gives finitely many affine `X_{c i}` covering `X` with
the `c i` all in one degree `e` (`Stacks.SectionExtension.exists_common_degree_affine_cover`). Each
`c i` is then an honest global section of `L^{⊗ e}` with the same nonvanishing locus
(`Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq`), hence a degree-one element of
`Γ_*(X, L^{⊗ e})` by `degreeOneSection`. -/
theorem exists_degreeOne_affine_cover (hL : IsAmple X L) :
    ∃ (e : ℕ) (r : ℕ) (t : Fin r → powSections (tensorPowModule X L (e : ℤ)) 1),
      1 ≤ e ∧ IsAmple X (tensorPowModule X L (e : ℤ)) ∧
        (∀ j, IsAffineOpen (nvOpen (tensorPowModule X L (e : ℤ)) (t j))) ∧
        ⨆ j, nvOpen (tensorPowModule X L (e : ℤ)) (t j) = ⊤ := by
  obtain ⟨N, -, F, c, hN, -, -, haff, hcov⟩ :=
    Stacks.SectionExtension.exists_common_degree_affine_cover L hL (n := 1) le_rfl 0
  choose σ hσ using fun i => Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq L N (c i)
  let E := Fintype.equivFin {y : X // y ∈ F}
  let t : Fin (Fintype.card {y : X // y ∈ F}) → powSections (tensorPowModule X L (N : ℤ)) 1 :=
    fun j => degreeOneSection _ (σ (E.symm j))
  have hopen : ∀ j, nvOpen (tensorPowModule X L (N : ℤ)) (t j) = nvOpen L (c (E.symm j)) :=
    fun j => Opens.ext (by rw [coe_nvOpen, coe_nvOpen, nvLocus_degreeOneSection, hσ])
  refine ⟨N, _, t, hN, Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L N hN hL,
    fun j => by rw [hopen j]; exact haff _, top_le_iff.mp ?_⟩
  refine hcov.trans (iSup_le fun i => ?_)
  refine le_trans ?_ (le_iSup _ (E i))
  rw [hopen, E.symm_apply_apply]

/-! ### The power of a section and its zero scheme -/

/-- **The `e`-th power of a global section of `L`**, as a global section of
`L^{⊗ e} = Stacks.Ample.tensorPowModule X L e`: the sectionwise power
`Stacks.SheafOfModules.Invertible.sectionPow'`, carried across
`Stacks.PowerFamilyBridge.tensorPowerModuleIso` and the reindexing `1 * e = e`. -/
def sectionPowTensorPow (s : Γ(L, ⊤)) (e : ℕ) : Γ(tensorPowModule X L (e : ℤ), ⊤) :=
  (Stacks.PowerFamilyBridge.tensorPowerModuleIso X L ((1 * e : ℕ) : ℤ) ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X L
        (show ((1 * e : ℕ) : ℤ) = (e : ℤ) by rw [one_mul])).hom.app ⊤
    ((Stacks.SheafOfModules.Invertible.sectionPow' L
      (Stacks.SheafOfModules.Invertible.sectionsDegreeOne L s) e).eval (op ⊤))

/-- **The zero scheme of `s^e` is the `e`-th power of the zero scheme of `s`.** -/
theorem zeroScheme_sectionPowTensorPow (s : Γ(L, ⊤)) (e : ℕ) :
    zeroScheme X (tensorPowModule X L (e : ℤ)) (sectionPowTensorPow L s e) =
      zeroScheme X L s ^ e := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 * e : ℕ) : ℤ)) :=
    AlgebraicGeometry.isInvertible_sheafObj_tensorPowerModule' (X := X) L _
  exact (zeroScheme_eq_of_iso _ rfl).symm.trans (zeroScheme_sectionPow'_degreeOne L s e)

/-- `Z(s)^e ≤ Z(s^e)`. -/
theorem pow_zeroScheme_le_zeroScheme_sectionPowTensorPow (s : Γ(L, ⊤)) (e : ℕ) :
    zeroScheme X L s ^ e ≤ zeroScheme X (tensorPowModule X L (e : ℤ)) (sectionPowTensorPow L s e) :=
  (zeroScheme_sectionPowTensorPow L s e).ge

/-- `Z(s^e) ≤ Z(s)` for `e ≥ 1`. -/
theorem zeroScheme_sectionPowTensorPow_le (s : Γ(L, ⊤)) {e : ℕ} (he : 1 ≤ e) :
    zeroScheme X (tensorPowModule X L (e : ℤ)) (sectionPowTensorPow L s e) ≤
      zeroScheme X L s := by
  rw [zeroScheme_sectionPowTensorPow]
  intro U
  exact Ideal.pow_le_self (by omega)

/-- `Z(s^e)` and `Z(s)` have the same support for `e ≥ 1`. -/
theorem support_zeroScheme_sectionPowTensorPow (s : Γ(L, ⊤)) {e : ℕ} (he : 1 ≤ e) :
    (zeroScheme X (tensorPowModule X L (e : ℤ)) (sectionPowTensorPow L s e)).support =
      (zeroScheme X L s).support := by
  rw [zeroScheme_sectionPowTensorPow]
  exact Scheme.IdealSheafData.support_pow _ _ (by omega)

/-- The section `s^e` as a degree-one element of the section ring of `L^{⊗ e}`; its nonvanishing
locus is that of `s^e` (`nvLocus_degreeOneSection`). -/
abbrev sectionPowDegreeOne (s : Γ(L, ⊤)) (e : ℕ) : powSections (tensorPowModule X L (e : ℤ)) 1 :=
  degreeOneSection _ (sectionPowTensorPow L s e)

end Stacks.Algebraization.SectionRingCone

end
