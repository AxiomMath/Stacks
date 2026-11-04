module

public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionPowerOpen
public import StacksFrontier.AlgebraicGeometry.TensorSectionProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Powers of a section over an open, in the tensor-power grading

A section `u` of `L ^⊗ n` over an open `U ⊆ X` has, for every `j`, a `(j+1)`-st power, a section of
`L ^⊗ (n (j+1))` over `U` with the same nonvanishing locus.

## Main definitions

* `Stacks.SectionPowerOverOpen.powObjIsoTensorPow`: the isomorphism `powObj A k ≅ A ^⊗ (k+1)`
  between the left-bracketed power `Stacks.TensorSectionPower.powObj` and
  `Stacks.Ample.tensorPowModule`.
* `Stacks.SectionPowerOverOpen.powSectionOnIso`: the isomorphism
  `powObj (L ^⊗ n) j ≅ L ^⊗ (n (j+1))`.
* `Stacks.SectionPowerOverOpen.powSectionOn`: the `(j+1)`-st power of a section of `L ^⊗ n` over
  an open `U`, as a section of `L ^⊗ (n (j+1))` over `U`.

## Main results

* `Stacks.SectionPowerOverOpen.nonvanishingLocusOn_congr`: the nonvanishing locus of a section
  over an open is unchanged by transport along an isomorphism of modules.
* `Stacks.SectionPowerOverOpen.nonvanishingLocusOn_tensorSection`: `U_{m ⊗ n} = U_m ∩ U_n` for
  two sections over the same open `U`.
* `Stacks.SectionPowerOverOpen.nonvanishingLocusOn_powSectionOn` and its bundled form
  `Stacks.SectionPowerOverOpen.nonvanishingOpenOn_powSectionOn`: the power of a section over an
  open has the same nonvanishing locus as the section.
* `Stacks.SectionPowerOverOpen.nonvanishingLocus_powSectionOn_top` and its bundled form
  `Stacks.SectionPowerOverOpen.powNonvanishingOpen_powSectionOn_top`: the same statement for
  `U = ⊤`, phrased with `Stacks.Ample.nonvanishingLocus` and
  `Stacks.AmpleTheory.powNonvanishingOpen`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.ModuleStalk
open Stacks.AmpleEventualGeneration (tensorPowAdd)
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn mem_nonvanishingLocusOn_iff
  nonvanishingLocusOn_top)
open Stacks.SectionPowerOpen (nonvanishingOpenOn coe_nonvanishingOpenOn)
open Stacks.SectionTensorFormula (tensorSection)
open Stacks.TensorSectionPower (powObj secPow)

universe u

namespace Stacks.SectionPowerOverOpen

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}}

/-! ### Transport of the nonvanishing locus of a section over an open -/

/-- A point of `U` is in the nonvanishing locus of the transport of `s` along `e` exactly when it
is in the nonvanishing locus of `s`. -/
theorem mem_nonvanishingLocusOn_congr_iff {A B : X.Modules} (e : A ≅ B) (U : X.Opens)
    (s : Γ(A, U)) {y : X} (hy : y ∈ U) :
    y ∈ nonvanishingLocusOn B U (e.hom.app U s) ↔ y ∈ nonvanishingLocusOn A U s := by
  rw [mem_nonvanishingLocusOn_iff B U hy, mem_nonvanishingLocusOn_iff A U hy,
    ← mapFun_germ e.hom y U hy, mem_maximalSmul_mapFun_iff]

/-- The nonvanishing locus of a section over an open is unchanged by transporting the section
along an isomorphism of `𝒪_X`-modules. -/
theorem nonvanishingLocusOn_congr {A B : X.Modules} (e : A ≅ B) (U : X.Opens) (s : Γ(A, U)) :
    nonvanishingLocusOn B U (e.hom.app U s) = nonvanishingLocusOn A U s :=
  Set.ext fun _ => ⟨fun h => (mem_nonvanishingLocusOn_congr_iff e U s h.1).mp h,
    fun h => (mem_nonvanishingLocusOn_congr_iff e U s h.1).mpr h⟩

/-- The nonvanishing open of a section over an open is unchanged by transporting the section
along an isomorphism of invertible `𝒪_X`-modules. -/
theorem nonvanishingOpenOn_congr {A B : X.Modules} [IsInvertibleModule X A]
    [IsInvertibleModule X B] (e : A ≅ B) (U : X.Opens) (s : Γ(A, U)) :
    nonvanishingOpenOn B U (e.hom.app U s) = nonvanishingOpenOn A U s :=
  Opens.ext (nonvanishingLocusOn_congr e U s)

/-! ### The product of two sections over one open -/

/-- `U_{m ⊗ n} = U_m ∩ U_n` for two sections `m`, `n` of invertible modules over the same
open `U`. -/
@[ega "0 5.5.3" "special case", ega "II 4.6.13.1" "(ii)"]
theorem nonvanishingLocusOn_tensorSection {F G : X.Modules} [IsInvertibleModule X F]
    [IsInvertibleModule X G] (U : X.Opens) (m : Γ(F, U)) (n : Γ(G, U)) :
    nonvanishingLocusOn (F ⊗ G : X.Modules) U (tensorSection F G m n) =
      nonvanishingLocusOn F U m ∩ nonvanishingLocusOn G U n := by
  refine Set.ext fun y => ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := (Stacks.TensorSectionProduct.germ_tensorSection_notMem_maximalSmul_iff
      m n h.1).mp ((mem_nonvanishingLocusOn_iff _ U h.1).mp h)
    exact ⟨⟨h.1, h2.1⟩, ⟨h.1, h2.2⟩⟩
  · exact ⟨h.1.1, (Stacks.TensorSectionProduct.germ_tensorSection_notMem_maximalSmul_iff
      m n h.1.1).mpr ⟨h.1.2, (mem_nonvanishingLocusOn_iff G U h.1.1).mp h.2⟩⟩

/-! ### The two gradings of a tensor power -/

/-- The isomorphism `powObj A k ≅ A ^⊗ (k+1)` between the left-bracketed power
`Stacks.TensorSectionPower.powObj` and `Stacks.Ample.tensorPowModule`. -/
def powObjIsoTensorPow (A : X.Modules) [IsInvertibleModule X A] :
    (k : ℕ) → powObj A k ≅ tensorPowModule X A ((k + 1 : ℕ) : ℤ)
  | 0 => (tensorPowModuleOneIso X A).symm
  | k + 1 =>
    whiskerRightIso (powObjIsoTensorPow A k) A ≪≫
      whiskerLeftIso (tensorPowModule X A ((k + 1 : ℕ) : ℤ)) (tensorPowModuleOneIso X A).symm ≪≫
      tensorPowAdd (L := A) (a := ((k + 1 : ℕ) : ℤ)) (b := 1) (c := ((k + 2 : ℕ) : ℤ))
        (by push_cast; ring)

/-- The isomorphism `powObj (L ^⊗ n) j ≅ L ^⊗ (n (j+1))`. -/
def powSectionOnIso (L : X.Modules) [IsInvertibleModule X L] (n j : ℕ) :
    powObj (tensorPowModule X L (n : ℤ)) j ≅ tensorPowModule X L ((n * (j + 1) : ℕ) : ℤ) :=
  powObjIsoTensorPow (tensorPowModule X L (n : ℤ)) j ≪≫
    Stacks.RelativeVeryAmple.tensorPowModulePowIso X L (n : ℤ) (j + 1) ≪≫
    Stacks.RelativeVeryAmple.tensorPowModuleCongr X L (by push_cast; ring)

/-! ### The power of a section over an open -/

/-- The `(j+1)`-st power of a section of `L ^⊗ n` over an open `U`, as a section of
`L ^⊗ (n (j+1))` over `U`. -/
def powSectionOn (L : X.Modules) [IsInvertibleModule X L] (n : ℕ) {U : X.Opens}
    (u : Γ(tensorPowModule X L (n : ℤ), U)) (j : ℕ) :
    Γ(tensorPowModule X L ((n * (j + 1) : ℕ) : ℤ), U) :=
  (powSectionOnIso L n j).hom.app U (secPow (tensorPowModule X L (n : ℤ)) u j)

/-- The power of a section over an open has the same nonvanishing locus as the section. -/
theorem nonvanishingLocusOn_powSectionOn (L : X.Modules) [IsInvertibleModule X L] (n : ℕ)
    {U : X.Opens} (u : Γ(tensorPowModule X L (n : ℤ), U)) (j : ℕ) :
    nonvanishingLocusOn (tensorPowModule X L ((n * (j + 1) : ℕ) : ℤ)) U (powSectionOn L n u j) =
      nonvanishingLocusOn (tensorPowModule X L (n : ℤ)) U u := by
  rw [powSectionOn, nonvanishingLocusOn_congr,
    Stacks.SectionPowerOpen.nonvanishingLocusOn_secPow]

/-- The power of a section over an open has the same nonvanishing open as the section. -/
theorem nonvanishingOpenOn_powSectionOn (L : X.Modules) [IsInvertibleModule X L] (n : ℕ)
    {U : X.Opens} (u : Γ(tensorPowModule X L (n : ℤ), U)) (j : ℕ) :
    nonvanishingOpenOn (tensorPowModule X L ((n * (j + 1) : ℕ) : ℤ)) U (powSectionOn L n u j) =
      nonvanishingOpenOn (tensorPowModule X L (n : ℤ)) U u :=
  Opens.ext (nonvanishingLocusOn_powSectionOn L n u j)

/-- The power of a global section of `L ^⊗ n` has the same nonvanishing locus
`Stacks.Ample.nonvanishingLocus` as the section. -/
theorem nonvanishingLocus_powSectionOn_top (L : X.Modules) [IsInvertibleModule X L] (n : ℕ)
    (u : Γ(tensorPowModule X L (n : ℤ), ⊤)) (j : ℕ) :
    nonvanishingLocus (tensorPowModule X L ((n * (j + 1) : ℕ) : ℤ)) (powSectionOn L n u j) =
      nonvanishingLocus (tensorPowModule X L (n : ℤ)) u := by
  rw [← nonvanishingLocusOn_top, ← nonvanishingLocusOn_top,
    nonvanishingLocusOn_powSectionOn]

/-- The power of a global section of `L ^⊗ n` has the same nonvanishing open
`Stacks.AmpleTheory.powNonvanishingOpen` as the section. -/
theorem powNonvanishingOpen_powSectionOn_top (L : X.Modules) [IsInvertibleModule X L] (n : ℕ)
    (u : Γ(tensorPowModule X L (n : ℤ), ⊤)) (j : ℕ) :
    Stacks.AmpleTheory.powNonvanishingOpen X L (n * (j + 1)) (powSectionOn L n u j) =
      Stacks.AmpleTheory.powNonvanishingOpen X L n u :=
  Opens.ext (nonvanishingLocus_powSectionOn_top L n u j)

end Stacks.SectionPowerOverOpen

end
