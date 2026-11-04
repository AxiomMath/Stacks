module

public import StacksFrontier.AlgebraicGeometry.FinGenFromCover.Powers
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ampleness of positive tensor powers

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `d ≥ 1`. Then `L` is ample if and only if
`L ^⊗ d` is ample.

## Main results

* `Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple`: if `L` is ample and `d ≥ 1`,
  then `L ^⊗ d` is ample.
* `Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule`: for `d ≥ 1`, `L` is ample if
  and only if `L ^⊗ d` is ample.

## References

* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [EGA II, Proposition 4.5.6(i)]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.Ample Stacks.GradedSections Stacks.AmpleFiniteAvoidance
open Stacks.AmpleAffineAvoidance Stacks.RelativeVeryAmple

universe u

namespace Stacks.AmplePositivePower

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- An ample invertible module has ample positive tensor powers: if `L` is ample and `d ≥ 1`,
then `L ^⊗ d` is ample. -/
@[ega "II 4.5.6" "(i)"]
theorem isAmple_tensorPowModule_of_isAmple (d : ℕ) (hd : 1 ≤ d) (hL : IsAmple X L) :
    IsAmple X (tensorPowModule X L (d : ℤ)) := by
  refine ⟨hL.1, fun x => ?_⟩
  obtain ⟨n, hn, s, U, hU, hxU, hUaff⟩ := hL.2 x
  obtain ⟨a, ha⟩ := exists_powSections_nvLocus_eq L n s
  have hnd : 1 ≤ n * d := Nat.mul_pos hn hd
  obtain ⟨b, hb⟩ := exists_pow_of_dvd L a ⟨d, rfl⟩ hnd
  obtain ⟨s', hs'⟩ := Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq L (n * d) b
  have e : tensorPowModule X (tensorPowModule X L (d : ℤ)) (n : ℤ) ≅
      tensorPowModule X L ((n * d : ℕ) : ℤ) :=
    tensorPowModulePowIso X L (d : ℤ) n ≪≫
      tensorPowModuleCongr X L (show (d : ℤ) * (n : ℤ) = ((n * d : ℕ) : ℤ) by push_cast; ring)
  refine ⟨n, hn, e.inv.app ⊤ s', U, ?_, hxU, hUaff⟩
  rw [hU, ← ha, ← hb, ← hs']
  exact (nonvanishingLocus_congr e.symm s').symm

/-- An invertible `𝒪_X`-module `L` is ample if and only if its tensor power `L ^⊗ d` is ample,
for any `d ≥ 1`. -/
@[stacks 01PT, ega "II 4.5.6" "(i)"]
theorem isAmple_iff_isAmple_tensorPowModule (d : ℕ) (hd : 1 ≤ d) :
    IsAmple X L ↔ IsAmple X (tensorPowModule X L (d : ℤ)) :=
  ⟨isAmple_tensorPowModule_of_isAmple L d hd, isAmple_of_isAmple_tensorPowModule L d hd⟩

end Stacks.AmplePositivePower

end
