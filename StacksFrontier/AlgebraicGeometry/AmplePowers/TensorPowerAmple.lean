module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.FinGenFromCover.Powers
public import StacksFrontier.AlgebraicGeometry.AmpleAffineAvoidance.Powers
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.FromAmple
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A positive tensor power of an ample module is ample

[Stacks, Tag 01PT] says that for `n ≥ 1` an invertible module `L` is ample if and only if
`L ^⊗ n` is, and its proof is the observation that `X_{s^n} = X_s`. This file states it for
`Stacks.Ample.IsAmple` at `Stacks.Ample.tensorPowModule`; the implication from the power to the
module is `Stacks.RelativeVeryAmple.isAmple_of_isAmple_tensorPowModule`.

## Main results

* `Stacks.AmplePowers.isAmple_tensorPowModule_of_isAmple`: a positive tensor power of an ample
  invertible module is ample.
* `Stacks.AmplePowers.isAmple_tensorPowModule_iff`: [Stacks, Tag 01PT] as a biconditional over
  `Stacks.Ample.IsAmple` and `Stacks.Ample.tensorPowModule`.

## Implementation notes

No tag attribute is attached: `01PT` is carried by
`AlgebraicGeometry.isAmple_iff_tensorPower_isAmple`, the same statement for the ampleness predicate
`AlgebraicGeometry.Scheme.Modules.IsAmple` at `Stacks.SheafOfModules.Invertible.tensorPower`.

Ampleness is stated with global sections `Γ(L ^⊗ n, ⊤)` and `Stacks.Ample.nonvanishingLocus`,
while the power arithmetic is stated with `Stacks.GradedSections.powSections` and
`Stacks.AmpleFiniteAvoidance.nvLocus`; `Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq`
and `Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq` pass between them, preserving the
nonvanishing locus.

## References

* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Ample AlgebraicGeometry.SheafOfModules
open Stacks.AmpleFiniteAvoidance Stacks.GradedSections

universe u

namespace Stacks.AmplePowers

/-- **A positive tensor power of an ample invertible module is ample**, [Stacks, Tag 01PT]. -/
@[ega "II 4.5.6" "(i)"]
theorem isAmple_tensorPowModule_of_isAmple {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (d : ℕ) (hd : 1 ≤ d) (hL : IsAmple X L) :
    IsAmple X (tensorPowModule X L (d : ℤ)) := by
  refine ⟨hL.1, fun x => ?_⟩
  obtain ⟨m, hm, s, U, hU, hxU, hUaff⟩ := hL.2 x
  obtain ⟨a, ha⟩ := Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq L m s
  obtain ⟨b, hb⟩ := Stacks.AmpleAffineAvoidance.exists_pow_of_dvd L a
    (Dvd.intro_left d rfl)
    (Nat.mul_pos (by omega) (by omega))
  obtain ⟨t, ht⟩ := Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq L (d * m) b
  have e : tensorPowModule X (tensorPowModule X L (d : ℤ)) (m : ℤ) ≅
      tensorPowModule X L ((d * m : ℕ) : ℤ) :=
    Stacks.RelativeVeryAmple.tensorPowModulePowIso X L (d : ℤ) m ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X L
        (show (d : ℤ) * (m : ℤ) = ((d * m : ℕ) : ℤ) by push_cast; ring)
  refine ⟨m, hm, e.inv.app ⊤ t, U, ?_, hxU, hUaff⟩
  rw [hU, ← ha, ← hb, ← ht]
  exact (nonvanishingLocus_congr e.symm t).symm

/-- **[Stacks, Tag 01PT]**: an invertible module is ample if and only if any one of its positive
tensor powers is. -/
@[ega "II 4.5.6"]
theorem isAmple_tensorPowModule_iff {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]
    (d : ℕ) (hd : 1 ≤ d) : IsAmple X L ↔ IsAmple X (tensorPowModule X L (d : ℤ)) :=
  ⟨isAmple_tensorPowModule_of_isAmple L d hd,
    Stacks.RelativeVeryAmple.isAmple_of_isAmple_tensorPowModule L d hd⟩

end Stacks.AmplePowers

end
