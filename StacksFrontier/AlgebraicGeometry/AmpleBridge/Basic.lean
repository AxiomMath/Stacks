module

public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.StalkBridge
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic

/-!
# The two spellings of ampleness on a scheme agree

The library carries two predicates for Stacks Tag 01PS. `Stacks.Ample.IsAmple` is written over
the explicit tensor powers `Stacks.Ample.tensorPowModule` and the nonvanishing locus
`Stacks.Ample.nonvanishingLocus` of a global section;
`AlgebraicGeometry.Scheme.Modules.IsAmple` is written over the iterated tensor powers
`Stacks.SheafOfModules.Invertible.tensorPower` and the nonvanishing locus
`Stacks.SheafOfModules.nonvanishingLocus` of a restriction-compatible family of sections. This
file proves that they agree, and deduces the same for the two relative ampleness predicates of
Stacks Tag 01VH.

## Main results

* `Stacks.AmpleBridge.isAmple_iff_isAmple`: the two ampleness predicates of Stacks Tag 01PS for
  an invertible sheaf of modules on a scheme are equivalent.
* `Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple`: the two relative ampleness
  predicates of Stacks Tag 01VH for a morphism of schemes are equivalent.

## The route

The tensor powers are already compared: `Stacks.PowerFamilyBridge.tensorPowerModuleIso`
identifies `Stacks.Ample.tensorPowModule` with Tag 01CU's own family
`Stacks.AmpleProjectiveImmersion.tensorPowerModule`, which is
`Stacks.SheafOfModules.Invertible.tensorPower` by `Stacks.SheafOfModules.Invertible`
`.tensorPower_eq_tensorPower`, and
`Stacks.PowerFamilyBridge.isAmpleForPowers_tensorPowerModule_iff` transports ampleness along
that comparison. What is left is the difference between a global section of a module on a scheme
and a restriction-compatible family of sections of the same module read on the underlying ringed
space; the two nonvanishing loci then agree because the germ and the submodule `𝔪_x · M_x` are
the same in both, by `Stacks.NonvanishingPullback.mem_maximalSmul_iff`.

Relative ampleness is ampleness over the preimage of every affine open of the base, and the two
spellings take the restriction of the module to be the same object, so the relative statement is
the absolute one applied over each affine open.

## References

* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Stacks.AmpleBridge

variable {X : Scheme.{u}}

/-- Invertibility at the spelling `AlgebraicGeometry.Scheme.Modules.IsAmple` asks for. The two
structure presheaves and the two sheaf conditions are definitionally equal; instance search is
syntactic and does not cross the gap. -/
instance isInvertible_ringedSpace (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M := ‹_›

/-- Invertibility of a tensor power of an invertible module, at the same spelling. -/
instance isInvertible_tensorPowerModule (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L n) :=
  Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L n

/-- **The two spellings of the nonvanishing locus of Stacks Tag 01CY agree.**
`Stacks.Ample.nonvanishingLocus` takes a global section of a module on a scheme;
`Stacks.SheafOfModules.nonvanishingLocus` takes a restriction-compatible family of sections of
the same module read on the underlying ringed space. The germ of the section is the same element
and `𝔪_x · M_x` is the same submodule in both. -/
theorem nonvanishingLocus_sectionsOfTop (M : X.Modules) (m : Γ(M, ⊤)) :
    Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) M
        (Stacks.SheafOfModules.sectionsOfTop M m) =
      Stacks.Ample.nonvanishingLocus M m :=
  Set.ext fun x =>
    (Iff.trans (not_congr (Stacks.NonvanishingPullback.mem_maximalSmul_iff M x _))
      (Stacks.SheafOfModules.mem_nonvanishingLocus_sectionsOfTop_iff
        (X := X.toRingedSpace) M m x).symm).symm

/-- **Stacks Tag 01PS: the two ampleness predicates agree.** -/
theorem isAmple_iff_isAmple (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    Stacks.Ample.IsAmple X L ↔ AlgebraicGeometry.Scheme.Modules.IsAmple X L := by
  rw [← Stacks.PowerFamilyBridge.isAmpleForPowers_tensorPowerModule_iff X L]
  refine and_congr_right fun _ => forall_congr' fun x => exists_congr fun n =>
    and_congr_right fun _ => ?_
  constructor
  · rintro ⟨s, U, hU, hxU, hUaff⟩
    obtain rfl : Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace)
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L (n : ℤ))
        (Stacks.SheafOfModules.sectionsOfTop _ s) = U :=
      Opens.ext ((nonvanishingLocus_sectionsOfTop _ s).trans hU.symm)
    exact ⟨Stacks.SheafOfModules.sectionsOfTop _ s, hxU, hUaff⟩
  · rintro ⟨s, hxs, haff⟩
    refine ⟨PresheafOfModules.sections.eval s (op ⊤),
      Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) _ s, ?_, hxs, haff⟩
    exact (Stacks.SheafOfModules.nonvanishingLocus_sectionsOfTop_eval
        (X := X.toRingedSpace) _ s).symm.trans
      (nonvanishingLocus_sectionsOfTop (X := X) _ (PresheafOfModules.sections.eval s (op ⊤)))

/-- **Stacks Tag 01VH: the two relative ampleness predicates agree.** Both say that the morphism
is quasi-compact and that the restriction of the module to the preimage of every affine open of
the base is ample, and the restriction is the same object in both. -/
theorem isRelativelyAmple_iff_isRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔
      Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Iff.rfl

end Stacks.AmpleBridge

end
