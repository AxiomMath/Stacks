module

public import StacksFrontier.AlgebraicGeometry.Bridge.SchemeBridge
public import StacksFrontier.AlgebraicGeometry.RegularSectionSequence.Basic

/-!
# What Tag 08KS's bridge discharges downstream

`Stacks.RegularSectionSequence.exists_cokernelIso_restrictionUnit` and
`Stacks.RegularSectionSequence.shortExact_restrictionUnit` each carry a hypothesis `hiso`,
documented there as being exactly Stacks Tag 08KS and withheld for that reason. This file
discharges it from the annihilation condition, which is the only thing a caller now has to
supply.

## Main results

* `Stacks.Tag08KS.isIso_restrictionUnit_app_of_annihilated`: for a closed subscheme `D` of `X`
  and an `𝒪_X`-module annihilated by the kernel ideal of `𝒪_X ⟶ i_*𝒪_D`, the unit of
  `i^* ⊣ i_*` is an isomorphism — which is `hiso`.
* `Stacks.Tag08KS.exists_cokernelIso_restrictionUnit_of_annihilated` and
  `Stacks.Tag08KS.shortExact_restrictionUnit_of_annihilated`: the two assertions of Tag 0C6K's
  `regular_section_sequence` label with `hiso` removed.

## Implementation notes

No Stacks attribute for Tag 0C6K is attached here and none is earned. The remaining hypothesis of
the two results below is `hz`, that the section restricts to zero on the subscheme, and at the
*zero scheme* of a section that is the non-trivial half of Stacks Tag 02OQ's description of its
ideal sheaf — still open, as the module docstring of
`Stacks.RegularSectionSequence.exists_cokernelIso_restrictionUnit` records. What this
file removes is the second of that statement's two hypotheses, not both.

This file is deliberately the only one of the directory that imports a consumer: the three
files it builds on (`Basic`, `EssentialImage`, `SchemeBridge`) import nothing downstream, so a
consumer may import them without a cycle.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Tag08KS

variable {X : Scheme.{u}} (D : X.IdealSheafData) (L : SheafOfModules.{u} X.ringCatSheaf)

/-- **Tag 0C6K's `hiso`, discharged by Tag 08KS.** For a closed subscheme `D ⊆ X`, the unit
`M ⟶ i_* i^* M` is an isomorphism as soon as the kernel ideal of `𝒪_X ⟶ i_* 𝒪_D` annihilates
`M`. -/
theorem isIso_restrictionUnit_app_of_annihilated
    (M : SheafOfModules.{u} X.ringCatSheaf)
    (hM : ∀ (U : Opens X) (a : X.ringCatSheaf.obj.obj (op U)),
      a ∈ RingHom.ker (D.subschemeι.toLRSHom.c.app (op U)).hom →
        ∀ m : M.val.obj (op U), a • m = 0) :
    IsIso ((Stacks.RegularSectionSequence.restrictionAdjunction D).unit.app M) :=
  (isIso_unit_app_iff_of_isClosedImmersion D.subschemeι M).mpr hM

/-- **The first assertion of Stacks Tag 0C6K's `regular_section_sequence`, with `hiso`
discharged.** The restriction map `L ⟶ i_*(L|_D)` is the cokernel of `f : 𝒪_X ⟶ L`, given only
that `f` restricts to zero on `D` and that the cokernel is annihilated by the ideal. -/
theorem exists_cokernelIso_restrictionUnit_of_annihilated
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (hz : f ≫ Stacks.RegularSectionSequence.restrictionUnit D L = 0)
    (hann : ∀ (U : Opens X) (a : X.ringCatSheaf.obj.obj (op U)),
      a ∈ RingHom.ker (D.subschemeι.toLRSHom.c.app (op U)).hom →
        ∀ m : (cokernel f).val.obj (op U), a • m = 0) :
    ∃ e : cokernel f ≅ (SheafOfModules.pushforward.{u} D.subschemeι.toRingCatSheafHom).obj
        ((SheafOfModules.pullback.{u} D.subschemeι.toRingCatSheafHom).obj L),
      cokernel.π f ≫ e.hom = Stacks.RegularSectionSequence.restrictionUnit D L :=
  have : IsIso ((Stacks.RegularSectionSequence.restrictionAdjunction D).unit.app (cokernel f)) :=
    isIso_restrictionUnit_app_of_annihilated D (cokernel f) hann
  Stacks.RegularSectionSequence.exists_cokernelIso_restrictionUnit D L f hz this

/-- **The second assertion of Stacks Tag 0C6K's `regular_section_sequence`, with `hiso`
discharged.** For a monomorphism `f : 𝒪_X ⟶ L` restricting to zero on `D`, the sequence
`0 → 𝒪_X → L → i_*(L|_D) → 0` is short exact. -/
theorem shortExact_restrictionUnit_of_annihilated
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ L) [Mono f]
    (hz : f ≫ Stacks.RegularSectionSequence.restrictionUnit D L = 0)
    (hann : ∀ (U : Opens X) (a : X.ringCatSheaf.obj.obj (op U)),
      a ∈ RingHom.ker (D.subschemeι.toLRSHom.c.app (op U)).hom →
        ∀ m : (cokernel f).val.obj (op U), a • m = 0) :
    ∃ hc : f ≫ Stacks.RegularSectionSequence.restrictionUnit D L = 0,
      (ShortComplex.mk f (Stacks.RegularSectionSequence.restrictionUnit D L) hc).ShortExact :=
  Stacks.RegularSectionSequence.shortExact_of_mono_of_exists_cokernelIso f _
    (exists_cokernelIso_restrictionUnit_of_annihilated D L f hz hann)

end Stacks.Tag08KS
