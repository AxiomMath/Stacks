module

public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.GlobalSectionsBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Multiplication
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.GradedModule

/-!
# The twist of `𝒪_X` in the spellings the vanishing theorems use

[Stacks, Tag 0FD8] states its vanishing over
`Stacks.Cohomology.TwistedGradedModule.twist X ℒ ℱ j`, the tensor product of `ℱ` with
`Stacks.SheafOfModules.TensorPower.tensorPower` taken over the `sectionSiteRing` spelling of the
structure sheaf of rings. At `ℱ = 𝒪_X` that is `ℒ^{⊗ j}` up to the left unitor and the
identification of two of the library's three tensor-power constructions, and this file names the
resulting isomorphism, which is the `e` argument of
`Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_subsingleton_sections_of_iso`.

Also here: the reading of a vanishing statement phrased as "every global section is zero", which
is the shape [Stacks, Tag 0FD7] concludes with, as a zero object of `AddCommGrpCat`.

## Main results

* `Stacks.AmpleSectionConnected.isZero_secF_top_of_forall_eq_zero`
* `Stacks.AmpleSectionConnected.twistedGradedUnitIso`

## Implementation notes

Three instances have to be supplied by hand, all of them derivable and none of them added
hypotheses. The twist asks for `Stacks.SheafOfModules.IsInvertible` while the tensor powers of
this development ask for `AlgebraicGeometry.SheafOfModules.IsInvertible`
(`Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry` converts), and both are needed at the
`sectionSiteRing X` spelling of the structure presheaf of rings rather than at
`X.toRingedSpace.presheaf`; the two presheaves are definitionally equal, so the transport is the
identity, but instance search is syntactic and will not find it.

`Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower` is an *equality*, not merely an
isomorphism, of the two tensor-power constructions, so the second half of the composite is an
`eqToIso`.

## References

* [Stacks Project, Tag 0FD7](https://stacks.math.columbia.edu/tag/0FD7)
* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AmpleSectionConnected

/-- **"Every global section is zero" is `Γ(X, M) = 0`.** -/
theorem isZero_secF_top_of_forall_eq_zero (X : Scheme.{u}) (M : X.Modules)
    (h : ∀ t : Γ(M, ⊤), t = 0) : IsZero ((secF X.ringCatSheaf ⊤).obj M) := by
  refine AddCommGrpCat.isZero_iff_subsingleton.mpr ?_
  change Subsingleton Γ(M, ⊤)
  exact ⟨fun a b => by rw [h a, h b]⟩

/-- **The twist of `𝒪_X` by `ℒ^{⊗ j}` is `ℒ^{⊗ j}`**, at the twisted-graded-module spelling of
the twist. -/
def twistedGradedUnitIso (X : Scheme.{u}) (L : X.Modules)
    [inst : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (j : ℤ) :
    letI : Stacks.SheafOfModules.IsInvertible (Stacks.SheafOfModules.sectionSiteRing X)
        (Stacks.SheafOfModules.sectionSiteSheaf X) L :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inst
    Stacks.Cohomology.TwistedGradedModule.twist X L (Stacks.Ample.unitModule X) j ≅
      tensorPowerModule' L j := by
  letI : Stacks.SheafOfModules.IsInvertible (Stacks.SheafOfModules.sectionSiteRing X)
      (Stacks.SheafOfModules.sectionSiteSheaf X) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inst
  letI : AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.SheafOfModules.sectionSiteRing X)
      (Stacks.SheafOfModules.sectionSiteSheaf X) L := inst
  refine Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor _ _ _ ≪≫ ?_
  exact eqToIso (Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower
    (Stacks.SheafOfModules.sectionSiteRing X)
    (Stacks.SheafOfModules.sectionSiteSheaf X) L j).symm

end Stacks.AmpleSectionConnected

end
