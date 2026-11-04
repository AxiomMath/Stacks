module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationCoproductSections
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent

/-!
# The module underlying `gradedAlgebraSheaf` is the coproduct over all of `ℤ`

`Stacks.RelativeSpec.gradedCoprodIsoUnderlyingModule` identifies the module underlying
`Stacks.RelativeSpec.gradedAlgebraSheaf X A hc` with the coproduct `∐_{n ≥ 0} A_n` of the
homogeneous pieces, **under the hypothesis that the pieces vanish in negative degrees**. A
Laurent algebra has no such vanishing, and the two left-hand entries of [Stacks, Tag 0EKG]'s
diagram are relative spectra of graded algebras indexed by all of `ℤ`.

**This file gives the identification over all of `ℤ`, with no vanishing hypothesis**, and
computes it on the coproduct injections. It is to
`Stacks.RelativeSpec.gradedCoprodIsoUnderlyingModule` what
`Stacks.RelativeSpec.coprodIntIsoUnderlyingModule` is to
`Stacks.RelativeSpec.coprodIsoUnderlyingModule`: the same statement for the other of the two
ungraded realizations the library carries.

## Main definitions

* `Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule`: **`∐_{n ∈ ℤ} A_n` is the module
  underlying `gradedAlgebraSheaf X A hc`.**

## Main results

* `Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule_hom_sigma_ι`: **the identification
  carries the `n`-th coproduct injection of a local section to the homogeneous local section it
  names**, `SheafOfModules.GradedAlgebra.ungradedIncl`. This is what pins the isomorphism down;
  a consumer that has to compare it with another map does so here.

## Implementation notes

The route is the one `Stacks.RelativeSpec.gradedCoprodIsoUnderlyingModule` takes with the
nonnegative reindexing deleted: `Stacks.sheafifyDirectSumIso` identifies the sheafification of
the objectwise direct sum with the coproduct — its index type is `Type`, so `ℤ` is allowed —
and `Stacks.RelativeSpec.gradedDirectSumIsoUnderlyingModule` identifies that sheafification
with the underlying module. Neither step needs a vanishing hypothesis; the hypothesis in the
nonnegative form is used only to see that the reindexing
`Stacks.directSumNatToInt` is locally bijective, and here there is no reindexing.

The section formula mirrors `SheafOfModules.GradedModule.coprodIsoUngradedSheaf_hom_sigma_ι`.
The sheafification counit appears in the morphism-level step because
`Stacks.sheafifyDirectSumIso` compares the two cocones through
`Stacks.sheafificationDirectSumComponentIso`; on sections nothing is lost, since every local
section of a sheaf is the counit image of its own unit image.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
    HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))

/-- **The module underlying `Stacks.RelativeSpec.gradedAlgebraSheaf` is the coproduct of its
homogeneous pieces over all of `ℤ`.** No vanishing in negative degrees is assumed, so this
applies to a Laurent algebra. -/
def gradedCoprodIntIsoUnderlyingModule :
    (∐ fun n : ℤ => A.piece n) ≅
      AlgebraSheaf.underlyingModule (gradedAlgebraSheaf X A hc) :=
  (Stacks.sheafifyDirectSumIso (fun n : ℤ => A.piece n)).symm ≪≫
    gradedDirectSumIsoUnderlyingModule X A hc

/-- The comparison morphism from the objectwise direct sum, evaluated on a homogeneous local
section: it is the homogeneous section, read in the ungraded realization. -/
theorem gradedDirectSumHom_of (U : (Opens ↥X)ᵒᵖ) (n : ℤ) (x : (A.piece n).val.obj U) :
    PresheafOfModules.Hom.app (gradedDirectSumHom X A hc) U
        (DirectSum.of (fun i : ℤ => ((A.piece i).val.obj U : Type u)) n x) =
      A.ungradedIncl n x :=
  rfl

/-- **The coproduct comparison on the coproduct injections** (morphism level). The sheafification
counit of the `n`-th piece appears because `Stacks.sheafifyDirectSumIso` compares the sheafified
objectwise direct sum with the coproduct through it. -/
theorem counit_comp_sigma_ι_comp_gradedCoprodIntIsoUnderlyingModule_hom (n : ℤ) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
          (A.piece n) ≫
        Sigma.ι (fun i : ℤ => A.piece i) n ≫
          (gradedCoprodIntIsoUnderlyingModule X A hc).hom =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (Stacks.inclHom (fun i : ℤ => (A.piece i).val) n) ≫
        (gradedDirectSumIsoUnderlyingModule X A hc).hom :=
  Stacks.counit_comp_sigma_ι_comp_sheafifyDirectSumIso_inv_assoc
    (fun i : ℤ => A.piece i) n (gradedDirectSumIsoUnderlyingModule X A hc).hom

/-- **The coproduct comparison sends the `n`-th coproduct injection of a local section to the
homogeneous local section it names.** -/
theorem gradedCoprodIntIsoUnderlyingModule_hom_sigma_ι (U : (Opens ↥X)ᵒᵖ) (n : ℤ)
    (x : (A.piece n).val.obj U) :
    (gradedCoprodIntIsoUnderlyingModule X A hc).hom.val.app U
        (PresheafOfModules.Hom.app (Sigma.ι (fun i : ℤ => A.piece i) n).val U x) =
      A.ungradedIncl n x := by
  have hx : PresheafOfModules.Hom.app
      ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
          (A.piece n))) U
      (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((A.piece n).val)) U x) = x :=
    PresheafOfModules.hom_congr_apply'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).right_triangle_components
        (A.piece n)) U x
  refine Eq.trans (congrArg (fun y => (gradedCoprodIntIsoUnderlyingModule X A hc).hom.val.app U
    (PresheafOfModules.Hom.app (Sigma.ι (fun i : ℤ => A.piece i) n).val U y)) hx.symm) ?_
  refine Eq.trans (congrArg
    (fun f => f.val.app U
      (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((A.piece n).val)) U x))
    (counit_comp_sigma_ι_comp_gradedCoprodIntIsoUnderlyingModule_hom X A hc n)) ?_
  refine Eq.trans (congrArg
    (fun y => PresheafOfModules.Hom.app
      (gradedDirectSumIsoUnderlyingModule X A hc).hom.val U y)
    (PresheafOfModules.unit_naturality_apply (α := 𝟙 X.ringCatSheaf.obj)
      (Stacks.inclHom (fun i : ℤ => (A.piece i).val) n) U x)) ?_
  exact (Stacks.sheafifyHomOfPresheafHom_unit_apply (gradedDirectSumHom X A hc) U
    (DirectSum.of (fun i : ℤ => ((A.piece i).val.obj U : Type u)) n x)).trans
    (gradedDirectSumHom_of X A hc U n x)

end Stacks.RelativeSpec

end
