module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationCoproductSections

/-!
# The total module of a graded module as the coproduct over all integer degrees

`SheafOfModules.GradedModule.coprodIsoUngradedSheaf` identifies the module underlying the total
module `⨁ₙ Mₙ` of a graded module with the coproduct `∐_{n : ℕ} Mₙ` of its homogeneous pieces
**in nonnegative degrees**, and therefore needs the negative pieces to vanish.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationCoproductSections` computes that
comparison on the coproduct injections and on multiplication by a homogeneous section of the
algebra.

**This file does the same for the coproduct over *all* integer degrees**, where no vanishing
hypothesis is needed. That is the form [Stacks, Tag 0897] is stated in: the graded modules of
`SheafOfModules.GradedModule` are `ℤ`-graded, and a graded module of finite type over an algebra
concentrated in nonnegative degrees is bounded below but need not vanish below degree zero, so
assuming it does would be a hypothesis the source does not make.

The two comparisons differ in the morphism out of the objectwise direct sum that they are built
from: `Stacks.GradedModule.directSumHom` here, and that precomposed with
`Stacks.directSumNatToInt` there. Everything else is shared — the sheafification lemmas
`Stacks.counit_comp_sigma_ι_comp_sheafifyDirectSumIso_inv` and
`Stacks.sheafifyHomOfPresheafHom_unit_apply` are already stated for an arbitrary index type, and
the computation of the action on homogeneous sections,
`SheafOfModules.GradedModule.ungradedIncl_smul_ungradedIncl`, mentions no index set at all.

## Main definitions

* `SheafOfModules.GradedModule.coprodIntIsoUngradedSheaf`: **the `R`-module underlying the total
  module is the coproduct of the homogeneous pieces over all integer degrees.**

## Main results

* `SheafOfModules.GradedModule.coprodIntIsoUngradedSheaf_hom_sigma_ι`: the comparison sends the
  `n`-th coproduct injection of a local section to `ungradedIncl n` of it.
* `SheafOfModules.GradedModule.coprodIntIsoUngradedSheaf_hom_sigma_ι_smul`: **multiplication by
  a homogeneous section of the algebra is degreewise under the comparison.**

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace SheafOfModules.GradedModule

open Stacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {A : GradedAlgebra.{w, w} R} [A.IsCommutative] (M : GradedModule.{w, w, w} A)
  [HasCoproduct fun n : ℤ => M.piece n]

/-- The morphism out of the objectwise direct sum over all integer degrees that the comparison
is built from. -/
noncomputable abbrev intDirectSumHom :
    Stacks.directSum (fun n : ℤ => (M.piece n).val) ⟶
      ((SheafOfModules.restrictScalars.{w} A.ungradedStructureMap).obj M.ungradedSheaf).val :=
  M.toPresheafGradedModule.directSumHom A.ungradedStructureMap
    (A.toPresheafGradedAlgebra.toTotalSheaf J) M.ungradedSheaf M.toUngradedSheaf
    (GradedModule.structureHom_comp_toTotalSheaf (A := A) (J := J))

/-- **The `R`-module underlying the total module `⨁ₙ Mₙ` is the coproduct of the homogeneous
pieces over all integer degrees.** -/
noncomputable def coprodIntIsoUngradedSheaf :
    (∐ fun n : ℤ => M.piece n) ≅
      (SheafOfModules.restrictScalars.{w} A.ungradedStructureMap).obj M.ungradedSheaf :=
  (Stacks.sheafifyDirectSumIso (fun n : ℤ => M.piece n)).symm ≪≫ M.directSumIsoUngradedSheaf

omit [HasCoproduct fun n : ℤ => M.piece n] in
/-- The comparison morphism, evaluated on a homogeneous local section: it is the homogeneous
section, read in the total module. It is the identity on sections. -/
theorem intDirectSumHom_of (U : Cᵒᵖ) (n : ℤ) (x : (M.piece n).val.obj U) :
    PresheafOfModules.Hom.app M.intDirectSumHom U
        (DirectSum.of (fun i : ℤ => ((M.piece i).val.obj U : Type w)) n x) =
      M.ungradedIncl n x := rfl

/-- **The coproduct comparison, on the coproduct injections** (morphism level). The
sheafification counit of the `n`-th piece appears because `Stacks.sheafifyDirectSumIso` compares
the sheafified objectwise direct sum with the coproduct through it. -/
theorem counit_comp_sigma_ι_comp_coprodIntIsoUngradedSheaf_hom (n : ℤ) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app (M.piece n) ≫
        Sigma.ι (fun i : ℤ => M.piece i) n ≫ M.coprodIntIsoUngradedSheaf.hom =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map
          (Stacks.inclHom (fun i : ℤ => (M.piece i).val) n) ≫
        Stacks.sheafifyHomOfPresheafHom M.intDirectSumHom :=
  Stacks.counit_comp_sigma_ι_comp_sheafifyDirectSumIso_inv_assoc
    (fun i : ℤ => M.piece i) n (Stacks.sheafifyHomOfPresheafHom M.intDirectSumHom)

/-- **The coproduct comparison sends the `n`-th coproduct injection of a local section to the
homogeneous local section it names.** -/
theorem coprodIntIsoUngradedSheaf_hom_sigma_ι (U : Cᵒᵖ) (n : ℤ)
    (x : (M.piece n).val.obj U) :
    M.coprodIntIsoUngradedSheaf.hom.val.app U
        (PresheafOfModules.Hom.app (Sigma.ι (fun i : ℤ => M.piece i) n).val U x) =
      M.ungradedIncl n x := by
  have hx : PresheafOfModules.Hom.app
      ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app (M.piece n))) U
      (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
          ((M.piece n).val)) U x) = x :=
    PresheafOfModules.hom_congr_apply'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).right_triangle_components
        (M.piece n)) U x
  refine Eq.trans (congrArg (fun y => M.coprodIntIsoUngradedSheaf.hom.val.app U
    (PresheafOfModules.Hom.app (Sigma.ι (fun i : ℤ => M.piece i) n).val U y)) hx.symm) ?_
  refine Eq.trans (congrArg
    (fun f => f.val.app U
      (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
          ((M.piece n).val)) U x))
    (M.counit_comp_sigma_ι_comp_coprodIntIsoUngradedSheaf_hom n)) ?_
  refine Eq.trans (congrArg
    (fun y => PresheafOfModules.Hom.app
      (Stacks.sheafifyHomOfPresheafHom M.intDirectSumHom).val U y)
    (PresheafOfModules.unit_naturality_apply (α := 𝟙 R.obj)
      (Stacks.inclHom (fun i : ℤ => (M.piece i).val) n) U x)) ?_
  exact (Stacks.sheafifyHomOfPresheafHom_unit_apply M.intDirectSumHom U
    (DirectSum.of (fun i : ℤ => ((M.piece i).val.obj U : Type w)) n x)).trans
    (M.intDirectSumHom_of U n x)

/-- **Multiplication by a homogeneous section of the algebra, read through the coproduct
comparison.** Multiplying the degree-`n` section `x` by the degree-`k` section `y` gives the
comparison image of the `m`-th coproduct injection of the degreewise action `M.smul n k U x y`,
transported along `n + k = m`. Together with `coprodIntIsoUngradedSheaf_hom_sigma_ι`, which
rewrites the left-hand side as the comparison image of the `n`-th injection of `x`, this says
that multiplication by a homogeneous section is degreewise under the comparison. -/
theorem coprodIntIsoUngradedSheaf_hom_sigma_ι_smul (U : Cᵒᵖ) (k n m : ℤ) (hm : n + k = m)
    (y : (A.piece k).val.obj U) (x : (M.piece n).val.obj U) :
    A.ungradedIncl k y • M.ungradedIncl n x =
      M.coprodIntIsoUngradedSheaf.hom.val.app U
        (PresheafOfModules.Hom.app (Sigma.ι (fun i : ℤ => M.piece i) m).val U
          ((eqToHom (congrArg M.piece hm)).val.app U (M.smul n k U x y))) := by
  rw [M.coprodIntIsoUngradedSheaf_hom_sigma_ι U m
      ((eqToHom (congrArg M.piece hm)).val.app U (M.smul n k U x y)),
    M.ungradedIncl_eqToHom U hm (M.smul n k U x y),
    M.ungradedIncl_smul_ungradedIncl U k n y x]

end SheafOfModules.GradedModule

end
