module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# `H¹(X, 𝒪_X) = 0` on a normal modification of a rational singularity

In Situation [Stacks, Tag 0B4W] the ring `A` defines a rational singularity, which by
[Stacks, Tag 0B4N] says exactly that the first cohomology of the structure sheaf of every normal
modification of `Spec(A)` vanishes. Applied to the modification `f : X ⟶ Spec(A)` of the
situation itself, this gives `H¹(X, 𝒪_X) = 0`.

The vanishing is supplied by `AlgebraicGeometry.DefinesRationalSingularity` in Mathlib's
`CategoryTheory.Sheaf.H` of the abelian sheaf underlying `𝒪_X`, whereas its consumers want the
first right derived functor of module-valued global sections. This file assembles the change of
model, which is [Stacks, Tag 03FD].

## Main results

* `AlgebraicGeometry.RationalSingularitySituation.isZero_firstCohomologyStructureSheaf`:
  `H¹(X, 𝒪_X) = 0` as a right derived functor of module-valued global sections.

## Implementation notes

The chain has three links, each already in the library, and no mathematics is redone:

* `Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top` replaces the
  global `Sheaf.H` by the value of Mathlib's cohomology presheaf at `⊤`, the terminal open;
* `Stacks.Cohomology.ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf`
  — the composite of [Stacks, Tag 03FD] with the identification of `Ext` out of the free abelian
  sheaf with right derived sections — replaces that by the derived sections of the module sheaf,
  still valued in abelian groups;
* `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` moves from the
  abelian-group-valued model to the module-valued `moduleGlobalSections`. Since forgetting the
  module structure does not change the carrier, `IsZero` transfers across it through
  `Subsingleton`: `ModuleCat.isZero_iff_subsingleton` on one side and
  `AddCommGrpCat.isZero_of_subsingleton` on the other.

Finally `Stacks.DerivedIndexing.rightDerivedIso` moves from Mathlib's `ℕ`-indexed
`Functor.rightDerived` to the `ℤ`-indexed `Functor.rightDerivedPlus` in which
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstCohomologyStructureSheaf` is stated.

The abelian sheaf `AlgebraicGeometry.DefinesRationalSingularity` speaks about is `𝒪_X` composed
with the two forgetful functors; the one the comparison speaks about is the image of
`SheafOfModules.unit` under `SheafOfModules.toSheaf`. The two are the same sheaf, so the
hypothesis is applied directly.

## References

* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace AlgebraicGeometry.RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

attribute [local instance] HasDerivedCategory.standard

/-- **`H¹(X, 𝒪_X) = 0` in Situation [Stacks, Tag 0B4W].** The ring `A` defines a rational
singularity, so the first cohomology of the structure sheaf of every normal modification of
`Spec(A)` vanishes; `f` is such a modification.

The hypothesis supplies the vanishing for Mathlib's `CategoryTheory.Sheaf.H` of the abelian sheaf
underlying `𝒪_X`; the statement here is the first right derived functor of module-valued global
sections, and the two are identified by [Stacks, Tag 03FD]. -/
theorem isZero_firstCohomologyStructureSheaf :
    IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj
      (SheafOfModules.unit S.X.ringCatSheaf)) := by
  let _ : EnoughInjectives (Sheaf (Opens.grothendieckTopology S.X) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  let _ : HasExt.{u} (Sheaf (Opens.grothendieckTopology S.X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  set R := S.X.ringCatSheaf with hR
  set W := (SheafOfModules.toSheaf.{u} R).obj (SheafOfModules.unit R) with hW
  -- The vanishing supplied by the situation.
  have hsub : Subsingleton (Sheaf.H.{u, u, u, u} W 1) :=
    S.definesRationalSingularity S.X S.f S.modification
  -- Transport it to the value of the cohomology presheaf at the terminal open.
  have hsub' : Subsingleton (Sheaf.H'.{u, u, u} W 1 (⊤ : Opens S.X)) :=
    (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top W 1).1 hsub
  have hzero' : IsZero (Sheaf.H'.{u, u, u} W 1 (⊤ : Opens S.X)) :=
    AddCommGrpCat.isZero_of_subsingleton _
  -- Tag 03FD: the abelian-group-valued derived sections of the module sheaf also vanish.
  have hsec : IsZero (((SheafOfModules.toSheaf.{u} R ⋙
      (sheafSections (Opens.grothendieckTopology S.X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens S.X))).rightDerived 1).obj (SheafOfModules.unit R)) :=
    (Stacks.Cohomology.ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf
      (Opens.grothendieckTopology S.X) R (⊤ : Opens S.X) 1 (SheafOfModules.unit R)).2 hzero'
  -- Forgetting the module structure does not change the carrier.
  have hforget : IsZero ((forget₂ (ModuleCat.{u} (R.obj.obj (op (⊤ : Opens S.X))))
      AddCommGrpCat.{u}).obj
      (((SheafOfModules.evaluation R (op (⊤ : Opens S.X))).rightDerived 1).obj
        (SheafOfModules.unit R))) :=
    hsec.of_iso
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso R
        (⊤ : Opens S.X) 1).app (SheafOfModules.unit R))
  have hmod : IsZero (((moduleGlobalSections S.X).rightDerived 1).obj
      (SheafOfModules.unit R)) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact AddCommGrpCat.isZero_iff_subsingleton.1 hforget
  -- Move to the `ℤ`-indexed derived functor.
  exact hmod.of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (moduleGlobalSections S.X) 1).app
      (SheafOfModules.unit R)).symm

end AlgebraicGeometry.RationalSingularitySituation

end

end
