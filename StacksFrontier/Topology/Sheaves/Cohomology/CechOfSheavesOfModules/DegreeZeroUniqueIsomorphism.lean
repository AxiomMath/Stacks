module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.AugmentationIsAKernel

/-!
# Degree-zero Čech cohomology of a sheaf of modules, as a unique isomorphism

For a cover `V = ⋃ i, U i` of an open subset of a space carrying a sheaf of rings, restriction
to the members of the cover induces the *unique* morphism of `R(V)`-modules from `ℱ(V)` to
`Ȟ⁰(𝒰, ℱ)` that is compatible with the inclusion of degree-zero Čech cohomology into the
degree-zero opcycles, and that morphism is an isomorphism.  This is the degree-zero clause of
[Stacks, Tag 01EP], in the packaged form the tag asks for.

## Main definitions

* `Stacks.Cohomology.CechSheaf.cechDegreeZeroRestriction`: the restriction map
  `ℱ(V) ⟶ Č⁰(𝒰, ℱ)`, with its source read as `SheafOfModules.evaluation`.

## Main results

* `Stacks.Cohomology.CechSheaf.existsUnique_cechRestrictionHomologyMap`: **the degree-zero
  clause of [Stacks, Tag 01EP]**, as a `∃!`.

## Implementation notes

Both halves of the content are already available.  Existence is
`Stacks.Cohomology.CechSheaf.homologyZeroIso`, which comes from the augmentation being a
kernel of the first Čech differential
(`Stacks.Cohomology.CechSheaf.isLimit_augmentedKernelFork`), composed with
`Stacks.Cohomology.CechSheaf.sectionsTerminalFunctorIso` to change the presentation of the
source from sections at the terminal object of the slice over `V` to
`SheafOfModules.evaluation`.  Uniqueness is nothing but `K.homologyι 0` being a
monomorphism, which holds for every homological complex with homology.

The compatibility `homologyZeroIso_inv_comp_homologyι` is the only computation.  It unwinds
`homologyZeroIso` once — the equation `homologyZeroIso_inv_eq` holds by `rfl`, since
`CategoryTheory.Iso.trans`, `CategoryTheory.Iso.symm` and `HomologicalComplex.isoHomologyπ`
are all built from the data they package — and then uses
`HomologicalComplex.homology_π_ι` to trade `homologyπ 0 ≫ homologyι 0` for
`iCycles 0 ≫ pOpcycles 0`, after which the cone-point comparison of the two kernel forks of
the first differential finishes it.

Everything below the restriction map is phrased at the
`CategoryTheory.cechComplexFunctor` spelling of the complex, and only the statement of the
final theorem at the `Stacks.Cohomology.CechSheaf.cechComplex` spelling; the two are
definitionally equal, so the final step is a single `exact`.  The reason for the discipline is
that `cechComplex` is a project `def`: instance search unifies at `instances` transparency and
therefore cannot cross it, so `IsIso` of the composite isomorphism is *not* synthesizable
against a goal stated with `cechComplex`, nor against a composite whose middle object is the
other spelling of the sections at the terminal object.  Hence the two isomorphisms are handed
to `CategoryTheory.IsIso.comp_isIso'` explicitly, which makes the elaborator check the
definitional equality instead of searching for it.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex

universe uX uR uM uI

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize

namespace Stacks.Cohomology.CechSheaf

noncomputable section

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  {ι : Type uI} [UnivLE.{uI, uM}]
  (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R)

/-- **The restriction map from the sections of `ℱ` on the covered open to degree zero of its
module-valued Čech complex.**

This is `Stacks.Cohomology.CechSheaf.cechAugmentation`, whose source is the sections at the
terminal object of the slice over `V`, with that source read as
`SheafOfModules.evaluation R (op V)` through `sectionsTerminalFunctorIso`. -/
def cechDegreeZeroRestriction :
    (SheafOfModules.evaluation.{uM} R (op V)).obj I ⟶ (cechComplex V U hU I).X 0 :=
  ((sectionsTerminalFunctorIso.{uX, uR, uM} V).app I).inv ≫ cechAugmentation V U hU I

/-- The inverse of `homologyZeroIso`, unwound into the comparison of the two kernel forks of
the first Čech differential followed by the projection to homology. -/
theorem homologyZeroIso_inv_eq :
    (homologyZeroIso V U hU I).inv =
      (IsLimit.conePointUniqueUpToIso
          (((cechComplexFunctor (coverObject U hU)).obj
            (sectionsPresheaf V I)).cyclesIsKernel 0 1 (by simp))
          (isLimit_augmentedKernelFork V U hU I)).inv ≫
        ((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).homologyπ 0 :=
  rfl

/-- The comparison of the two kernel forks of the first Čech differential carries the
inclusion of the cycles to the augmentation. -/
theorem conePointUniqueUpToIso_inv_comp_iCycles :
    (IsLimit.conePointUniqueUpToIso
        (((cechComplexFunctor (coverObject U hU)).obj
          (sectionsPresheaf V I)).cyclesIsKernel 0 1 (by simp))
        (isLimit_augmentedKernelFork V U hU I)).inv ≫
      ((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).iCycles 0 =
    cechAugmentation V U hU I :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (((cechComplexFunctor (coverObject U hU)).obj
      (sectionsPresheaf V I)).cyclesIsKernel 0 1 (by simp))
    (isLimit_augmentedKernelFork V U hU I) WalkingParallelPair.zero

/-- **`Ȟ⁰(𝒰, ℱ) ≅ Γ(V, ℱ)` is compatible with the inclusion into the degree-zero opcycles.**
Under that identification the Čech augmentation is the composite of the inverse isomorphism
with the inclusion of homology into opcycles. -/
theorem homologyZeroIso_inv_comp_homologyι :
    (homologyZeroIso V U hU I).inv ≫
        ((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).homologyι 0 =
      cechAugmentation V U hU I ≫
        ((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).pOpcycles 0 :=
  (congrArg
      (fun m => m ≫
        ((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).homologyι 0)
      (homologyZeroIso_inv_eq V U hU I)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg
            (fun m =>
              (IsLimit.conePointUniqueUpToIso
                  (((cechComplexFunctor (coverObject U hU)).obj
                    (sectionsPresheaf V I)).cyclesIsKernel 0 1 (by simp))
                  (isLimit_augmentedKernelFork V U hU I)).inv ≫ m)
            (HomologicalComplex.homology_π_ι
              (K := (cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I))
              (i := 0))).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg
            (fun m => m ≫
              ((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).pOpcycles 0)
            (conePointUniqueUpToIso_inv_comp_iCycles V U hU I)))))

/-- **The degree-zero clause of [Stacks, Tag 01EP].**  There is a unique `R(V)`-linear map from
the sections of `ℱ` on the covered open to degree-zero Čech cohomology whose composite with the
inclusion of homology into the degree-zero opcycles is the restriction map to the cover, and
that map is an isomorphism.

Existence is `homologyZeroIso`, which is the sheaf condition for the cover: the augmentation
is a kernel of the first Čech differential.  Uniqueness is the monomorphy of
`HomologicalComplex.homologyι`. -/
@[stacks 01EP "degree zero"]
theorem existsUnique_cechRestrictionHomologyMap :
    ∃! f : (SheafOfModules.evaluation.{uM} R (op V)).obj I ⟶ (cechComplex V U hU I).homology 0,
      IsIso f ∧
        f ≫ (cechComplex V U hU I).homologyι 0 =
          cechDegreeZeroRestriction V U hU I ≫ (cechComplex V U hU I).pOpcycles 0 := by
  have h : (((sectionsTerminalFunctorIso.{uX, uR, uM} V).app I).inv ≫
        (homologyZeroIso V U hU I).inv) ≫
      ((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).homologyι 0 =
      cechDegreeZeroRestriction V U hU I ≫
        ((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).pOpcycles 0 := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => ((sectionsTerminalFunctorIso.{uX, uR, uM} V).app I).inv ≫ m)
        (homologyZeroIso_inv_comp_homologyι V U hU I)).trans (Category.assoc _ _ _).symm)
  exact ⟨_, ⟨IsIso.comp_isIso'
    (Iso.isIso_inv ((sectionsTerminalFunctorIso.{uX, uR, uM} V).app I))
    (Iso.isIso_inv (homologyZeroIso V U hU I)), h⟩,
    fun g hg => (cancel_mono _).1 (hg.2.trans h.symm)⟩

end

end Stacks.Cohomology.CechSheaf

end
