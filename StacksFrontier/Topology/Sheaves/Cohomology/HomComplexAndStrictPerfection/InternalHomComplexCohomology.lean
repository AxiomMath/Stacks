module

public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomotopyCategoryHoms
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.RealizationComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of the sections of the internal Hom complex

Let `(X, O_X)` be a ringed space, let `L` and `M` be cochain complexes of `O_X`-modules and let
`U ⊆ X` be open. [Stacks, Tag 0A8L] records the identification
`H^n(Γ(U, SheafHom^•(L, M))) = Hom_{K(O_U)}(L|_U, M|_U[n])`, for all `n ∈ ℤ` and every open
`U ⊆ X`, where `SheafHom^•(L, M)` is the internal Hom complex constructed in
[Stacks, Tag 0A8K].

`Stacks.SheafOfModules.sheafHomComplexHomologyEquivHomotopyCategory` proves that identification
for an arbitrary realization `H` of the internal Hom complex. This file instantiates it at the
construction `Stacks.SheafOfModules.sheafHomComplex` of [Stacks, Tag 0A8K], so that the
identification holds with no hypothesis beyond the data `(X, O_X)`, `U`, `L`, `M` and `n` that
Stacks names, and proves that nothing is lost either way: the identification attached to an
arbitrary realization is the one attached to the construction, precomposed on homology with the
canonical comparison of the two realizations.

## Main definitions

* `Stacks.SheafOfModules.sectionComplexIsoOfRealizations`: the canonical isomorphism of two
  realizations of the internal Hom complex, read on sections over an open.
* `Stacks.SheafOfModules.sheafHomComplexHomologyEquiv`: [Stacks, Tag 0A8L] for the internal Hom
  complex of [Stacks, Tag 0A8K], with no realization parameter.

## Main results

* `Stacks.SheafOfModules.sectionComplexIsoOfRealizations_hom_comp_sectionsIso`: on sections over
  an open, the canonical comparison of two realizations carries the section identification of the
  target realization to that of the source.
* `Stacks.SheafOfModules.sheafHomComplexHomologyEquiv_sectionComplexIsoOfRealizations`: the
  identification of [Stacks, Tag 0A8L] attached to an arbitrary realization is the one attached to
  the construction of [Stacks, Tag 0A8K], precomposed with the comparison on homology.

## Implementation notes

`Stacks.SheafOfModules.sectionComplex` is the image of a complex under the section functor
`Stacks.SheafOfModules.sectionAbelianFunctor`, which is applied to complexes through
`CategoryTheory.Functor.mapHomologicalComplex` and therefore needs that functor to preserve zero
morphisms. That instance is local to
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.Defs`, so it is restated here;
`CategoryTheory.Functor.PreservesZeroMorphisms` is a `Prop`, so the restated instance and the
original are interchangeable and `sectionComplex` is unaffected.

## References

* [Stacks Project, Tag 0A8K](https://stacks.math.columbia.edu/tag/0A8K)
* [Stacks Project, Tag 0A8L](https://stacks.math.columbia.edu/tag/0A8L)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CochainComplex.HomComplex

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  {L M : CochainComplex (StructureSheafModules Rc) ℤ}

/-- Taking sections over an open sends a zero morphism to a zero morphism. -/
noncomputable local instance sectionAbelianFunctorPreservesZero (U : Opens X) :
    (sectionAbelianFunctor Rc U).PreservesZeroMorphisms where
  map_zero {A B} := by
    ext x
    rfl

/-- The canonical isomorphism `Stacks.SheafOfModules.isoOfRealizations` of two realizations of
the internal Hom complex `SheafHom^•(L, M)`, read on the complexes of sections over an open
`U`. -/
noncomputable def sectionComplexIsoOfRealizations
    (H H' : SheafHomComplex Rc L M) (U : Opens X) :
    sectionComplex Rc H.obj U ≅ sectionComplex Rc H'.obj U :=
  ((sectionAbelianFunctor Rc U).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    (isoOfRealizations Rc H H')

/-- The canonical comparison of two realizations carries the section identification of the target
realization to the section identification of the source: on sections over `U`, comparing and then
reading off the Hom cochain of `H'` is reading off the Hom cochain of `H`. -/
theorem sectionComplexIsoOfRealizations_hom_comp_sectionsIso
    (H H' : SheafHomComplex Rc L M) (U : Opens X) :
    (sectionComplexIsoOfRealizations Rc H H' U).hom ≫ (H'.sectionsIso U).hom =
      (H.sectionsIso U).hom := by
  ext n s
  exact isoOfRealizations_sectionsIso Rc H H' U n s

/-- **Stacks 0A8L.** The `n`-th cohomology of the sections over `U` of the internal Hom complex
`SheafHom^•(L, M)` of [Stacks, Tag 0A8K] is canonically the group of morphisms from `L|_U` to
`M|_U[n]` in the homotopy category of complexes of `O_U`-modules. -/
@[stacks 0A8L "H^n(Γ(U, SheafHom^•(L, M))) = Hom_{K(O_U)}(L|_U, M|_U[n]) for every open U of X
and every n ∈ ℤ, with SheafHom^•(L, M) the internal Hom complex constructed in Tag 0A8K."]
noncomputable def sheafHomComplexHomologyEquiv (U : Opens X)
    (L M : CochainComplex (StructureSheafModules Rc) ℤ) (n : ℤ) :
    (sectionComplex Rc (sheafHomComplex Rc L M).obj U).homology n ≃+
      ((HomotopyCategory.quotient
          (SheafOfModules.{u} ((structureSheaf Rc).over U))
          (ComplexShape.up ℤ)).obj (restrictComplex Rc L U) ⟶
        (HomotopyCategory.quotient
          (SheafOfModules.{u} ((structureSheaf Rc).over U))
          (ComplexShape.up ℤ)).obj ((restrictComplex Rc M U)⟦n⟧)) :=
  sheafHomComplexHomologyEquivHomotopyCategory Rc U L M (sheafHomComplex Rc L M) n

/-- The identification of [Stacks, Tag 0A8L] attached to an arbitrary realization `H` of the
internal Hom complex is the identification attached to the construction of [Stacks, Tag 0A8K],
precomposed on homology with the canonical comparison of the two realizations. So the realization
parameter carries no extra generality. -/
theorem sheafHomComplexHomologyEquiv_sectionComplexIsoOfRealizations
    (U : Opens X) (H : SheafHomComplex Rc L M) (n : ℤ)
    (x : (sectionComplex Rc H.obj U).homology n) :
    sheafHomComplexHomologyEquivHomotopyCategory Rc U L M H n x =
      sheafHomComplexHomologyEquiv Rc U L M n
        (Iso.addCommGroupIsoToAddEquiv (HomologicalComplex.homologyMapIso
          (sectionComplexIsoOfRealizations Rc H (sheafHomComplex Rc L M) U) n) x) := by
  have key : HomologicalComplex.homologyMap (H.sectionsIso U).hom n =
      HomologicalComplex.homologyMap
          (sectionComplexIsoOfRealizations Rc H (sheafHomComplex Rc L M) U).hom n ≫
        HomologicalComplex.homologyMap ((sheafHomComplex Rc L M).sectionsIso U).hom n := by
    rw [← HomologicalComplex.homologyMap_comp,
      sectionComplexIsoOfRealizations_hom_comp_sectionsIso]
  have hx : (AddCommGrpCat.Hom.hom (HomologicalComplex.homologyMap (H.sectionsIso U).hom n)) x =
      (AddCommGrpCat.Hom.hom (HomologicalComplex.homologyMap
          ((sheafHomComplex Rc L M).sectionsIso U).hom n))
        ((AddCommGrpCat.Hom.hom (HomologicalComplex.homologyMap
          (sectionComplexIsoOfRealizations Rc H (sheafHomComplex Rc L M) U).hom n)) x) := by
    rw [key]
    rfl
  simp only [sheafHomComplexHomologyEquivHomotopyCategory, sheafHomComplexHomologyEquiv,
    AddEquiv.trans_apply, Iso.addCommGroupIsoToAddEquiv, HomologicalComplex.homologyMapIso]
  exact congrArg (fun y ↦ CohomologyClass.homAddEquiv
    ((homologyAddEquiv (restrictComplex Rc L U) (restrictComplex Rc M U) n) y)) hx

end Stacks.SheafOfModules

end
