module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of the internal Hom complex

Let `(X, O_X)` be a ringed space, let `L` and `M` be cochain complexes of `O_X`-modules and
let `U ⊆ X` be open. The `n`-th cohomology of the complex of sections over `U` of the internal
Hom complex `SheafHom^•(L, M)` is the group of morphisms `L|_U ⟶ M|_U[n]` in the homotopy
category of complexes of `O_U`-modules:
`H^n(Γ(U, SheafHom^•(L, M))) = Hom_{K(O_U)}(L|_U, M|_U[n])`.

This is [Stacks, Tag 0A8L], and it is one identification composed of three: the defining
identification of the sections of the internal Hom complex with the ordinary Hom complex of
the restricted complexes, Mathlib's identification of the cohomology of a Hom complex with its
group of cohomology classes of cocycles, and Mathlib's identification of a cohomology class
with a morphism in the homotopy category.

## Main definitions

* `Stacks.SheafOfModules.sheafHomComplexHomologyEquivHomotopyCategory`: the identification
  above, as an additive equivalence.

## Implementation notes

The internal Hom complex enters as an arbitrary realization
`H : Stacks.SheafOfModules.SheafHomComplex Rc L M`, so the statement is about any complex with
the characterizing section data and not about one particular construction; the restriction to
`U` is on the slice site `Opens X / U`, matching that data. That realization parameter is not a
hypothesis of [Stacks, Tag 0A8L]: `Stacks.SheafOfModules.sheafHomComplexHomologyEquiv`
instantiates the equivalence below at the construction of [Stacks, Tag 0A8K] and
`Stacks.SheafOfModules.sheafHomComplexHomologyEquiv_sectionComplexIsoOfRealizations` shows the
two agree.

## References

* [Stacks Project, Tag 0A8L](https://stacks.math.columbia.edu/tag/0A8L)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CochainComplex.HomComplex

universe u

namespace Stacks.SheafOfModules

/-- The `n`-th cohomology of the sections over `U` of the internal Hom complex from `L` to `M` is
canonically the group of morphisms from `L|_U` to `M|_U[n]` in the homotopy category of complexes
of `O_U`-modules. -/
@[stacks 0A8L]
noncomputable def sheafHomComplexHomologyEquivHomotopyCategory
    {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
    (U : Opens X)
    (L M : CochainComplex (StructureSheafModules Rc) ℤ)
    (H : SheafHomComplex Rc L M) (n : ℤ) :
    (sectionComplex Rc H.obj U).homology n ≃+
      ((HomotopyCategory.quotient
          (SheafOfModules.{u} ((structureSheaf Rc).over U))
          (ComplexShape.up ℤ)).obj (restrictComplex Rc L U) ⟶
        (HomotopyCategory.quotient
          (SheafOfModules.{u} ((structureSheaf Rc).over U))
          (ComplexShape.up ℤ)).obj ((restrictComplex Rc M U)⟦n⟧)) :=
  ((HomologicalComplex.homologyMapIso (H.sectionsIso U) n).addCommGroupIsoToAddEquiv).trans
    ((homologyAddEquiv _ _ n).trans CohomologyClass.homAddEquiv)

end Stacks.SheafOfModules
