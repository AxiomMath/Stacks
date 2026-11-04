module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DirectSums

/-!
# A quasi-coherent module in degree zero as an object of `D_QCoh`

Let `X` be a scheme and `M` a quasi-coherent `𝒪_X`-module. The complex with `M` in degree zero
and `0` elsewhere lies in `D_QCoh(𝒪_X)`: its zeroth cohomology sheaf is `M` and all the others
vanish, and a zero module is quasi-coherent because the quasi-coherent modules form a weak Serre
subcategory. In particular the structure sheaf `𝒪_X` gives a distinguished object of
`D_QCoh(𝒪_X)`, which is the object the relative dualizing complex of [Stacks, Tag 0B6S] is the
value of the twisted inverse image on.

## Main definitions

* `Stacks.Duality.DerivedPushforward.derivedStructureSheaf` — `𝒪_X` in degree zero, as an object
  of `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj` — a quasi-coherent
  module placed in degree zero lies in `D_QCoh(𝒪_X)`.

## Implementation notes

The vanishing of the cohomology sheaves away from degree zero is read off the t-structure: a
single complex in degree `n` is both `IsGE n` and `IsLE n`, so
`DerivedCategory.isZero_of_isGE` and `DerivedCategory.isZero_of_isLE` apply, and the degree-zero
cohomology is identified with `M` by `DerivedCategory.singleFunctorCompHomologyFunctorIso`.

This is deliberately *not* built from the comparison functor `D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X)` of
[Stacks, Tag 06VT], which is not available here — it would need `QCoh(𝒪_X)` to be abelian
([Stacks, Tag 077P]). The object is produced directly as a member of the full subcategory, in the
same way `AlgebraicGeometry.derivedTilde` is produced as an `ObjectProperty.lift` rather than
through that comparison.

No `@[stacks]` attribute is attached: [Stacks, Tag 0BQT] is the statement that `𝒪_X` *generates*
`D_QCoh(𝒪_X)` for a quasi-affine scheme, which is not proved here, and this object alone is no
part of a complete covering set for any tag.

## References

* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe w u

namespace Stacks.Duality.DerivedPushforward

open Stacks.AlgebraicGeometry.QuasicoherentWeakSerre

variable {X : Scheme.{u}}

/-- **A quasi-coherent module in degree zero lies in `D_QCoh(𝒪_X)`.** Its zeroth cohomology sheaf
is the module itself and the others vanish, and a zero module is quasi-coherent. The model of the
derived category is arbitrary. -/
theorem derivedCategoryB_singleFunctor_obj [HasDerivedCategory.{w} X.Modules] (M : X.Modules)
    (hM : M.IsQuasicoherent) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((DerivedCategory.singleFunctor X.Modules 0).obj M) := by
  intro i
  rcases lt_trichotomy i 0 with h | rfl | h
  · exact DerivedCategoryB.zero_mem_of_isWeakSerre _ (isQuasicoherent_isWeakSerre X) _
      (DerivedCategory.isZero_of_isGE (C := X.Modules)
        ((DerivedCategory.singleFunctor X.Modules 0).obj M) 0 i h)
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app M).symm hM
  · exact DerivedCategoryB.zero_mem_of_isWeakSerre _ (isQuasicoherent_isWeakSerre X) _
      (DerivedCategory.isZero_of_isLE (C := X.Modules)
        ((DerivedCategory.singleFunctor X.Modules 0).obj M) 0 i h)

/-- **The structure sheaf in degree zero, as an object of `D_QCoh(𝒪_X)`.** This is the object
whose image under the twisted inverse image of a morphism `f : X ⟶ Y` is the relative dualizing
complex of [Stacks, Tag 0B6S]. -/
def derivedStructureSheaf (X : Scheme.{u}) : Stacks.Duality.quasiCoherentDerivedCategory X :=
  ⟨(DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf),
    derivedCategoryB_singleFunctor_obj _
      (inferInstance : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent)⟩

end Stacks.Duality.DerivedPushforward

end
