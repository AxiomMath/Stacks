module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitAtTerminal
public import StacksFrontier.CategoryTheory.Sites.Modules.SectionsOverObjectDerivedCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# A finite free module in degree zero is a coproduct of copies of `j_{⊤!} O`

Let `(C, O)` be a ringed site whose objects, morphisms and ring sections share one universe, and
let `U` be a *terminal* object of `C`.  At the module level the extension by zero of the structure
sheaf of the slice site over `U` is the structure sheaf itself,
`Stacks.Sites.ExtensionByZero.extensionByZeroUnitObjIsoUnit`, and consequently `O^{⊕ι}` is a
coproduct of copies of `j_{U!} O_U`.  This file carries that presentation into the derived
category: for a *finite* index type `ι`, the free module `O^{⊕ι}` placed in degree zero is a
colimiting `CategoryTheory.Limits.Cofan` of copies of
`Stacks.Sites.ExtensionByZero.singleExtensionByZeroUnit X U`.

Finiteness of `ι` is what makes the transport free: the degree-zero single functor
`C ⥤ D(C)` is additive, and an additive functor between preadditive categories preserves finite
coproducts (`CategoryTheory.Limits.preservesFiniteCoproductsOfAdditive`).  No statement about
infinite coproducts in a derived category is needed, and none is made.

This is what lets the local free surjection of the induction of Stacks 08HE (2) ⇒ (1) be fed to
the machinery stated in terms of extension-by-zero units: the lifting step
`AlgebraicGeometry.exists_lift_truncGEπ_zero_cofan_of_isAffineOpen` takes its source as a
colimiting cofan of copies of `singleExtensionByZeroUnit`, while the induction step
`AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift` takes it as
`(DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.free ι)`.  On an affine scheme one takes
`U = ⊤`, where nothing is shrunk and the surjection is global; `⊤` is terminal in the opens of a
scheme by `CategoryTheory.Limits.isTerminalTop`.

## Main definitions

* `Stacks.Sites.ExtensionByZero.singleExtensionByZeroUnitIsoSingleUnit`: **`j_{U!} O_U ≅ O` in
  degree zero**, at a terminal `U`.
* `Stacks.Sites.ExtensionByZero.freeCofanSingleExtensionByZeroUnit`: the cofan of `ι` copies of
  `j_{U!} O_U` in degree zero whose point is `O^{⊕ι}` in degree zero.

## Main results

* `Stacks.Sites.ExtensionByZero.singleExtensionByZeroUnit_eq`: the two spellings of `j_{U!} O_U`
  in degree zero — through `CochainComplex.singleFunctor` and the localization functor, and
  through `DerivedCategory.singleFunctor` — are definitionally equal.
* `Stacks.Sites.ExtensionByZero.isColimitFreeCofanSingleExtensionByZeroUnit`: **that cofan is
  colimiting for a finite index type.**

## Implementation notes

`Stacks.Sites.ExtensionByZero.singleExtensionByZeroUnit` is elaborated with the standard model
`CategoryTheory.HasDerivedCategory.standard` of the derived category, which that file installs as
a local instance; the same local instance is installed here, so the derived categories of the two
files are the same one and no comparison is needed.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Sites.ExtensionByZero

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- `j_{U!} O_U` placed in degree zero, as the degree-zero single functor of the derived category
applied to `j_{U!} O_U`.  The two spellings are definitionally equal: the single functors of the
derived category are by definition those of the category of cochain complexes postcomposed with
the localization functor. -/
theorem singleExtensionByZeroUnit_eq :
    singleExtensionByZeroUnit X U =
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (extensionByZeroUnitObj X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
  rfl

/-- **`j_{U!} O_U ≅ O` in degree zero**, at a terminal object of the site: the module-level
isomorphism `Stacks.Sites.ExtensionByZero.extensionByZeroUnitObjIsoUnit` read through the
degree-zero single functor. -/
def singleExtensionByZeroUnitIsoSingleUnit (hU : IsTerminal U) :
    singleExtensionByZeroUnit X U ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).mapIso
    (extensionByZeroUnitObjIsoUnit X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U hU)

/-- The cofan of `ι` copies of `j_{U!} O_U` in degree zero whose point is the free module
`O^{⊕ι}` in degree zero: the injections are those of
`Stacks.Sites.ExtensionByZero.freeCofanExtensionByZeroUnit`, read through the degree-zero single
functor. -/
abbrev freeCofanSingleExtensionByZeroUnit (hU : IsTerminal U) (ι : Type u) :
    Cofan (fun _ : ι => singleExtensionByZeroUnit X U) :=
  Cofan.mk ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι))
    (fun i => (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
      ((extensionByZeroUnitObjIsoUnit X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U hU).hom ≫
        SheafOfModules.ιFree i))

/-- **A finite free module in degree zero is a coproduct of copies of `j_{U!} O_U` in degree
zero**, at a terminal object `U` of the site.

The module-level presentation is
`Stacks.Sites.ExtensionByZero.isColimitFreeCofanExtensionByZeroUnit`, and the degree-zero single
functor carries it over because it is additive and `ι` is finite. -/
def isColimitFreeCofanSingleExtensionByZeroUnit (hU : IsTerminal U) (ι : Type u) [Finite ι] :
    IsColimit (freeCofanSingleExtensionByZeroUnit X U hU ι) :=
  isColimitCofanMkObjOfIsColimit
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0) _ _
    (isColimitFreeCofanExtensionByZeroUnit X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U hU ι)

end Stacks.Sites.ExtensionByZero

end
