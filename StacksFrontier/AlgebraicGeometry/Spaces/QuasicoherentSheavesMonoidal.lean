module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf

/-!
# The symmetric monoidal structure on the quasi-coherent sheaves on an algebraic space

Let `F` be an algebraic space.  `AlgebraicGeometry.Space.QuasicoherentSheaves` is the full
subcategory of `AlgebraicGeometry.Space.Modules` cut out by quasi-coherence on the small étale
ringed site, and `AlgebraicGeometry.Space.modulesMonoidalCategory` equips the ambient category
with the tensor product of Stacks 01CA.  Quasi-coherence is stable under that tensor product by
Stacks 03M1(5) and holds for its unit, so quasi-coherence is a monoidal property of objects and
`QCoh(𝒪_F)` inherits the whole symmetric monoidal structure.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentSheavesMonoidalCategory`: **the tensor product of
  quasi-coherent sheaves on an algebraic space.**
* `AlgebraicGeometry.Space.quasicoherentSheavesBraidedCategory` and
  `AlgebraicGeometry.Space.quasicoherentSheavesSymmetricCategory`: its braiding and the symmetry
  of that braiding.

## Main results

* `AlgebraicGeometry.Space.containsUnit_isQuasicoherentOnSite`,
  `AlgebraicGeometry.Space.tensorLE_isQuasicoherentOnSite` and
  `AlgebraicGeometry.Space.isMonoidal_isQuasicoherentOnSite`: **quasi-coherence on the small
  étale site is a monoidal property of `𝒪_F`-modules**, which is the content of the monoidal
  structure below.
* `AlgebraicGeometry.Space.quasicoherentSheavesTensorObj_obj` and
  `AlgebraicGeometry.Space.quasicoherentSheavesTensorUnit_obj`: the underlying `𝒪_F`-module of a
  tensor product of quasi-coherent sheaves is the tensor product of the underlying modules, and
  the underlying module of the unit is `𝒪_F`, both on the nose.  These are what pin the
  structure down: no associator or unitor is constructed here.

## Implementation notes

Both clauses of `CategoryTheory.ObjectProperty.IsMonoidal` are already proved and only need
packaging.  The tensor clause is `AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorObj`,
Stacks 03M1(5) for `AlgebraicGeometry.Space.modulesMonoidalCategory`; the generic tensor clause
of `Stacks.SheafOfModules.isQuasicoherentOnSite_tensorSheaf` is **not** usable here, for the
universe reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulesTensorQuasicoherent.lean`.  The unit clause is
`SheafOfModules.isQuasicoherentOnSite_unit`, which holds over any sheaf of rings on any site at
the module universe of the rings, and it applies on the nose because the unit of the tensor
product of `𝒪_F`-modules *is* the structure sheaf viewed as a module over itself, which is
`AlgebraicGeometry.Space.modulesTensorUnit_eq`.

Full coherence is then inherited from the ambient category by
`CategoryTheory.ObjectProperty.fullMonoidalSubcategory`, and the braiding and its symmetry by
`CategoryTheory.ObjectProperty.fullBraidedSubcategory` and
`CategoryTheory.ObjectProperty.fullSymmetricSubcategory`.  This mirrors
`AlgebraicGeometry.FibredSite.monoidalCategoryQuasicoherentModules` of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/QuasicoherentMonoidal.lean`, which does the
same for the fppf site of a category fibred in groupoids.

The three inherited structures are `instance_reducible` definitions rather than global
instances, exactly as `AlgebraicGeometry.Space.modulesMonoidalCategory` is and for the same
reason: a global monoidal instance on a category of sheaves of modules, or on a full subcategory
of one, is found by instance search in every statement about such sheaves, including the ones
whose intended tensor product is a different one.  The three `ObjectProperty` clauses, by
contrast, are global instances: their types name
`AlgebraicGeometry.Space.modulesMonoidalCategory` explicitly, so they are only found once that
structure has been activated.

No clause of Stacks 03M1 is proved here and no `@[stacks]` attribute is claimed: clause (5) is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorObj`, and this file packages it.  In
particular nothing here concerns Stacks 081V: a monoidal structure on `QCoh(𝒪_F)` is what makes
a quasi-coherent algebra a structure *in* `QCoh(𝒪_F)`, but the anti-equivalence of Stacks 081V
is between algebraic spaces affine over `X` and quasi-coherent `𝒪_X`-algebras, and nothing below
constructs a functor between those.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory
  modulesSymmetricCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Quasi-coherence on the small étale site contains the tensor unit.**  The unit of
`AlgebraicGeometry.Space.modulesMonoidalCategory` is `𝒪_F` viewed as a module over itself, by
`AlgebraicGeometry.Space.modulesTensorUnit_eq`, and the structure sheaf of a ringed site is
quasi-coherent over any sheaf of rings. -/
instance containsUnit_isQuasicoherentOnSite :
    ObjectProperty.ContainsUnit
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) where
  prop_unit := SheafOfModules.isQuasicoherentOnSite_unit _

/-- **Quasi-coherence on the small étale site is stable under the tensor product of
`𝒪_F`-modules.**  This is Stacks 03M1(5),
`AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorObj`, as a clause of
`CategoryTheory.ObjectProperty.IsMonoidal`. -/
instance tensorLE_isQuasicoherentOnSite :
    ObjectProperty.TensorLE
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) where
  prop_tensor M N hM hN :=
    have := hM
    have := hN
    isQuasicoherentOnSite_tensorObj B S hS F hF M N

/-- **Quasi-coherence on the small étale site is a monoidal property of `𝒪_F`-modules.**
Together with `CategoryTheory.ObjectProperty.fullMonoidalSubcategory` this is what gives the
tensor product of quasi-coherent sheaves its full coherence. -/
instance isMonoidal_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).IsMonoidal where

/-- **The tensor product of quasi-coherent sheaves on an algebraic space `F`.**  The tensor
product of two quasi-coherent `𝒪_F`-modules is their tensor product as `𝒪_F`-modules, which is
again quasi-coherent by Stacks 03M1(5), and the associator and the unitors are those of
`AlgebraicGeometry.Space.modulesMonoidalCategory`. -/
@[instance_reducible]
noncomputable def quasicoherentSheavesMonoidalCategory :
    MonoidalCategory (QuasicoherentSheaves.{u, u} B S hS F hF) :=
  ObjectProperty.fullMonoidalSubcategory _

attribute [local instance] quasicoherentSheavesMonoidalCategory

/-- The underlying `𝒪_F`-module of the tensor product of two quasi-coherent sheaves is the
tensor product of their underlying `𝒪_F`-modules, on the nose. -/
theorem quasicoherentSheavesTensorObj_obj (M N : QuasicoherentSheaves.{u, u} B S hS F hF) :
    (M ⊗ N).obj = M.obj ⊗ N.obj :=
  rfl

/-- The underlying `𝒪_F`-module of the unit of the tensor product of quasi-coherent sheaves is
`𝒪_F` itself, on the nose. -/
theorem quasicoherentSheavesTensorUnit_obj :
    (𝟙_ (QuasicoherentSheaves.{u, u} B S hS F hF)).obj =
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) :=
  rfl

/-- The braiding of the tensor product of quasi-coherent sheaves on an algebraic space, inherited
from the braiding of `AlgebraicGeometry.Space.modulesBraidedCategory`. -/
@[instance_reducible]
noncomputable def quasicoherentSheavesBraidedCategory :
    @BraidedCategory (QuasicoherentSheaves.{u, u} B S hS F hF) _
      (quasicoherentSheavesMonoidalCategory B S hS F hF) :=
  ObjectProperty.fullBraidedSubcategory _

/-- The tensor product of quasi-coherent sheaves on an algebraic space is symmetric. -/
@[instance_reducible]
noncomputable def quasicoherentSheavesSymmetricCategory :
    @SymmetricCategory (QuasicoherentSheaves.{u, u} B S hS F hF) _
      (quasicoherentSheavesMonoidalCategory B S hS F hF) :=
  ObjectProperty.fullSymmetricSubcategory _

end AlgebraicGeometry.Space

end
