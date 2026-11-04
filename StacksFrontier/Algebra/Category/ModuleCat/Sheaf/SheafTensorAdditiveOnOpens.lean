module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Geometry.RingedSpace.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery

/-!
# Additivity of the sheaf tensor product, named for the open-cover site of a space

`Stacks.SheafOfModules.Tensor.sheafTensor_additive` and
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive` are already global instances, proved for
an arbitrary small site `(C, J)` from the two hypotheses `HasWeakSheafify J AddCommGrpCat.{max u
v}` and `J.WEqualsLocallyBijective AddCommGrpCat.{max u v}`.  At the open-cover site `Opens Y` of
a space `Y : TopCat.{u}` those two hypotheses hold (the site is essentially small), but instance
search cannot find them on its own: it would have to solve `max ?v u =?= u` for the unknown
category-level `?v` of `Opens Y` before it can even look for the hypotheses, and that equation
has no unique solution. So every one of nine files restated `sheafTensor_additive` and
`sheafTensor_obj_additive` by name, each time at its own sheaf of rings. This file gives that
restatement one shared home, over an arbitrary space and sheaf of rings on it, so the nine copies
can be replaced by `attribute [local instance]` lines pointing here.

## Main definitions

* `Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive`
* `Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive`
* `Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor`: the total tensor
  complexes exist, at the same site.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.Topology.SheafTensorAdditiveOnOpens

/-- `⊗_{𝒪_Y}` is additive in its first variable, for a sheaf of commutative rings `Rc` on the
open-cover site of a space `Y`. -/
scoped instance sheafTensorAdditive {Y : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} Y) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive :=
  haveI : HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  haveI : (Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u}
    (J := Opens.grothendieckTopology Y) Rc

/-- `ℱ ⊗_{𝒪_Y} -` is additive, for a sheaf of commutative rings `Rc` on the open-cover site of a
space `Y`. -/
scoped instance sheafTensorObjAdditive {Y : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} Y)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Rc)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive :=
  haveI : HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  haveI : (Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
    (J := Opens.grothendieckTopology Y) Rc M

/-- The total complexes `Tot(K₁ ⊗_{𝒪_Y} K₂)` of the tensor double complexes exist, for a sheaf of
commutative rings `Rc` on the open-cover site of a space `Y`. -/
scoped instance hasMapBifunctorSheafTensor {Y : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} Y)
    (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Rc)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Rc)
      (ComplexShape.up ℤ) :=
  haveI : HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  haveI : (Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor (J := Opens.grothendieckTopology Y)
    Rc K₁ K₂

end Stacks.Topology.SheafTensorAdditiveOnOpens

end
