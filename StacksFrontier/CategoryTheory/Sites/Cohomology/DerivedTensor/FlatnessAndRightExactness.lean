module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-! # Reading flatness and right exactness off the tensor bifunctor of a ringed site

The canonical tensor bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` is the one used by
Tag 06YM and the K-flatness predicate of Tag 06Y9. Tag 05NB states preservation of colimits
directly for its fixed-left-factor functor. This file combines that result with the right-tensor
form of flatness from Tag 03ER (3) and the canonical braiding, so that the exactness and colimit
statements can be used in either tensor order.

## Main results

* `Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat` and its converse
  `isFlat_of_exactFunctor_sheafTensorFlip`: flatness read off the flipped `sheafTensor`.
* `Stacks.SheafOfModules.preservesColimits_sheafTensorObj` and
  `preservesColimits_sheafTensorFlipObj`: Tag 05NB in both tensor orders, with
  `preservesFiniteColimits_sheafTensorObj` and `preservesFiniteColimits_sheafTensorFlipObj`
  the right-exactness forms its consumers ask for.
* `Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat`: tensoring on the left with a flat
  sheaf of modules is exact.

## Implementation notes

Colimit preservation is applied directly to the canonical fixed-factor functor, without a
spelling isomorphism. The two flatness lemmas identify its flipped form with the functor used
by `AlgebraicGeometry.SheafOfModules.IsFlat`.

Passing between the two tensor orders is `Stacks.SheafOfModules.Tensor.sheafTensorBraiding`.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

-- The sections universe `w` is independent of the site universes, so Mathlib's
-- size-restricted instances do not supply the sheaf-condition composition used by `IsFlat`.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- **Tag 05NB** for the tensor bifunctor of Tag 06YM: tensoring on the left with a fixed sheaf
of modules preserves all colimits. -/
lemma preservesColimits_sheafTensorObj
    (X : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimitsOfSize.{w, w} ((Tensor.sheafTensor.{u, v, w, w, w} R).obj X) :=
  TensorColimits.tensorLeft_preservesColimits J R X

/-- Tensoring on the right with a fixed sheaf of modules preserves all colimits, by the
symmetry of the tensor product. -/
@[ega "0 4.1.5" "partial, tensor product"]
lemma preservesColimits_sheafTensorFlipObj
    (X : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimitsOfSize.{w, w}
      ((Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj X) := by
  have := preservesColimits_sheafTensorObj R X
  exact preservesColimits_of_natIso ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).app X)

/-- Tensoring on the left with a fixed sheaf of modules is right exact, preserving all
colimits by Tag 05NB. -/
lemma preservesFiniteColimits_sheafTensorObj
    (X : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesFiniteColimits ((Tensor.sheafTensor.{u, v, w, w, w} R).obj X) :=
  let := preservesColimits_sheafTensorObj R X
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Tensoring on the right with a fixed sheaf of modules is right exact, preserving all
colimits by Tag 05NB. -/
@[ega "0 4.1.5" "partial"]
lemma preservesFiniteColimits_sheafTensorFlipObj
    (X : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesFiniteColimits ((Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj X) :=
  let := preservesColimits_sheafTensorFlipObj R X
  PreservesColimitsOfSize.preservesFiniteColimits _

section Bridge

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.sheafTensor
  PresheafOfModules.tensorBifunctor
    AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
  AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorMap

/-- Flatness of a sheaf of modules, read off the tensor bifunctor of Tag 06YM: the endofunctor
whose exactness it asserts is the one that bifunctor gives when the flat sheaf is the right
tensor factor. -/
lemma exactFunctor_sheafTensorFlip_of_isFlat
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (h : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) M) :
    exactFunctor _ _ ((Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj M) := h

/-- The converse reading of `exactFunctor_sheafTensorFlip_of_isFlat`. -/
lemma isFlat_of_exactFunctor_sheafTensorFlip
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (h : exactFunctor _ _ ((Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj M)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) M := h

end Bridge

/-- Tensoring on the left with a flat sheaf of modules is an exact functor: flatness is
exactness of tensoring on the right, and the two orders agree. -/
lemma exact_sheafTensorObj_of_isFlat
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) M) :
    exactFunctor _ _ ((Tensor.sheafTensor.{u, v, w, w, w} R).obj M) :=
  (exactFunctor _ _).prop_of_iso ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).app M).symm
    (exactFunctor_sheafTensorFlip_of_isFlat R M hM)

end Stacks.SheafOfModules

end
