module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroTensorFreeModuleUniverse
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactnessFreeModuleUniverse
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18b.FlatRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to an object preserves flatness, at a free module universe

Let `(C, O)` be a ringed site whose objects lie in `Type u`, whose morphisms lie in `v` and
whose structure sheaf has sections in `w`, let `U` be an object of `C` and let `F` be a flat
sheaf of `O`-modules with sections in `max v a`. Then the restriction `F|_U` of `F` to the site
localized at `U` is a flat sheaf of `O|_U`-modules. This is Stacks 0E8J with the module
universe a free parameter and no smallness assumption on `C`.

## Main results

* `Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse.isFlat_over`: **Stacks 0E8J** at a
  free module universe.

## Universes

`Stacks.SheafOfModules.FlatRestriction.isFlat_over` states the same thing at
`RingedSite.{u, u, u}`. At a free module universe the two inputs are the following.

* The reflection of exactness by extension by zero, Stacks 0E8G, is
  `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.extensionByZero_exact_iff`, for objects in
  `Type u`, morphisms in `v`, ring sections in `w` and module sections in `max v a`.
* The comparison `j_{U!}(-) ⊗ F ≅ j_{U!}(- ⊗ F|_U)`, Stacks 0E8I, is
  `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.restrictionTensorIso`, at the same shape.

The module universe has the form `max v a`, which says that it dominates the universe `v` of the
morphisms of the site. The bound is used in 0E8G, on Grothendieck's AB4 for the direct sum over a
hom-set of `C` that computes the sections of an extension by zero.

## Strong sheafification is not an extra hypothesis

Stacks 0E8G at a free module universe asks for `HasSheafify`, the *left exact* sheafification,
on `X.J` and on `X.J.over U`, where this statement's hypotheses only name `HasWeakSheafify`.
Nothing is assumed to bridge that:
`AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective` produces `HasSheafify` from
`HasWeakSheafify` together with `GrothendieckTopology.WEqualsLocallyBijective`, at wholly
independent universes, and both of those are already hypotheses of the comparison
`restrictionTensorIso` that this proof runs through. The two instances are therefore derived
inside the proof, and the statement's hypotheses are exactly those of 0E8I at this shape.

## Implementation notes

The one abstract step of the proof — a functor that preserves and reflects exactness, an exact
functor it intertwines with, and the conclusion that the intertwined functor is exact — is
`Stacks.SheafOfModules.FlatRestriction.exactFunctor_of_reflecting_extension_exported`, whose
universes are already independent.

The auxiliary facts about tensoring that the argument needs (additivity, preservation of finite
colimits, and exactness of tensoring with a flat module) are stated here at independent
universes. The right-exactness they rest on,
`Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits` of Stacks 05NB, is already
stated at independent universes. `Stacks.SheafOfModules.FlatSquareZero.tensorLeft_additive` puts
the sections of the ring and the sections of the modules in one universe `w`, so it does not
apply here.

## References

* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
* [Stacks Project, Tag 0E8G](https://stacks.math.columbia.edu/tag/0E8G)
* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse

universe a w v u

open AlgebraicGeometry (RingedSite)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.SheafOfModules.TensorColimits (tensorLeft_preservesColimits)
open Stacks.Sites.ExtensionByZero.FreeModuleUniverse
  (tensorLeftIsoSheafTensorRight extendByZero sliceSheafTensorRight restrictionTensorIso)

/-! ### Tensoring with a flat sheaf of modules, at a free module universe -/

section SheafLevel

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v a}]
  [HasWeakSheafify J AddCommGrpCat.{max v a}]

/-- A functor between abelian categories that preserves finite colimits is additive. -/
private theorem additive_of_preservesFiniteColimits {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] (T : A ⥤ B) [PreservesFiniteColimits T] : T.Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  Functor.additive_of_preservesBinaryBiproducts T

/-- Tensoring with a sheaf of modules preserves finite colimits. -/
private theorem tensorLeft_preservesFiniteColimits (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{max v a} (ringSheaf O)) :
    PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max v a, max v a} O).obj F) := by
  have : PreservesColimitsOfSize.{0, max v a}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max v a, max v a} O).obj F) :=
    tensorLeft_preservesColimits J O F
  exact PreservesColimitsOfSize.preservesFiniteColimits
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max v a, max v a} O).obj F)

/-- Tensoring with a sheaf of modules is an additive functor, because it preserves
finite colimits. -/
private instance tensorLeft_additive (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{max v a} (ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max v a, max v a} O).obj F).Additive :=
  have := tensorLeft_preservesFiniteColimits J O F
  additive_of_preservesFiniteColimits _

/-- For a flat sheaf of modules, tensoring on the left with it is exact. -/
private theorem tensorLeft_exact_of_isFlat (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{max v a} (ringSheaf O))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat F) :
    exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max v a, max v a} O).obj F) := by
  have hRight : exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max v a, max v a} O).flip.obj F) := hF
  exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso
    (tensorLeftIsoSheafTensorRight J O F).symm hRight

end SheafLevel

/-! ### Restriction preserves flatness, at a free module universe -/

section Flat

variable (X : RingedSite.{u, v, w}) (U : X.C)
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max v a}]
  [HasWeakSheafify X.J AddCommGrpCat.{max v a}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v a}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{max v a}]

/-- Extension by zero is additive, being a left adjoint. -/
private instance extendByZero_additive : (extendByZero.{max v a} X U).Additive :=
  have : PreservesFiniteColimits (extendByZero.{max v a} X U) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} (extendByZero.{max v a} X U)
  additive_of_preservesFiniteColimits _

/-- **Restriction preserves flatness, at a free module universe.** Restriction to an object of
a ringed site preserves flatness of module sheaves, for objects of the site in `Type u`, morphisms
in `v`, the structure sheaf in `w` and the modules in `max v a`, with no smallness assumption on
the site. -/
@[stacks 0E8J "objects in Type u, morphisms in v, ring sections in w, modules in max v a, \
and no smallness assumption on the site", sga "4 V 1.6.1"]
public theorem isFlat_over
    (F : SheafOfModules.{max v a} (ringSheaf X.O))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat F) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := X.O.over U) (F.over U) := by
  have : HasSheafify X.J AddCommGrpCat.{max v a} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have : HasSheafify (X.J.over U) AddCommGrpCat.{max v a} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have hG : exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, max v a, max v a}
        (X.O.over U)).obj (F.over U)) :=
    @Stacks.SheafOfModules.FlatRestriction.exactFunctor_of_reflecting_extension_exported
      _ _ _ _ _ _
      (extendByZero.{max v a} X U)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max v a, max v a} X.O).obj F)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, max v a, max v a}
        (X.O.over U)).obj (F.over U))
      inferInstance inferInstance
      (tensorLeft_additive (X.J.over U) (X.O.over U) (F.over U))
      (fun S => Stacks.Sites.ExtensionByZero.FreeModuleUniverse.extensionByZero_exact_iff.{a,
        w, v, u} X.J (ringSheaf X.O) U S)
      (tensorLeft_exact_of_isFlat X.J X.O F hF)
      (tensorLeft_preservesFiniteColimits (X.J.over U) (X.O.over U) (F.over U))
      (Functor.isoWhiskerLeft (extendByZero.{max v a} X U)
          (tensorLeftIsoSheafTensorRight X.J X.O F) ≪≫
        restrictionTensorIso.{max v a} X U F ≪≫
        Functor.isoWhiskerRight
          (tensorLeftIsoSheafTensorRight (X.J.over U) (X.O.over U) (F.over U)).symm
          (extendByZero.{max v a} X U))
  change exactFunctor _ _
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, max v a, max v a}
      (X.O.over U)).flip.obj (F.over U))
  exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso
    (tensorLeftIsoSheafTensorRight (X.J.over U) (X.O.over U) (F.over U)) hG

end Flat

end Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse

end
