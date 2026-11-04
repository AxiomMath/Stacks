module

public import StacksFrontier.Deformation.ToposThickening.Basic

/-!
# Two extensions over one first order thickening of ringed topoi

Fix a first order thickening of ringed topoi, two extensions of modules over it, and maps
between their respective quotient and kernel modules. This file packages that standing data
and records the two canonical multiplication maps attached to it.

The four end terms are modules over the direct image of the structure sheaf of the thickened
topos. Their restrictions to the quotient structure sheaf are the end terms of the two Yoneda
extensions. The canonical map from the ideal tensored with each quotient to the corresponding
kernel is `Deformation.ToposThickening.extensionActionMap` applied to that extension, so its
specification is the local multiplication formula of the source.

## Main definitions

* `Deformation.ToposThickening.TwoExtensions`: two extensions over one first order thickening,
  together with morphisms of their quotient and kernel modules.
* `Deformation.ToposThickening.TwoExtensions.firstActionMap` and
  `Deformation.ToposThickening.TwoExtensions.secondActionMap`: the two canonical maps from the
  ideal tensored with a quotient to the corresponding extension kernel.

## Implementation notes

The instance arguments recording that the Grothendieck topologies admit the forgetful sheaf
compositions are placed before the morphism of ringed topoi, because
`AlgebraicGeometry.RingedToposHom` needs them to elaborate its own type.

## References

* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}}
  {Y : RingedTopos.{v', u', w'}}

/-- Two extensions over one first order thickening of ringed topoi, together with morphisms
of their quotient and kernel modules. -/
public structure TwoExtensions
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    (i : RingedToposHom X Y)
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] where
  /-- The square-zero thickening. -/
  thickening : FirstOrderThickening i
  /-- The quotient of the first extension. -/
  F : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
  /-- The kernel of the first extension. -/
  K : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
  /-- The quotient of the second extension. -/
  G : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
  /-- The kernel of the second extension. -/
  L : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
  /-- The first extension as a short exact sequence of modules over the thickened structure
  sheaf. -/
  firstExtension : Abelian.YonedaExtension
    ((SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
    ((SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0
  /-- The second extension as a short exact sequence of modules over the thickened structure
  sheaf. -/
  secondExtension : Abelian.YonedaExtension
    ((SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj G)
    ((SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj L) 0
  /-- The map of quotient modules. -/
  quotientMap : F ⟶ G
  /-- The map of kernel modules. -/
  kernelMap : K ⟶ L

namespace TwoExtensions

variable [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]

/-- The canonical multiplication map from the ideal tensored with the first quotient to the
first kernel, with its local-lift specification. -/
public noncomputable def firstActionMap (D : TwoExtensions i) :=
  extensionActionMap D.thickening D.firstExtension

/-- The canonical multiplication map from the ideal tensored with the second quotient to the
second kernel, with its local-lift specification. -/
public noncomputable def secondActionMap (D : TwoExtensions i) :=
  extensionActionMap D.thickening D.secondExtension

end TwoExtensions

end Deformation.ToposThickening

end
