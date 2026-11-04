module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.FiniteFree
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Conclusion (b) of Tag 0EX3 in positive degree along an affine morphism

`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/TensorComparison.lean` states the
canonicity condition `IsHigherDirectImageTensorMap` of conclusion (b) of [Stacks, Tag 0EX3] and
proves that at most one map satisfies it.

This file gives a map that provably does, in every **positive** degree along an
**affine** morphism of schemes, with quasi-coherent modules. There both sides of conclusion (b)
vanish — by [Stacks, Tag 01XC] for the right-hand side, and because the left-hand side is a
tensor product with a vanishing factor — so the condition holds for every map at all (two
morphisms into a zero object are equal) and any map is invertible. The conclusion is therefore
unconditional in that range, and the canonicity condition is **proved** rather than assumed.

The content of the statement is limited: in positive degree along an affine morphism the two
sheaves of conclusion (b) are both zero, and what is proved is that the tag's assertion is correct
there. It gives `eq_of_isHigherDirectImageTensorMap` a map to apply to, and
`topDirectImageTensorComparisonOfIsIso` an instantiation with every hypothesis discharged. The
degree-zero map, where the statement has content, is
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/TensorComparisonZero.lean`; there the
canonicity condition is still open.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorPullbackObj`: the module
  `F ⊗_{𝒪_X} f^* G`, with its type declared as `X.Modules` so that quasi-coherence is found by
  instance search at the spelling [Stacks, Tag 01XC] is stated over.

## Main results

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isZero_tensorSheaf_of_isZero_left`: a tensor product with a vanishing left factor vanishes.
* `isQuasicoherent_tensorPullbackObj`: `F ⊗_{𝒪_X} f^* G` is quasi-coherent, as an instance.
* `isZero_tensorSheaf_rightDerivedPlus_of_isAffineHom` and
  `isZero_rightDerivedPlus_tensorPullback_of_isAffineHom`: both sides of conclusion (b) vanish in
  positive degree along an affine morphism.
* `isHigherDirectImageTensorMap_of_isAffineHom`: **the canonicity condition holds, for every
  map**, in that range.
* `topDirectImageTensorComparisonPos`: **conclusion (b) of [Stacks, Tag 0EX3] in every positive
  degree along an affine morphism of schemes with quasi-coherent modules**, with no remaining
  hypothesis beyond those.

## Implementation notes

**Spellings, and a universe pitfall.** `SheafOfModules.IsQuasicoherent` applied to the tensor
product resolves over `structureSheafRing
  X.toRingedSpace`, while [Stacks, Tag
01XC] is stated over `X.ringCatSheaf`; the two are definitionally equal and instance search does
not cross between them. Writing the class out in full with the module ascribed to `X.Modules`
does not work either — it elaborates its universes to `0` before unification and reports
`X.Modules` of sort `Type (u+1)` against `SheafOfModules ?m` of sort `Type 1`. What works is a
`tensorPullbackObj` whose *declared return type* is `X.Modules`, after which dot notation finds
the right class; the instance is then supplied by
`AlgebraicGeometry.tensorSheaf_isQuasicoherent` with its own two arguments given as
`inferInstanceAs` at the scheme spelling. No transparency option and no option overrides is used.

**Why no map is named.** In this range the two objects are zero, so there is nothing to pin down:
the isomorphism is `IsZero.iso` of the two vanishing statements, and any other choice equals it.
That is the opposite of the degree-zero situation, where the map is the content and
`higherDirectImageTensorMapZero_comp_directImageZeroIso` is what pins it.

**No tag attribute.** Conclusion (b) of Tag 0EX3 is asserted at the top degree `d` of a
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` and the tag asserts conclusions (a), (b)
and (c) together; what is proved here is restricted to positive degree and to an affine
morphism, hypotheses the tag does not carry. So no Stacks attribute is attached below.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **A tensor product with a vanishing left factor vanishes.** Tensoring with a fixed module on
the right is an additive functor
(`Stacks.AffineProjectionFormula.tensorSheafSectL_additive`), and an additive functor carries a
zero object to a zero object.

The composite is ascribed `SheafOfModules (structureRingSheaf Z) ⥤ SheafOfModules
(structureRingSheaf Z)`, exactly as the additivity instance is. Without the ascription the
codomain elaborates to the `Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf` spelling that
`sheafTensor` carries in its own type, so the `HasZeroMorphisms` argument of
`PreservesZeroMorphisms` is the one at that spelling; the two ring sheaves are definitionally
equal but neither unfolds at the `instances` transparency instance search keys on, and
`preservesZeroMorphisms_of_additive` cannot then reach the additivity instance. -/
theorem isZero_tensorSheaf_of_isZero_left {Z : RingedSpace.{u, u}}
    {A B : SheafOfModules.{u} (structureRingSheaf Z)} (hA : IsZero A) :
    IsZero (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj A).obj B) :=
  Functor.map_isZero
    (Prod.sectL (SheafOfModules.{u} (structureRingSheaf Z)) B ⋙
      Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) :
      SheafOfModules.{u} (structureRingSheaf Z) ⥤ SheafOfModules.{u} (structureRingSheaf Z)) hA

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules)

/-- The module `F ⊗_{𝒪_X} f^* G` appearing on the right of conclusion (b), with its type
*declared* as `X.Modules`. The declaration is the point: at that spelling dot notation finds
`SheafOfModules.IsQuasicoherent` over `X.ringCatSheaf`, which is the spelling [Stacks, Tag 01XC]
is stated over, whereas the tensor product's own type carries the
`structureSheafRing` spelling and instance search does
  not cross between them. -/
@[ega "IV 2.1.5"]
abbrev tensorPullbackObj : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
    ((Scheme.Modules.pullback f).obj G)

/-- **`F ⊗_{𝒪_X} f^* G` is quasi-coherent**, from [Stacks, Tag 01BG] for the pullback and
[Stacks, Tag 01CE] for the tensor product. Stated as an instance at the `X.Modules` spelling so
that the vanishing theorem of [Stacks, Tag 01XC] applies to it. -/
instance isQuasicoherent_tensorPullbackObj [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (tensorPullbackObj f F G).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace F
    ((Scheme.Modules.pullback f).obj G)
    (inferInstanceAs F.IsQuasicoherent)
    (inferInstanceAs ((Scheme.Modules.pullback f).obj G).IsQuasicoherent)

variable [AlgebraicGeometry.IsAffineHom f] [F.IsQuasicoherent] [G.IsQuasicoherent]

omit [SheafOfModules.IsQuasicoherent G] in
/-- **The left-hand side of conclusion (b) vanishes in positive degree along an affine
morphism**: the higher direct image vanishes by [Stacks, Tag 01XC], and a tensor product with a
vanishing factor vanishes. -/
theorem isZero_tensorSheaf_rightDerivedPlus_of_isAffineHom (n : ℕ) (hn : 0 < n) :
    IsZero (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
      (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F)).obj G) :=
  isZero_tensorSheaf_of_isZero_left
    (Stacks.Cohomology.Affine.isZero_rightDerivedPlus_pushforward_of_isAffineHom f F n hn)

/-- **The right-hand side of conclusion (b) vanishes in positive degree along an affine
morphism**: `F ⊗_{𝒪_X} f^* G` is quasi-coherent, so [Stacks, Tag 01XC] applies to it. -/
theorem isZero_rightDerivedPlus_tensorPullback_of_isAffineHom (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
        ((Scheme.Modules.pullback f).obj G))) :=
  Stacks.Cohomology.Affine.isZero_rightDerivedPlus_pushforward_of_isAffineHom f
    (tensorPullbackObj f F G) n hn

/-- **The canonicity condition of [Stacks, Tag 0EX3] (b) holds, for every map**, in positive
degree along an affine morphism with quasi-coherent modules. Both sides of the defining equation
land in the restriction of a zero object, and two morphisms into a zero object are equal. -/
theorem isHigherDirectImageTensorMap_of_isAffineHom (n : ℕ) (hn : 0 < n)
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F)).obj G ⟶
      ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
          ((Scheme.Modules.pullback f).obj G))) :
    IsHigherDirectImageTensorMap f F G n c := fun V _ =>
  (Functor.map_isZero (Scheme.Modules.restrictFunctor V.ι)
    (isZero_rightDerivedPlus_tensorPullback_of_isAffineHom f F G n hn)).eq_of_tgt _ _

/-- **Conclusion (b) of [Stacks, Tag 0EX3] in every positive degree along an affine morphism of
schemes with quasi-coherent modules**, with the canonicity condition discharged and no
hypothesis left over. Both sheaves vanish, so `IsZero.iso` is the isomorphism and its inverse
satisfies the condition because every map does. -/
def topDirectImageTensorComparisonPos (n : ℕ) (hn : 0 < n) :
    { e : ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
            ((Scheme.Modules.pullback f).obj G)) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F)).obj G //
      IsHigherDirectImageTensorMap f F G n e.inv } :=
  haveI : IsIso
      (((isZero_tensorSheaf_rightDerivedPlus_of_isAffineHom f F G n hn).iso
        (isZero_rightDerivedPlus_tensorPullback_of_isAffineHom f F G n hn)).hom) :=
    Iso.isIso_hom _
  topDirectImageTensorComparisonOfIsIso f F G n
    (((isZero_tensorSheaf_rightDerivedPlus_of_isAffineHom f F G n hn).iso
      (isZero_rightDerivedPlus_tensorPullback_of_isAffineHom f F G n hn)).hom)
    (isHigherDirectImageTensorMap_of_isAffineHom f F G n hn _)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
