module

public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.InverseSystemsOnASpace

/-!
# The derived pullback of the structure sheaf

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. The structure sheaf `𝒪_Y` is a
flat `𝒪_Y`-module, so the complex `𝒪_Y[0]` is K-flat and the derived pullback `Lf^*(𝒪_Y[0])` is
the degreewise pullback `(f^*𝒪_Y)[0]`; composing with the ordinary identification
`f^*𝒪_Y ≅ 𝒪_X` of [Stacks, Tag 01CD] gives the unit comparison

`ν : Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`.

## Main definitions

* `derivedPullbackSingleUnitIso`: the identification `Lf^*(𝒪_Y[0]) ≅ (f^*𝒪_Y)[0]`.
* `derivedPullbackUnitIso`: the comparison `ν`.

## Main results

* `isFlat_unit`: the structure sheaf of a ringed space is a flat module over itself.
* `derivedPullbackUnitIso_hom`: the factorisation of `ν` through `(f^*𝒪_Y)[0]`.
* `derivedPullbackSingleUnitIso_inv_comp_derivedPullbackUnitIso_hom`: read through the
  identification of `Lf^*(𝒪_Y[0])` with `(f^*𝒪_Y)[0]`, the comparison `ν` is the degree-zero
  image of the ordinary comparison `f^*𝒪_Y ≅ 𝒪_X`.

## Implementation notes

*The sheaf of rings is spelled `structureSheafRing`.* Three names for it
are in circulation: that one, over which `f^*` and the derived pullback are stated;
`Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf`, over which flatness is stated; and
`Stacks.RingedSpace.structureRingSheaf`, over which the ordinary comparison of
[Stacks, Tag 01CD] is restated. All three are the same expression
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Y.sheaf`, by
`StacksDraft.KFlat.ringSheaf_eq` and `Stacks.RingedSpace.structureRingSheaf_eq_ringSheaf`, both
of which are `rfl`, but they carry different `Category` and `Abelian` instance terms and
typeclass synthesis does not unfold a `def` to identify them. The first is chosen because
`derivedPullbackSingleIso` and `modulePullbackObjUnitIso`, the two ingredients, are both stated
in it; the third is then never met, and the second only as the implicit argument of flatness.

*Flatness of the unit is imported, not reproved.*
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit` is stated for a ringed site, and
`isFlat_unit` below is that theorem at the ringed site of the opens of a ringed space.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.SpaceInverseSystems (ringedSiteOfSpace)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Cohomology.DerivedPullbackUnit

section Unit

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The structure sheaf of a ringed space is flat over itself**: tensoring with it is the
identity functor of `Mod(𝒪_Z)`, which is exact. This is
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit` at the ringed site of the opens of
`Z`. -/
theorem isFlat_unit :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.sheaf)
      (_root_.SheafOfModules.unit (structureSheafRing Z)) :=
  Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := ringedSiteOfSpace Z)

end Unit

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The identification `Lf^*(𝒪_Y[0]) ≅ (f^*𝒪_Y)[0]`: the complex `𝒪_Y[0]` is K-flat because
`𝒪_Y` is flat, so the derived pullback is computed by the degreewise one. -/
abbrev derivedPullbackSingleUnitIso :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y)) 0).obj
          (_root_.SheafOfModules.unit (structureSheafRing Y))) ≅
      (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj
        ((modulePullback f).obj (_root_.SheafOfModules.unit (structureSheafRing Y))) :=
  Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso f
    (_root_.SheafOfModules.unit (structureSheafRing Y)) (isFlat_unit Y)

/-- **The unit comparison `ν : Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`** of the derived pullback along a
morphism of ringed spaces: the identification of `Lf^*(𝒪_Y[0])` with the degreewise pullback
`(f^*𝒪_Y)[0]`, followed by the degree-zero image of the ordinary comparison
`f^*𝒪_Y ≅ 𝒪_X`. -/
def derivedPullbackUnitIso :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y)) 0).obj
          (_root_.SheafOfModules.unit (structureSheafRing Y))) ≅
      (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj
        (_root_.SheafOfModules.unit (structureSheafRing X)) :=
  derivedPullbackSingleUnitIso f ≪≫
    (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).mapIso
      (modulePullbackObjUnitIso f)

/-- The factorisation of `ν` through the degreewise pullback, in the forward direction. -/
theorem derivedPullbackUnitIso_hom :
    (derivedPullbackUnitIso f).hom =
      (derivedPullbackSingleUnitIso f).hom ≫
        (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).map
          (modulePullbackObjUnitIso f).hom :=
  rfl

/-- **`ν` on representatives is the degree-zero comparison `f^*𝒪_Y ≅ 𝒪_X`.** Read through the
identification of `Lf^*(𝒪_Y[0])` with `(f^*𝒪_Y)[0]`, the unit comparison of the derived
pullback is the image under `(-)[0]` of the ordinary unit comparison of [Stacks, Tag 01CD];
in particular it adds no data to it. -/
theorem derivedPullbackSingleUnitIso_inv_comp_derivedPullbackUnitIso_hom :
    (derivedPullbackSingleUnitIso f).inv ≫ (derivedPullbackUnitIso f).hom =
      (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).map
        (modulePullbackObjUnitIso f).hom := by
  rw [derivedPullbackUnitIso_hom, Iso.inv_hom_id_assoc]

end Stacks.Cohomology.DerivedPullbackUnit

end
