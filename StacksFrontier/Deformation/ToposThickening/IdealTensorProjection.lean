module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.SecondVariableOnSheaves
public import StacksFrontier.Deformation.ToposThickening.ExtensionRestrictTensor

/-!
# The projection formula for the ideal of a thickening

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site and let `I₀` be a sheaf
of `O₀`-modules, such as the ideal sheaf of a square-zero thickening. Writing `I = I₀|_O` for its
restriction, the *projection formula*

`(O₀ ⊗_O M) ⊗_{O₀} I₀ ≅ M ⊗_O I`  (as sheaves of `O`-modules, naturally in `M`)

identifies the two ways of forming the ideal part of a base change. This file states it as an
isomorphism of functors `Mod(O) ⥤ Mod(O)`, in both tensor orders.

## Main definitions

* `Deformation.ComplexLift.idealLeftTensorIso`: the projection formula with the ideal on the
  left, `I ⊗_O - ≅ ((O₀ ⊗_O -) ⊗_{O₀} I₀)|_O`.
* `Deformation.ComplexLift.idealTensorRightIso`: the same with the ideal on the right,
  `- ⊗_O I ≅ ((O₀ ⊗_O -) ⊗_{O₀} I₀)|_O`.

## References

* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))

/-- The restriction `I = I₀|_O` of the sheaf of `O₀`-modules `I₀` to a sheaf of `O`-modules along
`f`. -/
abbrev restrictIdeal : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  (SheafOfModules.restrictScalars (ringSheafMapOf J f)).obj I₀

/-- **The projection formula, with the ideal in the left-hand tensor slot.** The isomorphism of
functors `Mod(O) ⥤ Mod(O)`

`I ⊗_O - ≅ ((O₀ ⊗_O -) ⊗_{O₀} I₀)|_O`.

Its component at `M` is the sheafified sectionwise cancellation
`I₀ ⊗_{O₀} (O₀ ⊗_O M) ≅ I ⊗_O M`. -/
def idealLeftTensorIso :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj (restrictIdeal f I₀) ≅
      extensionOfScalars f ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).obj I₀ ⋙
          SheafOfModules.restrictScalars (ringSheafMapOf J f) :=
  NatIso.ofComponents
    (fun M ↦ (Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso f M).app I₀)
    (fun {_ _} γ ↦
      Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso_naturality_snd f γ I₀)

/-- **The projection formula, with the ideal in the right-hand tensor slot.** The isomorphism of
functors `Mod(O) ⥤ Mod(O)`

`- ⊗_O I ≅ ((O₀ ⊗_O -) ⊗_{O₀} I₀)|_O`,

which is `Deformation.ComplexLift.idealLeftTensorIso` between the braidings of the tensor
product on the two sides. -/
def idealTensorRightIso :
    tensorRight O (restrictIdeal f I₀) ≅
      extensionOfScalars f ⋙ tensorRight O₀ I₀ ⋙
        SheafOfModules.restrictScalars (ringSheafMapOf J f) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u', v', u} O).app
      (restrictIdeal f I₀)).symm ≪≫
    idealLeftTensorIso f I₀ ≪≫
    Functor.isoWhiskerLeft (extensionOfScalars f)
      (Functor.isoWhiskerRight
        ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u', v', u} O₀).app I₀)
        (SheafOfModules.restrictScalars (ringSheafMapOf J f)))

end Deformation.ComplexLift

end
