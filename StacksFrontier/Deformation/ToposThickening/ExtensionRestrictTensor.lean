module

public import StacksFrontier.AlgebraicGeometry.MeromorphicSectionsTensor.Sheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Deformation.ToposThickening.DerivedSheafTensorExists

/-!
# Restriction of scalars of an extension of scalars is a tensor product

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site. Extension of scalars
along `f` carries a sheaf of `O`-modules `M` to `O₀ ⊗_O M`, a sheaf of `O₀`-modules; reading that
again as a sheaf of `O`-modules along `f` gives the tensor product of `M` with `O₀` itself read as
a sheaf of `O`-modules. This holds as an isomorphism of functors `Mod(O) ⥤ Mod(O)`, in both
tensor orders:

`(O₀ ⊗_O M)|_O ≅ O₀|_O ⊗_O M ≅ M ⊗_O O₀|_O`.

## Main definitions

* `Deformation.ComplexLift.restrictUnitOf`: `O₀` read as a sheaf of `O`-modules along `f`.
* `Deformation.ComplexLift.restrictExtensionIsoLeftTensor`: the isomorphism
  `extensionOfScalars f ⋙ restrictScalars f ≅ O₀|_O ⊗_O -`.
* `Deformation.ComplexLift.restrictExtensionIsoTensorRight`: the isomorphism
  `extensionOfScalars f ⋙ restrictScalars f ≅ - ⊗_O O₀|_O`, with the fixed factor on the right.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
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

/-- `O₀`, read as a sheaf of `O`-modules by restriction of scalars along `f`. -/
abbrev restrictUnitOf : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  (SheafOfModules.restrictScalars (ringSheafMapOf J f)).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O₀))

/-- Restriction of scalars of an extension of scalars is the left tensor product with `O₀`: the
isomorphism of functors `Mod(O) ⥤ Mod(O)`

`(O₀ ⊗_O -)|_O ≅ O₀|_O ⊗_O -`

whose component at `M` is the identity on the common underlying abelian sheaf, the
sheafification of `U ↦ O₀(U) ⊗_{O(U)} M(U)`. -/
def restrictExtensionIsoLeftTensor :
    extensionOfScalars f ⋙ SheafOfModules.restrictScalars (ringSheafMapOf J f) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj (restrictUnitOf f) :=
  NatIso.ofComponents
    (fun M ↦ (Stacks.SheafOfModules.RestrictScalarsSheafification.sheafificationRestrictScalarsIso
      (ringSheafMapOf J f)
      ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj M.val)).symm)
    fun _ ↦ SheafOfModules.Hom.ext <| PresheafOfModules.hom_ext fun _ ↦
      ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl

/-- Restriction of scalars of an extension of scalars is the tensor product with `O₀` on the
right: the isomorphism of functors `Mod(O) ⥤ Mod(O)`

`(O₀ ⊗_O -)|_O ≅ - ⊗_O O₀|_O`,

which is `Deformation.ComplexLift.restrictExtensionIsoLeftTensor` followed by the braiding of
the tensor product. -/
def restrictExtensionIsoTensorRight :
    extensionOfScalars f ⋙ SheafOfModules.restrictScalars (ringSheafMapOf J f) ≅
      tensorRight O (restrictUnitOf f) :=
  restrictExtensionIsoLeftTensor f ≪≫
    (Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u', v', u} O).app (restrictUnitOf f)

end Deformation.ComplexLift

end
