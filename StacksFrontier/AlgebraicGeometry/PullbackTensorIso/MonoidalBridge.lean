module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal
public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic

/-!
# The pullback comparison of Tag 01CD at the two monoidal spellings

Sheaves of modules on a scheme carry two spellings of one monoidal structure:
`Stacks.SheafInternalHom.monoidalCategory`, obtained by localizing the sectionwise monoidal
structure on presheaves of modules along sheafification, and
`SheafOfModules.monoidalCategorySheafTensor`, whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor` on the nose, obtained from the localized structure by
`CategoryTheory.MonoidalCategory.reseat`. This file identifies the ingredients of the two
spellings, among them the tensorator `Stacks.ProjBundleInverseBaseChange.pullbackTensorIso` and
the unit comparison `Stacks.ProjBundleInverseBaseChange.pullbackUnitMonoidalIso` of the pullback
with those of `Stacks.PullbackSheafTensor.monoidal`. Each identification holds by `rfl`, except
that the tensor product sheaf ends with the sealed sheafification
`Stacks.SheafOfModules.Tensor.sheafification`, which `AlgebraicGeometry.SheafOfModules.tensorIso`
reaches along its defining equation and `SheafOfModules.sheafTensorIso` along
`Stacks.SheafOfModules.Tensor.sheafTensorObjIso`.

## Main results

* `Stacks.ProjBundleInverseBaseChange.monoidalCategory_eq_sheafOfModulesMonoidalCategory`: **the
  monoidal structure `Stacks.TensorPowers.TensorInverse.invIso` is read at is the one
  `SheafOfModules.monoidalCategorySheafTensor` re-seats**, on the nose.
* `Stacks.ProjBundleInverseBaseChange.pullbackFunctor_eq`: the scheme-level and ringed-space
  pullback functors on modules are the same functor.
* `Stacks.ProjBundleInverseBaseChange.tensorIso_eq` and `unitIso_eq`: the comparisons
  `F ⊗ G ≅ tensorSheaf F G` and `𝟙_ ≅ 𝒪` of the localized structure with the tensor product
  sheaf are the components of the re-seating isomorphism, `SheafOfModules.sheafTensorIso`
  followed by the inverse of `Stacks.SheafOfModules.Tensor.sheafTensorObjIso`, and its unit.
* `Stacks.ProjBundleInverseBaseChange.pullbackTensorSchemeIso_eq` and `pullbackUnitIso_eq`: Tag
  01CD and the comparison of structure sheaves at the two spellings.
* `Stacks.ProjBundleInverseBaseChange.pullbackTensorIso_hom_eq` and
  `pullbackUnitMonoidalIso_hom_eq`: **the tensorator and the unit comparison of the localized
  spelling are the ringed-space ones conjugated by the re-seating isomorphism.**

## Implementation notes

`AlgebraicGeometry.SheafOfModules.tensorIso` passes from Mathlib's sheafification to the sealed
one along `eqToIso` of `Stacks.SheafOfModules.Tensor.sheafification_def`, and
`Stacks.SheafOfModules.Tensor.sheafTensorObjIso` along
`Stacks.SheafOfModules.Tensor.sheafificationIso`, the comparison of two left adjoints;
`Stacks.SheafOfModules.Tensor.sheafificationIso_eq_eqToIso` identifies the two, after which
`tensorIso_eq` holds by `rfl`.

The three identifications of *isomorphisms* are `CategoryTheory.Iso.ext` of a tactic `rfl`
rather than a term `rfl`: the two sides are built from different composites whose equality the
elaborator checks only at default transparency, and the `inv` fields are not exposed, so a term
`rfl` is rejected with a metavariable type mismatch while `by rfl` succeeds.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)

universe u

namespace Stacks.ProjBundleInverseBaseChange

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

section SealedSheafification

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The inverse of `Stacks.SheafOfModules.Tensor.sheafTensorObjIso` is the component of the
isomorphism of the defining equation `Stacks.SheafOfModules.Tensor.sheafification_def`. -/
private theorem sheafTensorObjIso_inv_eq
    (F G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (Stacks.SheafOfModules.Tensor.sheafTensorObjIso R F G).inv =
      (eqToIso (Stacks.SheafOfModules.Tensor.sheafification_def R).symm).hom.app _ := by
  rw [← Stacks.SheafOfModules.Tensor.sheafificationIso_eq_eqToIso]
  rfl

end SealedSheafification

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- The sheaf of rings the tensor powers of Tag 01CU are indexed by is the structure sheaf of
the underlying ringed space. -/
theorem structureSheaf_eq_structureRingSheaf :
    structureSheaf X.presheaf (isSheaf_structureRingPresheaf X) =
      Stacks.RingedSpace.structureRingSheaf X.toRingedSpace := rfl

/-- **The monoidal structure `Stacks.TensorPowers.TensorInverse.invIso` is read at is the one
`SheafOfModules.monoidalCategorySheafTensor` re-seats.** Both localize the sectionwise monoidal
structure on presheaves of modules along sheafification, with the same unit comparison. -/
theorem monoidalCategory_eq_sheafOfModulesMonoidalCategory :
    Stacks.SheafInternalHom.monoidalCategory X.presheaf (isSheaf_structureRingPresheaf X) =
      _root_.SheafOfModules.monoidalCategory X.sheaf := rfl

/-- The scheme-level pullback of modules is the ringed-space one. -/
theorem pullbackFunctor_eq :
    pullbackFunctor g = Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom := rfl

/-- **The comparison of the monoidal tensor product with the tensor product sheaf is the
re-seating isomorphism**: `SheafOfModules.sheafTensorIso`, into Mathlib's sheafification of the
presheaf tensor product, followed by the inverse of
`Stacks.SheafOfModules.Tensor.sheafTensorObjIso`. -/
theorem tensorIso_eq (F G : Mods X) :
    AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
        (isSheaf_structureRingPresheaf X) F G =
      SheafOfModules.sheafTensorIso X.sheaf F G ≪≫
        (Stacks.SheafOfModules.Tensor.sheafTensorObjIso X.sheaf F G).symm :=
  Iso.ext (Eq.trans (by rfl)
    (congrArg ((SheafOfModules.sheafTensorIso X.sheaf F G).hom ≫ ·)
      (sheafTensorObjIso_inv_eq X.sheaf F G).symm))

/-- **The comparison of the monoidal unit with the structure sheaf is the unit of the
re-seating.** -/
theorem unitIso_eq :
    AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (isSheaf_structureRingPresheaf X) =
      SheafOfModules.unitIso X.sheaf := rfl

/-- **Tag 01CD at the two spellings**: the comparison the tensorator of the localized structure
is built from is the oplax tensorator of `Stacks.PullbackSheafTensor.monoidal`. -/
theorem pullbackTensorSchemeIso_eq (F G : Mods X) :
    Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso g F G =
      Stacks.PullbackSheafTensor.sheafTensorComparisonIso g.toLRSHom.toShHom F G :=
  Iso.ext (by rfl)

/-- **The comparison of structure sheaves at the two spellings.** -/
theorem pullbackUnitIso_eq :
    Scheme.Modules.pullbackUnitIso g =
      Stacks.PullbackSheafTensor.sheafTensorUnitIso g.toLRSHom.toShHom :=
  Iso.ext (by rfl)

/-- **The tensorator of the localized spelling is the ringed-space comparison conjugated by the
re-seating isomorphism**, whose components are `SheafOfModules.sheafTensorIso` followed by the
inverse of `Stacks.SheafOfModules.Tensor.sheafTensorObjIso`. -/
theorem pullbackTensorIso_hom_eq (F G : Mods X) :
    (pullbackTensorIso g F G).hom =
      (pullbackFunctor g).map ((SheafOfModules.sheafTensorIso X.sheaf F G).hom ≫
          (Stacks.SheafOfModules.Tensor.sheafTensorObjIso X.sheaf F G).inv) ≫
        Stacks.PullbackSheafTensor.sheafTensorComparison g.toLRSHom.toShHom F G ≫
          (Stacks.SheafOfModules.Tensor.sheafTensorObjIso X'.sheaf ((pullbackFunctor g).obj F)
              ((pullbackFunctor g).obj G)).hom ≫
            (SheafOfModules.sheafTensorIso X'.sheaf ((pullbackFunctor g).obj F)
              ((pullbackFunctor g).obj G)).inv := by
  simp only [pullbackTensorIso, tensorIso_eq, pullbackTensorSchemeIso_eq]
  rfl

/-- **The unit comparison of the localized spelling is the ringed-space one conjugated by the
unit of the re-seating.** -/
theorem pullbackUnitMonoidalIso_hom_eq :
    (pullbackUnitMonoidalIso g).hom =
      (pullbackFunctor g).map (SheafOfModules.unitIso X.sheaf).hom ≫
        (Stacks.PullbackSheafTensor.sheafTensorUnitIso g.toLRSHom.toShHom).hom ≫
          (SheafOfModules.unitIso X'.sheaf).inv := by
  simp only [pullbackUnitMonoidalIso, unitIso_eq, pullbackUnitIso_eq]
  rfl

end Stacks.ProjBundleInverseBaseChange

end
