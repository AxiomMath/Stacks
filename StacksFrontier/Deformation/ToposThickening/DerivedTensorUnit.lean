module

public import StacksFrontier.Deformation.ToposThickening.DerivedSheafTensorExists
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnitOfSize

/-!
# The derived tensor product with the structure sheaf is the identity

Let `(C, O)` be a site with a sheaf of commutative rings. The derived tensor product
`- ⊗_O^L O` of `StacksFrontier/Deformation/ToposThickening/DerivedSheafTensorExists.lean` is the
total left derived functor of the degreewise tensor product `- ⊗_O O`, and that functor is
isomorphic to the identity by the unit law of Tag 06YM. The identity functor is therefore itself
a left derived functor of `- ⊗_O O`, and uniqueness of left derived functors identifies the two.

The point of the file is the *naturality* of the resulting identification: the reduction triangle
of `StacksFrontier/Deformation/ToposThickening/DerivedReductionTriangle.lean` replaces the middle
vertex `K ⊗^L_O O` by `K` one object at a time, through an arbitrary preimage of `K` under the
localization, so the triangle it produces is not natural in `K`. The isomorphism below is a
natural isomorphism of functors, so a triangle built with it is.

## Main definitions

* `Deformation.ComplexLift.tensorRightUnitIso`: the degreewise unit law `- ⊗_O O ≅ 𝟭`, at the
  spelling of the sheaf of rings the lift statements use.
* `Deformation.ComplexLift.identityTensorRightUnitCounit`: the comparison exhibiting the
  identity functor of `D(O)` as a left derived functor of `- ⊗_O O`.
* `Deformation.ComplexLift.derivedTensorRightUnitIso`: **`- ⊗_O^L O ≅ 𝟭`**, as an isomorphism of
  functors on the derived category.

## Main results

* `Deformation.ComplexLift.isLeftDerivedFunctor_identityTensorRightUnitCounit`: the identity
  functor is a left derived functor of the degreewise tensor product with the structure sheaf,
  the comparison being invertible.
* `Deformation.ComplexLift.derivedTensorRightUnitIso_fac`: the identification is compatible with
  the two comparisons, which is what lets it be used inside a computation with the counit of
  `- ⊗_O^L O`.

## References

* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory

universe d v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (O : Sheaf J CommRingCat.{u})

/-- **The degreewise unit law `- ⊗_O O ≅ 𝟭`**, at the spelling
`Deformation.ComplexLift.ringSheafOf` of the underlying sheaf of rings that the lift statements
of Tags 0DIY and 0DIZ are written with.

This is `Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize`, whose module universe is free of
the two site universes; the two spellings of the sheaf of rings are definitionally equal. -/
def tensorRightUnitIso :
    tensorRight O (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) ≅
      𝟭 (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize.{u, v', u'} O

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]

/-- The comparison exhibiting the identity functor of `D(O)` as a left derived functor of the
degreewise tensor product with the structure sheaf: the degreewise unit law, read on complexes
and followed by the localization. It is an isomorphism. -/
def identityTensorRightUnitIso :
    DerivedCategory.Q ⋙ 𝟭
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) ≅
      (tensorRight O
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (Functor.rightUnitor DerivedCategory.Q) ≪≫
    (Functor.leftUnitor DerivedCategory.Q).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)).symm DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (tensorRightUnitIso O) (ComplexShape.up ℤ)).symm
      DerivedCategory.Q

/-- The comparison above, as a natural transformation. -/
abbrev identityTensorRightUnitCounit :
    DerivedCategory.Q ⋙ 𝟭
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) ⟶
      (tensorRight O
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (identityTensorRightUnitIso.{d} O).hom

/-- **The identity functor of `D(O)` is a left derived functor of `- ⊗_O O`.** The comparison is
an isomorphism, the degreewise tensor product with the structure sheaf being isomorphic to the
identity, so nothing has to be derived. -/
instance isLeftDerivedFunctor_identityTensorRightUnitCounit :
    (𝟭 (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))).IsLeftDerivedFunctor
      (identityTensorRightUnitCounit.{d} O)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ (identityTensorRightUnitIso.{d} O)

/-- **The derived tensor product with the structure sheaf is the identity:** `- ⊗_O^L O ≅ 𝟭`, as
an isomorphism of functors on `D(O)`.

Both sides are total left derived functors of the degreewise tensor product with `O`, so this is
uniqueness of left derived functors. Unlike
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso`, which is built one object at a time
through an arbitrary preimage under the localization, this is an isomorphism of functors. -/
def derivedTensorRightUnitIso :
    derivedTensorRight.{d} (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :=
  Functor.leftDerivedUnique _ _
    (derivedTensorRightCounit.{d} (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (identityTensorRightUnitCounit.{d} O)
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))

/-- **The identification is compatible with the two comparisons.** Whiskering it with the
localization and composing with the comparison of the identity functor gives back the counit of
`- ⊗_O^L O`; this is the factorization property of the isomorphism of left derived functors. -/
theorem derivedTensorRightUnitIso_fac :
    Functor.whiskerLeft DerivedCategory.Q (derivedTensorRightUnitIso.{d} O).hom ≫
        identityTensorRightUnitCounit.{d} O =
      derivedTensorRightCounit.{d} (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
        := by
  refine Eq.trans (Functor.leftDerivedNatTrans_fac _ _
    (derivedTensorRightCounit.{d} (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (identityTensorRightUnitCounit.{d} O)
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)) (𝟙 _)) ?_
  exact Category.comp_id _

end Deformation.ComplexLift

end
