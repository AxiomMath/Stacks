module

public import StacksFrontier.Deformation.ToposThickening.DerivedRestrictionTensorComparison
public import StacksFrontier.Deformation.ToposThickening.DerivedSheafTensorLeftDerived

/-!
# Two derived tensor products on a ringed site agree

The derived tensor product `- ⊗^L_O M[0]` of a ringed site, in the form
`Stacks.SheafOfModules.DerivedTensorProduct`, and the derived tensor product
`Deformation.ComplexLift.derivedTensorRight` built from flat resolutions are both total left
derived functors of the degreewise tensor product `- ⊗_O M`, so they are canonically isomorphic.
This file records that isomorphism.

The two live over two spellings of one category of sheaves of modules —
`AlgebraicGeometry.RingedSite.Modules` of `Deformation.ComplexLift.ringedSiteOf`, and
`SheafOfModules (Deformation.ComplexLift.Stacks.SheafOfModules.Tensor.ringSheaf O)` — which are
equal by `Deformation.ComplexLift.modules_ringedSiteOf`.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.singleTensorIsoOfLeftDerived`: a
  `DerivedTensorProduct`'s partial functor `- ⊗^L_O M[0]` is isomorphic to any total left
  derived functor of `- ⊗_O M`.
* `Deformation.ComplexLift.hasDerivedCategoryRingSheafOf`: the derived category of
  `Modules (ringedSiteOf J O)`, as a derived category of the equal category
  `SheafOfModules (ringSheaf O)`.
* `Deformation.ComplexLift.singleTensorIsoDerivedTensorRight`: the isomorphism
  `- ⊗^L_O M[0] ≅ - ⊗_O^L M`, the first spelled with the ringed site's derived tensor product
  and the second with flat resolutions.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe d v' u u'

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u', v', u}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u', v', u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (Modules.{u', v', u} X)]

/-- Any functor `G` on the derived category exhibited, by a comparison `γ`, as a total left
derived functor of the degreewise tensor product with `M` is isomorphic to the partial functor
`- ⊗^L_O M[0]` of a derived tensor product of the ringed site. -/
def singleTensorIsoOfLeftDerived (T : DerivedTensorProduct.{u', v', u, d} X)
    (M : Modules.{u', v', u} X)
    (G : DerivedCategory (Modules.{u', v', u} X) ⥤ DerivedCategory (Modules.{u', v', u} X))
    (γ : DerivedCategory.Q ⋙ G ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj M).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hG : G.IsLeftDerivedFunctor γ
      (HomologicalComplex.quasiIso (Modules.{u', v', u} X) (ComplexShape.up ℤ))) :
    T.tensor.flip.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Modules.{u', v', u} X) 0).obj M)) ≅ G :=
  haveI := hG
  haveI := T.isLeftDerivedFunctor_singleTensorComparison M
  Functor.leftDerivedUnique _ _ (T.singleTensorComparison M) γ
    (HomologicalComplex.quasiIso (Modules.{u', v', u} X) (ComplexShape.up ℤ))

end Stacks.SheafOfModules.DerivedTensorProduct

namespace Deformation.ComplexLift

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}
variable [HasDerivedCategory.{d} (Modules.{u', v', u} (ringedSiteOf J O))]

/-- The derived category of `Modules (ringedSiteOf J O)`, as a derived category of
`SheafOfModules (ringSheaf O)`; the two categories are equal by
`Deformation.ComplexLift.modules_ringedSiteOf`. -/
abbrev hasDerivedCategoryRingSheafOf :
    HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  inferInstanceAs (HasDerivedCategory.{d} (Modules.{u', v', u} (ringedSiteOf J O)))

attribute [local instance] hasDerivedCategoryRingSheafOf

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} (ringedSiteOf J O).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u}
    (ringedSiteOf J O).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u', v', u} (ringedSiteOf J O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (ringedSiteOf J O).O) (ComplexShape.up ℤ)]

/-- The partial functor `- ⊗^L_O M[0]` of a derived tensor product of the ringed site `(C, O)` is
isomorphic to the derived tensor product `- ⊗_O^L M` built from flat resolutions. -/
def singleTensorIsoDerivedTensorRight
    (T : DerivedTensorProduct.{u', v', u, d} (ringedSiteOf J O))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    T.tensor.flip.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor
          (Modules.{u', v', u} (ringedSiteOf J O)) 0).obj M)) ≅
      derivedTensorRight.{d} M :=
  T.singleTensorIsoOfLeftDerived M (derivedTensorRight.{d} M)
    (derivedTensorRightCounit.{d} M)
    (isLeftDerivedFunctor_derivedTensorRightCounit.{d} M)

end Deformation.ComplexLift

end
