module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionFac

/-!
# A derived tensor product of the ringed site attached to a sheaf of commutative rings

The reduction triangle a `Deformation.ComplexLift.DerivedReduction` transports is formed with a
`Stacks.SheafOfModules.DerivedTensorProduct` on the ringed site
`Deformation.ComplexLift.ringedSiteOf J O`. This file records the one the library constructs,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, read at that ringed site.

## Main definitions

* `Deformation.ComplexLift.derivedTensorProductRingedSiteOf`: **Stacks 06YU** at
  `Deformation.ComplexLift.ringedSiteOf`, the constructed derived tensor product.

## Main results

* `Deformation.ComplexLift.nonempty_derivedTensorProductRingedSiteOf`: such a datum exists.

## Implementation notes

The construction of Stacks 06YU in the library is stated for an
`AlgebraicGeometry.RingedSite.{c, u, u}`: the objects of the site live in a universe of their own,
while its morphisms and the sections of its structure sheaf and of its modules share one universe.
So the site here is a category `C : Type u'` with morphisms in `Type u`, the universe of the
sections of `O`. The derived-category universe stays independent of both.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe d u u'

namespace Deformation.ComplexLift

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules

variable {C : Type u'} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (O : Sheaf J CommRingCat.{u})
variable [HasDerivedCategory.{d} (Modules.{u', u, u} (ringedSiteOf J O))]

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', u, u, u, u} (ringedSiteOf J O).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', u, u, u, u}
    (ringedSiteOf J O).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u', u, u} (ringedSiteOf J O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (ringedSiteOf J O).O) (ComplexShape.up ℤ)]

/-- **The derived tensor product of the ringed site `(C, O)`**: the one constructed by Stacks 06YU,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, read at
`Deformation.ComplexLift.ringedSiteOf`. -/
def derivedTensorProductRingedSiteOf : DerivedTensorProduct.{u', u, u, d} (ringedSiteOf J O) :=
  canonicalDerivedTensorProduct.{u', u, d} (ringedSiteOf J O)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **A derived tensor product of the ringed site `(C, O)` exists**, at an independent
derived-category universe. This is `Stacks.SheafOfModules.exists_derivedTensorProduct` read at
`Deformation.ComplexLift.ringedSiteOf`, so the choice of such a datum that a reduction triangle
is formed with is never vacuous. -/
theorem nonempty_derivedTensorProductRingedSiteOf :
    Nonempty (DerivedTensorProduct.{u', u, u, d} (ringedSiteOf J O)) :=
  exists_derivedTensorProduct.{u', u, d} (ringedSiteOf J O)

end Deformation.ComplexLift

end
