module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorPullbackFunctors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedGoodResolutionDataConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodAcyclicDifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoMultiplicative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived tensor product with a differential graded bimodule

Let `(C, O)` be a ringed site, let `𝒜` and `𝒜'` be sheaves of differential graded `O`-algebras
and let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule. The functor
`K(Mod(𝒜, d)) ⟶ K(Mod(𝒜', d))`, `ℳ ↦ ℳ ⊗_𝒜 𝒩` of Tag 0FTE (along the identity of `(C, O)`),
followed by the localization `K(Mod(𝒜', d)) ⟶ D(𝒜', d)`, has a left derived extension
`D(𝒜, d) ⟶ D(𝒜', d)` (Tag 0FTF), whose value on a flat and K-flat module `𝒫` is `𝒫 ⊗_𝒜 𝒩`.
This functor is **the derived tensor product** `- ⊗^𝐋_𝒜 𝒩` of
[Stacks, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG) (1); the tag is registered on
`SheafOfModules.DifferentialGradedModule.derivedTensorProductTopos`, the functor of Tag 0FTF at the
identity morphism of a ringed topos, which is isomorphic to it compatibly with the comparison maps
(`SheafOfModules.DifferentialGradedModule.derivedTensorProductToposIso`).

## Main definitions

* `SheafOfModules.DifferentialGradedModule.tensorExactnessData`: the tensor product with `𝒩`
  commutes with cones (Tag 0FTE) and carries a flat, K-flat and acyclic module to an acyclic one
  (Tag 0FSI (1)).
* `SheafOfModules.DifferentialGradedModule.derivedTensorProduct`: **the derived tensor product
  `- ⊗^𝐋_𝒜 𝒩 : D(𝒜, d) ⥤ D(𝒜', d)`.**
* `SheafOfModules.DifferentialGradedModule.derivedTensorProductCounit`: its comparison map
  `ℳ ⊗^𝐋_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩`.
* `SheafOfModules.DifferentialGradedModule.derivedTensorProductObjIso`: its value at a flat and
  K-flat module `𝒫` is `𝒫 ⊗_𝒜 𝒩`.
* `SheafOfModules.DifferentialGradedModule.derivedTensorProductIsoOfIsLeftDerivedFunctor`: every
  left derived functor of `ℳ ↦ ℳ ⊗_𝒜 𝒩` followed by the localization is the derived tensor
  product.

## Main results

* `SheafOfModules.DifferentialGradedModule.isLeftDerivedFunctor_derivedTensorProduct`: the
  derived tensor product with its comparison map is the left derived functor of `ℳ ↦ ℳ ⊗_𝒜 𝒩`
  followed by the localization.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedTensorProductCounit_app`: the comparison
  map is invertible at a flat and K-flat module, in particular at a good one (Tag 0FSA).

## Implementation notes

The modules are resolved by the flat and K-flat ones (`GoodResolutionData.flat`, Tag 0FSH), and
these are all that the value clause needs: a good module in the sense of Tag 0FSA is in
particular flat and K-flat, so the value on good modules asserted by Tag 0FTF is a special case.
The sites, the morphisms and the coefficients live in one universe `u`, which is where the
derived categories `D(𝒜, d)` of Tag 0FT5 are localizations with a calculus of fractions and where
the relative tensor product of differential graded modules is constructed.

## References

* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A A' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (N : DifferentialGradedBimodule.{u, u, u} A A')

/-- The tensor product `ℳ ↦ ℳ ⊗_𝒜 𝒩` with the differential graded `(𝒜, 𝒜')`-bimodule `𝒩`, as a
tensor product functor. -/
@[sga "4 IV 12.12" "more general"]
abbrev tensorData : TensorFunctorData.{u, u, u, u, u} A A' N :=
  RelativeTensor.tensorFunctorDataDgTensorRight
    (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)))
    (B := (A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) N

/-- The resolving class computing `- ⊗^𝐋_𝒜 𝒩`: right differential graded `𝒜`-modules which are
flat as graded modules and K-flat (Tag 0FSH). -/
abbrev tensorGood : GoodResolutionData.{u, u, u, u, u} A :=
  GoodResolutionData.flat (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)))

/-- **The tensor product with a bimodule is exact on flat K-flat modules**: it commutes with
cones (Tag 0FTE), and it carries a flat, K-flat and acyclic module to an acyclic one
(Tag 0FSI (1)). -/
def tensorExactnessData :
    PullbackTensorExactnessData (idPullbackData.{u, u, u} (A := A)) (tensorData N)
      (tensorGood (A := A)) :=
  PullbackTensorExactnessData.ofAcyclicPullbackTensor _ _ _ fun hQ hQac =>
    acyclic_of_isTensorProduct_of_isKFlat_of_acyclic hQ.2 hQac ((tensorData N).isTensorProduct _)

/-- **The derived tensor product** `- ⊗^𝐋_𝒜 𝒩 : D(𝒜, d) ⥤ D(𝒜', d)` with a differential graded
`(𝒜, 𝒜')`-bimodule `𝒩` on a ringed site: the left derived extension of `ℳ ↦ ℳ ⊗_𝒜 𝒩` followed
by the localization `K(Mod(𝒜', d)) ⥤ D(𝒜', d)` (Tag 0FTF). It is the left derived functor of
that composite (`isLeftDerivedFunctor_derivedTensorProduct`), and its value on a flat and K-flat
module `𝒫`, in particular on a good one, is `𝒫 ⊗_𝒜 𝒩` (`derivedTensorProductObjIso`). -/
def derivedTensorProduct : derivedCategory.{u, u, u} A ⥤ derivedCategory.{u, u, u} A' :=
  derivedTensor (tensorExactnessData N)

/-- **The derived tensor product is the derived pullback-tensor functor at the identity.** It is,
by definition, the left derived extension `derivedPullbackTensor` of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` — the
construction of the proof of Tag 0FTF — for the identity morphism of ringed sites, along which a
module is its own pullback (`idPullbackData`), with the exactness of the tensor product
constructed (`tensorExactnessData`). -/
theorem derivedTensorProduct_eq_derivedPullbackTensor :
    derivedTensorProduct N =
      derivedPullbackTensor idPullbackDataHomotopyExtension (tensorExactnessData N) :=
  rfl

/-- The comparison `ℳ ⊗^𝐋_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩` of the derived tensor product with the tensor
product, natural in the object of `K(Mod(𝒜, d))`. -/
def derivedTensorProductCounit :
    toDerivedCategory.{u, u, u} A ⋙ derivedTensorProduct N ⟶
      HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N) ⋙
        toDerivedCategory.{u, u, u} A' :=
  derivedPullbackTensorCounit idPullbackDataHomotopyExtension (tensorExactnessData N)

/-- The derived tensor product, with its comparison map, is the left derived functor of the
tensor product with `𝒩` followed by the localization. -/
instance isLeftDerivedFunctor_derivedTensorProduct :
    (derivedTensorProduct N).IsLeftDerivedFunctor (derivedTensorProductCounit N)
      (quasiIsomorphisms.{u, u, u} A) :=
  isLeftDerivedFunctor_derivedPullbackTensorCounit _ _

/-- **Uniqueness of the derived tensor product**: a left derived functor of `ℳ ↦ ℳ ⊗_𝒜 𝒩`
followed by the localization is the derived tensor product. -/
def derivedTensorProductIsoOfIsLeftDerivedFunctor
    (LF : derivedCategory.{u, u, u} A ⥤ derivedCategory.{u, u, u} A')
    (α : toDerivedCategory.{u, u, u} A ⋙ LF ⟶
      HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N) ⋙
        toDerivedCategory.{u, u, u} A')
    (hLF : LF.IsLeftDerivedFunctor α (quasiIsomorphisms.{u, u, u} A)) :
    LF ≅ derivedTensorProduct N :=
  haveI := hLF
  Functor.leftDerivedNatIso LF (derivedTensorProduct N) α (derivedTensorProductCounit N)
    (quasiIsomorphisms.{u, u, u} A) (Iso.refl _)

/-- The isomorphism `derivedTensorProductIsoOfIsLeftDerivedFunctor` carries the comparison map of
the derived tensor product to the given one. -/
theorem derivedTensorProductIsoOfIsLeftDerivedFunctor_hom_fac
    (LF : derivedCategory.{u, u, u} A ⥤ derivedCategory.{u, u, u} A')
    (α : toDerivedCategory.{u, u, u} A ⋙ LF ⟶
      HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N) ⋙
        toDerivedCategory.{u, u, u} A')
    (hLF : LF.IsLeftDerivedFunctor α (quasiIsomorphisms.{u, u, u} A)) :
    Functor.whiskerLeft (toDerivedCategory.{u, u, u} A)
        (derivedTensorProductIsoOfIsLeftDerivedFunctor N LF α hLF).hom ≫
      derivedTensorProductCounit N = α :=
  have := hLF
  (Functor.leftDerivedNatTrans_fac LF (derivedTensorProduct N) α (derivedTensorProductCounit N)
    (quasiIsomorphisms.{u, u, u} A) (𝟙 _)).trans (Category.comp_id _)

/-- On a flat and K-flat module the derived tensor product is the tensor product: the comparison
map is invertible there. -/
theorem isIso_derivedTensorProductCounit_app {P : DifferentialGradedModule.{u, u, u} A}
    (hP : RelativeTensor.IsGradedFlat
        (GradedModule.ofDifferentialGraded
          (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) P) ∧
      RelativeTensor.IsKFlat (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) P) :
    IsIso ((derivedTensorProductCounit N).app ((HomotopyCategory.quotient A).obj P)) :=
  isIso_derivedPullbackTensorCounit_app_of_isGood _ _ hP

/-- **The value of the derived tensor product on a flat and K-flat module**: at the image in
`D(𝒜, d)` of a flat and K-flat right differential graded `𝒜`-module `𝒫`, the derived tensor
product is the image in `D(𝒜', d)` of `𝒫 ⊗_𝒜 𝒩`. -/
def derivedTensorProductObjIso {P : DifferentialGradedModule.{u, u, u} A}
    (hP : RelativeTensor.IsGradedFlat
        (GradedModule.ofDifferentialGraded
          (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) P) ∧
      RelativeTensor.IsKFlat (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) P) :
    (derivedTensorProduct N).obj
        ((toDerivedCategory A).obj ((HomotopyCategory.quotient A).obj P)) ≅
      (toDerivedCategory A').obj
        ((HomotopyCategory.quotient A').obj ((tensorData N).functor.obj P)) :=
  derivedTensorObjIso (tensorExactnessData N) hP

end SheafOfModules.DifferentialGradedModule

end
