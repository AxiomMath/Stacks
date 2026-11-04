module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorBarStructure

/-!
# Tensoring with the constant integer sheaf, derived

Let `S` be a simplicial-site situation. The endofunctor `ℤ ⊗_ℤ -` of abelian sheaves on the
total site — `CategoryTheory.SimplicialSiteSituation.unitIntegerTensorAb`, the left factor of
the tensor product of Stacks 0GMW fixed at the constant integer sheaf — is the tensor product of
sheaves of modules over the constant sheaf of rings `ℤ` conjugated by the equivalence
`Stacks.DerivedTensor.AbelianSheaves.moduleEquivalence`. The constant integer sheaf is, read
across that equivalence, the structure sheaf of the ringed site
`Stacks.DerivedTensor.AbelianSheaves.intRingedSite`, hence flat; so `ℤ ⊗_ℤ -` is exact, it
induces a functor of unbounded derived categories, and that functor is the derived tensor
product `ℤ ⊗^L_ℤ -` placed in degree zero.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.totalIntegerModuleIsoUnit`: the constant integer
  sheaf, read as a module over the constant sheaf of rings `ℤ`, is the structure sheaf of
  `intRingedSite`.
* `CategoryTheory.SimplicialSiteSituation.unitIntegerTensorAbDerivedIso`: **`ℤ ⊗^L_ℤ -` is the
  derived functor of `ℤ ⊗_ℤ -`.**

## Main results

* `CategoryTheory.SimplicialSiteSituation.isFlat_moduleEquivalenceInverseTotalIntegerSheaf`:
  **the constant integer sheaf is flat.**
* `CategoryTheory.SimplicialSiteSituation.exactFunctor_unitIntegerTensorAb`: **`ℤ ⊗_ℤ -` is
  exact.**

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

attribute [local instance] CategoryTheory.SimplicialSiteSituation.hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

namespace CategoryTheory.SimplicialSiteSituation

open Stacks.DerivedTensor.AbelianSheaves Stacks.SheafOfModules.Tensor

variable (S : SimplicialSiteSituation.{u})

/-- **The constant integer sheaf is the structure sheaf of `intRingedSite`**: read as a module
over the constant sheaf of rings `ℤ`, `ℤ` is the unit of the tensor product of Stacks 06YM. -/
def totalIntegerModuleIsoUnit :
    (moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S) ≅
      SheafOfModules.unit (intRings S.totalTopology) :=
  (moduleEquivalence S.totalTopology).inverse.mapIso
      (intSheafIsoConstantSheaf S.totalTopology) ≪≫
    ((moduleEquivalence S.totalTopology).unitIso.app
      (SheafOfModules.unit (intRings S.totalTopology))).symm

/-- **The constant integer sheaf is flat**, read as a sheaf of modules over the constant sheaf of
rings `ℤ`. -/
theorem isFlat_moduleEquivalenceInverseTotalIntegerSheaf :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := intRingSheaf S.totalTopology)
      ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)) :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_iso.{u, u, u} _ (totalIntegerModuleIsoUnit S).symm
    (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
      (Y := intRingedSite S.totalTopology))

/-- **Tensoring with `ℤ` is exact.** The endofunctor `ℤ ⊗_ℤ -` of abelian sheaves on the total
site preserves finite limits and finite colimits. -/
theorem exactFunctor_unitIntegerTensorAb :
    exactFunctor (Sheaf S.totalTopology Ab.{u}) (Sheaf S.totalTopology Ab.{u})
      (unitIntegerTensorAb S) := by
  have hM := Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.exactFunctor_sheafTensorObj
    (intRingSheaf S.totalTopology)
    ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
    (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)
  obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff _).1 hM
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/-- `ℤ ⊗_ℤ -` preserves finite limits. -/
instance preservesFiniteLimits_unitIntegerTensorAb :
    PreservesFiniteLimits (unitIntegerTensorAb S) :=
  (exactFunctor_unitIntegerTensorAb S).1

/-- `ℤ ⊗_ℤ -` preserves finite colimits. -/
instance preservesFiniteColimits_unitIntegerTensorAb :
    PreservesFiniteColimits (unitIntegerTensorAb S) :=
  (exactFunctor_unitIntegerTensorAb S).2

/-- `ℤ ⊗_ℤ -` is additive. -/
instance additive_unitIntegerTensorAb : (unitIntegerTensorAb S).Additive :=
  Functor.additive_of_preserves_binary_products _

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- Tensoring on the left with `ℤ` in sheaves of modules over the constant sheaf of rings `ℤ` is
exact. -/
theorem exactFunctor_sheafTensorTotalIntegerModule :
    exactFunctor _ _
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))) :=
  Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.exactFunctor_sheafTensorObj
    (intRingSheaf S.totalTopology)
    ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
    (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)

/-- Tensoring on the left with `ℤ` in sheaves of modules preserves finite limits. -/
instance preservesFiniteLimits_sheafTensorTotalIntegerModule :
    PreservesFiniteLimits
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))) :=
  ((exactFunctor_iff _).1 (exactFunctor_sheafTensorTotalIntegerModule S)).1

/-- Tensoring on the left with `ℤ` in sheaves of modules preserves finite colimits. -/
instance preservesFiniteColimits_sheafTensorTotalIntegerModule :
    PreservesFiniteColimits
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))) :=
  ((exactFunctor_iff _).1 (exactFunctor_sheafTensorTotalIntegerModule S)).2

/-- **The derived functor of `ℤ ⊗_ℤ -`, in sheaves of modules, is the derived tensor product by
`ℤ` placed in degree zero**, read through the equivalence of abelian sheaves with modules over
the constant sheaf of rings `ℤ`. -/
def unitIntegerTensorFlatIso :
    ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        ((moduleEquivalence S.totalTopology).inverse.obj
          (totalIntegerSheaf S))).mapDerivedCategory ≅
      (intDerivedTensorProduct S.totalTopology).tensor.obj
        ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
            (totalIntegerSheaf S))) :=
  (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso
      (intRingSheaf S.totalTopology) (intDerivedTensorProduct S.totalTopology)
      ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
      (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)).symm ≪≫
    (intDerivedTensorProduct S.totalTopology).tensor.mapIso
      (((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
        (totalIntegerSheaf S)).symm

/-- **`ℤ ⊗^L_ℤ -` is the derived functor of `ℤ ⊗_ℤ -`**: the derived functor of `ℤ ⊗_ℤ -` on
abelian sheaves on the total site is the derived tensor product with `ℤ` placed in degree
zero. -/
def unitIntegerTensorAbDerivedIso :
    (unitIntegerTensorAb S).mapDerivedCategory ≅
      (derivedTensor S.totalTopology).obj
        ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
          (totalIntegerSheaf S)) :=
  derivedCompIso (moduleEquivalence S.totalTopology).inverse
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
          ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)) ⋙
        (moduleEquivalence S.totalTopology).functor) (unitIntegerTensorAb S) (Iso.refl _) ≪≫
    Functor.isoWhiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
        (derivedCompIso
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
          (moduleEquivalence S.totalTopology).functor _ (Iso.refl _)) ≪≫
      Functor.isoWhiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
        (Functor.isoWhiskerRight (unitIntegerTensorFlatIso S)
          (moduleEquivalence S.totalTopology).functor.mapDerivedCategory)

/-- **The three factors of `unitIntegerTensorAbDerivedIso`**: the compositor that splits off the
outer conjugation by the equivalence with modules, the compositor that splits off the inner one,
and the identification `unitIntegerTensorFlatIso` of the derived functor of the tensor product
with the derived tensor product. -/
theorem unitIntegerTensorAbDerivedIso_hom :
    (unitIntegerTensorAbDerivedIso S).hom =
      (derivedCompIso (moduleEquivalence S.totalTopology).inverse
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
                ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)) ⋙
              (moduleEquivalence S.totalTopology).functor) (unitIntegerTensorAb S)
            (Iso.refl _)).hom ≫
        Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
            (derivedCompIso
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
                ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
              (moduleEquivalence S.totalTopology).functor _ (Iso.refl _)).hom ≫
          Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
            (Functor.whiskerRight (unitIntegerTensorFlatIso S).hom
              (moduleEquivalence S.totalTopology).functor.mapDerivedCategory) :=
  rfl

end Derived

end CategoryTheory.SimplicialSiteSituation

end
