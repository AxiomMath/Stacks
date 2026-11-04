module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatSingleTensor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerLowerShriekFlat

/-!
# Tensoring with the lower shriek image of the constant integer sheaf

Let `S` be a simplicial-site situation and `n` a simplicial degree. The endofunctor
`g_{n!}ℤ ⊗_ℤ -` of abelian sheaves on the total site is the tensor product of sheaves of modules
over the constant sheaf of rings `ℤ`, conjugated by the equivalence
`Stacks.DerivedTensor.AbelianSheaves.moduleEquivalence` of abelian sheaves with those modules.
Since `g_{n!}ℤ` is flat (`isFlat_moduleEquivalenceInverseComponentIntegerSheaf`), that endofunctor
is exact, so it induces a functor of unbounded derived categories, and that functor is the derived
tensor product `g_{n!}ℤ ⊗^L_ℤ -` placed in degree zero.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.integerTensorAb`: the endofunctor `g_{n!}ℤ ⊗_ℤ -` of
  abelian sheaves on the total site.
* `CategoryTheory.SimplicialSiteSituation.integerTensorAbDerivedIso`: its derived functor is the
  derived tensor product `g_{n!}ℤ ⊗^L_ℤ -`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.exactFunctor_integerTensorAb`: it is exact.

## References

* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

open Stacks.DerivedTensor.AbelianSheaves Stacks.SheafOfModules.Tensor

variable (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)

/-- `g_{n!}ℤ`, read as a sheaf of modules over the constant sheaf of rings `ℤ`. -/
abbrev componentIntegerModule :
    Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology) :=
  (moduleEquivalence S.totalTopology).inverse.obj (componentIntegerSheaf S n)

/-- **The endofunctor `g_{n!}ℤ ⊗_ℤ -` of abelian sheaves on the total site**: tensoring with
`g_{n!}ℤ` in sheaves of modules over the constant sheaf of rings `ℤ`, conjugated by the
equivalence of abelian sheaves with those modules. -/
abbrev integerTensorAb :
    Sheaf S.totalTopology Ab.{u} ⥤ Sheaf S.totalTopology Ab.{u} :=
  (moduleEquivalence S.totalTopology).inverse ⋙
    (sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj (componentIntegerModule S n) ⋙
    (moduleEquivalence S.totalTopology).functor

/-- Tensoring on the left with `g_{n!}ℤ` in sheaves of modules over `ℤ` is exact. -/
private theorem exactFunctor_sheafTensor_componentIntegerModule :
    exactFunctor _ _
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
          (componentIntegerModule S n)) :=
  Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.exactFunctor_sheafTensorObj
    (intRingSheaf S.totalTopology) (componentIntegerModule S n)
    (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S n)

/-- **Tensoring with `g_{n!}ℤ` is exact.** -/
theorem exactFunctor_integerTensorAb :
    exactFunctor (Sheaf S.totalTopology Ab.{u}) (Sheaf S.totalTopology Ab.{u})
      (integerTensorAb S n) := by
  obtain ⟨hlim, hcolim⟩ :=
    (exactFunctor_iff _).1 (exactFunctor_sheafTensor_componentIntegerModule S n)
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/-- `g_{n!}ℤ ⊗_ℤ -` preserves finite limits. -/
instance preservesFiniteLimits_integerTensorAb :
    PreservesFiniteLimits (integerTensorAb S n) :=
  (exactFunctor_integerTensorAb S n).1

/-- `g_{n!}ℤ ⊗_ℤ -` preserves finite colimits. -/
instance preservesFiniteColimits_integerTensorAb :
    PreservesFiniteColimits (integerTensorAb S n) :=
  (exactFunctor_integerTensorAb S n).2

/-- `g_{n!}ℤ ⊗_ℤ -` is additive. -/
instance additive_integerTensorAb : (integerTensorAb S n).Additive :=
  Functor.additive_of_preserves_binary_products _

section Derived

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] SimplicialSiteSituation.hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-- Tensoring on the left with `g_{n!}ℤ` in sheaves of modules over `ℤ` is exact. -/
theorem exactFunctor_sheafTensorComponentIntegerModule :
    exactFunctor _ _
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
          (componentIntegerModule S n)) :=
  exactFunctor_sheafTensor_componentIntegerModule S n

/-- Tensoring on the left with `g_{n!}ℤ` in sheaves of modules preserves finite limits. -/
instance preservesFiniteLimits_sheafTensorComponentIntegerModule :
    PreservesFiniteLimits
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
          (componentIntegerModule S n)) :=
  ((exactFunctor_iff _).1 (exactFunctor_sheafTensorComponentIntegerModule S n)).1

/-- Tensoring on the left with `g_{n!}ℤ` in sheaves of modules preserves finite colimits. -/
instance preservesFiniteColimits_sheafTensorComponentIntegerModule :
    PreservesFiniteColimits
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
          (componentIntegerModule S n)) :=
  ((exactFunctor_iff _).1 (exactFunctor_sheafTensorComponentIntegerModule S n)).2

/-- **The derived functor of `g_{n!}ℤ ⊗_ℤ -`, in sheaves of modules, is the derived tensor
product by `g_{n!}ℤ` placed in degree zero.** -/
noncomputable def integerTensorFlatIso :
    ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        (componentIntegerModule S n)).mapDerivedCategory ≅
      (Stacks.DerivedTensor.AbelianSheaves.intDerivedTensorProduct S.totalTopology).tensor.obj
        ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
            (componentIntegerSheaf S n))) :=
  (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso
      (intRingSheaf S.totalTopology)
      (Stacks.DerivedTensor.AbelianSheaves.intDerivedTensorProduct S.totalTopology)
      (componentIntegerModule S n)
      (isFlat_moduleEquivalenceInverseComponentIntegerSheaf S n)).symm ≪≫
    (Stacks.DerivedTensor.AbelianSheaves.intDerivedTensorProduct S.totalTopology).tensor.mapIso
      (((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
        (componentIntegerSheaf S n)).symm

/-- **`g_{n!}ℤ ⊗^L_ℤ -` is the derived functor of `g_{n!}ℤ ⊗_ℤ -`.** -/
noncomputable def integerTensorAbDerivedIso :
    (integerTensorAb S n).mapDerivedCategory ≅
      (Stacks.DerivedTensor.AbelianSheaves.derivedTensor S.totalTopology).obj
        ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
          (componentIntegerSheaf S n)) :=
  derivedCompIso (moduleEquivalence S.totalTopology).inverse
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
          (componentIntegerModule S n) ⋙
        (moduleEquivalence S.totalTopology).functor) (integerTensorAb S n) (Iso.refl _) ≪≫
    Functor.isoWhiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
        (derivedCompIso
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
              (componentIntegerModule S n))
          (moduleEquivalence S.totalTopology).functor _ (Iso.refl _)) ≪≫
      Functor.isoWhiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
        (Functor.isoWhiskerRight (integerTensorFlatIso S n)
          (moduleEquivalence S.totalTopology).functor.mapDerivedCategory)

/-- **The three factors of `integerTensorAbDerivedIso`**: the compositor that splits off the
outer conjugation by the equivalence with modules, the compositor that splits off the inner one,
and the identification `integerTensorFlatIso` of the derived functor of the tensor product with
the derived tensor product. -/
theorem integerTensorAbDerivedIso_hom :
    (integerTensorAbDerivedIso S n).hom =
      (derivedCompIso (moduleEquivalence S.totalTopology).inverse
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
                (componentIntegerModule S n) ⋙
              (moduleEquivalence S.totalTopology).functor) (integerTensorAb S n)
            (Iso.refl _)).hom ≫
        Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
            (derivedCompIso
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
                  (componentIntegerModule S n))
              (moduleEquivalence S.totalTopology).functor _ (Iso.refl _)).hom ≫
          Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
            (Functor.whiskerRight (integerTensorFlatIso S n).hom
              (moduleEquivalence S.totalTopology).functor.mapDerivedCategory) :=
  rfl

end Derived

end CategoryTheory.SimplicialSiteSituation

end
