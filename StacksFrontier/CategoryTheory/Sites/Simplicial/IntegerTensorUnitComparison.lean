module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatSingleTensorNaturality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedCompIsoNaturality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedModuleEquivalenceCounit
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorUnitTransport

/-!
# The derived unit identification, in compositor-first normal form

Let `S` be a simplicial-site situation and write `e` for the equivalence
`Stacks.DerivedTensor.AbelianSheaves.moduleEquivalence` of abelian sheaves on the total site with
modules over the constant sheaf of rings `ℤ`. The unit identification `ℤ ⊗_ℤ - ≅ 𝟭` is written as
a composite of whiskerings of the coefficient transport `totalIntegerModuleIsoUnit`, of the
sheaf-level left unit law `Stacks.SheafOfModules.unitSheafTensorNatIso` and of the counit of `e`;
its derived transformation is then written with the compositor `CategoryTheory.derivedCompIso`
first and `Stacks.DerivedTensor.AbelianSheaves.derivedCounitIso` last.

All names are in the namespace `CategoryTheory.SimplicialSiteSituation`.

## Main results

* `unitTensorIso_hom_eq`: `unitTensorIso` is the whiskering by `e` of the tensor product with
  `totalIntegerModuleIsoUnit`, followed by the whiskering by `e` of `unitSheafTensorNatIso`,
  followed by the counit of `e`.
* `unitTensorIso_hom_eq_whiskerRight`: the same, with the two sheaf-of-modules factors fused into
  one whiskering.
* `derivedNatTrans_unitTensorIso_eq`: the derived transformation of `unitTensorIso`, followed by
  `derivedIdIso`, is the compositor of `unitIntegerTensorAb`, followed by the whiskered derived
  transformation of the fused factor, followed by `derivedCounitIso`.

## References

* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
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

/-- **The unit identification, factored as a transformation of functors**: the whiskering by
`moduleEquivalence` of the tensor product with `totalIntegerModuleIsoUnit`, then that of
`unitSheafTensorNatIso`, then the counit of `moduleEquivalence`. -/
theorem unitTensorIso_hom_eq :
    (unitTensorIso S).hom =
      Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse
          (Functor.whiskerRight
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
              (totalIntegerModuleIsoUnit S).hom)
            (moduleEquivalence S.totalTopology).functor) ≫
        Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse
            (Functor.whiskerRight
              (Stacks.SheafOfModules.unitSheafTensorNatIso
                (Y := intRingedSite S.totalTopology)).hom
              (moduleEquivalence S.totalTopology).functor) ≫
          (moduleEquivalence S.totalTopology).counitIso.hom := by
  refine NatTrans.ext (funext fun F => ?_)
  rw [unitTensorIso_hom_app_eq_unitSheafTensorNatIso]
  exact Eq.trans
    (CategoryTheory.Functor.map_comp (moduleEquivalence S.totalTopology).functor _ _ =≫
      (moduleEquivalence S.totalTopology).counitIso.hom.app F)
    (Category.assoc _ _ _)

/-- **The unit identification, with its two sheaf-of-modules factors fused** into one
whiskering by `moduleEquivalence`, followed by the counit of `moduleEquivalence`. -/
theorem unitTensorIso_hom_eq_whiskerRight :
    (unitTensorIso S).hom =
      (show unitIntegerTensorAb S ⟶
            (moduleEquivalence S.totalTopology).inverse ⋙
              (moduleEquivalence S.totalTopology).functor from
          Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse
            (Functor.whiskerRight
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
                  (totalIntegerModuleIsoUnit S).hom ≫
                (Stacks.SheafOfModules.unitSheafTensorNatIso
                  (Y := intRingedSite S.totalTopology)).hom)
              (moduleEquivalence S.totalTopology).functor)) ≫
        (moduleEquivalence S.totalTopology).counitIso.hom := by
  rw [unitTensorIso_hom_eq, Functor.whiskerRight_comp, Functor.whiskerLeft_comp,
    Category.assoc]

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The derived unit identification, in `derivedCompIso`-first normal form**: the derived
transformation of `unitTensorIso`, followed by `derivedIdIso`, is the compositor `derivedCompIso`,
then the whiskered derived transformation of the fused sheaf-of-modules factor, then
`derivedCounitIso`. -/
theorem derivedNatTrans_unitTensorIso_eq :
    derivedNatTrans (unitIntegerTensorAb S) (𝟭 (Sheaf S.totalTopology Ab.{u}))
          (unitTensorIso S).hom ≫
        (derivedIdIso (A := Sheaf S.totalTopology Ab.{u})).hom =
      (derivedCompIso (moduleEquivalence S.totalTopology).inverse
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
                ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)) ⋙
              (moduleEquivalence S.totalTopology).functor) (unitIntegerTensorAb S)
            (Iso.refl _)).hom ≫
        Functor.whiskerLeft
            (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory
            (derivedNatTrans
              ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
                  ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)) ⋙
                (moduleEquivalence S.totalTopology).functor)
              (moduleEquivalence S.totalTopology).functor
              (Functor.whiskerRight
                ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
                    (totalIntegerModuleIsoUnit S).hom ≫
                  (Stacks.SheafOfModules.unitSheafTensorNatIso
                    (Y := intRingedSite S.totalTopology)).hom)
                (moduleEquivalence S.totalTopology).functor)) ≫
          (derivedCounitIso S.totalTopology).hom := by
  rw [unitTensorIso_hom_eq_whiskerRight, derivedNatTrans_comp, Category.assoc,
    derivedNatTrans_counitIso_eq_derivedCounitIso, ← Category.assoc,
    derivedCompIso_refl_hom_whiskerLeft, Category.assoc]

end Derived

end CategoryTheory.SimplicialSiteSituation

end
