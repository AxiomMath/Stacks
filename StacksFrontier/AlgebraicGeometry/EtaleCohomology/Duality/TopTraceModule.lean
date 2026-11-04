module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopTraceDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopDirectImageForget

/-!
# `R² f_*` of sheaves of modules against the abelian top-degree sheaf

For `f : X ⟶ S` and a sheaf `M` of `ℤ/N`-modules on `X`, the underlying abelian sheaf of
`R² f_* M`, computed in sheaves of modules on bounded below derived categories
(`Stacks.EtaleCohomology.singleHomology` of
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImage`), is `R² f_*` of the underlying abelian
sheaf of `M`, naturally in `M` (`Stacks.EtaleCohomology.TopTrace.singleHomologyForgetIso`):
forgetting the module structure is exact and commutes with `Rf_*` (Stacks 03FD,
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageForgetIso`), with placing in degree zero and
with cohomology. Hence `U(R²f_*(f⁻¹G)) ≅ H⁰(Rf_*(U(f⁻¹G)[2]))`, the sheaf
`Stacks.EtaleCohomology.TopTrace.topSheaf f` on which the top-degree trace is built
(`Stacks.EtaleCohomology.TopTrace.moduleTopSheafIso`). This is a step of the construction of the
top-degree trace of an elementary fibration in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The derived categories are those of the standard model `HasDerivedCategory.standard`.

## Main definitions

* `Stacks.EtaleCohomology.TopTrace.forgetPlusSingleNatIso`.
* `Stacks.EtaleCohomology.TopTrace.singleHomologyForgetIso`.
* `Stacks.EtaleCohomology.TopTrace.moduleTopSheafIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.TopTrace

attribute [local instance] HasDerivedCategory.standard
  isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Sheaf.monoidalCategory
  isMonoidal_W_etaleModules

variable {N : ℕ}

/-- **Forgetting the module structure commutes with placing in degree zero**, on bounded below
derived categories, naturally in the sheaf. -/
def forgetPlusSingleNatIso (Z : Scheme.{u}) :
    DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} (ZMod N) Z) 0 ⋙
        (etaleModuleUnderlyingAbelian Z (ZMod N)).mapDerivedCategoryPlus ≅
      etaleModuleUnderlyingAbelian Z (ZMod N) ⋙ DerivedCategory.Plus.singleFunctor _ 0 :=
  ((Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight _).preimageIso
    ((etaleModuleUnderlyingAbelian Z (ZMod N)).mapDerivedCategorySingleFunctor 0)

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`U(R² f_* M) ≅ R² f_*(U M)`**, naturally in the sheaf of `ℤ/N`-modules `M` on `X`: the
left side computed in sheaves of modules on bounded below derived categories, the right side
the classical right derived functor of the direct image of abelian sheaves. -/
def singleHomologyForgetIso :
    singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) f) 2 ⋙
        etaleModuleUnderlyingAbelian S (ZMod N) ≅
      etaleModuleUnderlyingAbelian X (ZMod N) ⋙ (etaleAbelianDirectImage.{u, 0} f).rightDerived 2 :=
  letI := etaleModules_enoughInjectives.{u, 0} (ZMod N) X
  Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (StacksDraft.DerivedSectionsComparison.singlePlusQIso (EtaleModules.{u, 0} (ZMod N) X))
      (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) f ⋙ DerivedCategory.Plus.homologyFunctor _ 2))
      (etaleModuleUnderlyingAbelian S (ZMod N)) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod N) f)
      (Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
          (etaleModuleUnderlyingAbelian S (ZMod N)) 2)).symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (Functor.isoWhiskerRight (etaleModuleDerivedDirectImageForgetIso (ZMod N) f)
        (DerivedCategory.Plus.homologyFunctor _ 2)) ≪≫
    Functor.isoWhiskerRight (forgetPlusSingleNatIso (N := N) X)
      ((etaleAbelianDirectImage.{u, 0} f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ 2) ≪≫
    Functor.isoWhiskerLeft (etaleModuleUnderlyingAbelian X (ZMod N))
      (Stacks.DerivedIndexing.rightDerivedIso (etaleAbelianDirectImage.{u, 0} f) 2).symm

/-- **`U(R² f_*(f⁻¹G)) ≅ H⁰(Rf_*(U(f⁻¹G)[2]))`**, naturally in the sheaf of `ℤ/N`-modules `G` on
`S`. -/
def moduleTopSheafIso :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙
        singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) f) 2 ⋙
          etaleModuleUnderlyingAbelian S (ZMod N) ≅
      topSheaf f (N := N) :=
  Functor.isoWhiskerLeft _ (singleHomologyForgetIso f) ≪≫ (topSheafIsoRightDerived f).symm

end Stacks.EtaleCohomology.TopTrace
