module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlus

/-!
# The base change map for sheaves of modules on bounded below derived categories

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes and `Λ` a ring. This file constructs the base change map
$$
g^{-1} Rf_* \longrightarrow Rf'_* (g')^{-1}
$$
of functors `D⁺(X_étale, Λ) ⥤ D⁺(Y'_étale, Λ)` on the bounded below derived categories of
sheaves of `Λ`-modules for the small étale topologies ([Stacks, Tag 0DDE]). The inverse image
`g^{-1}` is exact, so it acts on `D⁺` degreewise, and `Rf_* ⋙ g^{-1}` is a right derived functor
of degreewise `f_* ⋙ g^{-1}`; the base change map is the map induced by the degreewise comparison
`g^{-1} f_* ⟶ f'_* (g')^{-1}` followed by the derived-functor unit of `Rf'_*`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedInverseImagePlus`: the inverse image on `D⁺`.
* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChange`: the base change map
  `Rf_* ⋙ g^{-1} ⟶ (g')^{-1} ⋙ Rf'_*`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChange_fac`: precomposed with `g^{-1}` of the
  derived-functor unit of `Rf_*`, the base change map is the degreewise comparison followed by
  the derived-functor unit of `Rf'_*`.
* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_app_of_quasiIso`: a criterion for
  the base change map to be an isomorphism at a bounded below complex of injectives.

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ]

/-- The inverse image `g^{-1}` on bounded below derived categories of sheaves of `Λ`-modules on
small étale sites: inverse image is exact, so it acts degreewise. -/
abbrev etaleModuleDerivedInverseImagePlus {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ Y) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ Y') :=
  (etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryPlus

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
  (w : f' ≫ g = g' ≫ f)

/-- The derived-functor unit exhibiting `Rf_* ⋙ g^{-1}` as a right derived functor of
degreewise `f_* ⋙ g^{-1}`: the unit of `Rf_*` whiskered with `g^{-1}`. -/
abbrev etaleModuleDerivedBaseChangeUnit :
    ((etaleModuleDirectImage.{u, r} Λ f).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        etaleModuleDerivedInverseImagePlus.{u, r} Λ g ⟶
      DerivedCategory.Plus.Qh ⋙ (etaleModuleDerivedDirectImage.{u, r} Λ f ⋙
        etaleModuleDerivedInverseImagePlus.{u, r} Λ g) :=
  Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlusUnit
    (etaleModuleDirectImage.{u, r} Λ f) (etaleModuleInverseImage.{u, r} Λ g)

/-- The degreewise comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` on bounded below complexes, localized,
followed by the derived-functor unit of `Rf'_*`, on the source of the derived-functor unit of
`Rf_* ⋙ g^{-1}`. -/
abbrev etaleModuleDerivedBaseChangeAux :
    ((etaleModuleDirectImage.{u, r} Λ f).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        etaleModuleDerivedInverseImagePlus.{u, r} Λ g ⟶
      DerivedCategory.Plus.Qh ⋙ (etaleModuleDerivedInverseImagePlus.{u, r} Λ g' ⋙
        etaleModuleDerivedDirectImage.{u, r} Λ f') :=
  Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlusAux
    (etaleModuleDirectImage.{u, r} Λ f) (etaleModuleDirectImage.{u, r} Λ f')
    (etaleModuleInverseImage.{u, r} Λ g) (etaleModuleInverseImage.{u, r} Λ g')
    (etaleModuleBaseChange Λ f f' g g' w)

/-- The base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on the bounded below derived categories of
sheaves of `Λ`-modules for the small étale topologies, attached to a commutative square
`f' ≫ g = g' ≫ f` of schemes ([Stacks, Tag 0DDE]). -/
abbrev etaleModuleDerivedBaseChange :
    etaleModuleDerivedDirectImage.{u, r} Λ f ⋙ etaleModuleDerivedInverseImagePlus.{u, r} Λ g ⟶
      etaleModuleDerivedInverseImagePlus.{u, r} Λ g' ⋙ etaleModuleDerivedDirectImage.{u, r} Λ f' :=
  Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus
    (etaleModuleDirectImage.{u, r} Λ f) (etaleModuleDirectImage.{u, r} Λ f')
    (etaleModuleInverseImage.{u, r} Λ g) (etaleModuleInverseImage.{u, r} Λ g')
    (etaleModuleBaseChange Λ f f' g g' w)

/-- At the object represented by a bounded below complex `K`, the base change map precomposed
with `g^{-1}` of the derived-functor unit of `Rf_*` is the localized degreewise comparison
`g^{-1} f_* K ⟶ f'_* (g')^{-1} K` followed by the derived-functor unit of `Rf'_*`. -/
theorem etaleModuleDerivedBaseChange_fac (K : HomotopyCategory.Plus (EtaleModules.{u, r} Λ X)) :
    (etaleModuleDerivedInverseImagePlus.{u, r} Λ g).map
        ((etaleModuleDirectImage.{u, r} Λ f).rightDerivedFunctorPlusUnith.app K) ≫
      (etaleModuleDerivedBaseChange.{u, r} Λ f f' g g' w).app (DerivedCategory.Plus.Qh.obj K) =
    (etaleModuleDerivedBaseChangeAux.{u, r} Λ f f' g g' w).app K :=
  Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus_fac _ _ _ _ _ K

/-- For functors between categories of étale sheaves of modules and a quasi-isomorphism
`i : G' I ⟶ L` of bounded below complexes of injectives, the derived base change map of `α` is an
isomorphism at `I` if `α_I` followed by `F'(i)` becomes an isomorphism in the derived category. -/
theorem isIso_derivedBaseChangePlus_app_of_quasiIso_etaleModules {X X' Y Y' : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ X ⥤ EtaleModules.{u, r} Λ Y)
    (F' : EtaleModules.{u, r} Λ X' ⥤ EtaleModules.{u, r} Λ Y')
    (G : EtaleModules.{u, r} Λ Y ⥤ EtaleModules.{u, r} Λ Y')
    (G' : EtaleModules.{u, r} Λ X ⥤ EtaleModules.{u, r} Λ X')
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (α : F ⋙ G ⟶ G' ⋙ F')
    (I : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) [∀ n, Injective (I.obj.X n)]
    (L : CochainComplex.Plus (EtaleModules.{u, r} Λ X')) [∀ n, Injective (L.obj.X n)]
    (i : G'.mapCochainComplexPlus.obj I ⟶ L) (hi : QuasiIso i.hom)
    (hx : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I.obj ≫
        (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom))) :
    IsIso ((Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus F F' G G' α).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj I))) :=
  Stacks.Cohomology.DerivedBaseChangePlus.isIso_derivedBaseChangePlus_app_of_quasiIso _ _ _ _ _
    I L i hi hx

/-- Let `I` be a bounded below complex of injective sheaves of `Λ`-modules on `X_étale` and
`i : (g')^{-1} I ⟶ L` a quasi-isomorphism onto a bounded below complex of injective sheaves on
`X'_étale`. If the morphism of complexes `g^{-1} f_* I ⟶ f'_* (g')^{-1} I ⟶ f'_* L`, the degreewise
comparison followed by `f'_*(i)`, is a quasi-isomorphism, then the base change map is an
isomorphism at `I`. -/
theorem isIso_etaleModuleDerivedBaseChange_app_of_quasiIso
    (I : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) [∀ n, Injective (I.obj.X n)]
    (L : CochainComplex.Plus (EtaleModules.{u, r} Λ X')) [∀ n, Injective (L.obj.X n)]
    (i : (etaleModuleInverseImage.{u, r} Λ g').mapCochainComplexPlus.obj I ⟶ L)
    (hi : QuasiIso i.hom)
    (hx : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (etaleModuleBaseChange Λ f f' g g' w)
        (ComplexShape.up ℤ)).app I.obj ≫
      ((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map
        i.hom))) :
    IsIso ((etaleModuleDerivedBaseChange.{u, r} Λ f f' g g' w).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj I))) :=
  isIso_derivedBaseChangePlus_app_of_quasiIso_etaleModules Λ _ _ _ _ _ I L i hi hx

end Stacks.EtaleCohomology
