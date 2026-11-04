module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksCore.CategoryTheory.Filtration.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Support.AffineLifting
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunctionUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedOpenClosedConservativity

/-!
# Extension by zero on the unbounded derived category of sheaves of `Λ`-modules

Let `Λ` be a ring and let `j : U ⟶ X` be an étale morphism of schemes. The unbounded derived
extension by zero `Rj_!` of `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnbounded`
is left adjoint to the derived inverse image `j^{-1}` on `D(-_étale, Λ)`. For an open immersion
`j`, the unit of this adjunction is invertible, and with the derived inverse image to a closed
complement, `j^{-1}` detects isomorphisms and kills the objects extended by zero from `U`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedAdj`: the adjunction
  `Rj_! ⊣ j^{-1}` on unbounded derived categories.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedExtensionByZeroUnboundedAdj_unit`: the unit is
  invertible for an open immersion.
* `Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleDerivedInverseImage_of_range_eq_compl`: the
  derived inverse images to an open and to its closed complement jointly reflect isomorphisms.
* `Stacks.EtaleCohomology.isZero_etaleModuleDerivedInverseImage_extensionByZero_general`:
  the derived inverse image to the closed complement of an extension by zero from the open
  vanishes.
* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion_unconditional`:
  base change along an open immersion is invertible for sheaves of `Λ`-modules.

## Implementation notes

The bounded below adjunction is
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroAdj`, built from
`CategoryTheory.Adjunction.rightDerivedFunctorPlus`; on unbounded derived categories both
functors are exact and the adjunction is `CategoryTheory.Adjunction.mapDerivedCategory`, carried
to `Rj_!` along `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedIso` and to the
inverse image along `Stacks.EtaleCohomology.etaleModuleInverseImageRestrictionIso`.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

section Adjunction

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- **The adjunction `Rj_! ⊣ j^{-1}` on unbounded derived categories of sheaves of
`Λ`-modules** for an étale morphism `j : U ⟶ X`. -/
def etaleModuleDerivedExtensionByZeroUnboundedAdj :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j ⊣
      etaleModuleDerivedInverseImageGeneral.{u, r} Λ j :=
  ((Adjunction.mapDerivedCategory (etaleModuleExtensionByZeroAdj.{u, r} Λ j)).ofNatIsoRight
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModuleInverseImageRestrictionIso.{u, r} Λ j).symm)).ofNatIsoLeft
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).symm

/-- **The unit of `Rj_! ⊣ j^{-1}` is invertible for an open immersion** `j`, `j` being a
monomorphism. -/
instance isIso_etaleModuleDerivedExtensionByZeroUnboundedAdj_unit [IsOpenImmersion j] :
    IsIso (etaleModuleDerivedExtensionByZeroUnboundedAdj.{u, r} Λ j).unit := by
  have := Adjunction.isIso_mapDerivedCategory_unit (etaleModuleExtensionByZeroAdj.{u, r} Λ j)
  rw [etaleModuleDerivedExtensionByZeroUnboundedAdj, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoRight_unit]
  infer_instance

/-- **Forgetting the module structure commutes with `Rj_!`.** -/
def etaleModuleDerivedExtensionByZeroUnboundedForgetIso :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j ⋙ etaleModuleForgetDerived.{u, r} Λ X ≅
      etaleModuleForgetDerived.{u, r} Λ U ⋙ (extensionByZero.{u, r} j).mapDerivedCategory :=
  Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j) _ ≪≫
    etaleModuleExtensionByZeroMapDerivedCategoryForgetIso.{u, r} Λ j

end Adjunction

section Complementary

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [Etale j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij

omit [Etale j] in
/-- **The derived inverse images to an open and to its closed complement jointly reflect
isomorphisms** in `D(X_étale, Λ)`: they do on cohomology sheaves, both being exact. -/
theorem isIso_of_isIso_etaleModuleDerivedInverseImage_of_range_eq_compl
    {K L : DerivedCategory (EtaleModules.{u, r} Λ X)} (γ : K ⟶ L)
    (hi : IsIso ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ i).map γ))
    (hj : IsIso ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ j).map γ)) : IsIso γ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have := ((etaleModuleInverseImage.{u, r} Λ i).isIso_mapDerivedCategory_map_iff γ).1 hi n
  have := ((etaleModuleInverseImage.{u, r} Λ j).isIso_mapDerivedCategory_map_iff γ).1 hj n
  exact isIso_of_isIso_etaleModuleInverseImage Λ i j hij _

/-- **The derived inverse image to the closed complement of an extension by zero vanishes**:
`i^{-1} Rj_! M = 0` for every `M` in `D(U_étale, Λ)`, on cohomology sheaves by
`Stacks.EtaleCohomology.isZero_etaleModuleInverseImage_extensionByZero`. -/
theorem isZero_etaleModuleDerivedInverseImage_extensionByZero_general
    (M : DerivedCategory (EtaleModules.{u, r} Λ U)) :
    IsZero ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ i).obj
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).obj M)) := by
  refine IsZero.of_iso ?_ ((etaleModuleDerivedInverseImageGeneral.{u, r} Λ i).mapIso
    ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).app M))
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  refine IsZero.of_iso ?_ (((etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryHomologyIso
    n).app _)
  refine IsZero.of_iso ?_ ((etaleModuleInverseImage.{u, r} Λ i).mapIso
    (((etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategoryHomologyIso n).app M))
  exact isZero_etaleModuleInverseImage_extensionByZero Λ i j hij _

end Complementary

/-- **Base change along an open immersion is invertible for sheaves of `Λ`-modules.** For a
cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
with `g` an open immersion, the base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on
`D(-_étale, Λ)` is an isomorphism, since the abelian one is
(`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion`). -/
theorem isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion_unconditional {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g)
    [IsOpenImmersion g] : IsIso (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ f g g' f' sq.w) := by
  have := isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion.{u, r} f g g' f' sq
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun K ↦ isIso_etaleModuleDerivedBaseChange_app_of_isIso.{u, r} Λ f g g' f' sq.w K
    inferInstance

/-- **Stacks 0DDE for sheaves of `Λ`-modules: the base change map on bounded below complexes with
torsion cohomology.** Suppose that cohomology commutes with base change for `f : X ⟶ Y` (for `f`
proper this is the proper base change theorem, [Stacks, Tag 095T]), and let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square. For every object `E` of `D(X_étale, Λ)` which is bounded below and whose
underlying complex of abelian sheaves has torsion cohomology sheaves, the base change map
`g^{-1} Rf_* E ⟶ Rf'_* (g')^{-1} E` is an isomorphism. -/
theorem isIso_etaleModuleDerivedBaseChange_of_cohomologyCommutesWithBaseChange
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} (hf : CohomologyCommutesWithBaseChange.{u, r} f)
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    (E : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) [E.IsGE n]
    (hT : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj E)) :
    IsIso ((etaleModuleDerivedBaseChangeGeneral.{u, r} Λ f g g' f' sq.w).app E) :=
  isIso_etaleModuleDerivedBaseChange_app_of_isIso.{u, r} Λ f g g' f' sq.w E
    (isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange.{u, r} hf sq _ n
      (Functor.isGE_obj_mapDerivedCategory _ E n inferInstance) hT)

end Stacks.EtaleCohomology

end
