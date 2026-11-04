module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.InverseImageKFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImageExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompactSupportFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricPointStalkCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.DeltaFunctor
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.GeometricFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.AddCommGrpCatTransported
public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import StacksFrontier.CategoryTheory.Sites.InverseImageTensor
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianLowerShriek.Exact
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Bifunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits
public import Mathlib.CategoryTheory.Sites.Monoidal
public import StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedStalkLeftAdjoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.BifunctorTransport
public import StacksFrontier.Algebra.Homology.HomotopyCategory.JointAcyclicity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import Mathlib.Algebra.Homology.TotalComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# The stalk of the derived lower shriek at a geometric point

Let `f : X ⟶ Y` be a separated morphism of finite type, with a compactification `j` over `Y`,
let `Λ` be a ring and let `ȳ : Spec k ⟶ Y` be a geometric point, with geometric fibre
`f_ȳ : X_ȳ ⟶ Spec k`. [Stacks, Tag 0GK0] says that there is a canonical isomorphism
```
(Rf_! K)_ȳ ≅ RΓ_c(X_ȳ, K|_{X_ȳ})
```
in `D(Λ)`, for `K` bounded below with torsion cohomology sheaves, and for every `K` when `Λ` is a
torsion ring.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedStalk` — the stalk `D(Y_étale, Λ) ⥤ D(Λ)` at a
  geometric point: the stalk functor of Mathlib's point
  `AlgebraicGeometry.Scheme.pointSmallEtale` of the small étale site, which is exact, applied
  degreewise.
* `Stacks.EtaleCohomology.etaleModuleDerivedInverseImageGlobalSectionsIsoDerivedStalk` —
  **Tag 04JN on derived categories, in the model `EtaleModules`**:
  `RΓ(Spec k, ȳ⁻¹ M) ≅ M_ȳ`, naturally in `M ∈ D(Y_étale, Λ)`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedStalkIso` — **Tag 0GK0** for `K` bounded
  below with torsion cohomology, granted the proper base change theorem `h095T`.

## Implementation notes

The source's proof is one line: the base change isomorphism `ȳ⁻¹ Rf_! K ≅ Rf_{ȳ,!}(K|_{X_ȳ})` of
Tag 0F7L, read through the alternative description of the stalk (Tag 04JN). The first half is
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedGeometricFibreIso` (and its torsion-ring
analogue below). The second half is assembled here from three identifications:

* over `Spec k`, `k` separably closed, `RΓ(Spec k, -)` is global sections applied degreewise,
  `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnboundedIsoOfIsSepClosed`;
* global sections over `Spec k` is the stalk at the canonical point of `Spec k`, the identity
  being an initial étale neighbourhood,
  `Stacks.EtaleCohomology.presheafFiberUliftIdIsoSections`;
* the stalk at the canonical point of the pullback along `ȳ` is the stalk at `ȳ`,
  `Stacks.EtaleCohomology.etaleModuleInverseImageSheafFiberIso`.

Every functor involved is exact, so the identifications descend to derived categories through
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`.

The derived lower shriek is computed through a compactification `j`, which is part of the data,
as for every statement about `Stacks.EtaleCohomology.derivedLowerShriekUnbounded`; the source
obtains one from the quasi-compactness and quasi-separatedness of `Y` (Nagata). On the
geometric fibre `RΓ_c(X_ȳ, -)` is computed through the base change of `j`.

## References

* [Stacks Project, Tag 0GK0](https://stacks.math.columbia.edu/tag/0GK0)
* [Stacks Project, Tag 04JN](https://stacks.math.columbia.edu/tag/04JN)
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.CompactificationOf

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-! ### The derived stalk at a geometric point -/

section Stalk

/-- The stalk functor at a point of the small étale site preserves finite limits on sheaves of
`Λ`-modules: it is a filtered colimit, and filtered colimits of modules are exact. -/
instance preservesFiniteLimits_sheafFiber_etaleModule {Z : Scheme.{u}}
    (Φ : GrothendieckTopology.Point.{max (u + 1) r} Z.smallEtaleTopology) :
    PreservesFiniteLimits (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)) :=
  inferInstance

/-- The stalk functor at a point of the small étale site preserves finite colimits on sheaves of
`Λ`-modules, being a left adjoint. -/
instance preservesFiniteColimits_sheafFiber_etaleModule {Z : Scheme.{u}}
    (Φ : GrothendieckTopology.Point.{max (u + 1) r} Z.smallEtaleTopology) :
    PreservesFiniteColimits (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)) :=
  inferInstance

/-- **The derived stalk at a geometric point**, `M ↦ M_ȳ`, from `D(Y_étale, Λ)` to `D(Λ)`: the
stalk functor of the point `AlgebraicGeometry.Scheme.pointSmallEtale` of the small étale site
defined by `ȳ`, which is exact, applied degreewise. -/
abbrev etaleModuleDerivedStalk {Y : Scheme.{u}} (y : GeometricPoint Y) :
    DerivedCategory (EtaleModules.{u, r} Λ Y) ⥤ DerivedCategory (ModuleCat.{max (u + 1) r} Λ) :=
  (((pointSmallEtale y.hom).ulift.{max (u + 1) r}).sheafFiber
    (A := ModuleCat.{max (u + 1) r} Λ)).mapDerivedCategory

end Stalk

/-! ### The alternative description of the stalk, on derived categories -/

section AlternativeStalk

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- **Global sections over a separably closed field is the stalk at the canonical point**, for
sheaves of `Λ`-modules: both are evaluation at the final object of the small étale site of
`Spec Ω`, the stalk because the identity lift is an initial étale neighbourhood. -/
def etaleModuleSheafFiberUliftIdIsoGlobalSections :
    ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) r}).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ) ≅
      etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω)) :=
  (Functor.isoWhiskerLeft
      (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
      (presheafFiberUliftIdIsoSections.{u, r} Ω (ModuleCat.{max (u + 1) r} Λ))).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
      (isTerminalEtaleMkId (Spec (.of Ω)))).symm

variable {Y : Scheme.{u}} (s : Spec (.of Ω) ⟶ Y)

/-- **Tag 04JN for sheaves of `Λ`-modules on Mathlib's small étale site.** The stalk at a
morphism `s : Spec Ω ⟶ Y`, `Ω` separably closed, is global sections of the pullback along `s`:
the pullback followed by the stalk at the canonical point of `Spec Ω` is the stalk at
`𝟙 ≫ s = s`, and that stalk is global sections. -/
def etaleModuleInverseImageGlobalSectionsIsoSheafFiber :
    etaleModuleInverseImage.{u, r} Λ s ⋙ etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω)) ≅
      ((pointSmallEtale s).ulift.{max (u + 1) r}).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ) :=
  Functor.isoWhiskerLeft _ (etaleModuleSheafFiberUliftIdIsoGlobalSections.{u, r} Λ Ω).symm ≪≫
    etaleModuleInverseImageSheafFiberIso.{u, r} Λ s (𝟙 (Spec (.of Ω))) ≪≫
    eqToIso (by rw [Category.id_comp])

/-- **Tag 04JN on derived categories, in the model `EtaleModules`.** For `s : Spec Ω ⟶ Y`,
`Ω` separably closed, `RΓ(Spec Ω, s⁻¹ M) ≅ M_s` naturally in `M ∈ D(Y_étale, Λ)`: over `Spec Ω`
the derived global sections are global sections applied degreewise
(`Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnboundedIsoOfIsSepClosed`), and the
composite of the exact functors `s⁻¹` and `Γ(Spec Ω, -)` is the stalk at `s`
(`Stacks.EtaleCohomology.etaleModuleInverseImageGlobalSectionsIsoSheafFiber`). -/
def etaleModuleDerivedInverseImageGlobalSectionsIsoDerivedStalk :
    etaleModuleRingDerivedInverseImage.{u, r} Λ s ⋙
        etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of Ω)) ≅
      (((pointSmallEtale s).ulift.{max (u + 1) r}).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapDerivedCategory :=
  haveI := isEquivalence_etaleModuleGlobalSections_of_isSepClosed.{u, r} Λ Ω
  Functor.isoWhiskerLeft _ (etaleModuleDerivedGlobalSectionsUnboundedIsoOfIsSepClosed.{u, r} Λ Ω) ≪≫
    (DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
    DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModuleInverseImageGlobalSectionsIsoSheafFiber.{u, r} Λ Ω s)

end AlternativeStalk

/-! ### Tag 0GK0 -/

section GeometricFibre

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (y : GeometricPoint Y)

/-- **[Stacks, Tag 0GK0] for `K` bounded below with torsion cohomology, granted the proper base
change theorem.** Let `f : X ⟶ Y` be a separated morphism of finite type with a compactification
`j`, let `Λ` be a ring and let `ȳ : Spec k ⟶ Y` be a geometric point, with geometric fibre
`f_ȳ : X_ȳ ⟶ Spec k`. For every `K` in `D(X_étale, Λ)` bounded below whose cohomology sheaves are
torsion there is a canonical isomorphism
```
(Rf_! K)_ȳ ≅ RΓ_c(X_ȳ, K|_{X_ȳ})
```
in `D(Λ)`, where `(-)_ȳ` is the derived stalk `Stacks.EtaleCohomology.etaleModuleDerivedStalk`
and `RΓ_c(X_ȳ, -)` is computed through the base change of `j`.

It is the base change isomorphism `ȳ⁻¹ Rf_! K ≅ Rf_{ȳ,!}(K|_{X_ȳ})` of Tag 0F7L under
`RΓ(Spec k, -)`, `Stacks.EtaleCohomology.derivedLowerShriekUnboundedGeometricFibreIso`, composed
with the alternative description `RΓ(Spec k, ȳ⁻¹ -) ≅ (-)_ȳ` of the stalk (Tag 04JN,
`Stacks.EtaleCohomology.etaleModuleDerivedInverseImageGlobalSectionsIsoDerivedStalk`).

closing step: `h095T` is Stacks Tag 095T. -/
def derivedLowerShriekUnboundedStalkIso
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) [K.IsGE n]
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) r} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K)) :
    (etaleModuleDerivedStalk.{u, r} Λ y).obj ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K) ≅
      (compactlySupportedCohomologyUnbounded.{u, r} y.residueField (pullback.snd f y.hom)
          (j.baseChange (IsPullback.of_hasPullback f y.hom)) Λ).obj
        ((etaleModuleRingDerivedInverseImage.{u, r} Λ (pullback.fst f y.hom)).obj K) :=
  ((etaleModuleDerivedInverseImageGlobalSectionsIsoDerivedStalk.{u, r} Λ y.residueField
      y.hom).app ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K)).symm ≪≫
    derivedLowerShriekUnboundedGeometricFibreIso.{u, r} Λ f j y h095T K n hK

end GeometricFibre

end Stacks.EtaleCohomology

end
