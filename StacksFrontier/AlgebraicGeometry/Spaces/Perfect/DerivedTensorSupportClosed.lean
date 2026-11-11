module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProjectionFormulaUnitHomSupported
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupportEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange

/-!
# The derived tensor product of an object supported on a closed subset

Let `X` be an algebraic space and `Z ⊆ |X|` closed. If `K ∈ D(𝒪_X)` is supported on `Z`
(Stacks 08GF), then so is `E ⊗^L K` for every `E ∈ D(𝒪_X)`: on the open complement `U` of `Z`,
`(E ⊗^L K)|_U = E|_U ⊗^L K|_U` vanishes with `K|_U`.

## Main results

* `AlgebraicGeometry.Space.isZero_etaleModulePullback_derivedTensor_of_disjoint`: the restriction
  of `E ⊗^L K` along an étale morphism whose image misses `Z` vanishes.
* `AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedTensor_of_right`: `E ⊗^L K` is
  supported on `Z`.

## References

* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The restriction of `E ⊗^L K` along an étale morphism missing the support of `K`
vanishes.** -/
theorem isZero_etaleModulePullback_derivedTensor_of_disjoint {X Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ X) (hg : IsEtale B S hS g.hom) (Z : Set (points B S hS X.1))
    (E K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : CohomologySupportedOn B S hS X.1 X.2 Z K)
    (hdisj : Disjoint (Set.range (pointsMap B S hS Y.1 g.hom)) Z) :
    IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj
      (((smallEtaleDerivedTensor B S hS X).obj E).obj K)) := by
  have hK1 : IsZero ((smallEtaleDerivedModulePullback B S hS g).obj K) :=
    (isZero_etaleModulePullback_mapDerivedCategory_of_disjoint B S hS g hg Z K hK hdisj).of_iso
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS g hg).app K)
  have hT : IsZero (((smallEtaleDerivedTensorProduct B S hS Y).tensor.obj
      ((smallEtaleDerivedModulePullback B S hS g).obj E)).obj
        ((smallEtaleDerivedModulePullback B S hS g).obj K)) := by
    let := (smallEtaleDerivedTensorProduct B S hS Y).commShift_right
      ((smallEtaleDerivedModulePullback B S hS g).obj E)
    have := (smallEtaleDerivedTensorProduct B S hS Y).exact_right
      ((smallEtaleDerivedModulePullback B S hS g).obj E)
    exact Functor.map_isZero _ hK1
  exact hT.of_iso (((smallEtaleDerivedModulePullbackIsoEtale B S hS g hg).app _).symm ≪≫
    (smallEtaleDerivedPullbackTensorIso g).app (E, K))

/-- **`E ⊗^L K` is supported on a closed subset supporting `K`** (Stacks 08GF): its restriction to
the open complement of `Z` vanishes, by
`AlgebraicGeometry.Space.isZero_etaleModulePullback_derivedTensor_of_disjoint`. -/
theorem cohomologySupportedOn_smallEtaleDerivedTensor_of_right {X : AlgebraicSpaces B S hS}
    (Z : Set (points B S hS X.1)) (hZ : IsClosed Z)
    (E K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : CohomologySupportedOn B S hS X.1 X.2 Z K) :
    CohomologySupportedOn B S hS X.1 X.2 Z (((smallEtaleDerivedTensor B S hS X).obj E).obj K) := by
  let O := (openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Zᶜ, hZ.isOpen_compl⟩
  let U : AlgebraicSpaces B S hS := ⟨O.1.toFunctor, O.2.1⟩
  let g : U ⟶ X := ObjectProperty.homMk O.1.ι
  have hg : IsEtale B S hS g.hom := isEtale_of_isOpenImmersion B S hS O.2.2
  have hrange : Set.range (pointsMap B S hS U.1 g.hom) = Zᶜ :=
    range_pointsMap_openSubspacesOrderIso_symm (X := X) Z hZ
  have h0 := isZero_etaleModulePullback_derivedTensor_of_disjoint g hg Z E K hK
    (by rw [hrange]; exact disjoint_compl_left)
  have := etaleModulePullback_additive.{u, u} B S hS g hg
  have := preservesFiniteLimits_etaleModulePullback B S hS g hg
  have := preservesFiniteColimits_etaleModulePullback B S hS g hg
  intro i x hx
  by_contra hxZ
  obtain ⟨y, rfl⟩ : x ∈ Set.range (pointsMap B S hS U.1 g.hom) := hrange ▸ hxZ
  have hH : IsZero ((etaleModulePullback.{u, u} B S hS g hg).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj K))) :=
    (Functor.map_isZero (DerivedCategory.homologyFunctor _ i) h0).of_iso
      (((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryHomologyIso i).app _).symm
  have hy := (supportOfSheaf_eq_empty_iff_isZero B S hS U _).2 hH
  rw [supportOfSheaf_toSheaf_etaleModulePullback] at hy
  exact (Set.eq_empty_iff_forall_notMem.1 hy) y hx

end AlgebraicGeometry.Space

end
