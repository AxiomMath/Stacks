module

public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineChartPerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.CategoryTheory.Sites.Modules.LinearOfUnitEndomorphisms
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExactAlongAnIsomorphism
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackUnit
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# The ring model of a module on an affine chart

Let `T` be an object of the big fppf site whose scheme `T₀` is affine, with ring of functions
`A = Γ(T₀, 𝒪)`.  The functor

`Φ : Mod(A) ⥤ Mod(𝒪_{h_T})`,  `M ↦ ε^*(isoSpec^*(M̃))`,

from `A`-modules to modules on the small étale site of the algebraic space `h_T` represented by
`T` is the composite of the associated sheaf on `Spec A`, the pullback along
`isoSpec : T₀ ≅ Spec A`, and the comparison `ε^*` of Zariski and étale modules.  It is exact,
preserves colimits and carries `A` to `𝒪`; so it induces a ring homomorphism
`A →+* Γ(h_T, 𝒪)` for which it is `A`-linear (`Stacks.SheafOfModules.linear_of_unitIso`).  Every
object of `D(𝒪_{h_T})` with quasi-coherent cohomology is `Φ` of an object of `D(A)`, and `Φ`
carries perfect objects to perfect objects.

## Main definitions

* `AlgebraicGeometry.Space.chartRingModel`: the functor `Φ`.
* `AlgebraicGeometry.Space.chartModelRingHom`: the induced ring homomorphism `A →+* Γ(h_T, 𝒪)`.
* `AlgebraicGeometry.Space.chartModelLinear`: the induced `A`-linear structure on
  `𝒪_{h_T}`-modules.

## Main results

* `AlgebraicGeometry.Space.chartRingModel_linear`: `Φ` is `A`-linear.
* `AlgebraicGeometry.Space.exists_chartRingModel_iso`: every object with quasi-coherent
  cohomology has a ring model.
* `AlgebraicGeometry.Space.isPerfect_chartRingModel`: `Φ` preserves perfectness.

## References

* [Stacks Project, Tag 08IS](https://stacks.math.columbia.edu/tag/08IS)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] SmallEtale.preservesFiniteLimits_associatedModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- The isomorphism `T₀ ≅ Spec Γ(T₀, 𝒪)` of the ringed spaces underlying an affine scheme. -/
abbrev chartSpecIso [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] :
    ((BigFppfOver.toScheme B S hS).obj T).toLocallyRingedSpace.toRingedSpace ≅
      (Spec Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)).toLocallyRingedSpace.toRingedSpace :=
  Stacks.Cohomology.TransportAlongIso.ringedSpaceIsoOfSchemeIso
    ((BigFppfOver.toScheme B S hS).obj T).isoSpec

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The associated sheaf on `Spec A`, as a functor to modules over the structure sheaf of the
underlying ringed space. -/
abbrev chartTilde :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) ⥤
      SheafOfModules.{u} (structureSheafRing
        (Spec Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)).toLocallyRingedSpace.toRingedSpace) :=
  tilde.functor Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)

/-- The comparison `ε^*`, as a functor out of modules over the structure sheaf of the ringed
space underlying `T₀`. -/
abbrev chartAssociated :
    SheafOfModules.{u} (structureSheafRing
        ((BigFppfOver.toScheme B S hS).obj T).toLocallyRingedSpace.toRingedSpace) ⥤
      Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) :=
  representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)

/-- The associated-sheaf functor on `Spec A` is additive. -/
instance : (chartTilde B S hS T).Additive :=
  inferInstanceAs (tilde.functor _).Additive

/-- The associated-sheaf functor on `Spec A` preserves finite limits. -/
instance : PreservesFiniteLimits (chartTilde B S hS T) :=
  have := AlgebraicGeometry.tilde.preservesFiniteLimits Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
  inferInstanceAs (PreservesFiniteLimits (tilde.functor _))

/-- The associated-sheaf functor on `Spec A` preserves finite colimits. -/
instance : PreservesFiniteColimits (chartTilde B S hS T) :=
  have := Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor
    Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
  inferInstanceAs (PreservesFiniteColimits (tilde.functor _))

/-- The associated-sheaf functor on `Spec A` preserves colimits. -/
instance : PreservesColimitsOfSize.{u, u} (chartTilde B S hS T) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u} (tilde.functor _))

/-- The comparison `ε^*` is additive. -/
instance : (chartAssociated B S hS T).Additive :=
  inferInstanceAs (representedAssociatedModule B S hS T _).Additive

/-- The comparison `ε^*` preserves finite limits. -/
instance : PreservesFiniteLimits (chartAssociated B S hS T) :=
  inferInstanceAs (PreservesFiniteLimits (SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙ representedModulePushforward B S hS T))

/-- The comparison `ε^*` preserves finite colimits. -/
instance : PreservesFiniteColimits (chartAssociated B S hS T) :=
  inferInstanceAs (PreservesFiniteColimits (SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙ representedModulePushforward B S hS T))

/-- The comparison `ε^*` preserves colimits. -/
instance : PreservesColimitsOfSize.{u, u} (chartAssociated B S hS T) := by
  have : (representedModulePushforward B S hS T).IsEquivalence :=
    inferInstanceAs (representedModuleEquivalence.{u, u} B S hS T).functor.IsEquivalence
  exact inferInstanceAs (PreservesColimitsOfSize.{u, u}
    (SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
        representedModulePushforward B S hS T))

/-- Module pullback along `isoSpec : T₀ ≅ Spec A` preserves colimits. -/
instance : PreservesColimitsOfSize.{u, u}
    (RingedSpaceModuleAdjunction.modulePullback (chartSpecIso B S hS T).hom) := by
  have := Stacks.Cohomology.modulePullbackIso_isEquivalence (chartSpecIso B S hS T)
  infer_instance

/-- **The ring model functor** `Φ : Mod(A) ⥤ Mod(𝒪_{h_T})`, `M ↦ ε^*(isoSpec^*(M̃))`, for
`A = Γ(T₀, 𝒪)`. -/
def chartRingModel :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) ⥤
      Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) :=
  chartTilde B S hS T ⋙
    RingedSpaceModuleAdjunction.modulePullback (chartSpecIso B S hS T).hom ⋙
    chartAssociated B S hS T

/-- The ring model functor `Φ` is additive. -/
instance : (chartRingModel B S hS T).Additive := by
  dsimp only [chartRingModel]
  infer_instance

/-- The ring model functor `Φ` preserves finite limits. -/
instance : PreservesFiniteLimits (chartRingModel B S hS T) := by
  dsimp only [chartRingModel]
  infer_instance

/-- The ring model functor `Φ` preserves finite colimits. -/
instance : PreservesFiniteColimits (chartRingModel B S hS T) := by
  dsimp only [chartRingModel]
  infer_instance

/-- The ring model functor `Φ` preserves colimits. -/
instance : PreservesColimitsOfSize.{u, u} (chartRingModel B S hS T) := by
  dsimp only [chartRingModel]
  infer_instance

/-- `Φ(A) ≅ 𝒪`. -/
def chartRingModelUnitIso :
    (chartRingModel B S hS T).obj (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O) :=
  (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).mapIso
      (RingedSpaceModuleAdjunction.modulePullbackUnitIso (chartSpecIso B S hS T).hom) ≪≫
    representedAssociatedModuleObjUnitIso B S hS T (isAlgebraicSpace_yoneda B S hS T)

/-- **The ring homomorphism `Γ(T₀, 𝒪) →+* Γ(h_T, 𝒪)` induced by the ring model functor.** -/
def chartModelRingHom :
    Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+*
      Stacks.Cohomology.SiteModules.GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O) :=
  Stacks.SheafOfModules.unitIsoRingHom _ (chartRingModel B S hS T) (chartRingModelUnitIso B S hS T)

/-- **The `Γ(T₀, 𝒪)`-linear structure on modules over the algebraic space `h_T`** induced by the
ring model functor. -/
@[instance_reducible]
def chartModelLinear :
    Linear Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :=
  Stacks.SheafOfModules.linearOver _ (chartModelRingHom B S hS T)

/-- **The ring model functor is `Γ(T₀, 𝒪)`-linear.** -/
theorem chartRingModel_linear :
    letI := chartModelLinear B S hS T
    (chartRingModel B S hS T).Linear Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  Stacks.SheafOfModules.linear_of_unitIso _ (chartRingModel B S hS T)
    (chartRingModelUnitIso B S hS T)

/-! ### The ring model on derived categories -/

/-- **`Φ` on derived categories is `ε^* ∘ L isoSpec^* ∘ (-)~`.** -/
def chartRingModelDerivedIso (M : DerivedCategory (ModuleCat.{u}
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))) :
    (chartRingModel B S hS T).mapDerivedCategory.obj M ≅
      (representedDerivedAssociatedModule B S hS T).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (chartSpecIso B S hS T).hom).obj
          ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)).mapDerivedCategory.obj M)) :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso (chartTilde B S hS T)
      (RingedSpaceModuleAdjunction.modulePullback (chartSpecIso B S hS T).hom ⋙
        chartAssociated B S hS T)).app M ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (RingedSpaceModuleAdjunction.modulePullback (chartSpecIso B S hS T).hom)
        (chartAssociated B S hS T)).app _ ≪≫
    (chartAssociated B S hS T).mapDerivedCategory.mapIso
      ((Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIsoMapDerivedCategory
        (chartSpecIso B S hS T)).symm.app _)

/-- **Every object `K` of `D(𝒪_{h_T})` with quasi-coherent cohomology has a ring model**: there
are an object `ω` of `D(T₀)` with quasi-coherent cohomology and an `M ∈ D(A)` such that
`ε^*ω ≅ K`, the pullback of `ω` to `Spec A` is isomorphic to `M̃`, and `Φ(M) ≅ K`. -/
theorem exists_chartRingModel_iso
    (K : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)).O))) K) :
    ∃ (ω : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω).IsQuasicoherent) ∧
      Nonempty ((representedDerivedAssociatedModule B S hS T).obj ω ≅ K) ∧
      Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (chartSpecIso B S hS T).inv).obj ω ≅
        (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)).mapDerivedCategory.obj M) ∧
      Nonempty ((chartRingModel B S hS T).mapDerivedCategory.obj M ≅ K) := by
  obtain ⟨ω, hωqc, ⟨eω⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS T K hK
  have hqc' := fun i : ℤ =>
    Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
      ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv ω hωqc i
  obtain ⟨M, ⟨eM⟩⟩ :=
    Stacks.AffineTilde.exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard
      (R := Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (chartSpecIso B S hS T).inv).obj ω) hqc'
  refine ⟨ω, M, hωqc, ⟨eω⟩, ⟨eM.symm⟩, ⟨?_⟩⟩
  exact chartRingModelDerivedIso B S hS T M ≪≫
    (representedDerivedAssociatedModule B S hS T).mapIso
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (chartSpecIso B S hS T).hom).mapIso eM ≪≫
        (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackInvHomIso
          (chartSpecIso B S hS T)).app ω) ≪≫ eω

/-- **The ring model functor carries perfect complexes to perfect objects.** -/
theorem isPerfect_chartRingModel
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)))
    (hM : StacksDraft.Perfect.IsPerfect M) :
    (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).IsPerfect
      ((chartRingModel B S hS T).mapDerivedCategory.obj M) := by
  have h₁ := (isPerfect_tilde_iff M).2 hM
  have h₂ := (Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_scheme_iff
    ((BigFppfOver.toScheme B S hS).obj T).isoSpec _).2 h₁
  obtain ⟨K, hK, ⟨e⟩⟩ := isPerfect_representedDerivedAssociatedModule B S hS T _ h₂
  exact ⟨K, hK, ⟨e ≪≫ (chartRingModelDerivedIso B S hS T M).symm⟩⟩

/-- **A ring model of a pseudo-coherent Zariski model is pseudo-coherent.** -/
theorem isPseudoCoherent_of_chartRingModel
    (ω : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)))
    (e : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (chartSpecIso B S hS T).inv).obj ω ≅
        (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)).mapDerivedCategory.obj M)
    (hω : RingedSpace.IsPseudoCoherent
      (X := ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace) ω) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent M := by
  refine (isPseudoCoherent_mapDerivedCategory_tilde_iff M).1 ?_
  exact (RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback
    (chartSpecIso B S hS T).inv ω hω).of_iso e

end AlgebraicGeometry.Space

end
