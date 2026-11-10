module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictedCohomologyDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafPullback
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFundamentalExactSequence
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.SuccBijective

/-!
# Comparing `H^i(π₁(X_K), M)` with `H^i(X_K, ℱ_M)`

Let `X` be a connected scheme over a field `k` and `K/k` an extension with `X_K` connected, and
`Λ` a finite ring. On finite `Λ`-modules `M` with a continuous action of
`π₁(X, y)` (for `y` a geometric point of `X_K`) there are two cohomological δ-functors:

* the group side `M ↦ H^i(π₁(X_K, y), M)`
  (`AlgebraicGeometry.geometricGroupCohomology`, built from
  `Stacks.ContinuousCohomology.restrictedCohomologyDelta`), and
* the étale side `M ↦ H^i(X_K, ℱ_M)` (`AlgebraicGeometry.geometricRepresentationCohomology`).

In degree zero both are `M ↦ M^{π₁(X_K, y)}` (Tag 03VL,
`AlgebraicGeometry.geometricGlobalSectionsIsoInvariants`). When `K` is an algebraic closure of
`k` and `X` is quasi-compact and quasi-separated, `π₁(X_K) → π₁(X)` is a topological embedding
(Tag 0BTX), so the group side is universal and there is a unique morphism of δ-functors
`AlgebraicGeometry.geometricComparison` extending the degree-zero identification. It is bijective
in degree one, the étale side being effaced there by finite étale covers of `X`
(`AlgebraicGeometry.exists_unit_map_eq_zero_of_eq_one`).

## Main definitions

* `AlgebraicGeometry.geometricGroupCohomology` — the group side.
* `AlgebraicGeometry.geometricComparisonZero` — the identification in degree zero.
* `AlgebraicGeometry.geometricComparison` — the morphism of δ-functors.

## Main results

* `AlgebraicGeometry.bijective_geometricComparison_app_zero` and
  `AlgebraicGeometry.bijective_geometricComparison_app_one` — `H^i(π₁(X_K), M) ≅ H^i(X_K, ℱ_M)` for
  `i ≤ 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- Enough injectives for continuous discrete modules at the module universe of the group, pinned:
the general instance is indexed by `max u v w`, which instance search cannot match with `u + 1`. -/
local instance (priority := 3000) enoughInjectives_continuousModule_groupUniverse (Λ : Type)
    [Ring Λ] (G : Type (u + 1)) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ G) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u + 1, 0} Λ G

section Invariants

variable (Λ : Type) [Ring Λ] {G Γ : Type (u + 1)} [Group G] [TopologicalSpace G]
  [Group Γ] [TopologicalSpace Γ] (φ : G →ₜ* Γ)

/-- The invariants of a finite module, read on the continuous discrete modules, are the invariants
of `Stacks.GroupCohomology.finiteTypeContinuousModuleInvariants`. -/
def continuousModuleInvariantsResIso :
    finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ Γ ⋙ continuousModuleRes.{0, u + 1, u + 1} Λ φ ⋙
        continuousModuleRingInvariants.{0, u + 1, u + 1} Λ G ≅
      finiteTypeContinuousModuleRes.{0, u + 1, u + 1} Λ φ ⋙
        finiteTypeContinuousModuleInvariants.{0, u + 1, u + 1} Λ G :=
  NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    { toFun := fun x ↦ ⟨x.1, fun g ↦ x.2 g⟩
      invFun := fun x ↦ ⟨x.1, fun g ↦ x.2 g⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl })
    (fun _ ↦ by ext; rfl)

/-- Raising the module universe from `u + 1` to `u + 1` is the identity, up to isomorphism. -/
def moduleCatUliftFunctorIsoId : ModuleCat.uliftFunctor.{0, u + 1} Λ ≅ 𝟭 (ModuleCat.{u + 1} Λ) :=
  NatIso.ofComponents (fun _ ↦ ULift.moduleEquiv.toModuleIso) (fun _ ↦ rfl)

end Invariants

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (Λ : Type) [Ring Λ]
  [Finite Λ] {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K] (hK : B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
  [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
  (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))

/-- The homomorphism `π₁(X_K, y) → π₁(X, y)` induced by the projection. -/
abbrev geometricFundamentalGroupMap :
    EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y →ₜ*
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom) :=
  etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f K hK).hom y

/-- **The group side `M ↦ H^i(π₁(X_K, y), M)`** on finite `Λ`-modules with a continuous action of
`π₁(X, y)`. -/
def geometricGroupCohomology :
    DeltaFunctor (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)))
      (ModuleCat.{u + 1} Λ) :=
  haveI := forall_finite_finiteEtaleFiberFunctor_obj y
  haveI := forall_finite_finiteEtaleFiberFunctor_obj (y.map (fieldBaseChangeObjProj B X f K hK).hom)
  restrictedCohomologyDelta Λ (geometricFundamentalGroupMap B X f K hK y)

/-- **The two δ-functors agree in degree zero**: both are the invariants under `π₁(X_K, y)`
(Tag 03VL). -/
def geometricComparisonZero :
    (geometricGroupCohomology B X Λ f K hK y).functor 0 ≅
      (geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
        Λ f K).functor 0 :=
  haveI := forall_finite_finiteEtaleFiberFunctor_obj y
  haveI := forall_finite_finiteEtaleFiberFunctor_obj (y.map (fieldBaseChangeObjProj B X f K hK).hom)
  Functor.isoWhiskerLeft
      (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y))
      (eqToIso (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor _ 0) ≪≫
        (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ _).rightDerivedZeroIsoSelf) ≪≫
    continuousModuleInvariantsResIso Λ (geometricFundamentalGroupMap B X f K hK y) ≪≫
    (Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (moduleCatUliftFunctorIsoId Λ) ≪≫
      Functor.rightUnitor _)).symm ≪≫
    (geometricGlobalSectionsIsoInvariants B X Λ f K hK y).symm ≪≫
    Functor.isoWhiskerLeft _ (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerivedZeroIsoSelf.symm ≪≫
    eqToIso (geometricRepresentationCohomology_functor B X _ Λ f K 0).symm

section Comparison

variable [IsAlgClosure k K] [CompactSpace X.1] [QuasiSeparatedSpace X.1]

/-- `π₁(X_K, y) → π₁(X, y)` is a topological embedding, for `K` an algebraic closure of `k`
(Tag 0BTX). -/
theorem isInducing_geometricFundamentalGroupMap :
    Topology.IsInducing (geometricFundamentalGroupMap B X f K hK y) :=
  have : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    inferInstanceAs (ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
  (topologicalShortExact_etaleFundamentalGroupMap_isAlgClosure k K f y).2.1.isInducing

/-- The group side is a universal δ-functor (`π₁(X_K) → π₁(X)` being an embedding). -/
theorem isUniversal_geometricGroupCohomology :
    (geometricGroupCohomology B X Λ f K hK y).IsUniversal :=
  have := forall_finite_finiteEtaleFiberFunctor_obj y
  have := forall_finite_finiteEtaleFiberFunctor_obj (y.map (fieldBaseChangeObjProj B X f K hK).hom)
  isUniversal_restrictedCohomologyDelta Λ _ (isInducing_geometricFundamentalGroupMap B X f K hK y)

/-- **The comparison morphism `H^i(π₁(X_K, y), M) ⟶ H^i(X_K, ℱ_M)`**: the unique morphism of
δ-functors out of the universal group side extending the degree-zero identification
`AlgebraicGeometry.geometricComparisonZero`. -/
def geometricComparison :
    geometricGroupCohomology B X Λ f K hK y ⟶
      geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
        Λ f K :=
  haveI := isUniversal_geometricGroupCohomology B X Λ f K hK y
  DeltaFunctor.IsUniversal.lift _ (geometricComparisonZero B X Λ f K hK y).hom

/-- In degree zero the comparison morphism is the identification
`AlgebraicGeometry.geometricComparisonZero`. -/
theorem geometricComparison_app_zero :
    (geometricComparison B X Λ f K hK y).app 0 = (geometricComparisonZero B X Λ f K hK y).hom :=
  have := isUniversal_geometricGroupCohomology B X Λ f K hK y
  DeltaFunctor.IsUniversal.lift_app_zero _ _

/-- **`H⁰(π₁(X_K, y), M) ≅ H⁰(X_K, ℱ_M)`** through the comparison morphism. -/
theorem bijective_geometricComparison_app_zero
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    Function.Bijective (((geometricComparison B X Λ f K hK y).app 0).app M) := by
  rw [geometricComparison_app_zero]
  exact ConcreteCategory.bijective_of_isIso ((geometricComparisonZero B X Λ f K hK y).hom.app M)

/-- **`H¹(π₁(X_K, y), M) ≅ H¹(X_K, ℱ_M)`** through the comparison morphism: both sides are effaced
in degree one, the group side by coinduction and the étale side by finite étale covers of `X`. -/
theorem bijective_geometricComparison_app_one
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    Function.Bijective (((geometricComparison B X Λ f K hK y).app 1).app M) := by
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  have := forall_finite_finiteEtaleFiberFunctor_obj y
  have := forall_finite_finiteEtaleFiberFunctor_obj (y.map (fieldBaseChangeObjProj B X f K hK).hom)
  have := elementwiseEffaceable_restrictedCohomologyDelta Λ
    (geometricFundamentalGroupMap B X f K hK y)
    (isInducing_geometricFundamentalGroupMap B X f K hK y)
  refine DeltaFunctor.bijective_app_succ _ 0 (bijective_geometricComparison_app_zero B X Λ f K hK y)
    (fun N x ↦ DeltaFunctor.ElementwiseEffaceable.exists_mono (F := restrictedCohomologyDelta Λ
      (geometricFundamentalGroupMap B X f K hK y)) x) (fun N ξ ↦ ?_) M
  obtain ⟨W, π, hπf, hπe, hπs, hξ⟩ := exists_unit_map_eq_zero_of_eq_one B X
    (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K N ξ
  exact exists_mono_geometricRepresentationCohomology_map_eq_zero_of_unit B X _ Λ f K ξ π hξ

end Comparison

end AlgebraicGeometry

end
