module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.NagataConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CompactSupportCurveFiniteness
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexAlgebra
public import StacksFrontier.Algebra.Homology.DerivedCategory.WeakSerreClassRightDerivedFunctorPlus
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.DirectImage

/-!
# Finite compactly supported cohomology over an algebraically closed field, in any dimension

Let `k` be an algebraically closed field, `X` a separated scheme of finite type over `k`, `ℓ` a
prime and `F` a constructible sheaf of `ℤ/ℓᵐ`-modules on `X_étale`. Then `H^q_c(X, F)` is a finite
`ℤ/ℓᵐ`-module for every `q`.

This is the consequence of Stacks 0GL0 for `X ⟶ Spec k`: the cohomology sheaves of `Rf_! F` are
constructible on `Spec k`, and `H^q_c(X, F)` is `H^q(RΓ(Spec k, Rf_! F))`, which is assembled from
the finite modules `H^p(Spec k, G)` of constructible sheaves `G` on `Spec k` (Stacks 0GKR for
`Spec k` itself) by the dévissage of Stacks 015J. Stacks 0GL0 is used over the Nagata scheme
`Spec k` (`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_plus_of_isNagataScheme`),
and Stacks 0GKV enters through it as the hypothesis `h0GKV`.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.module_finite_compactlySupportedCohomologyGroup_zmod`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

attribute [-instance] hasSheafifyEtale

attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

namespace TorsionModules

/-- **Finite compactly supported cohomology over an algebraically closed field, in any
dimension, from Stacks 0GKV.** Let `k` be an algebraically closed field, `X` a separated scheme of
finite type over `k`, `j` a compactification of `X` over `k`, `ℓ` a prime, `m : ℕ`, and `F` a
constructible sheaf of `ℤ/ℓᵐ`-modules on `X_étale` (it is torsion). Then `H^q_c(X, F)` is a finite
`ℤ/ℓᵐ`-module for every `q`. This is Stacks 0GKR without the bound on the dimension of `X`, for
the coefficient rings `ℤ/ℓᵐ`; it follows from Stacks 0GL0. `h0GKV` is Stacks 0GKV. -/
theorem module_finite_compactlySupportedCohomologyGroup_zmod {k : Type u} [Field k]
    [IsAlgClosed k] (B : BigEtaleSite.{u}) (X : B.Scheme) (f : X.obj ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (j : CompactificationOf (Over.mk f))
    (ℓ m : ℕ) [Fact ℓ.Prime]
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (F : EtaleModules.{u, 0} (ZMod (ℓ ^ m)) X.obj)
    (hc : IsBigSiteConstructibleEtaleModule B X (ZMod (ℓ ^ m)) F)
    (ht : IsTorsionEtaleModule (ZMod (ℓ ^ m)) X.obj F) (q : ℤ) :
    Module.Finite (ZMod (ℓ ^ m)) ((compactlySupportedCohomologyGroup.{u, 0} k f j
      (ZMod (ℓ ^ m)) q).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  let Λ := ZMod (ℓ ^ m)
  have hpos : 0 < ℓ ^ m := pow_pos (Fact.out : ℓ.Prime).pos m
  have hΛ : ((ℓ ^ m : ℕ) : Λ) = 0 := ZMod.natCast_self _
  by_cases hX : Nonempty X.obj
  swap
  · -- an empty `X` has dimension `⊥ ≤ 1`, so this is Stacks 0GKR
    rw [not_nonempty_iff] at hX
    exact module_finite_compactlySupportedCohomologyGroup B X f
      (by rw [(topologicalKrullDim_eq_bot_iff_isEmpty X.obj).mpr hX]; exact bot_le) j Λ F hc ht q
  -- `Spec k` is a Noetherian Nagata scheme of `B`
  have : Flat f := Stacks.KunnethLowDegree.flat_of_spec_field f
  have : Surjective f := ⟨fun t => by
    obtain ⟨x⟩ := hX
    exact ⟨x, Subsingleton.elim _ _⟩⟩
  have hk : B.Contains (Spec (.of k)) :=
    Scheme.size_lt_of_flat_of_surjective_of_isStrongPrelimit B.cutoff_isStrongPrelimit f
      X.property
  let K : B.Scheme := B.obj (Spec (.of k)) hk
  have : IsNoetherian K.obj := inferInstanceAs (IsNoetherian (Spec (.of k)))
  have hKN : IsNagataScheme K.obj := isNagataScheme_spec_of_field k
  -- the cohomology sheaves of `Rf_! F` are constructible on `Spec k`
  let L := (derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  have hL : ∀ p : ℤ, IsBigSiteConstructibleEtaleModule B K Λ
      ((DerivedCategory.Plus.homologyFunctor _ p).obj L) := fun p =>
    isConstructibleEtaleModule_homology_derivedLowerShriek_plus_of_isNagataScheme B K hKN X f j Λ
      (ℓ ^ m) hpos hΛ h0GKV _ (fun q' => isConstructibleEtaleModule_homology_singleFunctor hc q') p
  -- the cohomology of constructible sheaves on `Spec k` is finite (Stacks 0GKR for `Spec k`)
  have hdim0 : topologicalKrullDim K.obj ≤ 1 := by
    change topologicalKrullDim (PrimeSpectrum k) ≤ 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      ringKrullDim_eq_zero_of_isField (Field.toIsField k)]
    exact zero_le_one
  have hF0 : ∀ M : EtaleModules.{u, 0} Λ K.obj, IsBigSiteConstructibleEtaleModule B K Λ M → ∀ p : ℕ,
      Module.Finite Λ (((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of k))).rightDerived p).obj M) :=
    fun M hM p => by
    let j₀ := CompactificationOf.ofProper (𝟙 (Spec (.of k)))
    have h := module_finite_compactlySupportedCohomologyGroup B K (𝟙 (Spec (.of k))) hdim0 j₀ Λ M
      hM (isTorsionEtaleModule_of_natCast_eq_zero Λ (ℓ ^ m) hpos hΛ _) p
    exact Module.Finite.equiv ((compactlySupportedCohomologyGroupSingleIso Λ k (𝟙 _) j₀ p M ≪≫
      ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of k))).rightDerived p).mapIso
        ((etaleModuleExtensionByZeroIdIso Λ (Spec (.of k))).app M)).toLinearEquiv)
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B K Λ
  have := (etaleModuleGlobalSections.{u, 0} Λ
    (Spec (.of k))).derivedCategoryBPlus_rightDerivedFunctorPlus_obj
      (IsBigSiteConstructibleEtaleModule B K Λ) (AlgebraicGeometry.DeRhamTypeComplex.moduleFinite Λ) hF0 L hL
  exact this.2 q

end TorsionModules

end Stacks.EtaleCohomology

end
