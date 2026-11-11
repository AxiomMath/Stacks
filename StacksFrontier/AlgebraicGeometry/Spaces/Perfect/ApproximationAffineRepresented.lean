module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ModulesAtSchemeUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtalePerfectForward
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedOpenSubspaceAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedPerfectPseudoCoherentTransport
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentDescent
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.AffineCover
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparisonConverse
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens
import StacksCore.Tactic.StacksAttribute

/-!
# Approximation on an algebraic space representable by an affine scheme

Let `S` be a scheme and let `X = h_U = yoneda.obj U` be the algebraic space represented by an
object `U` of the big fppf site over `S` whose underlying scheme `T` is affine. Then
approximation holds for every triple `(Z, E, m)` for which there is an integer `r ≥ 0` with

1. `E` is `m`-pseudo-coherent,
2. `Hⁱ(E)` is supported on `Z` for `i ≥ m - r + 1`,
3. `X ∖ Z` is the union of `r` affine opens,

and in particular approximation by perfect complexes holds for `X`. Both are deduced from the
corresponding statements on `T` by pulling back along the comparison `ε : X_étale ⟶ T_Zar`,
whose pullback is `AlgebraicGeometry.Space.representedDerivedAssociatedModule`.

## Main results

* `AlgebraicGeometry.Space.approximationHolds_of_isAffine_represented`: approximation holds for a
  triple `(Z, E, m)` as above, at `X = h_U`.
* `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_isAffine_represented`:
  approximation by perfect complexes holds at `X = h_U`.

## References

* [Stacks Project, Tag 08HM](https://stacks.math.columbia.edu/tag/08HM)
* [Stacks Project, Tag 08HI](https://stacks.math.columbia.edu/tag/08HI)
* [Stacks Project, Tag 08HJ](https://stacks.math.columbia.edu/tag/08HJ)
* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] pointTopology SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance 10000] SmallEtale.hasSheafify_smallEtale
  SmallEtale.wEqualsLocallyBijective_smallEtale SmallEtale.hasSheafify_smallEtaleOver
  SmallEtale.wEqualsLocallyBijective_smallEtaleOver smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over


attribute [local instance 10000] smallEtaleModulesAbelianAtSchemeUniverse
  smallEtaleModulesHasDerivedCategory

/-- The support of a cohomology sheaf of `ε^*K`, for `K` with quasi-coherent cohomology in that
degree, is the preimage of the support of the corresponding cohomology sheaf of `K`. -/
theorem mem_supportOfSheaf_homology_representedDerivedAssociatedModule_iff
    (K : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Modules) (i : ℤ)
    (hK : ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent)
    (p : points B S hS (yoneda.obj U)) :
    p ∈ supportOfSheaf B S hS (yoneda.obj U)
        ((SheafOfModules.toSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (yoneda.obj U)
            (isAlgebraicSpace_yoneda B S hS U)) i).obj
              ((representedDerivedAssociatedModule B S hS U).obj K))) ↔
      ¬ IsZero (TopCat.Presheaf.stalk (X := (BigFppfOver.toScheme B S hS).obj U)
          ((DerivedCategory.homologyFunctor _ i).obj K).val.presheaf
          (schemePointsHomeomorph B S hS U p)) :=
  (Set.ext_iff.1 (supportOfSheaf_eq_of_sheafIso B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) ((SheafOfModules.toSheaf _).mapIso
      (((representedAssociatedModule B S hS U
        (isAlgebraicSpace_yoneda B S hS U)).mapDerivedCategoryHomologyIso i).app K))) p).trans
    (mem_supportOfSheaf_representedAssociatedModule_iff B S hS U _ hK p)

/-- Let `ε^*E₀ ≅ E`. If the support of `Hⁱ(E)` lies in `Z`, then `Hⁱ(E₀)` vanishes at every point
of `T` outside the image of `Z`. -/
theorem isZero_stalk_homology_of_supportOfSheaf_subset
    (E : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    (E₀ : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (eE : (representedDerivedAssociatedModule B S hS U).obj E₀ ≅ E.obj)
    (hqc₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E₀).IsQuasicoherent)
    (Z : Set (points B S hS (yoneda.obj U))) (i : ℤ)
    (h : supportOfSheaf B S hS (yoneda.obj U)
        ((SheafOfModules.toSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (yoneda.obj U)
            (isAlgebraicSpace_yoneda B S hS U)) i).obj E.obj)) ⊆ Z)
    (x : (BigFppfOver.toScheme B S hS).obj U) (hx : x ∉ schemePointsHomeomorph B S hS U '' Z) :
    IsZero (TopCat.Presheaf.stalk (X := (BigFppfOver.toScheme B S hS).obj U)
      ((DerivedCategory.homologyFunctor _ i).obj E₀).val.presheaf x) := by
  obtain ⟨p, rfl⟩ := (schemePointsHomeomorph B S hS U).surjective x
  by_contra hne
  refine hx ⟨p, h ?_, rfl⟩
  exact (Set.ext_iff.1 (supportOfSheaf_eq_of_sheafIso B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) ((SheafOfModules.toSheaf _).mapIso
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)) i).mapIso eE))) p).1
    ((mem_supportOfSheaf_homology_representedDerivedAssociatedModule_iff B S hS U E₀ i
      (hqc₀ i) p).2 hne)

/-- If `ε^*E₀ ≅ E` and `E` is `m`-pseudo-coherent, then so is `E₀`. -/
private theorem isPseudoCoherentFrom_of_iso_represented
    (E : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    (E₀ : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (eE : (representedDerivedAssociatedModule B S hS U).obj E₀ ≅ E.obj) (m : ℤ)
    (hpc : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherentFrom E.obj m) :
    RingedSpace.IsPseudoCoherentFrom
      (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) E₀ m := by
  obtain ⟨K, hK, ⟨f⟩⟩ := hpc
  exact isPseudoCoherentFrom_of_representedDerivedAssociatedModule B S hS U E₀ m
    ⟨K, hK, ⟨f ≪≫ eE.symm⟩⟩

/-- If approximation holds on `T` for the triple `(ρ(Z), E₀, m)` and `ε^*E₀ ≅ E`, then
approximation holds on `h_U` for `(Z, E, m)`. -/
theorem approximationHolds_of_approximationHolds_scheme
    (Z : Set (points B S hS (yoneda.obj U)))
    (E : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) (m : ℤ)
    (E₀ : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (eE : (representedDerivedAssociatedModule B S hS U).obj E₀ ≅ E.obj)
    (h : PerfectApproximation.ApproximationHolds ((BigFppfOver.toScheme B S hS).obj U)
      (schemePointsHomeomorph B S hS U '' Z) E₀ m) :
    ApproximationHolds B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) Z E m := by
  obtain ⟨P₀, hP₀, hsupp₀, α₀, hiso, hepi⟩ := h
  refine ⟨(representedDerivedAssociatedModule B S hS U).obj P₀,
    isPerfect_representedDerivedAssociatedModule B S hS U P₀ hP₀, ?_,
    (representedDerivedAssociatedModule B S hS U).map α₀ ≫ eE.hom, ?_, ?_⟩
  · intro i p hp
    rw [mem_supportOfSheaf_homology_representedDerivedAssociatedModule_iff B S hS U P₀ i
      (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ P₀ hP₀ i)] at hp
    by_contra hpZ
    exact hp (hsupp₀ i _ fun hmem =>
      hpZ (((schemePointsHomeomorph B S hS U).injective.mem_set_image).1 hmem))
  · intro i hi
    have h₁ := (representedAssociatedModule B S hS U
      (isAlgebraicSpace_yoneda B S hS U)).isIso_homologyFunctor_map_mapDerivedCategory_map α₀ i
        (hiso i hi)
    have h₂ := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) i).map_isIso eE.hom
    rw [Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
  · have h₁ := (representedAssociatedModule B S hS U
      (isAlgebraicSpace_yoneda B S hS U)).epi_homologyFunctor_map_mapDerivedCategory_map α₀ m hepi
    have h₂ := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) m).map_isIso eE.hom
    rw [Functor.map_comp]
    exact @epi_comp _ _ _ _ _ _ h₁ _ (@IsIso.epi_of_iso _ _ _ _ _ h₂)

/-! ### Approximation at a represented algebraic space -/

/-- Let `S` be a scheme and let `X = h_U` be the algebraic space represented by an object `U` with
affine underlying scheme. Then approximation holds for every triple `(Z, E, m)` for which there
is an integer `r ≥ 0` with

1. `E` `m`-pseudo-coherent,
2. `Hⁱ(E)` supported on `Z` for `i ≥ m - r + 1`,
3. `X ∖ Z` the union of `r` affine opens `V₁, …, V_r` of `X`. -/
theorem approximationHolds_of_isAffine_represented
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (Z : Set (points B S hS (yoneda.obj U)))
    (E : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) (m : ℤ) (r : ℕ)
    (hpc : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherentFrom E.obj m)
    (hsupp : ∀ i : ℤ, m - (r : ℤ) + 1 ≤ i →
      supportOfSheaf B S hS (yoneda.obj U)
        ((SheafOfModules.toSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (yoneda.obj U)
            (isAlgebraicSpace_yoneda B S hS U)) i).obj E.obj)) ⊆ Z)
    (V : Fin r → {G : Subfunctor (yoneda.obj U) // IsOpenSubspace B S hS G})
    (hV : ∀ k, IsAffineSpace B S hS (V k).1.toFunctor)
    (hcover : ⋃ k, Set.range (pointsMap B S hS (V k).1.toFunctor (V k).1.ι) = Zᶜ) :
    ApproximationHolds B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) Z E m := by
  obtain ⟨E₀, hqc₀, ⟨eE⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS U E.obj E.property
  refine approximationHolds_of_approximationHolds_scheme B S hS U Z E m E₀ eE
    (PerfectApproximation.approximationHolds_of_affineCover _ _
      (fun k => opensOfOpenSubspace B S hS U (V k).1 (V k).2)
      (fun k => isAffineOpen_opensOfOpenSubspace B S hS U (V k).1 (V k).2 (hV k)) ?_ E₀ m hqc₀
      ?_ fun i hi x hx => isZero_stalk_homology_of_supportOfSheaf_subset B S hS U E E₀ eE hqc₀ Z i
        (hsupp i hi) x hx)
  · rw [TopologicalSpace.Opens.coe_iSup]
    simp_rw [coe_opensOfOpenSubspace]
    rw [← Set.image_iUnion, hcover, Set.image_compl_eq (schemePointsHomeomorph B S hS U).bijective]
  · exact isPseudoCoherentFrom_of_iso_represented B S hS U E E₀ eE m hpc

/-- Approximation by perfect complexes holds on `h_U` for `U` with affine underlying scheme. -/
theorem approximationByPerfectComplexes_of_isAffine_represented
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] :
    ApproximationByPerfectComplexes.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) := by
  intro Z hZ hqc
  obtain ⟨hcl, hret⟩ := isClosed_image_and_isRetrocompact_compl B S hS U
    (isAlgebraicSpace_yoneda B S hS U) Z hZ hqc
  obtain ⟨r, hr⟩ := PerfectApproximation.approximationByPerfectComplexes_of_isAffine
    ((BigFppfOver.toScheme B S hS).obj U) _ hcl hret
  refine ⟨r, fun E m hpc hsupp => ?_⟩
  obtain ⟨E₀, hqc₀, ⟨eE⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS U E.obj E.property
  exact approximationHolds_of_approximationHolds_scheme B S hS U Z E m E₀ eE
    (hr E₀ m hqc₀ (isPseudoCoherentFrom_of_iso_represented B S hS U E E₀ eE _ hpc)
      fun i x hi hx => isZero_stalk_homology_of_supportOfSheaf_subset B S hS U E E₀ eE hqc₀ Z i
        (hsupp i hi) x hx)

end AlgebraicGeometry.Space

end
