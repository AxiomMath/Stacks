module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.CurveConstructibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.FiniteCoefficients.ConstantCoefficientsOfIsUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage

/-!
# [Stacks, Tag 0GKX] for a module killed by an integer invertible on the base

The steps of the proof of Tag 0GKX in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.CurveConstructibility`
(the smooth proper part of the curve diagram of Tag 0GK7, the induction step on that diagram, the
generic step and the conclusion), for a finite `Λ`-module killed by an integer `n > 0` invertible
on the base. Then [Stacks, Tag 0GKV] is needed only at primes invertible on the base, through
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isUnit`.

## Main results

* `isConstructibleEtaleComplex_derivedLowerShriekUnbounded_constantSheaf_of_nsmul_of_isUnit`.

## References

* [Stacks Project, Tag 0GKX](https://stacks.math.columbia.edu/tag/0GKX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat
attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ] (M : ModuleCat.{u + 1} Λ)
  [Module.Finite Λ M]

/-- **The smooth proper part of the curve diagram of Tag 0GK7**, granted Tags 095T and 0GKV. Let
`q̄ : Ȳ ⟶ T` be proper and smooth with geometrically connected fibres of dimension at most one,
let `t : T ⟶ V` be finite étale over a Noetherian scheme, and let `j : U ⟶ Ȳ` be an open
immersion meeting every fibre of `q̄`. For a Noetherian ring `Λ` with `n · 1 = 0` and a finite
`Λ`-module `M`, `R(U ⟶ V)_! M̲` has constructible cohomology sheaves, computed through the
compactification `Ȳ` of `U` over `V`.

As in the source: the distinguished triangle of Tag 0GKP for `U ⊆ Ȳ` and the complement `Z`
reduces this to `R(Ȳ ⟶ V)_! M̲ = t_* Rq̄_* M̲`, which is constructible by Tag 0GKW and Tag 095H,
and to `R(Z ⟶ V)_! M̲`, where `Z ⟶ V` is quasi-finite because `U` is dense in the fibres of `q̄`.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV (Tag 0GKW is
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isUnit`
from it). -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_restrictOpen_ofIsProper_of_isUnit
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit ((ℓ : ℕ) : Γ(S, ⊤)) → ∀ (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {n : ℕ} (hn0 : 0 < n) (hM : ∀ m : M, n • m = 0)
    {Ybar T V U : Scheme.{u}} (qbar : Ybar ⟶ T) (t : T ⟶ V) [IsProper qbar] [Smooth qbar]
    [GeometricallyConnected qbar] (hqd : ∀ s, topologicalKrullDim (qbar.fiber s) ≤ 1)
    [IsFinite t] [Etale t] [IsNoetherian V] (jU : U ⟶ Ybar) [IsOpenImmersion jU]
    (hjU : ∀ s : T, ∃ y : U, qbar (jU y) = s) (hnV : IsUnit ((n : ℕ) : Γ(V, ⊤))) :
    IsConstructibleEtaleComplex Λ
      ((derivedLowerShriekUnbounded.{u, u + 1} (jU ≫ qbar ≫ t)
        ((CompactificationOf.ofIsProper (qbar ≫ t)).restrictOpen jU) Λ).obj
        (constantEtaleComplex Λ M U)) := by
  classical
  let Jbar := CompactificationOf.ofIsProper (qbar ≫ t)
  let iZ := complementClosedImmersion jU
  have hij : Set.range jU.base = (Set.range iZ.base)ᶜ := by
    rw [range_complementClosedImmersion, compl_compl]
  obtain ⟨a, b, c, hT⟩ := (exists_distTriang_derivedLowerShriek_openClosed.{u, u + 1} Λ Jbar jU iZ
    hij).2 (constantEtaleComplex Λ M Ybar)
  refine isConstructibleEtaleComplex_of_iso Λ
    ((derivedLowerShriekUnbounded.{u, u + 1} _ _ Λ).mapIso
      (constantEtaleComplexRestrictionIso Λ M jU))
    (isConstructibleEtaleComplex_obj₁_of_distinguished Λ _ hT ?_ ?_)
  · -- the middle term: `R(q̄ ≫ t)_* M̲ = t_* Rq̄_* M̲`
    show IsConstructibleEtaleComplex Λ ((etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ
      (qbar ≫ t)).obj ((etaleModuleDerivedExtensionByZeroUnbounded.{u, u + 1} Λ (𝟙 Ybar)).obj
        (constantEtaleComplex Λ M Ybar)))
    let e₁ : (etaleModuleDerivedExtensionByZeroUnbounded.{u, u + 1} Λ (𝟙 Ybar)).obj
        (constantEtaleComplex Λ M Ybar) ≅ constantEtaleComplex Λ M Ybar :=
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, u + 1} Λ (𝟙 Ybar)).app _ ≪≫
        ((etaleModuleExtensionByZero.{u, u + 1} Λ (𝟙 Ybar)).mapDerivedCategorySingleFunctor
          0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((etaleModuleExtensionByZeroIdIsoUnconditional Λ Ybar).app _)
    refine isConstructibleEtaleComplex_of_iso Λ
      ((etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ (qbar ≫ t)).mapIso e₁).symm ?_
    refine isConstructibleEtaleComplex_of_iso Λ
      ((etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, u + 1} Λ qbar t (qbar ≫ t)
        rfl).app _).symm fun q ↦ ?_
    refine (IsConstructibleEtaleModule Λ).prop_of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso
        ((etaleModuleDerivedDirectImageUnboundedIsoOfIsIntegralHom.{u, u + 1} Λ t).app _) ≪≫
        ((etaleModuleDirectImage.{u, u + 1} Λ t).mapDerivedCategoryHomologyIso q).app _).symm ?_
    exact isConstructibleEtaleModule_etaleModuleDirectImage_of_finite_of_etale Λ t _
      (isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isUnit h0GKV qbar
        (fun s ↦ hqd s) Λ M n hn0 hM (Stacks.Kummer.isUnit_natCast_of_hom t hnV) q)
  · -- the closed complement is quasi-finite over `V`
    have hdense : ∀ s, Dense ((qbar.fiberι s) ⁻¹' (jU.opensRange : Set Ybar)) := by
      intro s
      rw [dense_preimage_fiberι_iff]
      have hirr := isIrreducible_preimage_singleton_of_smooth qbar s
      have := isIrreducible_iff_irreducibleSpace.1 hirr
      obtain ⟨y, hy⟩ := hjU s
      exact IsOpen.dense (jU.opensRange.isOpen.preimage continuous_subtype_val)
        ⟨⟨jU y, hy⟩, ⟨y, rfl⟩⟩
    have : LocallyQuasiFinite (iZ ≫ qbar) :=
      locallyQuasiFinite_comp_of_dense_fiber qbar hqd jU.opensRange hdense iZ (by
        rw [range_complementClosedImmersion]
        exact subset_rfl)
    have : LocallyQuasiFinite (iZ ≫ qbar ≫ t) := by rw [← Category.assoc]; infer_instance
    have : LocallyOfFinitePresentation (iZ ≫ qbar ≫ t) :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
    have := Functor.isGE_obj_mapDerivedCategory (etaleModuleInverseImage.{u, u + 1} Λ iZ)
      (constantEtaleComplex Λ M Ybar) 0 inferInstance
    exact isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_locallyQuasiFinite Λ h095T
      (iZ ≫ qbar ≫ t) _ _ 0
      (torsionCohomologyProperty_etaleModuleForgetDerived_inverseImage.{u, u + 1} Λ iZ _
        (torsionCohomologyProperty_constantEtaleComplex Λ M hn0 hM Ybar))
      (isConstructibleEtaleComplex_etaleModuleDerivedInverseImage Λ iZ _
        (isConstructibleEtaleComplex_constantEtaleComplex Λ M Ybar))

/-- **The induction step of the proof of Tag 0GKX on the curve diagram of Tag 0GK7**, granted
Tags 095T and 0GKV. Let `p_V : X_V ⟶ V` be separated, quasi-compact and locally of finite type
over a Noetherian scheme, with fibres of dimension at most one, and let `t : T ⟶ V`,
`q̄ : Ȳ ⟶ T`, `j : Y ⟶ Ȳ`, `ν : Y ⟶ X_V` and `W ⊆ X_V` be as in Tag 0GK7 (`t` finite étale,
`q̄` smooth proper with geometrically connected fibres of dimension at most one, `j` an open
immersion, `ν` finite surjective with `ν ≫ p_V = j ≫ q̄ ≫ t`, `ν⁻¹(W) ⟶ W` a closed immersion,
and `ν⁻¹(W)` meeting every fibre of `j ≫ q̄`). Then `R(p_V)_! M̲` has constructible cohomology
sheaves, for every compactification of `p_V`.

As in the source: the triangle of Tag 0GKP for `W ⊆ X_V` and its complement `Z`, quasi-finite over
`V` because `W` is dense in the fibres of `p_V`, reduces this to `R(W ⟶ V)_! M̲`; since
`ν⁻¹(W) ⟶ W` is a thickening, Tag 0GKQ identifies that with `R(ν⁻¹(W) ⟶ V)_! M̲`, which is computed
through the compactification `Ȳ` of `ν⁻¹(W)` (Tag 0F7I) and handled by
`isConstructibleEtaleComplex_derivedLowerShriekUnbounded_restrictOpen_ofIsProper_of_isUnit`.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV (Tag 0GKW is
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isUnit`
from it). -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_curveDiagram_of_isUnit
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit ((ℓ : ℕ) : Γ(S, ⊤)) → ∀ (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {n : ℕ} (hn0 : 0 < n) (hM : ∀ m : M, n • m = 0)
    {XV V T Ybar Y : Scheme.{u}} (pV : XV ⟶ V) [IsSeparated pV] [QuasiCompact pV]
    [LocallyOfFiniteType pV] [IsNoetherian V] (hpd : ∀ s, topologicalKrullDim (pV.fiber s) ≤ 1)
    (JV : CompactificationOf (Over.mk pV)) (t : T ⟶ V) (qbar : Ybar ⟶ T) (jY : Y ⟶ Ybar)
    (ν : Y ⟶ XV) (W : XV.Opens) (hcomm : ν ≫ pV = jY ≫ qbar ≫ t) [IsFinite t] [Etale t]
    [Smooth qbar] [IsProper qbar] [GeometricallyConnected qbar]
    (hqd : ∀ s, topologicalKrullDim (qbar.fiber s) ≤ 1) [IsOpenImmersion jY] [IsFinite ν]
    [Surjective ν] (hW : IsClosedImmersion (ν ∣_ W))
    (hWs : ∀ s : T, ∃ y : Y, ν y ∈ W ∧ qbar (jY y) = s) (hnV : IsUnit ((n : ℕ) : Γ(V, ⊤))) :
    IsConstructibleEtaleComplex Λ
      ((derivedLowerShriekUnbounded.{u, u + 1} pV JV Λ).obj (constantEtaleComplex Λ M XV)) := by
  classical
  have : IsNoetherian XV := isNoetherian_of_locallyOfFiniteType pV
  have hfp : ∀ {Z : Scheme.{u}} (g : Z ⟶ V) [LocallyOfFiniteType g],
      LocallyOfFinitePresentation g :=
    fun g _ ↦ LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  -- density of `W` in the fibres
  have hO : IsOpen (ν ⁻¹' (W : Set XV)) := W.isOpen.preimage ν.continuous
  have hdense₁ : ∀ s : T, Dense (((jY ≫ qbar).fiberι s) ⁻¹' (ν ⁻¹' (W : Set XV))) :=
    dense_preimage_fiberι_of_smooth qbar jY hO hWs
  have hdense : ∀ s : V, Dense ((pV.fiberι s) ⁻¹' (W : Set XV)) :=
    dense_preimage_fiberι_of_surjective pV t (jY ≫ qbar) ν (by rw [hcomm, Category.assoc]) _
      hdense₁
  -- the triangle of `W ⊆ X_V` and its complement
  let iZ := complementClosedImmersion W.ι
  have hij : Set.range W.ι.base = (Set.range iZ.base)ᶜ := by
    rw [range_complementClosedImmersion, compl_compl]
  obtain ⟨a, b, c, hT⟩ := (exists_distTriang_derivedLowerShriek_openClosed.{u, u + 1} Λ JV W.ι iZ
    hij).2 (constantEtaleComplex Λ M XV)
  refine isConstructibleEtaleComplex_obj₂_of_distinguished Λ _ hT ?_ ?_
  · -- the open part: through the thickening `ν⁻¹(W) ⟶ W` and the compactification `Ȳ`
    let τ := ν ∣_ W
    have hτs : Function.Surjective τ.base := fun w ↦ by
      obtain ⟨y, hy⟩ := ν.surjective w.1
      exact ⟨⟨y, show ν y ∈ W from hy ▸ w.2⟩, Subtype.ext
        ((morphismRestrict_base_coe ν W ⟨y, show ν y ∈ W from hy ▸ w.2⟩).trans hy)⟩
    let JW := JV.restrictOpen W.ι
    let jU := (ν ⁻¹ᵁ W).ι ≫ jY
    have hg : τ ≫ W.ι ≫ pV = jU ≫ qbar ≫ t := by
      simp only [τ, jU, morphismRestrict_ι_assoc, Category.assoc, hcomm]
    let J₂ := CompactificationOf.ofEq hg
      ((CompactificationOf.ofIsProper (qbar ≫ t)).restrictOpen jU)
    have h₂ : IsConstructibleEtaleComplex Λ
        ((derivedLowerShriekUnbounded.{u, u + 1} (τ ≫ W.ι ≫ pV) J₂ Λ).obj
          (constantEtaleComplex Λ M (ν ⁻¹ᵁ W))) :=
      isConstructibleEtaleComplex_derivedLowerShriekUnbounded_restrictOpen_ofIsProper_of_isUnit Λ M
        h095T h0GKV hn0 hM qbar t hqd jU (fun s ↦ by
          obtain ⟨y, hy, hys⟩ := hWs s
          exact ⟨⟨y, hy⟩, hys⟩) hnV
    let K₁ := (etaleModuleRestriction.{u, u + 1} Λ W.ι).mapDerivedCategory.obj
      (constantEtaleComplex Λ M XV)
    refine isConstructibleEtaleComplex_of_iso Λ
      ((derivedLowerShriekUnboundedThickeningIso.{u, u + 1} Λ JW τ hτs).app K₁) ?_
    let e : (etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ τ).obj K₁ ≅
        constantEtaleComplex Λ M (ν ⁻¹ᵁ W) :=
      (etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ τ).mapIso
          (constantEtaleComplexRestrictionIso Λ M W.ι) ≪≫
        etaleModuleDerivedInverseImageSingleConstantIso Λ τ M
    show IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} (τ ≫ W.ι ≫ pV)
      (JW.restrictClosed τ) Λ).obj ((etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ τ).obj K₁))
    refine isConstructibleEtaleComplex_of_iso Λ
      ((derivedLowerShriekUnbounded.{u, u + 1} _ _ Λ).mapIso e).symm ?_
    exact isConstructibleEtaleComplex_of_iso Λ
      (derivedLowerShriekUnboundedCompactificationIsoUnconditional.{u, u + 1} Λ J₂
        (JW.restrictClosed τ) h095T
        (constantEtaleComplex Λ M (ν ⁻¹ᵁ W)) 0
        (torsionCohomologyProperty_constantEtaleComplex Λ M hn0 hM _)) h₂
  · -- the closed complement is quasi-finite over `V`
    have : LocallyQuasiFinite (iZ ≫ pV) :=
      locallyQuasiFinite_comp_of_dense_fiber pV hpd W hdense iZ (by
        rw [range_complementClosedImmersion, Scheme.Opens.range_ι])
    have := hfp (iZ ≫ pV)
    have := Functor.isGE_obj_mapDerivedCategory (etaleModuleInverseImage.{u, u + 1} Λ iZ)
      (constantEtaleComplex Λ M XV) 0 inferInstance
    exact isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_locallyQuasiFinite Λ h095T
      (iZ ≫ pV) _ _ 0
      (torsionCohomologyProperty_etaleModuleForgetDerived_inverseImage.{u, u + 1} Λ iZ _
        (torsionCohomologyProperty_constantEtaleComplex Λ M hn0 hM XV))
      (isConstructibleEtaleComplex_etaleModuleDerivedInverseImage Λ iZ _
        (isConstructibleEtaleComplex_constantEtaleComplex Λ M XV))

/-- **The generic step of the proof of Tag 0GKX**, granted Tags 095T and 0GKV. Let `S` be a
Noetherian scheme, `f : X ⟶ S` separated, quasi-compact and smooth of relative dimension one, and
`η` a generic point of an irreducible component of `S`. Then `Rf_! M̲` has constructible cohomology
sheaves over an open neighbourhood of `η`.

As in the source: Tag 0GK7 gives an open `U ∋ η`, a finite surjective universally injective
`V ⟶ U` and the curve diagram over `V`; by Tag 095Q it suffices to show that the inverse image of
`Rf_! M̲` to `V` is constructible, and by Tag 0F7L this is `R(X_V ⟶ V)_! M̲`, which is
`isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_curveDiagram_of_isUnit`.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV (Tag 0GKW is
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isUnit`
from it). -/
theorem
  exists_mem_isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_mem_genericPoints_of_isUnit
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit ((ℓ : ℕ) : Γ(S, ⊤)) → ∀ (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {n : ℕ} (hn0 : 0 < n) (hM : ∀ m : M, n • m = 0)
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension 1 f] (J : CompactificationOf (Over.mk f)) (η : S)
    (hη : η ∈ genericPoints S) (hnS : IsUnit ((n : ℕ) : Γ(S, ⊤))) :
    ∃ U : S.Opens, η ∈ U ∧ IsConstructibleEtaleComplex Λ
      ((etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ U.ι).obj
        ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj (constantEtaleComplex Λ M X))) := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have hfd : ∀ s, topologicalKrullDim (f.fiber s) ≤ 1 := fun s ↦ by
    simpa using topologicalKrullDim_fiber_le_of_smoothOfRelativeDimension 1 f s
  obtain ⟨U, hηU, V, v, hvf, hvs, hvi, XV, a, pV, hsq, T, Ybar, Y, t, qbar, jY, ν, W, hcomm, htf,
    hte, hqs, hqp, hqc, hqd, hj, hνf, hνs, hW, hWs⟩ := exists_curveDiagram_single f hfp η hη (hfd η)
  refine ⟨U, hηU, ?_⟩
  have : CompactSpace U :=
    isCompact_iff_compactSpace.1 (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian U := ⟨⟩
  have := hvf
  have := hvs
  have : IsNoetherian V := isNoetherian_of_locallyOfFiniteType v
  have := htf
  have := hte
  have := hqs
  have := hqp
  have := hqc
  have := hj
  have := hνf
  have := hνs
  refine isConstructibleEtaleComplex_of_inverseImage_of_surjective Λ v _ ?_
  rw [← isConstructibleEtaleComplex_inverseImage_comp_iff]
  have : IsSeparated pV := MorphismProperty.of_isPullback hsq ‹IsSeparated f›
  have : QuasiCompact pV := MorphismProperty.of_isPullback hsq ‹QuasiCompact f›
  have : LocallyOfFiniteType pV :=
    MorphismProperty.of_isPullback hsq (inferInstance : LocallyOfFiniteType f)
  refine isConstructibleEtaleComplex_of_iso Λ
    (constantEtaleComplexDerivedLowerShriekBaseChangeIso Λ M h095T hn0 hM hsq J).symm ?_
  exact isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_curveDiagram_of_isUnit Λ M h095T
    h0GKV hn0 hM pV (forall_topologicalKrullDim_fiber_le_of_isPullback hsq hfd) _ t qbar jY ν W
    hcomm hqd hW hWs (Stacks.Kummer.isUnit_natCast_of_hom (v ≫ U.ι) hnS)

/-- **Tag 0GKX for a module killed by an integer**, granted Tags 095T and 0GKV. Let `S` be a
Noetherian scheme, `f : X ⟶ S` separated, quasi-compact and smooth of relative dimension one, `Λ`
a Noetherian ring and `M` a finite `Λ`-module killed by an integer `n > 0`. Then `Rf_! M̲` has
constructible cohomology sheaves, for every compactification `j` of `f`.

This is the form of the tag that does not ask `Λ` to be torsion; the integer `n` is asked to be
invertible on `S`, so that Tag 0GKV is needed only at primes invertible on the base.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV (Tag 0GKW is
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isUnit`
from it). -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_constantSheaf_of_nsmul_of_isUnit
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit ((ℓ : ℕ) : Γ(S, ⊤)) → ∀ (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {n : ℕ} (hn0 : 0 < n) (hM : ∀ m : M, n • m = 0)
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension 1 f] (j : CompactificationOf (Over.mk f))
    (hnS : IsUnit ((n : ℕ) : Γ(S, ⊤))) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} f j Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  classical
  refine isConstructibleEtaleComplex_of_forall_exists_opens Λ _ fun T i _ hT ↦ ?_
  have : IsNoetherian T := isNoetherian_of_isClosedImmersion i
  obtain ⟨x⟩ := hT
  let η := (genericPoints.ofComponent ⟨irreducibleComponent x,
    irreducibleComponent_mem_irreducibleComponents x⟩).1
  have hη : η ∈ genericPoints T := (genericPoints.ofComponent _).2
  let sq := IsPullback.of_hasPullback f i
  have : SmoothOfRelativeDimension 1 (pullback.snd f i) :=
    let := smoothOfRelativeDimension_isStableUnderBaseChange 1
    MorphismProperty.of_isPullback sq inferInstance
  obtain ⟨U, hηU, hU⟩ :=
   exists_mem_isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_mem_genericPoints_of_isUnit
      Λ M h095T h0GKV hn0 hM (pullback.snd f i) (j.baseChange sq) η hη
      (Stacks.Kummer.isUnit_natCast_of_hom i hnS)
  refine ⟨U, ⟨η, hηU⟩, ?_⟩
  rw [isConstructibleEtaleComplex_inverseImage_comp_iff]
  exact isConstructibleEtaleComplex_of_iso Λ
    ((etaleModuleDerivedInverseImageGeneral.{u, u + 1} Λ U.ι).mapIso
      (constantEtaleComplexDerivedLowerShriekBaseChangeIso Λ M h095T hn0 hM sq j).symm) hU

end Stacks.EtaleCohomology

end
