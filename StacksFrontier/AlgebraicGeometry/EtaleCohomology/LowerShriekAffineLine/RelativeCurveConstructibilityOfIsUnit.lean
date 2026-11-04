module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.RelativeCurveConstructibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.CurveConstructibilityOfIsUnit

/-!
# `Rf_!` of a constructible sheaf on a smooth family of curves, exponent invertible on the base

Let `Y` be Noetherian and `f : X ⟶ Y` separated, quasi-compact and smooth of relative dimension
one. For a constructible sheaf `ℱ` of `Λ`-modules on `X_étale` killed by an integer `n > 0`
invertible on `Y`, `Rf_!(ℱ[0])` has constructible cohomology sheaves. These are the forms of
`isConstructibleEtaleComplex_derivedLowerShriekUnbounded_extensionByZero_constantSheaf`
and
`isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_smoothOfRelativeDimension_one`
for sheaves killed by an integer invertible on the base, built on
`isConstructibleEtaleComplex_derivedLowerShriekUnbounded_constantSheaf_of_nsmul_of_isUnit`:
[Stacks, Tag 0GKV] is then needed only at primes invertible on the base.

## References

* [Stacks Project, Tag 0GKX](https://stacks.math.columbia.edu/tag/0GKX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance] Abelian.hasFiniteBiproducts

universe u

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat
attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **`Rf_!` of an étale extension by zero of `M̲`**, granted Tags 095T and 0GKV and the comparison
`e_! = π_* ∘ ι_!` for an étale `e = ι ≫ π` with `ι` an open immersion and `π` finite
(`Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIsoDirectImage`). Let `f : X ⟶ Y` be
separated, quasi-compact and smooth of relative dimension one over a Noetherian scheme, `J` a
compactification of `f`, `e : W ⟶ X` étale with `W` affine, and `M` a finite `Λ`-module killed
by `n > 0`. Then `Rf_!(e_! M̲)` has constructible cohomology sheaves.

Zariski's main theorem factors the étale `W ⟶ X̄` as an open immersion `ι : W ⟶ T` followed by a
finite `π : T ⟶ X̄`; then `Rf_!(e_! M̲) = Rf̄_* π_* ι_! M̲ = R(e ≫ f)_! M̲`, computed through the
compactification `T` of `W` over `Y`, and `e ≫ f` is separated, quasi-compact and smooth of
relative dimension one, so Tag 0GKX applies.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV. -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_extensionByZero_constantSheaf_of_isUnit
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
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] {n : ℕ} (hn0 : 0 < n)
    (hM : ∀ m : M, n • m = 0) {X Y W : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [SmoothOfRelativeDimension 1 f] (J : CompactificationOf (Over.mk f))
    (e : W ⟶ X) [Etale e] [IsAffine W] (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj
        ((etaleModuleExtensionByZero.{u, u + 1} Λ e).obj
          ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  classical
  let G := (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  have : IsNoetherian J.space := isNoetherian_of_locallyOfFiniteType J.toBase
  let ε := e ≫ J.immersion
  have : LocallyOfFinitePresentation ε :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  obtain ⟨T, ι, π, hι, hιqc, hπ, hπfp, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_finitePresentation_factorization ε
  have := hι
  have := hπ
  have : Etale (ι ≫ π) := hfac ▸ (inferInstance : Etale ε)
  have hg : ι ≫ π ≫ J.toBase = e ≫ f := by
    rw [← Category.assoc, ← hfac]
    simp [ε]
  let J' := CompactificationOf.ofFactorizationGeneral (e ≫ f) ι (π ≫ J.toBase) hg
  have : SmoothOfRelativeDimension 0 e :=
    (Etale.iff_smoothOfRelativeDimension_zero e).1 inferInstance
  have : SmoothOfRelativeDimension 1 (e ≫ f) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  have h0GKX :=
    isConstructibleEtaleComplex_derivedLowerShriekUnbounded_constantSheaf_of_nsmul_of_isUnit Λ M
      h095T h0GKV hn0 hM (e ≫ f) J' hnY
  -- `R(e ≫ f)_! M̲ = R(π ≫ f̄)_* ι_! M̲ = Rf̄_* π_* ι_! M̲ = Rf̄_* ε_! M̲ = Rf_! e_! M̲`
  let S := DerivedCategory.singleFunctor
  let e₁ : (derivedLowerShriekUnbounded.{u, u + 1} (e ≫ f) J' Λ).obj ((S _ 0).obj G) ≅
      (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ J.toBase).obj
        ((S _ 0).obj ((etaleModuleDirectImage.{u, u + 1} Λ π).obj
          ((etaleModuleExtensionByZero.{u, u + 1} Λ ι).obj G))) :=
    (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ (π ≫ J.toBase)).mapIso
        ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, u + 1} Λ ι).app _ ≪≫
          ((etaleModuleExtensionByZero.{u, u + 1} Λ ι).mapDerivedCategorySingleFunctor 0).app G) ≪≫
      (etaleModuleDerivedDirectImageUnboundedCompIso.{u, u + 1} Λ π J.toBase).app _ ≪≫
      (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ J.toBase).mapIso
        (((etaleModuleDirectImage.{u, u + 1} Λ π).mapDerivedCategorySingleFunctor 0).app _)
  let e₂ : (derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj
      ((S _ 0).obj ((etaleModuleExtensionByZero.{u, u + 1} Λ e).obj G)) ≅
      (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ J.toBase).obj
        ((S _ 0).obj ((etaleModuleDirectImage.{u, u + 1} Λ π).obj
          ((etaleModuleExtensionByZero.{u, u + 1} Λ ι).obj G))) :=
    (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ J.toBase).mapIso
      ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, u + 1} Λ J.immersion).app _ ≪≫
        ((etaleModuleExtensionByZero.{u, u + 1} Λ J.immersion).mapDerivedCategorySingleFunctor
          0).app _ ≪≫
        (S _ 0).mapIso
          ((etaleModuleExtensionByZeroCompIso.{u, u + 1} Λ e J.immersion).app G).symm ≪≫
        (S _ 0).mapIso (eqToIso (congrArg (fun F ↦ F.obj G)
          (etaleModuleExtensionByZero_congr Λ hfac))) ≪≫
        (S _ 0).mapIso ((etaleModuleExtensionByZeroCompIsoDirectImage Λ ι π).app G))
  exact isConstructibleEtaleComplex_of_iso Λ (e₁ ≪≫ e₂.symm) h0GKX

/-- **`Rf_!` of a constructible torsion sheaf on a smooth family of curves is constructible**,
granted Tags 095T, 0GKV and 095U. Let `Y` be Noetherian, `f : X ⟶ Y` separated, quasi-compact and
smooth of relative dimension one, `J` a compactification of `f` and `ℱ` a constructible torsion
sheaf of `Λ`-modules on `X_étale`. Then `Rf_!(ℱ[0])` has constructible cohomology sheaves.

The proof is by descending induction on the degree, over all constructible sheaves on `X` killed
by an integer `n` killing `ℱ`: `R^q f_! = 0` for `q` beyond the bound of Tag 0G2A (from
Tag 095U); a constructible sheaf killed by `n` is a quotient of a finite sum `𝒢` of `e_! (Λ/nΛ)̲`
with `e` étale from an affine scheme (Tag 095N); `Rf_! 𝒢` is constructible by Tag 0GKX applied to
`e ≫ f`; the kernel `𝒦` is again constructible and killed by `n`; and in the long exact sequence of
`0 → 𝒦 → 𝒢 → ℱ → 0` the sheaf `R^q f_! ℱ` sits between the image of `R^q f_! 𝒢`, a quotient of a
constructible sheaf, and the kernel of `R^{q+1} f_! 𝒦 → R^{q+1} f_! 𝒢`.

Hypotheses: `h095T` is Stacks Tag 095T; `h0GKV` is Stacks Tag 0GKV (Tag 0GKW is
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isUnit`
from it); `h095U` is Stacks Tag 095U. -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_smoothOfRelativeDimension_one_of_isUnit
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
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, u + 1} p).rightDerived q).obj F))
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension 1 f] (J : CompactificationOf (Over.mk f))
    (F : EtaleModules.{u, u + 1} Λ X) (hF : IsConstructibleEtaleModule Λ F) {n : ℕ} (hn0 : 0 < n)
    (hn : n • 𝟙 F = 0) (hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} f J Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj F)) := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨N, hNall⟩ := exists_bound_derivedLowerShriekUnbounded.{u, u + 1} Λ h095U J
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, u + 1} Λ J.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, u + 1} Λ J.toBase
  let Φ := derivedLowerShriekUnbounded.{u, u + 1} f J Λ
  let G' := (etaleModuleExtensionByZero.{u, u + 1} Λ J.immersion).mapDerivedCategory ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ J.toBase
  let eΦ : Φ ≅ G' := derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, u + 1} Λ J
  have : Φ.Additive := Functor.additive_of_iso eΦ.symm
  let S := DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0
  let H := fun q : ℤ ↦ DerivedCategory.homologyFunctor (EtaleModules.{u, u + 1} Λ Y) q
  have htransport : ∀ (q : ℤ) (K : DerivedCategory (EtaleModules.{u, u + 1} Λ X)),
      IsConstructibleEtaleModule Λ ((H q).obj (Φ.obj K)) ↔
        IsConstructibleEtaleModule Λ ((H q).obj (G'.obj K)) := fun q K ↦
    ⟨(IsConstructibleEtaleModule Λ).prop_of_iso ((H q).mapIso (eΦ.app K)),
      (IsConstructibleEtaleModule Λ).prop_of_iso ((H q).mapIso (eΦ.app K)).symm⟩
  -- vanishing above the bound
  have hvan : ∀ G : EtaleModules.{u, u + 1} Λ X, n • 𝟙 G = 0 → ∀ q : ℤ, (N : ℤ) < q →
      IsZero ((H q).obj (Φ.obj (S.obj G))) := by
    intro G hG q hq
    have hB : DerivedCategoryB.derivedCategoryBPlus (IsTorsionEtaleModule.{u, u + 1} Λ X)
        (S.obj G) := by
      have hz : ∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ m).obj (S.obj G)) :=
        fun m hm ↦ IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology _ _ _ m hm)
          ((DerivedCategory.homologyFunctor _ m).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ _ 0).app G) ≪≫
            (DerivedCategory.homologyFunctorFactors _ m).app _)
      refine ⟨⟨0, fun m hm ↦ hz m (by omega)⟩, fun m ↦ ?_⟩
      by_cases hm : m = 0
      · subst hm
        exact ObjectProperty.prop_of_iso (P := IsTorsionEtaleModule.{u, u + 1} Λ X)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app G).symm
          (isTorsionEtaleModule_of_nsmul_id_eq_zero Λ hn0 hG)
      · exact ObjectProperty.prop_of_isZero (P := IsTorsionEtaleModule.{u, u + 1} Λ X) (hz m hm)
    have := (hNall (S.obj G) hB).2.2.2 0 inferInstance
    exact DerivedCategory.isZero_of_isLE (hX := this) _ (0 + N) q (by omega)
  -- the good sheaves
  let Mn := quotientNSMul Λ n
  have hMn : ∀ m : Mn, n • m = 0 := nsmul_quotientNSMul Λ n
  have hbase :=
    @isConstructibleEtaleComplex_derivedLowerShriekUnbounded_extensionByZero_constantSheaf_of_isUnit
      Λ _ _ h095T h0GKV Mn _ n hn0 hMn
  have hgood : ∀ {m : ℕ} (W : Fin m → Scheme.{u}) (e : ∀ i, W i ⟶ X) (_ : ∀ i, Etale (e i))
      (_ : ∀ i, IsAffine (W i)),
      IsConstructibleEtaleModule Λ (∐ fun i ↦ (etaleModuleExtensionByZero.{u, u + 1} Λ (e i)).obj
        ((constantSheaf (W i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj Mn)) ∧
      n • 𝟙 (∐ fun i ↦ (etaleModuleExtensionByZero.{u, u + 1} Λ (e i)).obj
        ((constantSheaf (W i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj Mn)) = 0 ∧
      ∀ q : ℤ, IsConstructibleEtaleModule Λ ((H q).obj (Φ.obj (S.obj
        (∐ fun i ↦ (etaleModuleExtensionByZero.{u, u + 1} Λ (e i)).obj
          ((constantSheaf (W i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj Mn))))) := by
    intro m W e he hW
    let E : Fin m → EtaleModules.{u, u + 1} Λ X := fun i ↦
      (etaleModuleExtensionByZero.{u, u + 1} Λ (e i)).obj
        ((constantSheaf (W i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj Mn)
    have hEn : ∀ i, n • 𝟙 (E i) = 0 := fun i ↦ by
      have hM' : n • 𝟙 Mn = 0 := by ext x; simpa using hMn x
      have := (constantSheaf (W i).smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        etaleModuleExtensionByZero.{u, u + 1} Λ (e i)).map_nsmul (f := 𝟙 Mn) (n := n)
      rw [CategoryTheory.Functor.map_id, hM', Functor.map_zero] at this
      exact this.symm
    refine ⟨isConstructibleEtaleModule_sigma Λ E fun i ↦
      isConstructibleEtaleModule_etaleModuleExtensionByZero_of_etale Λ (e i) _
        (isConstructibleEtaleModule_constantSheaf Λ (W i) Mn), ?_, fun q ↦ ?_⟩
    · refine Sigma.hom_ext _ _ fun i ↦ ?_
      rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero, ← Category.id_comp (Sigma.ι E i),
        ← Preadditive.nsmul_comp, hEn, zero_comp]
    · let Ψ := S ⋙ Φ ⋙ H q
      refine (IsConstructibleEtaleModule Λ).prop_of_iso
        ((Ψ.mapIso (biproduct.isoCoproduct E)).symm ≪≫ Ψ.mapBiproduct E).symm ?_
      exact Stacks.ExtKilling.prop_biproduct _ fun i ↦ hbase f J (e i) hnY q
  -- the descending induction
  have key : ∀ k : ℕ, ∀ G : EtaleModules.{u, u + 1} Λ X, IsConstructibleEtaleModule Λ G →
      n • 𝟙 G = 0 → ∀ q : ℤ, (N : ℤ) + 1 - k ≤ q →
        IsConstructibleEtaleModule Λ ((H q).obj (Φ.obj (S.obj G))) := by
    intro k
    induction k with
    | zero =>
      intro G _ hG q hq
      exact (IsConstructibleEtaleModule Λ).prop_of_isZero (hvan G hG q (by omega))
    | succ k ih =>
      intro G hGc hG q hq
      by_cases hq' : (N : ℤ) + 1 - k ≤ q
      · exact ih G hGc hG q hq'
      obtain ⟨m, W, e, he, hW, p, hp⟩ :=
        exists_epi_sigma_etaleModuleExtensionByZero_quotientNSMul Λ G hGc hG
      obtain ⟨hGtc, hGtn, hGt⟩ := hgood W e he hW
      let Gt := ∐ fun i ↦ (etaleModuleExtensionByZero.{u, u + 1} Λ (e i)).obj
        ((constantSheaf (W i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj Mn)
      let K := kernel p
      have hKc : IsConstructibleEtaleModule Λ K :=
        (IsConstructibleEtaleModule Λ).prop_kernel p hGtc hGc
      have hKn : n • 𝟙 K = 0 := by
        rw [← cancel_mono (kernel.ι p), zero_comp, Preadditive.nsmul_comp, Category.id_comp,
          show n • kernel.ι p = kernel.ι p ≫ (n • 𝟙 Gt) by
            rw [Preadditive.comp_nsmul, Category.comp_id], hGtn, comp_zero]
      have hS : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p))
          inferInstance hp
      have hT := G'.map_distinguished _ hS.singleTriangle_distinguished
      refine (htransport q _).2 ?_
      exact isConstructibleEtaleModule_homology_obj₃_of_distinguished Λ _ hT q
        ((htransport q _).1 (hGt q))
        ((htransport (q + 1) _).1 (ih K hKc hKn (q + 1) (by omega)))
        ((htransport (q + 1) _).1 (hGt (q + 1)))
  intro q
  by_cases hq : q < 0
  · exact (IsConstructibleEtaleModule Λ).prop_of_isZero <| DerivedCategory.isZero_of_isGE
      (hX := isGE_derivedLowerShriekUnbounded_obj.{u, u + 1} Λ J _ 0) _ 0 q hq
  · exact key (N + 1 - q).toNat F hF hn q (by omega)

end Stacks.EtaleCohomology

end
