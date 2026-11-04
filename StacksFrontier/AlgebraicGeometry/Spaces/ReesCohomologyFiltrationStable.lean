module

public import StacksFrontier.AlgebraicGeometry.Spaces.ReesTotalModuleComparison
public import StacksFrontier.RingTheory.FiltrationStableOfReesEmbedding

/-!
# The filtration of cohomology by the images of the products `IⁿN`

Let `T` be an affine object of the site with Noetherian `A = Γ(T₀, ⊤)`, `f : X ⟶ h_T` and
`J ⊆ A` an ideal.  For an `𝒪_X`-module `N`, the images of `H^p(X, JⁿN) ⟶ H^p(X, N)` form a
`J`-filtration of the `A`-module `H^p(X, N)` (Stacks 08AW, 08AX).  With `R = A[Jt]` the Rees
algebra, `π : X_R ⟶ X` and `ψ : X_{A[t]} ⟶ X_R` the base changes, the monomials `tᵏ` are
independent in `H^p(X, π_*ψ_*ψ^*π^*N)` (Stacks 073K).

## Main definitions

* `AlgebraicGeometry.Space.cohomologyIdealPowFiltration`: the `J`-filtration of `H^p(X, N₀)` by
  the images of `H^p(X, IᵐN₀)`.

## Main results

* `ModuleCat.eq_zero_of_sum_comparison`: independence transported along a comparison.
* `AlgebraicGeometry.Space.eq_zero_of_sum_cohomology_comparison_of_isPullback`: Stacks 073K
  independence, read through a comparison `W ≅ g'_*g'^*N`.
* `AlgebraicGeometry.Space.eq_zero_of_sum_reesTotalCohomologyAction`: the monomials `tᵏ` are
  independent in `H^p(X, π_*ψ_*ψ^*π^*N)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

universe v u

/-- **Independence transported along a comparison**, for abstract functors: if `β : V ≅ P K`
carries `ρₖ` to `P(gₖ)`, `H'(gₖ)` is multiplication by `bₖ`, and the `bₖ · pb(yₖ)` are
independent, then so are the `H(ρₖ)(H(u) yₖ)`. -/
theorem ModuleCat.eq_zero_of_sum_comparison {C C' : Type*} [Category C] [Category C']
    {Γ Γ' : Type*} [CommRing Γ] [CommRing Γ'] (H : C ⥤ ModuleCat.{v} Γ)
    (H' : C' ⥤ ModuleCat.{v} Γ') (φ : Γ →+* Γ') (P : C' ⥤ C) {N V : C} {K : C'} (u : N ⟶ V)
    (β : V ⟶ P.obj K) (η : N ⟶ P.obj K) (ρc : ℕ → (V ⟶ V)) (g : ℕ → (K ⟶ K))
    (c' : (ModuleCat.restrictScalars φ).obj (H'.obj K) ≅ H.obj (P.obj K))
    (pb : H.obj N ⟶ (ModuleCat.restrictScalars φ).obj (H'.obj K))
    (hu : u ≫ β = η) (hρ : ∀ k, ρc k ≫ β = β ≫ P.map (g k)) (hfac : pb ≫ c'.hom = H.map η)
    (hnat : ∀ k, (ModuleCat.restrictScalars φ).map (H'.map (g k)) ≫ c'.hom =
      c'.hom ≫ H.map (P.map (g k)))
    (b : ℕ → Γ') (hg : ∀ k, H'.map (g k) = b k • 𝟙 _) {Γ₀ : Type*} [CommRing Γ₀] (ψ : Γ₀ →+* Γ)
    (pb₀ : H.obj N ⟶ (ModuleCat.restrictScalars φ).obj (H'.obj K)) (hpb : pb₀ = pb)
    (b₀ : ℕ → Γ') (hb : ∀ k, b₀ k = b k)
    (hind : ∀ v : ℕ →₀ (ModuleCat.restrictScalars ψ).obj (H.obj N),
      (v.sum fun k y => b₀ k • (show H'.obj K from pb₀.hom y)) = 0 → v = 0)
    (v : ℕ →₀ H.obj N) (hv : (v.sum fun k y => (H.map (ρc k)).hom ((H.map u).hom y)) = 0) :
    v = 0 := by
  rw [hpb, funext hb] at hind
  refine hind v ?_
  have hc : Function.Injective c'.hom.hom :=
    ((ConcreteCategory.isIso_iff_bijective c'.hom).1 inferInstance).1
  apply hc
  have key : ∀ k y, (H.map β).hom ((H.map (ρc k)).hom ((H.map u).hom y)) =
      c'.hom.hom (b k • (show H'.obj K from pb.hom y)) := fun k y =>
    ModuleCat.comparison_apply_of_fac H H' φ P u β η
      (ρc k) (g k) c' pb hu (hρ k) hfac (hnat k) (b k) (hg k) y
  have h1 := congrArg (H.map β).hom hv
  rw [map_finsuppSum, map_zero] at h1
  calc c'.hom.hom (v.sum fun k y => b k • (show H'.obj K from pb.hom y))
      = v.sum fun k y => c'.hom.hom (b k • (show H'.obj K from pb.hom y)) :=
        map_finsuppSum c'.hom.hom v _
    _ = v.sum fun k y => (H.map β).hom ((H.map (ρc k)).hom ((H.map u).hom y)) :=
        Finsupp.sum_congr fun k _ => (key k _).symm
    _ = 0 := h1
    _ = c'.hom.hom 0 := (map_zero _).symm

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 073K independence through a comparison.**  For a cartesian square
`g' : X' ⟶ X`, `f' : X' ⟶ Y'` over `f : X ⟶ Y`, `g : Y' ⟶ Y` with `g` flat and `Y`, `Y'`
affine, a basis `(bₖ)` of `Γ(Y')` over `Γ(Y)`, and a module `W` with `β : W ≅ g'_*g'^*N`
carrying `u : N ⟶ W` to the unit and `ρₖ` to multiplication by `sₖ = f'♯ bₖ`: if
`∑ₖ H^p(ρₖ)(H^p(u) yₖ) = 0` then all `yₖ = 0`. -/
theorem eq_zero_of_sum_cohomology_comparison_of_isPullback {X X' Y Y' : AlgebraicSpaces B S hS}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (hsq : IsPullback g' f' f g)
    (V₀ : SmallEtale B S hS Y.1) [IsIso V₀.obj.hom] (V₀' : SmallEtale B S hS Y'.1)
    [IsIso V₀'.obj.hom] [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')]
    (hZ : B.Contains (⊤_ Scheme.{u})) (hg : IsFlat B S hS g.hom)
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom) (p : ℕ)
    (b : Module.Basis ℕ (RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)
      ((ModuleCat.restrictScalars.{u + 1} (globalSectionsRingHomSite B S hS g)).obj
        (ModuleCat.of _ (RingCat.sectionsSubring
          (ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O).obj))))
    (N : Modules.{u, u} B S hS X.1 X.2) (hN : N.IsQuasicoherentOnSite)
    {W : Modules.{u, u} B S hS X.1 X.2} (u : N ⟶ W)
    (β : W ⟶ (modulePushforward B S hS g').obj ((modulePullback B S hS g').obj N))
    (hu : u ≫ β = (modulePullbackAdjunction B S hS g').unit.app N)
    (s : ℕ → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj)
    (hs : ∀ k, s k = globalSectionsRingHomSite B S hS f' (b k)) (ρ : ℕ → (W ⟶ W))
    (hρ : ∀ k, ρ k ≫ β = β ≫ (modulePushforward B S hS g').map
      (globalSmul _ (s k) ((modulePullback B S hS g').obj N)))
    (v : ℕ →₀ (modulesCohomologyFunctor B S hS X p).obj N)
    (hv : (v.sum fun k y => ((modulesCohomologyFunctor B S hS X p).map (ρ k)).hom
      (((modulesCohomologyFunctor B S hS X p).map u).hom y)) = 0) :
    v = 0 := by
  have hρ' : ∀ k, ρ k ≫ β = β ≫ (modulePushforward B S hS g').map
      (globalSmul _ (globalSectionsRingHomSite B S hS f' (b k))
        ((modulePullback B S hS g').obj N)) := fun k => hs k ▸ hρ k
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  have hY := isAffineSpace_of_isIso_chart B S hS Y V₀
  have hY' := isAffineSpace_of_isIso_chart B S hS Y' V₀'
  let Dg := @BaseChangeDiagram.mk B S hS X' X Y' Y g' f' f g hsq N hN
  have haff : IsAffineHom B S hS g'.hom := Dg.isAffineHom_g' hY hY'
  have hflat : IsFlat B S hS g'.hom := Dg.isFlat_g' hg
  have hK := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' N hN
  have hind := Dg.eq_zero_of_sum_smul_cohomologyPullbackMap B S hS V₀ V₀' hZ hg hqc hqs p b
  exact ModuleCat.eq_zero_of_sum_comparison (modulesCohomologyFunctor B S hS X p)
    (modulesCohomologyFunctor B S hS X' p) (globalSectionsRingHomSite B S hS g')
    (modulePushforward B S hS g') u β ((modulePullbackAdjunction B S hS g').unit.app N) ρ
    (fun k => globalSmul _ (globalSectionsRingHomSite B S hS f' (b k))
      ((modulePullback B S hS g').obj N))
    (cohomologyPushforwardIsoOfIsFlatOfIsAffineHom B S hS g' haff hflat _ hK p)
    (cohomologyPullbackMap B S hS g' haff hflat N hN p) hu hρ'
    (cohomologyPullbackMap_fac B S hS g' haff hflat N hN p)
    (fun k => cohomologyPushforwardIsoOfIsFlatOfIsAffineHom_hom_naturality B S hS g' haff hflat
      hK hK _ p)
    (fun k => globalSectionsRingHomSite B S hS f' (b k))
    (fun k => rightDerived_globalSections_map_globalSmul B S hS X'
      (globalSectionsRingHomSite B S hS f' (b k)) ((modulePullback B S hS g').obj N) p)
    (globalSectionsRingHomSite B S hS f)
    (cohomologyPullbackMap B S hS Dg.g'
      (Dg.isAffineHom_g' (isAffineSpace_of_isIso_chart B S hS Dg.Y V₀)
        (isAffineSpace_of_isIso_chart B S hS Dg.Y' V₀'))
      (Dg.isFlat_g' hg) Dg.F Dg.isQuasicoherent p) rfl
    (fun k => globalSectionsRingHomSite B S hS Dg.f'
      (show RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS Dg.Y'.1 Dg.Y'.2).O).obj from b k))
    (fun k => rfl) hind v hv

section Rees

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)
  (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] in
/-- `tᵏ ∈ Γ(X_{A[t]})` is the image of the basis element `tᵏ` of `Γ(h_{Spec A[t]})`. -/
theorem algebraBaseChangeScalar_X_pow_eq (k : ℕ) :
    algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T) (Polynomial.X ^ k) =
      globalSectionsRingHomSite B S hS
        (algebraBaseChangeStructure B S hS T f (basePolynomialRing B S hS T))
        (polynomialSpectrumGlobalSectionsBasis B S hS T k) :=
  (algebraBaseChangeScalar_apply B S hS T f (basePolynomialRing B S hS T)
    (Polynomial.X ^ k)).trans (congrArg (globalSectionsRingHomSite B S hS
      (algebraBaseChangeStructure B S hS T f (basePolynomialRing B S hS T)))
      (polynomialSpectrumGlobalSectionsBasis_apply B S hS T k).symm)

/-- `AlgebraicGeometry.Space.reesTotalCohomologyAction` on elements. -/
theorem reesTotalCohomologyAction_apply (N : Modules.{u, u} B S hS X.1 X.2) (p : ℕ)
    (c : basePolynomialRing B S hS T)
    (q : (modulesCohomologyFunctor B S hS X p).obj
      (algebraImageTotal B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N)) :
    reesTotalCohomologyAction B S hS T f J N p c q =
      ((modulesCohomologyFunctor B S hS X p).map
        (algebraImageScalarEnd B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
          (reesAlgebra J).val N
          (algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T) c))).hom q :=
  rfl

/-- **The monomials are independent in `H^p(X, π_*ψ_*ψ^*π^*N)`** (Stacks 073K): if
`∑ₖ tᵏ · u(yₖ) = 0`, with `u : H^p(X, N) ⟶ H^p(X, V)` induced by the units, then all `yₖ = 0`. -/
theorem eq_zero_of_sum_reesTotalCohomologyAction (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) (hN : N.IsQuasicoherentOnSite) (p : ℕ)
    (v : ℕ →₀ (modulesCohomologyFunctor B S hS X p).obj N)
    (hv : (v.sum fun k y => reesTotalCohomologyAction B S hS T f J N p (Polynomial.X ^ k)
      (((modulesCohomologyFunctor B S hS X p).map
        (algebraImageTotalUnit B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
          (reesAlgebra J).val N)).hom y)) = 0) :
    v = 0 := by
  obtain ⟨β, -, hβu, hβc⟩ := exists_isIso_algebraImageTotal B S hS T f J N
  let V₀ : SmallEtale B S hS (schemeSpace T).1 := idEtaleChart B S hS T
  let V₀' : SmallEtale B S hS
      (schemeSpace (algebraSpectrumOver B S hS T (basePolynomialRing B S hS T))).1 :=
    idEtaleChart B S hS (algebraSpectrumOver B S hS T (basePolynomialRing B S hS T))
  have : IsIso V₀.obj.hom := IsIso.id (yoneda.obj T)
  have : IsIso V₀'.obj.hom :=
    IsIso.id (yoneda.obj (algebraSpectrumOver B S hS T (basePolynomialRing B S hS T)))
  have : IsAffine (chartScheme V₀) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  have : IsAffine (chartScheme V₀') :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj
      (algebraSpectrumOver B S hS T (basePolynomialRing B S hS T))))
  refine eq_zero_of_sum_cohomology_comparison_of_isPullback B S hS
    (algebraBaseChangeProjection B S hS T f (basePolynomialRing B S hS T))
    (algebraBaseChangeStructure B S hS T f (basePolynomialRing B S hS T)) f
    (schemeSpaceMap (algebraSpectrumSiteHom B S hS T (basePolynomialRing B S hS T)))
    (IsPullback.of_hasPullback _ _) V₀ V₀'
    hZ (isFlat_polynomialSpectrumSiteHom B S hS T) hqc hqs p
    (polynomialSpectrumGlobalSectionsBasis B S hS T) N hN
    (algebraImageTotalUnit B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val N) β hβu
    (fun k => algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T) (Polynomial.X ^ k))
    (algebraBaseChangeScalar_X_pow_eq B S hS T f)
    (fun k => algebraImageScalarEnd B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val N
      (algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T) (Polynomial.X ^ k)))
    (fun k => hβc _) v ?_
  refine (Finsupp.sum_congr fun k _ => ?_).trans hv
  exact (reesTotalCohomologyAction_apply B S hS T f J N p _ _).symm

end Rees

section Filtration

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)
  (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))

/-- `Iᵐ⁺¹N₀ ⊆ IᵐN₀ ⊆ N₀` composes to `Iᵐ⁺¹N₀ ⊆ N₀`. -/
theorem homOfLE_idealPowSmul_succ_comp_incl (F : Modules.{u, u} B S hS X.1 X.2)
    (N₀ : F.Submodule) (I : IdealSheaves B S hS X.1 X.2) (m : ℕ) :
    Stacks.SheafOfModules.Submodule.homOfLE (Stacks.Sites.idealPowSmul_succ_le I m N₀) ≫
      idealPowSmulIncl B S hS F N₀ I m = idealPowSmulIncl B S hS F N₀ I (m + 1) := by
  rw [← cancel_mono N₀.ι, Category.assoc, Stacks.SheafOfModules.Submodule.homOfLE_comp_ι,
    Stacks.SheafOfModules.Submodule.homOfLE_comp_ι, Stacks.SheafOfModules.Submodule.homOfLE_comp_ι]

/-- Multiplication by `c ∈ I` on `N₀`, restricted to `IᵐN₀`, factors through `Iᵐ⁺¹N₀`. -/
theorem idealPowSmulIncl_comp_globalSmul (F : Modules.{u, u} B S hS X.1 X.2)
    (N₀ : F.Submodule) (I : IdealSheaves B S hS X.1 X.2) (m : ℕ)
    (c : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
    (hc : ∀ W : SmallEtale B S hS X.1, c.1 (op W) ∈ I.obj (op W)) :
    idealPowSmulIncl B S hS F N₀ I m ≫ globalSmul _ c N₀.toSheafOfModules =
      idealSmulHom I c hc (Stacks.Sites.idealPowSmul (M := F) I m N₀)
        (Stacks.Sites.idealPowSmul (M := F) I (m + 1) N₀)
        (idealPowSmul_succ_eq_idealSmul I m N₀).symm.le ≫
        idealPowSmulIncl B S hS F N₀ I (m + 1) := by
  rw [← cancel_mono N₀.ι, Category.assoc, Category.assoc,
    Stacks.SheafOfModules.Submodule.homOfLE_comp_ι, idealSmulHom_ι,
    ← Stacks.Cohomology.SiteModules.comp_globalSmul,
    Stacks.SheafOfModules.Submodule.homOfLE_comp_ι_assoc]

/-- **The filtration of `H^p(X, N₀)` by the images of `H^p(X, IᵐN₀)`**, a `J`-filtration of the
`A`-module `H^p(X, N₀)` when the functions of `J` lie in `I`. -/
def cohomologyIdealPowFiltration (F : Modules.{u, u} B S hS X.1 X.2) (N₀ : F.Submodule)
    (I : IdealSheaves B S hS X.1 X.2)
    (hJ : ∀ a ∈ J, ∀ W : SmallEtale B S hS X.1, (baseScalar f a).1 (op W) ∈ I.obj (op W))
    (p : ℕ) :
    J.Filtration ((ModuleCat.restrictScalars (baseScalarRingHom B S hS T f)).obj
      ((modulesCohomologyFunctor B S hS X p).obj N₀.toSheafOfModules)) where
  N m := LinearMap.range ((ModuleCat.restrictScalars (baseScalarRingHom B S hS T f)).map
    ((modulesCohomologyFunctor B S hS X p).map (idealPowSmulIncl B S hS F N₀ I m))).hom
  mono m := by
    rintro _ ⟨z, rfl⟩
    refine ⟨((modulesCohomologyFunctor B S hS X p).map
      (Stacks.SheafOfModules.Submodule.homOfLE (Stacks.Sites.idealPowSmul_succ_le I m N₀))).hom z,
      ?_⟩
    have h1 := congrArg (fun φ => ((modulesCohomologyFunctor B S hS X p).map φ).hom z)
      (homOfLE_idealPowSmul_succ_comp_incl B S hS F N₀ I m)
    simp only [Functor.map_comp, ModuleCat.hom_comp] at h1
    exact (ModuleCat.restrictScalars_map_hom_apply _ _ _).trans
      (h1.trans (ModuleCat.restrictScalars_map_hom_apply _ _ _).symm)
  smul_le m := by
    rw [Submodule.smul_le]
    rintro a ha _ ⟨z, rfl⟩
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    refine ⟨((modulesCohomologyFunctor B S hS X p).map (idealSmulHom I (baseScalar f a)
      (hJ a ha) (Stacks.Sites.idealPowSmul (M := F) I m N₀)
        (Stacks.Sites.idealPowSmul (M := F) I (m + 1) N₀)
        (idealPowSmul_succ_eq_idealSmul I m N₀).symm.le)).hom z, ?_⟩
    have h1 := congrArg (fun φ => ((modulesCohomologyFunctor B S hS X p).map φ).hom z)
      (idealPowSmulIncl_comp_globalSmul B S hS F N₀ I m (baseScalar f a) (hJ a ha))
    simp only [Functor.map_comp, ModuleCat.hom_comp] at h1
    have h2 := congrArg (fun φ => φ.hom (((modulesCohomologyFunctor B S hS X p).map
      (idealPowSmulIncl B S hS F N₀ I m)).hom z))
      (rightDerived_globalSections_map_globalSmul B S hS X (baseScalar f a)
        N₀.toSheafOfModules p)
    refine (ModuleCat.restrictScalars_map_hom_apply _ _ _).trans (h1.symm.trans (h2.trans ?_))
    exact (congrArg (fun c => c • (((modulesCohomologyFunctor B S hS X p).map
      (idealPowSmulIncl B S hS F N₀ I m)).hom z)) (baseScalarRingHom_apply B S hS T f a)).symm

end Filtration

end AlgebraicGeometry.Space

end
