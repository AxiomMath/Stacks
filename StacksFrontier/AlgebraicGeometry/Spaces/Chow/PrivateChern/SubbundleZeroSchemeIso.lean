module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SubbundleZeroSchemeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic

/-!
# `𝐏(ℱ)` is the zero scheme of the section of `𝒪_{𝐏(ℰ)}(1) ⊗ π^*ℒ^{-1}`

Let `0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` be short exact on an algebraic space `X`, with `ℒ` invertible and `ℰ`,
`ℱ` finite locally free, and `Z(σ) ⊆ 𝐏(ℰ)` the zero scheme of the section of
`𝒪(1) ⊗ π^*ℒ^{-1}` attached to `s : π^*ℒ ⟶ π^*ℰ ⟶ 𝒪(1)`. The morphism `ι : 𝐏(ℱ) ⟶ 𝐏(ℰ)`
factors through `Z(σ)` (`AlgebraicGeometry.Space.PrivateChern.exists_subbundleZeroScheme_lift`),
and **the factorization `𝐏(ℱ) ⟶ Z(σ)` is an isomorphism**.

It is a monomorphism because `ι` is one: `𝐏(ℱ_U) = 𝐏(ℱ) ×_{𝐏(ℰ)} 𝐏(ℰ_U)` over the presenting
chart and `𝐏(ℱ_U) ⟶ 𝐏(ℰ_U)` is a closed immersion
(`AlgebraicGeometry.Space.PrivateChern.mono_of_isPullback_of_isLocallySurjective`). It is
locally surjective: a point of `Z(σ)` lifts locally to the chart `𝐏(ℰ_U)`, where it comes from
`𝐏(ℱ_U)` by `exists_comp_chartEmbedding_eq_of_modulePullback_map_eq_zero`. A monomorphism of
sheaves which is locally surjective is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.exists_iso_subbundleZeroScheme`: `𝐏(ℱ) ≅ Z(σ)` over
  `𝐏(ℰ)`.
* `AlgebraicGeometry.Space.PrivateChern.mono_projectiveBundleEmbedding`: `ι` is a monomorphism.
* `AlgebraicGeometry.Space.PrivateChern.mono_of_isPullback_of_isLocallySurjective`: a morphism
  of presheaves whose base change along a locally surjective morphism from a representable is
  a monomorphism from a representable is a monomorphism, for a separated source.

## References

* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [-instance] CategoryTheory.catToReflQuiver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism of presheaves `ι : A' ⟶ A` is a monomorphism** if `A'` is a sheaf and the base
change of `ι` along a locally surjective `u : h_U ⟶ A` is a monomorphism `h_V ⟶ h_U`: two
sections of `A'` with the same image agree on the covering sieve on which that image lifts to
`U`, since there they both lift to `V` over the same point of `U`. -/
theorem mono_of_isPullback_of_isLocallySurjective {A' A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A') {U V : BigFppfOver B S hS}
    {a : yoneda.obj V ⟶ A'} {p : V ⟶ U} {ι : A' ⟶ A} {u : yoneda.obj U ⟶ A}
    (sq : IsPullback a (yoneda.map p) ι u) [Mono (yoneda.map p)]
    (hu : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) u) : Mono ι := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨T⟩
  rw [mono_iff_injective]
  intro α β hαβ
  have hsep := ((isSheaf_iff_isSheaf_of_type _ A').1 hA').isSeparated
  refine (hsep _ (Presheaf.imageSieve_mem _ u (ι.app _ α))).ext fun T' f hf => ?_
  obtain ⟨x, hx⟩ := hf
  have key : ∀ γ : A'.obj (op T), ι.app _ γ = ι.app _ α →
      ∃ v : yoneda.obj T' ⟶ yoneda.obj V, v ≫ yoneda.map p = yonedaEquiv.symm x ∧
        v ≫ a = yonedaEquiv.symm (A'.map f.op γ) := by
    intro γ hγ
    refine ⟨sq.lift (yonedaEquiv.symm (A'.map f.op γ)) (yonedaEquiv.symm x) ?_,
      sq.lift_snd _ _ _, sq.lift_fst _ _ _⟩
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hx,
      ← hγ]
    exact NatTrans.naturality_apply ι f.op γ
  obtain ⟨v₁, hv₁, hv₁'⟩ := key α rfl
  obtain ⟨v₂, hv₂, hv₂'⟩ := key β hαβ.symm
  have hv : v₁ = v₂ := (cancel_mono (yoneda.map p)).1 (hv₁.trans hv₂.symm)
  apply yonedaEquiv.symm.injective
  rw [← hv₁', ← hv₂', hv]

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {X : AlgebraicSpaces B S hS} {E F L : Modules.{u, u} B S hS X.1 X.2}
  [hE : E.IsQuasicoherentOnSite] [hF : F.IsQuasicoherentOnSite]
  (hfreeE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfreeF : SheafOfModules.IsFiniteLocallyFreeOnSite F) (q : E ⟶ F)
  (hq : ∀ V : SmallEtale B S hS X.1, Epi (chartModuleMap q V)) (i : L ⟶ E)
  (hL : IsInvertibleModule X L)

/-- The closed immersion of chart bundles over the presenting chart is a monomorphism of the
site. -/
instance mono_siteApp_projectiveBundleFamilyEmbedding :
    Mono ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp (bundleBaseChart X)) := by
  have := isFiniteLocallyFree_chartBundleModule E hfreeE (bundleBaseChart X)
  have := isFiniteLocallyFree_chartBundleModule F hfreeF (bundleBaseChart X)
  have := hq (bundleBaseChart X)
  have : Mono ((BigFppfOver.toScheme B S hS).map
      ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).siteApp (bundleBaseChart X))) := by
    change Mono ((Stacks.RelativeProj.bundlePresentationIso
        (chartBundleModule F (bundleBaseChart X))).inv ≫
      Stacks.Chow.GenuineChern.bundleEmbedding (chartModuleMap q (bundleBaseChart X)) ≫
        (Stacks.RelativeProj.bundlePresentationIso (chartBundleModule E (bundleBaseChart X))).hom)
    have h1 : _root_.AlgebraicGeometry.IsClosedImmersion
        (Stacks.Chow.GenuineChern.bundleEmbedding (chartModuleMap q (bundleBaseChart X))) :=
      Stacks.Chow.GenuineChern.isClosedImmersion_bundleEmbedding _
    have : Mono
        (Stacks.Chow.GenuineChern.bundleEmbedding (chartModuleMap q (bundleBaseChart X))) :=
      ((_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono _).1 h1).2
    have t1 : IsIso (Stacks.RelativeProj.bundlePresentationIso
        (chartBundleModule E (bundleBaseChart X))).hom := Iso.isIso_hom _
    have t2 : IsIso (Stacks.RelativeProj.bundlePresentationIso
        (chartBundleModule F (bundleBaseChart X))).inv := Iso.isIso_inv _
    exact @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ t2) _
      (@mono_comp _ _ _ _ _ _ this _ (@IsIso.mono_of_iso _ _ _ _ _ t1))
  exact (BigFppfOver.toScheme B S hS).mono_of_mono_map this

/-- The presenting chart `𝐏(ℰ_U) ⟶ 𝐏(ℰ)` is locally surjective. -/
private theorem isLocallySurjective_projectiveBundleChartPresentation_toSpace :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (projectiveBundleChartPresentation E hfreeE).toSpace :=
  isLocallySurjective_of_presheafSurjective_etale _
    (projectiveBundleChartPresentation E hfreeE).surjective
    (projectiveBundleChartPresentation E hfreeE).etale

/-- **`ι : 𝐏(ℱ) ⟶ 𝐏(ℰ)` is a monomorphism.** -/
theorem mono_projectiveBundleEmbedding :
    Mono (projectiveBundleEmbedding hfreeE hfreeF q hq).hom :=
  mono_of_isPullback_of_isLocallySurjective (projectiveBundle F hfreeF).2.isSheaf
    ((projectiveBundleFamilyEmbedding hfreeE hfreeF q hq).isPullback_glued _ _
      (isPullback_projectiveBundlePresentation X) (surjective_projectiveBundlePresentation X))
    (isLocallySurjective_projectiveBundleChartPresentation_toSpace hfreeE)

/-- **A point of `𝐏(ℰ)` with values in `T` which lies in `Z(σ)`** is, on the presenting chart,
a point `x : T ⟶ 𝐏(ℰ_U)` along which `s` vanishes. -/
theorem modulePullback_map_subbundleMorphism_eq_zero_of_mem {T : BigFppfOver B S hS}
    (x : T ⟶ (projectiveBundleChartPresentation E hfreeE).U)
    (hx : (projectiveBundleChartPresentation E hfreeE).toSpace.app (op T) x ∈
      (subbundleZeroScheme hfreeE i hL).1.obj (op T)) :
    (modulePullback B S hS
      (representedSpaceMap B S hS x ≫ projectiveBundleAtlas E hfreeE)).map
        (subbundleMorphism hfreeE i) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : yoneda.obj T ⟶ (subbundleZeroScheme hfreeE i hL).1.toFunctor,
      yonedaEquiv k = ⟨_, hx⟩ := ⟨_, yonedaEquiv.apply_symm_apply _⟩
  refine (exists_comp_eq_zeroScheme_morphismSection_iff
    (isInvertibleModule_subbundleSource hfreeE hL) (subbundleMorphism hfreeE i)
    (isInvertibleModule_projectiveBundleTwist E hfreeE) _).1
    ⟨ObjectProperty.homMk k, ObjectProperty.hom_ext _ ?_⟩
  apply yonedaEquiv.injective
  show yonedaEquiv (k ≫ (subbundleZeroScheme hfreeE i hL).1.ι) =
    yonedaEquiv (yoneda.map x ≫ (projectiveBundleChartPresentation E hfreeE).toSpace)
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, hk]
  rfl

include hE hF in
/-- **The factorization `𝐏(ℱ) ⟶ Z(σ)` of `ι` is locally surjective**: a point of `Z(σ)` lifts
locally to the presenting chart `𝐏(ℰ_U)`, where `s` vanishes along it, so that it comes from
the presenting chart `𝐏(ℱ_U)`. -/
theorem isLocallySurjective_subbundleZeroSchemeLift (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hLq : L.IsQuasicoherentOnSite)
    (h : projectiveBundle F hfreeF ⟶ (⟨(subbundleZeroScheme hfreeE i hL).1.toFunctor,
        (subbundleZeroScheme hfreeE i hL).2.1⟩ : AlgebraicSpaces B S hS))
    (hh : h ≫ ObjectProperty.homMk (subbundleZeroScheme hfreeE i hL).1.ι =
        projectiveBundleEmbedding hfreeE hfreeF q hq) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) h.hom := by
  have hhom : h.hom ≫ (subbundleZeroScheme hfreeE i hL).1.ι =
      (projectiveBundleEmbedding hfreeE hfreeF q hq).hom := congrArg (fun m => m.hom) hh
  have hatlas := toSpace_comp_projectiveBundleEmbedding hfreeE hfreeF q hq
  have := isLocallySurjective_projectiveBundleChartPresentation_toSpace hfreeE
  refine ⟨fun {T} z => ?_⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (Presheaf.imageSieve_mem _ (projectiveBundleChartPresentation E hfreeE).toSpace (U := op T)
      ((subbundleZeroScheme hfreeE i hL).1.ι.app (op T) z))
  rintro T' f ⟨x, hx⟩
  have hmem : (projectiveBundleChartPresentation E hfreeE).toSpace.app (op T') x ∈
      (subbundleZeroScheme hfreeE i hL).1.obj (op T') := by
    rw [hx]
    exact ((subbundleZeroScheme hfreeE i hL).1.toFunctor.map f.op z).2
  obtain ⟨x', hx'⟩ := exists_comp_chartEmbedding_eq_of_modulePullback_map_eq_zero (hfreeE := hfreeE)
    (hfreeF := hfreeF) (q := q) (hq := hq) (i := i) (hiq := hiq) (hC := hC) (hLq := hLq) (x := x)
    (modulePullback_map_subbundleMorphism_eq_zero_of_mem hfreeE i hL x hmem)
  refine ⟨(projectiveBundleChartPresentation F hfreeF).toSpace.app (op T') x', Subtype.ext ?_⟩
  have k1 : ∀ y, (subbundleZeroScheme hfreeE i hL).1.ι.app (op T') (h.hom.app (op T') y) =
      (projectiveBundleEmbedding hfreeE hfreeF q hq).hom.app (op T') y := fun y => by
    rw [← NatTrans.comp_app_apply, hhom]
  have k2 : (projectiveBundleEmbedding hfreeE hfreeF q hq).hom.app (op T')
      ((projectiveBundleChartPresentation F hfreeF).toSpace.app (op T') x') =
      (projectiveBundleChartPresentation E hfreeE).toSpace.app (op T')
        ((yoneda.map (chartEmbedding hfreeE hfreeF q hq)).app (op T') x') := by
    rw [← NatTrans.comp_app_apply, ← NatTrans.comp_app_apply, hatlas]
  show (subbundleZeroScheme hfreeE i hL).1.ι.app (op T')
      (h.hom.app (op T') ((projectiveBundleChartPresentation F hfreeF).toSpace.app (op T') x')) =
    (projectiveBundle E hfreeE).1.map f.op ((subbundleZeroScheme hfreeE i hL).1.ι.app _ z)
  rw [k1, k2, ← hx, ← hx']
  rfl

include hE hF in
/-- **`𝐏(ℱ)` is the zero scheme `Z(σ)`**: the factorization of `ι : 𝐏(ℱ) ⟶ 𝐏(ℰ)` through
`Z(σ)` is an isomorphism. -/
theorem exists_iso_subbundleZeroScheme (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hLq : L.IsQuasicoherentOnSite) :
    ∃ e : projectiveBundle F hfreeF ≅ (⟨(subbundleZeroScheme hfreeE i hL).1.toFunctor,
        (subbundleZeroScheme hfreeE i hL).2.1⟩ : AlgebraicSpaces B S hS),
      e.hom ≫ ObjectProperty.homMk (subbundleZeroScheme hfreeE i hL).1.ι =
        projectiveBundleEmbedding hfreeE hfreeF q hq := by
  have : Epi q := hC.epi_g
  obtain ⟨h, hh⟩ := exists_subbundleZeroScheme_lift hfreeE hfreeF q hq i hL hiq
  have hhom : h.hom ≫ (subbundleZeroScheme hfreeE i hL).1.ι =
      (projectiveBundleEmbedding hfreeE hfreeF q hq).hom := congrArg (fun m => m.hom) hh
  have := mono_projectiveBundleEmbedding hfreeE hfreeF q hq
  have : Mono h.hom := mono_of_mono_fac hhom
  have : IsIso h.hom :=
    NormalizationGluing.isIso_of_mono_of_isLocallySurjective_of_isSheaf B S hS
      (projectiveBundle F hfreeF).2.isSheaf (subbundleZeroScheme hfreeE i hL).2.1.isSheaf h.hom
      inferInstance
      (isLocallySurjective_subbundleZeroSchemeLift hfreeE hfreeF q hq i hL hiq hC hLq h hh)
  have : IsIso ((ObjectProperty.ι _).map h) := this
  have : IsIso h := isIso_of_fully_faithful (ObjectProperty.ι _) h
  exact ⟨asIso h, hh⟩

end AlgebraicGeometry.Space.PrivateChern

end
