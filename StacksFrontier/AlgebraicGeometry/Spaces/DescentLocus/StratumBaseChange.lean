module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.DegreeZeroBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.StratumLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankStratumExistence

/-!
# Base change of `f_*E` over the bottom rank stratum

Let `f : X ⟶ Y` be flat, proper and of finite presentation, `E` a finite locally free
`𝒪_X`-module, `K = Rf_*E`, and `q : Y₀ ⟶ Y` universally of bottom rank `r` for `K` in degree `0`.
For the base change `f₀ : X₀ ⟶ Y₀` of `f` and `E₀` the pullback of `E`, the base change map
`h^*f₀_*E₀ ⟶ f_{h,*}(h')^*E₀` is an isomorphism for every `h : T ⟶ Y₀`.

This is the step of the proof of Stacks 0D23 in which the formation of `f_*E` commutes with base
change over the stratum: `Rf₀_*E₀ = Lq^*K` is computed by the K-flat model `q^*K'` of a K-flat
model `K'` of `K`, the comparison `h^*H^0(q^*K') ⟶ H^0(h^*q^*K')` is an isomorphism over the
stratum (Stacks 0D21, (3)), and the derived base change map of `f₀` at `E₀` is an isomorphism by
cohomology and base change (Stacks 0CTM). It is a private, unregistered helper.

## Implementation notes

The bottom rank stratum of Stacks 0D21 is
`AlgebraicGeometry.Space.BottomRankLocus.exists_isBottomRankStratum_isFinitePresentation`, for
`E` perfect of Tor amplitude in `[a, b]`. Here `K = Rf_*E` is perfect and `H^j(Lg^*K) = 0` for
`j < 0` and every `g`, but a global upper bound on its Tor amplitude is only available locally
on `Y`. The two facts about the stratum that the proof of 0D23 uses are therefore recombined from
the base's building blocks under that vanishing hypothesis: the bottom models on charts
(`AlgebraicGeometry.Space.exists_smallEtale_bottomModel`, which consumes exactly the vanishing),
and from them the split bottom models over a morphism universally of bottom rank `r` and the
comparison `g^*H^a(j^*K') ⟶ H^a(g^*j^*K')` for an arbitrary K-flat model `K'`.

## Main results

* `AlgebraicGeometry.Space.DescentStratum.exists_chart_bottomModel_of_vanishing`
* `AlgebraicGeometry.Space.DescentStratum.isIso_homologyComparison_of_isUniversallyFreeBottom`
* `AlgebraicGeometry.Space.DescentStratum.isIso_moduleBaseChangeMap_of_isUniversallyFreeBottom`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.DescentStratum

open BottomRankLocus

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The stratum of an object whose derived pullbacks vanish below `a` -/

section Vanishing

variable {X : AlgebraicSpaces B S hS}
  {E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
  {a : ℤ} {r : ℕ}

/-- **Every object of `D(𝒪_X)` has a K-flat model with flat terms** (Stacks 06YS on the small
étale site of `X`). -/
theorem exists_kFlat_model
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ∃ K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ,
      smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ∧
      Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  obtain ⟨R₀, hR₀, t₀, ht₀⟩ := smallEtaleModuleKFlat_hasResolutions B S hS X
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (DerivedCategory.Q.objPreimage E))
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective R₀
  obtain ⟨t, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective t₀
  have : IsIso (DerivedCategory.Q.map t) := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso, ← HomologicalComplex.mem_quasiIso_iff,
      ← HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact ⟨K, hR₀, ⟨asIso (DerivedCategory.Q.map t) ≪≫ DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-- Every point lies in an affine étale chart carrying a bottom model of `E` in degree `a`, when
`E` is perfect and its derived pullbacks have no cohomology below degree `a`
(`AlgebraicGeometry.Space.exists_smallEtale_bottomModel`). -/
theorem exists_chart_bottomModel_of_vanishing
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hvan : ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X) (j : ℤ), j < a →
      IsZero (pullbackHomology E j f)) (x : points B S hS X.1) :
    ∃ V : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) (repRing V.1.left)),
        Nonempty (BottomModel (Y := schemeSpace V.1.left)
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
          (repRho V.1.left) A) :=
  exists_smallEtale_bottomModel B S hS E hE a hvan x

/-- **Split bottom models along a morphism universally of bottom rank `r`**, for `E` perfect
with derived pullbacks vanishing below `a`: every point of `Z` lies in a chart of `Z` on which
`E` pulled back along it has a bottom model whose matrix has a free kernel splitting of rank
`r`. The matrix of a bottom model on a chart of `X` becomes split over the basic opens of a
cover cut out by the Fitting ideals
(`Matrix.exists_span_hasFreeKernelSplitting_kernelRankStratum`). -/
theorem exists_chart_splitBottomModel_of_vanishing
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hvan : ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X) (j : ℤ), j < a →
      IsZero (pullbackHomology E j f)) {Z : AlgebraicSpaces B S hS}
    (j : Z ⟶ X) (hj : IsUniversallyFreeBottom E a r j) (z : points B S hS Z.1) :
    ∃ (W : SmallEtale B S hS Z.1) (O : ((BigFppfOver.toScheme B S hS).obj W.1.left).Opens),
      z ∈ Set.range (pointsMap B S hS (yoneda.obj (openChart B S hS Z.1 W O).1.left)
        (openChart B S hS Z.1 W O).1.hom) ∧
      ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) (repRing (openSub W.1.left O))),
        A.HasFreeKernelSplittingKernelRankStratum r ∧
        Nonempty (BottomModel (Y := representedAlgebraicSpace B S hS (openSub W.1.left O))
          ((smallEtaleDerivedModulePullback B S hS
            ((representedSpaceMap B S hS (openSubHom W.1.left O) ≫ chartToSpace B S hS Z W) ≫
              j)).obj E) a (repRho (openSub W.1.left O)) A) := by
  obtain ⟨V, hV, -, m, n, A, hM⟩ :=
    exists_chart_bottomModel_of_vanishing hE hvan (pointsMap B S hS Z.1 j.hom z)
  obtain ⟨M⟩ := hM
  obtain ⟨W₀, k, hzW₀, hW₀, hk⟩ := exists_affine_smallEtale_chart_lift j V z hV
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W₀.1.left) := hW₀
  have hu : IsUniversallyFreeBottom ((smallEtaleDerivedModulePullback B S hS
      (chartToSpace B S hS X V)).obj E) a r (representedSpaceMap B S hS k) := by
    have h0 := hj.comp (chartToSpace B S hS Z W₀)
    rw [hk] at h0
    exact (isUniversallyFreeBottom_comp_iff _ _).1 h0
  obtain ⟨h₁, h₂⟩ := (BottomModel.isUniversallyFreeBottom_iff (U := V.1.left) M k).1 hu
  obtain ⟨ι, s, hs, hsplit⟩ := Matrix.exists_span_hasFreeKernelSplitting_kernelRankStratum _ r h₁ h₂
  obtain ⟨w, rfl⟩ := hzW₀
  have hcov := iSup_basicOpen_of_span_eq_top (X := (BigFppfOver.toScheme B S hS).obj W₀.1.left) ⊤
    (Set.range fun i => (s i : Γ((BigFppfOver.toScheme B S hS).obj W₀.1.left, ⊤))) hs
  have hw : pointsToScheme B S hS W₀.1.left w ∈
      (⊤ : ((BigFppfOver.toScheme B S hS).obj W₀.1.left).Opens) := trivial
  rw [← hcov] at hw
  simp only [TopologicalSpace.Opens.mem_iSup, exists_prop] at hw
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hw
  let O := ((BigFppfOver.toScheme B S hS).obj W₀.1.left).basicOpen
    (s i : Γ((BigFppfOver.toScheme B S hS).obj W₀.1.left, ⊤))
  let o := openSubHom W₀.1.left O
  refine ⟨W₀, O, ?_, m, n, A.map (repTheta (o ≫ k)), ?_, ⟨?_⟩⟩
  · rw [range_pointsMap_openChart]
    exact ⟨w, hi, rfl⟩
  · let ℓ := IsLocalization.Away.lift (S := Localization.Away (s i)) (s i)
      (isUnit_repTheta_openSubHom W₀.1.left (s i))
    have hℓ : ℓ.comp (algebraMap _ (Localization.Away (s i))) = repTheta o :=
      IsLocalization.Away.lift_comp _ _
    have h1 := (hsplit i).map ℓ
    rw [Matrix.map_map, ← RingHom.coe_comp, hℓ] at h1
    have heq : A.map (repTheta (o ≫ k)) = (A.map (repTheta k)).map (repTheta o) :=
      Matrix.ext fun p q => repTheta_comp_apply o k _
    exact heq ▸ h1
  · have heq : (representedSpaceMap B S hS o ≫ chartToSpace B S hS Z W₀) ≫ j =
        representedSpaceMap B S hS (o ≫ k) ≫ chartToSpace B S hS X V := by
      refine InducedCategory.hom_ext ?_
      have hk' : W₀.1.hom ≫ j.hom = yoneda.map k ≫ V.1.hom := congrArg (·.hom) hk
      change (yoneda.map o ≫ W₀.1.hom) ≫ j.hom = yoneda.map (o ≫ k) ≫ V.1.hom
      rw [Category.assoc, hk', Functor.map_comp, Category.assoc]
    have e : (smallEtaleDerivedModulePullback B S hS
        ((representedSpaceMap B S hS o ≫ chartToSpace B S hS Z W₀) ≫ j)).obj E ≅
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (o ≫ k))).obj
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) :=
      eqToIso (congrArg (fun φ : representedAlgebraicSpace B S hS (openSub W₀.1.left O) ⟶ X =>
          (smallEtaleDerivedModulePullback B S hS φ).obj E) heq) ≪≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS (o ≫ k))
          (chartToSpace B S hS X V)).app E).symm
    exact BottomModel.ofIso (X := representedAlgebraicSpace B S hS (openSub W₀.1.left O))
      (BottomModel.pullbackRep (U := V.1.left) M (o ≫ k)) e

/-- **The degree-`a` homology of a K-flat model commutes with pullback along a morphism into a
stratum.** If `E` is perfect, its derived pullbacks have no cohomology below degree `a`,
`j : Z ⟶ X` is universally of bottom rank `r`, and `K` is a K-flat model of `E`, then for every
`g : Y ⟶ Z` the comparison `g^*H^a(j^*K) ⟶ H^a(g^*j^*K)` is an isomorphism: on a chart of `Y` it
is the comparison for a bottom model with a split matrix
(`AlgebraicGeometry.Space.isIso_homologyComparison_of_bottomModel`). -/
theorem isIso_homologyComparison_of_isUniversallyFreeBottom
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hvan : ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X) (j : ℤ), j < a →
      IsZero (pullbackHomology E j f)) {Z : AlgebraicSpaces B S hS}
    (j : Z ⟶ X) (hj : IsUniversallyFreeBottom E a r j)
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hK : smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (e : DerivedCategory.Q.obj K ≅ E) {Y : AlgebraicSpaces B S hS} (g : Y ⟶ Z) :
    IsIso ((pb g).homologyComparisonRightExactHomologyComparison
      (((pb j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a) := by
  let N := ((pb j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hN : smallEtaleModuleKFlat B S hS Z
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) := smallEtaleModuleKFlat_pb j K hK
  have : (pb g).Additive := modulePullback_additive _
  have := preservesFiniteColimits_pb g
  have hloc : ∀ y : points B S hS Y.1, ∃ W : SmallEtale B S hS Y.1,
      y ∈ Set.range (pointsMap B S hS (yoneda.obj W.1.left) W.1.hom) ∧
      IsIso ((pb (chartToSpace B S hS Y W)).map
          ((pb g).homologyComparisonRightExactHomologyComparison N a)) := by
    intro y
    obtain ⟨W₀, O, hz, m, n, A, hA, hM⟩ :=
      exists_chart_splitBottomModel_of_vanishing hE hvan j hj (pointsMap B S hS Y.1 g.hom y)
    let φ := representedSpaceMap B S hS (openSubHom W₀.1.left O) ≫ chartToSpace B S hS Z W₀
    have : PreservesFiniteLimits (pb φ) := by
      have h := preservesFiniteLimits_pb_chartToSpace Z (openChart B S hS Z.1 W₀ O)
      rwa [chartToSpace_openChart] at h
    let M' := hM.some.ofIso ((smallEtaleDerivedModulePullback B S hS φ).mapIso
      ((smallEtaleDerivedModulePullbackObjQIsoOfKFlat j K hK).symm ≪≫
        (smallEtaleDerivedModulePullback B S hS j).mapIso e) ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS φ j).app E)
    obtain ⟨W, k, hyW, hk⟩ := exists_smallEtale_chart_lift B S hS Y.2 g.hom
      (openChart B S hS Z.1 W₀ O) y hz
    refine ⟨W, hyW, ?_⟩
    let ψ : chartSpace B S hS Y W ⟶ representedAlgebraicSpace B S hS (openSub W₀.1.left O) :=
      ObjectProperty.homMk (yoneda.map k)
    have h1 := isIso_homologyComparison_of_bottomModel φ N hN M' hA ψ
    have := preservesFiniteLimits_pb_chartToSpace Y W
    have : (pb (chartToSpace B S hS Y W)).Additive := modulePullback_additive _
    have := preservesFiniteColimits_pb (chartToSpace B S hS Y W)
    have : IsIso ((pb (chartToSpace B S hS Y W)).homologyComparisonRightExactHomologyComparison
        (((pb g).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) a) :=
      (pb _).isIso_homologyComparison_of_preservesFiniteLimits_rightExactHomologyComparison _ a
    have heq : ψ ≫ φ = chartToSpace B S hS Y W ≫ g := by
      refine InducedCategory.hom_ext ?_
      change yoneda.map k ≫ (yoneda.map (openSubHom W₀.1.left O) ≫ W₀.1.hom) = W.1.hom ≫ g.hom
      exact hk
    exact (Functor.isIso_map_homologyComparison_iff_leftExactHomologyComparison (pb g)
      (pb (chartToSpace B S hS Y W)) (pb (chartToSpace B S hS Y W ≫ g))
      (modulePullbackCompIso B S hS _ g) N a).2 ((isIso_homologyComparison_congr heq N a).1 h1)
  choose V hV hiso using hloc
  exact isIso_of_isIso_modulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_of_forall_mem_range B S hS fun y => ⟨y, hV y⟩) _ hiso

end Vanishing

/-! ### Base change of `f_*E` over the stratum -/

/-- **The formation of `f₀_*E₀` commutes with base change over the stratum.** -/
theorem isIso_moduleBaseChangeMap_of_isUniversallyFreeBottom {X Y Y₀ : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hP : IsProper B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (E : Modules.{u, u} B S hS X.1 X.2)
    (hE : SheafOfModules.IsFiniteLocallyFree E) (q : Y₀ ⟶ Y) {r : ℕ}
    (hq : IsUniversallyFreeBottom (pushforwardComplex f E) 0 r q)
    {T : AlgebraicSpaces B S hS} (h : T ⟶ Y₀) :
    IsIso ((moduleBaseChangeMap (pullback.snd f q) h (pullback.snd (pullback.snd f q) h)
      (pullback.fst (pullback.snd f q) h) pullback.condition).app
        ((modulePullback B S hS (pullback.fst f q)).obj E)) := by
  have hE₀ : SheafOfModules.IsFiniteLocallyFree
      ((modulePullback B S hS (pullback.fst f q)).obj E) :=
    isFiniteLocallyFree_modulePullback _ hE
  obtain ⟨Kc, hKc, ⟨eK⟩⟩ := exists_kFlat_model (pushforwardComplex f E)
  have hcmp := isIso_homologyComparison_of_isUniversallyFreeBottom
    (isPerfect_pushforwardComplex f hP hfp hfl E hE)
    (fun Y' g j hj => isZero_pullbackHomology_pushforwardComplex f hP hfp hfl E hE g j hj)
    q hq Kc hKc eK h
  obtain ⟨e₁⟩ := nonempty_pullback_pushforwardComplex_iso f hP hfp hfl E hE q
  have hbc := (isPerfect_derivedModulePushforward_single_and_isIso_baseChange
    (pullback.snd f q) (isProper_snd f q hP) (isFinitePresentation_snd f q hfp) _
    (isFinitePresentation_modules_of_isFiniteLocallyFree _ hE₀)
    (isFlatOver_of_isFiniteLocallyFree _ (isFlat_snd f q hfl) _ hE₀)).2 h
    (pullback.snd (pullback.snd f q) h) (pullback.fst (pullback.snd f q) h)
    (IsPullback.of_hasPullback _ _)
  exact isIso_moduleBaseChangeMap_app_of_isIso_homologyComparison (pullback.snd f q) h
    (pullback.snd (pullback.snd f q) h) (pullback.fst (pullback.snd f q) h) pullback.condition
    _ _ (smallEtaleModuleKFlat_pb q Kc hKc)
    (((smallEtaleDerivedModulePullback B S hS q).mapIso eK.symm ≪≫
      smallEtaleDerivedModulePullbackObjQIsoOfKFlat q Kc hKc).symm ≪≫ e₁) hcmp hbc

end AlgebraicGeometry.Space.DescentStratum

end
