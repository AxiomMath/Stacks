module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackScalarFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyClosedSubfunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankChartModelExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankFitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorAmplitudeKFlatModel

/-!
# The bottom rank stratum of a perfect complex on an algebraic space

Let `E` be a perfect object of `D(𝒪_X)` of Tor amplitude in `[a, b]` on an algebraic space `X`
and let `r ≥ 0`. The subfunctor of `X` of the morphisms universally of bottom rank `r` is a
locally closed subspace of finite presentation: on an affine étale chart carrying a bottom model
with matrix `A` it is `V(Fit_{r-1}(C_A)) ∩ D(Fit_r(C_A))`. This is Stacks 0D21,
`AlgebraicGeometry.Space.BottomRankLocus.exists_isBottomRankStratum_isFinitePresentation`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.BottomRankLocus

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
  {a : ℤ} {r : ℕ}

/-- A morphism of represented functors is the image under `yoneda` of the morphism of the site it
corresponds to under `yonedaEquiv`. -/
theorem yoneda_map_yonedaEquiv {U T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ yoneda.obj U) :
    yoneda.map (yonedaEquiv f) = f :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map _)

/-- **The candidate stratum is étale local on the source.** -/
theorem isEtaleLocalOnSource_bottomRankSubfunctor :
    IsEtaleLocalOnSource (bottomRankSubfunctor E a r) := by
  intro T x hx
  change IsUniversallyFreeBottom E a r (sectionMap T x)
  refine isUniversallyFreeBottom_of_forall_chart _ fun y => ?_
  obtain ⟨W, hW, hmem⟩ := hx y
  refine ⟨W, hW, ?_⟩
  have h : IsUniversallyFreeBottom E a r
      (sectionMap W.1.left (X.1.map (yonedaEquiv W.1.hom).op x)) := hmem
  rw [sectionMap_map] at h
  have e : chartToSpace B S hS (representedAlgebraicSpace B S hS T) W =
      representedSpaceMap B S hS (yonedaEquiv W.1.hom) :=
    InducedCategory.hom_ext (yoneda_map_yonedaEquiv W.1.hom).symm
  rw [e]
  exact h

/-- The morphism to `X` given by the section of an étale chart `V` is the chart map of `V`. -/
theorem sectionMap_yonedaEquiv (V : SmallEtale B S hS X.1) :
    sectionMap V.1.left (yonedaEquiv V.1.hom) = chartToSpace B S hS X V :=
  InducedCategory.hom_ext (Equiv.symm_apply_apply _ _)

/-- **On an affine chart with a bottom model of matrix `A`, the candidate stratum is cut out by
`Fit_{r-1}(C_A)` and `Fit_r(C_A)`.** -/
theorem isCutOutBy_bottomRankSubfunctor (V : SmallEtale B S hS X.1) {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) (repRing V.1.left)}
    (M : BottomModel (Y := representedAlgebraicSpace B S hS V.1.left)
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
      (repRho V.1.left) A) :
    IsCutOutBy (bottomRankSubfunctor E a r) V.1.hom
      (_root_.fittingIdeal (R := repRing V.1.left) (M := A.cokerTransposeKernelRankStratum)
        ((r : ℤ) - 1))
      (_root_.fittingIdeal (R := repRing V.1.left) (M := A.cokerTransposeKernelRankStratum)
        (r : ℤ)) := by
  intro T hT t
  have := hT
  have hθ : repTheta t = ((BigFppfOver.toScheme B S hS).map t).appTop.hom :=
    RingHom.ext (repTheta_apply t)
  have key := M.isUniversallyFreeBottom_iff (r := r) t
  rw [Matrix.fittingIdeal_cokerTranspose_map_kernelRankStratum,
    Matrix.fittingIdeal_cokerTranspose_map_kernelRankStratum, hθ] at key
  refine Iff.trans ?_ key
  change IsUniversallyFreeBottom E a r (sectionMap T (X.1.map t.op (yonedaEquiv V.1.hom))) ↔ _
  rw [sectionMap_map, sectionMap_yonedaEquiv]
  exact isUniversallyFreeBottom_comp_iff _ _

open Stacks.SheafOfModules (DerivedTensorProduct) in
/-- Every point lies in an affine étale chart carrying a bottom model of `E` in degree `a`, when
`E` is perfect of Tor amplitude in `[a, b]`. -/
theorem exists_chart_bottomModel
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (b : ℤ)
    (hT : DerivedTensorProduct.HasTorAmplitude T E a b) (x : points B S hS X.1) :
    ∃ V : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) (repRing V.1.left)),
        Nonempty (BottomModel (Y := representedAlgebraicSpace B S hS V.1.left)
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
          (repRho V.1.left) A) :=
  exists_smallEtale_bottomModel B S hS E hE a (fun _ f j hj =>
    isZero_pullbackHomology_of_hasTorAmplitudeGE T E a
      (Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_of_hasTorAmplitude T E a b hT)
      f j hj) x

open Stacks.SheafOfModules (DerivedTensorProduct) in
/-- **The candidate stratum is a locally closed subspace of finite presentation.** -/
theorem isAlgebraicSpace_isImmersion_isFinitePresentation_bottomRankSubfunctor
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (b : ℤ)
    (hT : DerivedTensorProduct.HasTorAmplitude T E a b) :
    IsAlgebraicSpace B S hS (bottomRankSubfunctor E a r).toFunctor ∧
      IsImmersion B S hS (bottomRankSubfunctor E a r).ι ∧
      IsFinitePresentation B S hS (bottomRankSubfunctor E a r).ι := by
  have hchart : ∀ x : points B S hS X.1, ∃ V : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ I J : Ideal Γ(chartScheme V, ⊤),
        IsCutOutBy (bottomRankSubfunctor E a r) V.1.hom I J ∧ I.FG ∧ J.FG := by
    intro x
    obtain ⟨V, hx, hV, m, n, A, hM⟩ := exists_chart_bottomModel T hE b hT x
    have M := hM.some
    exact ⟨V, hx, hV, _, _, isCutOutBy_bottomRankSubfunctor V M,
      Matrix.fg_fittingIdeal_cokerTranspose_kernelRankStratum A _,
      Matrix.fg_fittingIdeal_cokerTranspose_kernelRankStratum A _⟩
  have hchart₀ : ∀ x : points B S hS X.1, ∃ V : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ I J : Ideal Γ(chartScheme V, ⊤),
        IsCutOutBy (bottomRankSubfunctor E a r) V.1.hom I J := fun x => by
    obtain ⟨V, hx, hV, I, J, h, -⟩ := hchart x
    exact ⟨V, hx, hV, I, J, h⟩
  obtain ⟨h₁, h₂⟩ := isAlgebraicSpace_and_isImmersion_of_isCutOutBy X.2
    isEtaleLocalOnSource_bottomRankSubfunctor hchart₀
  exact ⟨h₁, h₂, isFinitePresentation_ι_of_isCutOutBy X.2
    isEtaleLocalOnSource_bottomRankSubfunctor hchart⟩

/-- A morphism factors through the candidate stratum, read as an algebraic space, exactly when
it is universally of bottom rank `r`. -/
theorem exists_comp_homMk_ι_iff
    (hZ : IsAlgebraicSpace B S hS (bottomRankSubfunctor E a r).toFunctor)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    (∃ g : Y ⟶ ⟨_, hZ⟩, g ≫ ObjectProperty.homMk (bottomRankSubfunctor E a r).ι = f) ↔
      IsUniversallyFreeBottom E a r f := by
  rw [← exists_lift_bottomRankSubfunctor_iff f]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.hom, rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨ObjectProperty.homMk g, InducedCategory.hom_ext hg⟩

/-- The candidate stratum, once it is a locally closed subspace, is a bottom rank `r` stratum. -/
theorem isBottomRankStratum_homMk_ι
    (hZ : IsAlgebraicSpace B S hS (bottomRankSubfunctor E a r).toFunctor)
    (himm : IsImmersion B S hS (bottomRankSubfunctor E a r).ι) :
    IsBottomRankStratum E a r
      (ObjectProperty.homMk (bottomRankSubfunctor E a r).ι :
        (⟨_, hZ⟩ : AlgebraicSpaces B S hS) ⟶ X) where
  isImmersion := himm
  freeRank := ((exists_comp_homMk_ι_iff hZ _).1 ⟨𝟙 _, Category.id_comp _⟩).self
  factorsThrough_iff _Y f := exists_comp_homMk_ι_iff hZ f

/-- A chart lift as in `AlgebraicGeometry.Space.exists_smallEtale_chart_lift`, through an affine
chart. -/
theorem exists_affine_smallEtale_chart_lift {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (V : SmallEtale B S hS X.1) (y : points B S hS Y.1)
    (hy : pointsMap B S hS Y.1 f.hom y ∈
      Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom)) :
    ∃ (W : SmallEtale B S hS Y.1) (k : W.1.left ⟶ V.1.left),
      y ∈ Set.range (pointsMap B S hS (yoneda.obj W.1.left) W.1.hom) ∧
        IsAffine (chartScheme W) ∧
        chartToSpace B S hS Y W ≫ f = representedSpaceMap B S hS k ≫ chartToSpace B S hS X V := by
  obtain ⟨W, k, ⟨w, rfl⟩, hk⟩ := exists_smallEtale_chart_lift B S hS Y.2 f.hom V y hy
  obtain ⟨_, ⟨O, hO, rfl⟩, hwO, -⟩ :=
    (chartScheme W).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pointsToScheme B S hS W.1.left w)) isOpen_univ
  refine ⟨openChart B S hS Y.1 W O, openSubHom _ O ≫ k, ?_, hO, ?_⟩
  · rw [range_pointsMap_openChart]
    exact ⟨w, hwO, rfl⟩
  · refine InducedCategory.hom_ext ?_
    change (yoneda.map (openSubHom _ O) ≫ W.1.hom) ≫ f.hom =
      yoneda.map (openSubHom _ O ≫ k) ≫ V.1.hom
    rw [Functor.map_comp, Category.assoc, Category.assoc, hk]

/-- The restriction to an affine chart `W` of `H^a(Lf^*E)` is the cohomology of the pullback of `E`
to `V` along the factorization `W ⟶ V` of the composite `W ⟶ Y ⟶ X`. -/
private def pullbackHomologyChartIso {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (V : SmallEtale B S hS X.1) (W : SmallEtale B S hS Y.1) (k : W.1.left ⟶ V.1.left)
    (hk : chartToSpace B S hS Y W ≫ f = representedSpaceMap B S hS k ≫ chartToSpace B S hS X V) :
    (modulePullback B S hS (chartToSpace B S hS Y W)).obj (pullbackHomology E a f) ≅
      pullbackHomology (X := representedAlgebraicSpace B S hS V.1.left)
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
        (representedSpaceMap B S hS k) :=
  (homologyDerivedPullbackChartIso B S hS f E a W).symm ≪≫
    eqToIso (congrArg (fun φ => pullbackHomology E a φ) hk) ≪≫
    (pullbackHomologyCompIso E a _ _).symm

/-- A morphism is universally of bottom rank `r` as soon as, at every point, it is so after pulling
back `E` to an affine chart with a bottom model whose matrix has `Fit_r(C_A) = Γ`, along a
factorization of the chart of the source through the chart of the model. -/
private theorem isUniversallyFreeBottom_of_forall_chart_bottomModel
    (hchart : ∀ x : points B S hS X.1, ∃ V : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) (repRing V.1.left)),
        Nonempty (BottomModel (Y := representedAlgebraicSpace B S hS V.1.left)
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
          (repRho V.1.left) A) ∧
        _root_.fittingIdeal (R := repRing V.1.left) (M := A.cokerTransposeKernelRankStratum)
          (r : ℤ) = ⊤)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (h : ∀ (V : SmallEtale B S hS X.1) {m n : ℕ} {A : Matrix (Fin m) (Fin n) (repRing V.1.left)},
      BottomModel (Y := representedAlgebraicSpace B S hS V.1.left)
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
        (repRho V.1.left) A →
      ∀ (W : SmallEtale B S hS Y.1) (k : W.1.left ⟶ V.1.left),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) →
      _root_.fittingIdeal (R := repRing V.1.left) (M := A.cokerTransposeKernelRankStratum)
        (r : ℤ) = ⊤ →
      chartToSpace B S hS Y W ≫ f = representedSpaceMap B S hS k ≫ chartToSpace B S hS X V →
      IsUniversallyFreeBottom ((smallEtaleDerivedModulePullback B S hS
        (chartToSpace B S hS X V)).obj E) a r (representedSpaceMap B S hS k)) :
    IsUniversallyFreeBottom E a r f := by
  refine isUniversallyFreeBottom_of_forall_chart f fun y => ?_
  obtain ⟨V, hV, m, n, A, hM, htop⟩ := hchart (pointsMap B S hS Y.1 f.hom y)
  obtain ⟨W, k, hyW, hWaff, hk⟩ := exists_affine_smallEtale_chart_lift f V y hV
  refine ⟨W, hyW, ?_⟩
  rw [hk]
  exact (isUniversallyFreeBottom_comp_iff _ _).2 (h V hM.some W k hWaff htop hk)

/-- **Where `Fit_r` is the unit ideal on charts, plain local freeness is universal**: if every
point lies in an affine chart with a bottom model whose matrix has `Fit_r(C_A) = Γ`, then a
morphism `f` with `H^a(Lf^*E)` finite locally free of rank `r` is universally of bottom rank
`r`. -/
theorem isUniversallyFreeBottom_of_isFiniteLocallyFreeOfIntRank
    (hchart : ∀ x : points B S hS X.1, ∃ V : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) (repRing V.1.left)),
        Nonempty (BottomModel (Y := representedAlgebraicSpace B S hS V.1.left)
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
          (repRho V.1.left) A) ∧
        _root_.fittingIdeal (R := repRing V.1.left) (M := A.cokerTransposeKernelRankStratum)
          (r : ℤ) = ⊤)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : SheafOfModules.IsFiniteLocallyFreeOfIntRank (pullbackHomology E a f) (r : ℤ)) :
    IsUniversallyFreeBottom E a r f := by
  refine isUniversallyFreeBottom_of_forall_chart_bottomModel hchart f
    fun V _ _ _ M W k _ htop hk => M.isUniversallyFreeBottom_of_fittingIdeal_eq_top k htop ?_
  exact isFiniteLocallyFreeOfIntRank_of_iso B S hS (pullbackHomologyChartIso f V W k hk)
    (isFiniteLocallyFreeOfIntRank_modulePullback_chartToSpace B S hS _ r hf W)

/-! ### Betti numbers at geometric points -/

/-- The morphism to `X` from the spectrum of the field of a geometric point. -/
abbrev geometricPointMap (p : GeometricPoint B S hS X.1) :
    representedAlgebraicSpace B S hS p.val.siteObject ⟶ X :=
  sectionMap p.val.siteObject p.val.value

/-- **The `a`-th Betti number of `E` at a field point** `x : Spec k ⟶ X` given by a section `x`
of `X` over the object `T = Spec k` of the site: the dimension of the global sections of
`H^a(Lx^*E)`, that is, of `H^a(E ⊗^L k)`. -/
def bettiAt (E : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS X))) (a : ℤ) (T : BigFppfOver B S hS)
    (x : X.1.obj (op T)) : ℕ :=
  sectionsFinrank T (pullbackHomology E a (sectionMap T x))

/-- The morphism to `X` given by the section of an étale chart `V` restricted along `t : T ⟶ V`
is the chart map of `V` precomposed with the represented morphism of `t`. -/
theorem sectionMap_app_chartToSpace (V : SmallEtale B S hS X.1) {T : BigFppfOver B S hS}
    (t : T ⟶ V.1.left) :
    sectionMap T (V.1.hom.app _ t) =
      representedSpaceMap B S hS t ≫ chartToSpace B S hS X V :=
  InducedCategory.hom_ext (yonedaEquiv.injective (by
    change yonedaEquiv (yonedaEquiv.symm (V.1.hom.app _ t)) = yonedaEquiv (yoneda.map t ≫ V.1.hom)
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]))

/-- At a field point of a chart carrying a bottom model, the Betti number bounds the rank of a
free kernel splitting of the pulled-back matrix. -/
theorem le_of_bettiAt_le (V : SmallEtale B S hS X.1) {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) (repRing V.1.left)}
    (M : BottomModel (Y := representedAlgebraicSpace B S hS V.1.left)
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
      (repRho V.1.left) A)
    {T : BigFppfOver B S hS} (t : T ⟶ V.1.left) [Nontrivial (repRing T)]
    (hβ : bettiAt E a T (V.1.hom.app _ t) ≤ r) {d : ℕ}
    (hsplit : (A.map (repTheta t)).HasFreeKernelSplittingKernelRankStratum d) : d ≤ r := by
  have h1 : sectionsFinrank T (pullbackHomology E a (sectionMap T (V.1.hom.app _ t))) ≤ r := hβ
  have e : pullbackHomology E a (sectionMap T (V.1.hom.app _ t)) ≅
      pullbackHomology (X := representedAlgebraicSpace B S hS V.1.left)
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
        (representedSpaceMap B S hS t) :=
    eqToIso (congrArg (fun k => pullbackHomology E a k) (sectionMap_app_chartToSpace V t)) ≪≫
      (pullbackHomologyCompIso E a _ _).symm
  exact BottomModel.le_of_sectionsFinrank_le_of_iso (U := V.1.left) M t hsplit e h1

/-- **A bound on the Betti numbers makes `Fit_r(C_A)` the unit ideal on every affine chart with a
bottom model of matrix `A`.** -/
theorem fittingIdeal_eq_top_of_geometricPointBetti_le
    (hβ : ∀ p : GeometricPoint B S hS X.1, bettiAt E a p.val.siteObject p.val.value ≤ r)
    (V : SmallEtale B S hS X.1) [IsAffine (chartScheme V)] {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) (repRing V.1.left)}
    (M : BottomModel (Y := representedAlgebraicSpace B S hS V.1.left)
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
      (repRho V.1.left) A) :
    _root_.fittingIdeal (R := repRing V.1.left) (M := A.cokerTransposeKernelRankStratum)
      (r : ℤ) = ⊤ := by
  by_contra hne
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := ‹IsAffine (chartScheme V)›
  obtain ⟨q, hq⟩ := exists_geometricPoint_repTheta_eq_zero V.1.left _ hne
  let ε : repRing q.val.siteObject ≃+* q.val.carrier :=
    (Scheme.ΓSpecIso (CommRingCat.of q.val.carrier)).commRingCatIsoToRingEquiv
  let φ : repRing V.1.left →+* q.val.carrier := ε.toRingHom.comp (repTheta q.val.value)
  refine Matrix.not_fittingIdeal_cokerTranspose_le_kernelRankStratum A φ r ?_
    (fun f hf => (RingHom.mem_ker).2 (by simp [φ, hq f hf]))
  have hsplit := (Matrix.hasFreeKernelSplitting_finrank_ker (A.map φ)).map ε.symm.toRingHom
  have hφ : (A.map φ).map ε.symm.toRingHom =
      A.map (repTheta (T := q.val.siteObject) q.val.value) := by
    ext i j
    simp only [Matrix.map_apply, φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  rw [hφ] at hsplit
  have : Nontrivial (repRing q.val.siteObject) := ε.symm.injective.nontrivial
  have h2 : bettiAt E a q.val.siteObject (V.1.hom.app (op q.val.siteObject) q.val.value) ≤ r :=
    hβ ⟨FieldValuedPoint.map B S hS _ V.1.hom q.val, q.property⟩
  have key : ∀ d, (A.map (repTheta (T := q.val.siteObject)
      q.val.value)).HasFreeKernelSplittingKernelRankStratum d → d ≤ r :=
    fun d h => le_of_bettiAt_le (T := q.val.siteObject) V M q.val.value h2 h
  exact key _ hsplit


open Stacks.SheafOfModules (DerivedTensorProduct) in
/-- Under a Betti bound, every point lies in an affine chart with a bottom model whose matrix has
`Fit_r(C_A)` the unit ideal. -/
theorem exists_chart_bottomModel_fittingIdeal_eq_top
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (b : ℤ)
    (hT : DerivedTensorProduct.HasTorAmplitude T E a b)
    (hβ : ∀ p : GeometricPoint B S hS X.1, bettiAt E a p.val.siteObject p.val.value ≤ r)
    (x : points B S hS X.1) :
    ∃ V : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) (repRing V.1.left)),
        Nonempty (BottomModel (Y := representedAlgebraicSpace B S hS V.1.left)
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) a
          (repRho V.1.left) A) ∧
        _root_.fittingIdeal (R := repRing V.1.left) (M := A.cokerTransposeKernelRankStratum)
          (r : ℤ) = ⊤ := by
  obtain ⟨V, hx, hV, m, n, A, hM⟩ := exists_chart_bottomModel T hE b hT x
  have : IsAffine (chartScheme V) := hV
  exact ⟨V, hx, hV, m, n, A, hM, fittingIdeal_eq_top_of_geometricPointBetti_le hβ V hM.some⟩

open Stacks.SheafOfModules (DerivedTensorProduct) in
/-- **Under a Betti bound the candidate stratum is closed.** -/
theorem isClosedImmersion_bottomRankSubfunctor
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (b : ℤ)
    (hT : DerivedTensorProduct.HasTorAmplitude T E a b)
    (hβ : ∀ p : GeometricPoint B S hS X.1, bettiAt E a p.val.siteObject p.val.value ≤ r) :
    IsClosedImmersion B S hS (bottomRankSubfunctor E a r).ι := by
  refine isClosedImmersion_ι_of_isCutOutBy X.2 isEtaleLocalOnSource_bottomRankSubfunctor
    fun x => ?_
  obtain ⟨V, hx, hV, m, n, A, hM, htop⟩ :=
    exists_chart_bottomModel_fittingIdeal_eq_top T hE b hT hβ x
  have h := isCutOutBy_bottomRankSubfunctor (r := r) V hM.some
  rw [htop] at h
  exact ⟨V, hx, hV, _, h⟩

open Stacks.SheafOfModules (DerivedTensorProduct) in
/-- **Under a Betti bound, plain local freeness of `H^a(Lf^*E)` is universal.** -/
theorem isUniversallyFreeBottom_iff_of_bettiAt_le
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (b : ℤ)
    (hT : DerivedTensorProduct.HasTorAmplitude T E a b)
    (hβ : ∀ p : GeometricPoint B S hS X.1, bettiAt E a p.val.siteObject p.val.value ≤ r)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    IsUniversallyFreeBottom E a r f ↔
      SheafOfModules.IsFiniteLocallyFreeOfIntRank (pullbackHomology E a f) (r : ℤ) :=
  ⟨fun h => h.self, isUniversallyFreeBottom_of_isFiniteLocallyFreeOfIntRank (fun x => by
    obtain ⟨V, hx, -, m, n, A, hM, htop⟩ :=
      exists_chart_bottomModel_fittingIdeal_eq_top T hE b hT hβ x
    exact ⟨V, hx, m, n, A, hM, htop⟩) f⟩


/-! ### Split bottom models on the charts of the stratum -/

/-- The chart map of the open subchart of `W` on `O` is the chart map of `W` precomposed with
the represented inclusion of `O`. -/
theorem chartToSpace_openChart {Z : AlgebraicSpaces B S hS} (W : SmallEtale B S hS Z.1)
    (O : ((BigFppfOver.toScheme B S hS).obj W.1.left).Opens) :
    chartToSpace B S hS Z (openChart B S hS Z.1 W O) =
      representedSpaceMap B S hS (openSubHom W.1.left O) ≫ chartToSpace B S hS Z W :=
  InducedCategory.hom_ext rfl

open Stacks.SheafOfModules (DerivedTensorProduct) in
/-- **Split bottom models along a morphism universally of bottom rank `r`.** If `j : Z ⟶ X` is
universally of bottom rank `r`, every point of `Z` lies in a chart `W` of `Z` on which `E`
pulled back along `W ⟶ Z ⟶ X` has a bottom model whose matrix has a free kernel splitting of
rank `r`. -/
theorem exists_chart_splitBottomModel
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (b : ℤ)
    (hT : DerivedTensorProduct.HasTorAmplitude T E a b) {Z : AlgebraicSpaces B S hS}
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
    exists_chart_bottomModel T hE b hT (pointsMap B S hS Z.1 j.hom z)
  have M := hM.some
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
      have hk' := congrArg (fun φ => φ.hom) hk
      change W₀.1.hom ≫ j.hom = yoneda.map k ≫ V.1.hom at hk'
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


open Stacks.SheafOfModules (DerivedTensorProduct) in
/-- **Base change of the bottom cohomology along a morphism universally of bottom rank `r`.**
If `E` is perfect of Tor amplitude in `[a, b]` and `j : Z ⟶ X` is universally of bottom rank `r`,
then for every `g : Y ⟶ Z` the comparison `g^* H^a(Lj^*E) ⟶ H^a(L(g ∘ j)^*E)`, read on a K-flat
model of `E` vanishing below `a`, is an isomorphism. -/
theorem nonempty_pullbackHomology_comp_iso
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (b : ℤ)
    (hT : DerivedTensorProduct.HasTorAmplitude T E a b) {Z : AlgebraicSpaces B S hS}
    (j : Z ⟶ X) (hj : IsUniversallyFreeBottom E a r j) {Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ Z) :
    Nonempty (pullbackHomology E a (g ≫ j) ≅ (pb g).obj (pullbackHomology E a j)) := by
  obtain ⟨K, hK, hKa, ⟨e⟩⟩ := exists_kFlat_isStrictlyGE_of_hasTorAmplitudeGE T E a
    (DerivedTensorProduct.hasTorAmplitudeGE_of_hasTorAmplitude T E a b hT)
  let N := ((pb j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hN : smallEtaleModuleKFlat B S hS Z
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) := smallEtaleModuleKFlat_pb j K hK
  have : (pb g).Additive := modulePullback_additive _
  have := preservesFiniteColimits_pb g
  have key : IsIso ((pb g).homologyComparisonRightExactHomologyComparison N a) := by
    have hloc : ∀ y : points B S hS Y.1, ∃ W : SmallEtale B S hS Y.1,
        y ∈ Set.range (pointsMap B S hS (yoneda.obj W.1.left) W.1.hom) ∧
        IsIso ((pb (chartToSpace B S hS Y W)).map
          ((pb g).homologyComparisonRightExactHomologyComparison N a)) := by
      intro y
      obtain ⟨W₀, O, hz, m, n, A, hA, hM⟩ :=
        exists_chart_splitBottomModel T hE b hT j hj (pointsMap B S hS Y.1 g.hom y)
      let φ := representedSpaceMap B S hS (openSubHom W₀.1.left O) ≫ chartToSpace B S hS Z W₀
      have : PreservesFiniteLimits (pb φ) := by
        have h := preservesFiniteLimits_pb_chartToSpace Z (openChart B S hS Z.1 W₀ O)
        rw [chartToSpace_openChart] at h
        exact h
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
      have heq : ψ ≫ φ = chartToSpace B S hS Y W ≫ g := InducedCategory.hom_ext hk
      have h2 := (isIso_homologyComparison_congr heq N a).1 h1
      exact (Functor.isIso_map_homologyComparison_iff_leftExactHomologyComparison (pb g)
        (pb (chartToSpace B S hS Y W)) (pb (chartToSpace B S hS Y W ≫ g))
        (modulePullbackCompIso B S hS _ g) N a).2 h2
    choose V hV hiso using hloc
    exact isIso_of_isIso_modulePullback_chartToSpace B S hS
      (SmallEtale.coversTop_of_forall_mem_range B S hS fun y => ⟨y, hV y⟩) _ hiso
  let hj' : pullbackHomology E a j ≅ N.homology a :=
    (DerivedCategory.homologyFunctor _ a).mapIso
      (smallEtaleDerivedModulePullbackObjIsoOfKFlat K hK e j) ≪≫
      (DerivedCategory.homologyFunctorFactors _ a).app N
  have : (pb (g ≫ j)).Additive := modulePullback_additive _
  have : (pb j).Additive := modulePullback_additive _
  exact ⟨(DerivedCategory.homologyFunctor _ a).mapIso
      (smallEtaleDerivedModulePullbackObjIsoOfKFlat K hK e (g ≫ j)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ a).app _ ≪≫
    HomologicalComplex.homologyMapIso
      (Functor.mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison (pb j) (pb g)
        (pb (g ≫ j)) (modulePullbackCompIso B S hS g j) K) a ≪≫
    (asIso ((pb g).homologyComparisonRightExactHomologyComparison N a)).symm ≪≫
      (pb g).mapIso hj'.symm⟩


/-! ### Rank one: faithfulness of the scalar action -/

open Stacks.SheafOfModules (DerivedTensorProduct) in
/-- **Under a Betti bound `β_a ≤ 1`, a faithful action of `𝒪_Y` on `H^a(Lf^*E)` makes `f`
universally of bottom rank one.** On an affine chart with a bottom model of matrix `A`, the ideal
`Fit_1(C_A)` is the unit ideal, and every `x ∈ Fit_0(C_A)` has `N A = x · 1` for some `N`, so it
kills `ker A ≅ H^a(Lf^*E)|_W` and therefore vanishes. -/
theorem isUniversallyFreeBottom_of_isScalarFaithful
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (b : ℤ)
    (hT : DerivedTensorProduct.HasTorAmplitude T E a b)
    (hβ : ∀ p : GeometricPoint B S hS X.1, bettiAt E a p.val.siteObject p.val.value ≤ 1)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : AlgebraicGeometry.SheafOfModules.IsScalarFaithful (pullbackHomology E a f)) :
    IsUniversallyFreeBottom E a 1 f := by
  refine isUniversallyFreeBottom_of_forall_chart_bottomModel
    (fun x => let ⟨V, hx, _, h⟩ :=
        exists_chart_bottomModel_fittingIdeal_eq_top (r := 1) T hE b hT hβ x
      ⟨V, hx, h⟩) f fun V _ _ _ M W k _ htop hk => (M.isUniversallyFreeBottom_iff k).2 ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_bot]
    have h10 : ((1 : ℕ) : ℤ) - 1 = 0 := by norm_num
    rw [h10] at hx
    obtain ⟨N, hN⟩ := Matrix.exists_mul_eq_smul_one_of_mem_fittingIdeal_zero_kernelRankStratum _ hx
    have h3 := (isScalarFaithful_modulePullback B S hS (chartToSpace B S hS Y W)
      (isEtale_chartToSpace B S hS Y W) hf).of_iso (pullbackHomologyChartIso f V W k hk)
    have h4 := h3.of_iso (M.pullbackRep k).homologyIsoKernel
    exact h4.eq_zero_of_mul_eq_smul_one (isTerminal_idChart B S hS W.1.left) hN
  · rw [Matrix.fittingIdeal_cokerTranspose_map_kernelRankStratum, htop, Ideal.map_top]

/-! ### The bottom rank stratum -/

open Stacks.SheafOfModules (DerivedTensorProduct) in
/-- **Stacks 0D21.** Let `E` be a perfect object of `D(𝒪_X)` of Tor amplitude in `[a, b]` and
`r ≥ 0`. There is an immersion `j : Z ⟶ X` of algebraic spaces, of finite presentation, such that
(1) `H^a(Lj^*E)` is finite locally free of rank `r`, (2) a morphism `f : Y ⟶ X` factors through
`j` exactly when `H^a(L(f ∘ g)^*E)` is finite locally free of rank `r` for every `g : Y' ⟶ Y`,
(3) for `f = j ∘ g` we have `H^a(Lf^*E) ≅ g^*H^a(Lj^*E)`, and (4) if `β_a(p) ≤ r` at every
geometric point `p` of `X` (`bettiAt`, the dimension of `H^a(E ⊗^L k(p))`), then `j` is a closed
immersion, `f` factors through `j` exactly when `H^a(Lf^*E)` is finite locally free of rank `r`,
and, for `r = 1`, exactly when `𝒪_Y → ℋom(H^a(Lf^*E), H^a(Lf^*E))` is injective.

The source writes `H^0` in (4)(b) and (4)(c); for `a ≠ 0` that reading is false: for
`E = 𝒪_X[-a]` and `r = 1` the stratum is all of `X`, so every `f : Y ⟶ X` factors through it, while
`H^0(Lf^*E) = 0` is not locally free of rank `1` when `Y` is nonempty. The statement here uses
`H^a`, as in the corrected scheme version [stacks 0BDL]. -/
@[stacks 0D21]
theorem exists_isBottomRankStratum_isFinitePresentation
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) (b : ℤ)
    (hT : DerivedTensorProduct.HasTorAmplitude T E a b) (r : ℕ) :
    ∃ (Z : AlgebraicSpaces B S hS) (j : Z ⟶ X),
      IsBottomRankStratum E a r j ∧ IsFinitePresentation B S hS j.hom ∧
        (∀ (Y : AlgebraicSpaces B S hS) (g : Y ⟶ Z),
          Nonempty (pullbackHomology E a (g ≫ j) ≅ (pb g).obj (pullbackHomology E a j))) ∧
        ((∀ p : GeometricPoint B S hS X.1, bettiAt E a p.val.siteObject p.val.value ≤ r) →
          IsClosedImmersion B S hS j.hom ∧ (∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X),
            ((∃ g : Y ⟶ Z, g ≫ j = f) ↔
              SheafOfModules.IsFiniteLocallyFreeOfIntRank (pullbackHomology E a f) (r : ℤ))) ∧
          (r = 1 → ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X),
            ((∃ g : Y ⟶ Z, g ≫ j = f) ↔
              AlgebraicGeometry.SheafOfModules.IsScalarFaithful (pullbackHomology E a f)))) := by
  obtain ⟨hZ, himm, hfp⟩ :=
    isAlgebraicSpace_isImmersion_isFinitePresentation_bottomRankSubfunctor (r := r) T hE b hT
  have hstr := isBottomRankStratum_homMk_ι hZ himm
  have hb := fun
      (hβ : ∀ p : GeometricPoint B S hS X.1, bettiAt E a p.val.siteObject p.val.value ≤ r)
      (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X) =>
    (hstr.factorsThrough_iff Y f).trans (isUniversallyFreeBottom_iff_of_bettiAt_le T hE b hT hβ f)
  refine ⟨_, _, hstr, hfp, fun Y g =>
    nonempty_pullbackHomology_comp_iso T hE b hT _ hstr.isUniversallyFreeBottom g,
    fun hβ => ⟨isClosedImmersion_bottomRankSubfunctor T hE b hT hβ, hb hβ, ?_⟩⟩
  rintro rfl Y f
  refine ⟨fun h => ?_, fun h => (hstr.factorsThrough_iff Y f).2
    (isUniversallyFreeBottom_of_isScalarFaithful T hE b hT hβ f h)⟩
  have h1 := (hb hβ Y f).1 h
  rw [Nat.cast_one] at h1
  exact AlgebraicGeometry.SheafOfModules.isScalarFaithful_of_isFiniteLocallyFreeOfIntRank_one _ h1

end AlgebraicGeometry.Space.BottomRankLocus
