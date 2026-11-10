module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapFinitePresentationClause
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartPointLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexGluing

/-!
# Relative dualizing complexes of algebraic spaces are étale local on the base

Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite presentation and
`(ω, τ)` a pair of a `Y`-perfect object of `D(𝒪_X)` and a map `Rf_* ω ⟶ 𝒪_Y`. If the base
changes of `(ω, τ)` to the members `Y_i` of an affine étale covering of `Y` are the pairs
`(a_i(𝒪_{Y_i}), Tr)`, then `(ω, τ)` is a relative dualizing complex (Stacks 0E60), granted that
`(a'(𝒪_{Y'}), Tr)` is a relative dualizing complex over every affine `Y'` (the third remark after
Stacks 0E5X). Over an affine `Y'` the map `L(g')^* ω ⟶ a'(𝒪_{Y'})` adjoint to `Lg^* τ` is
étale locally on `X'` a morphism of pairs over an affine base, hence an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isAffineBaseChangePair_of_iso`: the base change condition passes along
  isomorphisms of pairs.
* `AlgebraicGeometry.Space.RelativeDualizingPair.isAffineBaseChangePair_paste`: transitivity of
  the base change condition.
* `AlgebraicGeometry.Space.RelativeDualizingPair.isAffineBaseChangePair_of_isEtaleCovering`,
  `AlgebraicGeometry.Space.RelativeDualizingComplex.ofIsEtaleCovering`: Stacks 0E60, granted the
  affine case.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

section Aux

variable {C : Type*} [Category* C]

/-- The diagram chase behind `isAffineBaseChangePair_of_iso`, in an arbitrary category. -/
theorem isAffineBaseChangePair_of_iso_aux {P Q R T W O V : C} {a : P ⟶ Q} {b₁ : P ⟶ R}
    {b₂ : Q ⟶ T} {x : R ⟶ T} {y : T ⟶ W} {tr : W ⟶ O} {s₁ : P ⟶ V} {s₂ : Q ⟶ V} {u : V ⟶ O}
    {z : R ⟶ W} (hn : a ≫ b₂ = b₁ ≫ x) (h₂ : s₂ ≫ u = b₂ ≫ y ≫ tr) (hs : s₁ = a ≫ s₂)
    (hz : z = x ≫ y) : s₁ ≫ u = b₁ ≫ z ≫ tr := by
  rw [hs, hz, Category.assoc, h₂]
  simp only [Category.assoc]
  rw [reassoc_of% hn]

/-- The diagram chase behind `RelativeDualizingPair.isAffineBaseChangePair_paste`, in an
arbitrary category. -/
theorem isAffineBaseChangePair_paste_aux {D : Type*} [Category* D] (M : C ⥤ D) {P Q R : C}
    {U V O : D} {c : P ⟶ Q} {ci : Q ⟶ P} (hci : ci ≫ c = 𝟙 Q) {e₃ : P ⟶ R}
    {Tp : M.obj Q ⟶ O} {Ti : M.obj P ⟶ O} {tr : M.obj R ⟶ O} {a : O ⟶ O} {ai : O ⟶ O}
    (ha : a ≫ ai = 𝟙 O) (hA : Ti = M.map c ≫ Tp ≫ a) (hB : Ti = M.map e₃ ≫ tr)
    {bp : U ⟶ M.obj Q} {s : U ⟶ V} {uu : V ⟶ O} (hC : bp ≫ Tp = s ≫ uu) :
    s ≫ uu = bp ≫ M.map (ci ≫ e₃) ≫ tr ≫ ai := by
  have hTp : Tp = M.map ci ≫ Ti ≫ ai := by
    rw [hA]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hci, CategoryTheory.Functor.map_id, Category.id_comp, ha,
      Category.comp_id]
  rw [← hC, hTp, hB, Functor.map_comp]
  simp only [Category.assoc]

/-- A morphism conjugate to the image of an isomorphism is an isomorphism. -/
theorem isIso_of_eq_conj_aux {D : Type*} [Category* D] (F : C ⥤ D) {P Q : C} {P' Q' : D}
    {a : P' ⟶ F.obj P} {b : F.obj Q ⟶ Q'} (ha : IsIso a) (hb : IsIso b) {x : P ⟶ Q}
    (hx : IsIso x) {y : P' ⟶ Q'} (h : a ≫ F.map x ≫ b = y) : IsIso y := by
  subst h
  have := ha
  have := hb
  have := hx
  infer_instance

/-- A morphism whose composite with an isomorphism is invertible is invertible. -/
theorem isIso_of_isIso_comp_inv_aux {P Q R : C} {φ : P ⟶ Q} (e : R ≅ Q) (h : IsIso (φ ≫ e.inv)) :
    IsIso φ := by
  have := h
  exact IsIso.of_isIso_comp_right φ e.inv

/-- Cancelling an isomorphism inside a functor, in an arbitrary category. -/
theorem map_comp_inv_map_hom_aux {D : Type*} [Category* D] (F : C ⥤ D) {P Q R : C} {U : D}
    (φ : P ⟶ Q) (e : R ≅ Q) (T : F.obj Q ⟶ U) :
    F.map (φ ≫ e.inv) ≫ F.map e.hom ≫ T = F.map φ ≫ T := by
  rw [← Functor.map_comp_assoc, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- Composing with the inverse of an isomorphism compatible with the maps to `U`. -/
private theorem map_comp_inv_comp_eq {D : Type*} [Category* D] (F : C ⥤ D) {P Q R : C} {U : D}
    (φ : P ⟶ Q) (e : R ≅ Q) {T : F.obj Q ⟶ U} {T' : F.obj R ⟶ U} {τ : F.obj P ⟶ U}
    (he : F.map e.hom ≫ T = T') (h : F.map φ ≫ T = τ) : F.map (φ ≫ e.inv) ≫ T' = τ :=
  (whisker_eq _ he.symm).trans ((map_comp_inv_map_hom_aux F φ e T).trans h)

end Aux

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hfp : IsFinitePresentation B S hS f.hom)

/-- The base change condition only depends on the morphisms of the cartesian square. -/
theorem isAffineBaseChangePair_of_eq {g₁ g₂ : Y' ⟶ Y} {f' : X' ⟶ Y'} {g'₁ g'₂ : X' ⟶ X}
    (sq₁ : IsPullback g'₁ f' f g₁) (sq₂ : IsPullback g'₂ f' f g₂) (hg : g₁ = g₂)
    (hg' : g'₁ = g'₂) (hY' : IsAffineSpace B S hS Y'.1)
    {ω : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    {τ : (derivedModulePushforward B S hS f).obj ω ⟶ (derivedStructureSheaf B S hS Y.1 Y.2).obj}
    (h : IsAffineBaseChangePair hZ sq₁ hfp hY' ω τ) :
    IsAffineBaseChangePair hZ sq₂ hfp hY' ω τ := by
  subst hg hg'
  exact h

/-- **The base change condition passes along isomorphisms of pairs**: if `e : ω₁ ≅ ω₂` carries
`τ₂` to `τ₁` and the base change of `(ω₂, τ₂)` to an affine `Y'` is `(a'(𝒪_{Y'}), Tr)`, then so is
that of `(ω₁, τ₁)`. -/
theorem isAffineBaseChangePair_of_iso {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1)
    {ω₁ ω₂ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (e : ω₁ ≅ ω₂)
    {τ₁ : (derivedModulePushforward B S hS f).obj ω₁ ⟶ (derivedStructureSheaf B S hS Y.1 Y.2).obj}
    {τ₂ : (derivedModulePushforward B S hS f).obj ω₂ ⟶ (derivedStructureSheaf B S hS Y.1 Y.2).obj}
    (he : (derivedModulePushforward B S hS f).map e.hom ≫ τ₂ = τ₁)
    (h : IsAffineBaseChangePair hZ sq hfp hY' ω₂ τ₂) :
    IsAffineBaseChangePair hZ sq hfp hY' ω₁ τ₁ := by
  obtain ⟨e₂, h₂⟩ := h
  exact ⟨(smallEtaleDerivedModulePullback B S hS g').mapIso e ≪≫ e₂,
    isAffineBaseChangePair_of_iso_aux
      (smallEtaleDerivedModuleBaseChangeMap_naturality B S hS f g f' g' sq.w e.hom) h₂
      ((congrArg (smallEtaleDerivedModulePullback B S hS g).map he).symm.trans
        (Functor.map_comp _ _ _)) (Functor.map_comp _ _ _)⟩

end Square

section Cover

variable {X' Y' Y : AlgebraicSpaces B S hS}

/-- **Charts over an étale covering of the base cover.** Let `g : Y' ⟶ Y` be a morphism and
`{Y_i ⟶ Y}` an étale covering. The étale charts of `X'` carrying an affine chart diagram over
`f' : X' ⟶ Y'` to an affine chart of `Y'` that maps to some `Y_i` over `Y` cover `X'`. -/
theorem coversTop_hasAffineChartDiagramWith_of_isEtaleCovering (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    {ι : Type v} {Yi : ι → AlgebraicSpaces B S hS} {gi : ∀ i, Yi i ⟶ Y}
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (gi i).hom)) :
    (SmallEtale.topology B S hS X'.1).CoversTop (Subtype.val : {W : SmallEtale B S hS X'.1 //
      HasAffineChartDiagramWith B S hS f' (fun V => ∃ i, ∃ k : chartSpace B S hS Y' V ⟶ Yi i,
        k ≫ gi i = chartToSpace B S hS Y' V ≫ g) W} → SmallEtale B S hS X'.1) := by
  refine fun U => mem_topology_of_hasAffineChartDiagramWith B S hS _ f' ?_ ?_ U _
    fun {W} _ hW => ⟨⟨W, hW⟩, ⟨𝟙 W⟩⟩
  · rintro V V' a ⟨i, k, hk⟩
    exact ⟨i, chartMap B S hS Y' a ≫ k, by
      rw [Category.assoc, hk, ← Category.assoc, chartMap_comp_chartToSpace]⟩
  · intro x
    have hx : pointsMap B S hS Y'.1 g.hom x ∈
        ⋃ i, Set.range (pointsMap B S hS (Yi i).1 (gi i).hom) := by
      rw [hcov.jointly_surjective]
      exact Set.mem_univ _
    obtain ⟨i, w, hw⟩ := Set.mem_iUnion.1 hx
    obtain ⟨p, hp₁, hp₂⟩ := exists_point_of_isPullback B S hS
      (IsPullback.of_hasPullback (gi i) g) w x hw
    obtain ⟨E, t, ht⟩ := SmallEtale.exists_mem_range_of_coversTop B S hS (pullback (gi i) g).2
      (SmallEtale.coversTop_affineCharts B S hS _) p
    have hsnd : IsEtale B S hS (pullback.snd (gi i) g).hom :=
      isEtale_of_isPullback B S hS _ _ _ _ (IsPullback.of_hasPullback (gi i) g) (hcov.etale i)
    refine ⟨(smallEtalePostcomp B S hS _ hsnd).obj E.1,
      ⟨i, chartToSpace B S hS _ E.1 ≫ pullback.fst _ _, ?_⟩, t, ?_⟩
    · exact (Category.assoc _ _ _).trans ((whisker_eq _ pullback.condition).trans
        (Category.assoc _ _ _).symm)
    · change pointsMap B S hS _ (E.1.1.hom ≫ (pullback.snd (gi i) g).hom) t = x
      rw [pointsMap_comp_apply, ht, hp₂]

end Cover

namespace RelativeDualizingPair

variable {hZ} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {hfl : IsFlat B S hS f.hom} {hfp : IsFinitePresentation B S hS f.hom}
  (P : RelativeDualizingPair f hfl hfp)
  {X' Y' : AlgebraicSpaces B S hS} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g)

/-- **Transitivity of the base change condition**: if the base change to `X'` of `(ω, τ)` has
the base change condition along a further cartesian square over an affine `Y''`, then `(ω, τ)`
has it along the composite square. -/
theorem isAffineBaseChangePair_paste ⦃X'' Y'' : AlgebraicSpaces B S hS⦄ {f'' : X'' ⟶ Y''}
    {h : Y'' ⟶ Y'} {g'' : X'' ⟶ X'} (sq₂ : IsPullback g'' f'' f' h)
    (hY'' : IsAffineSpace B S hS Y''.1)
    (h₃ : IsAffineBaseChangePair hZ sq₂
      ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp) hY''
      (P.baseChange sq).ω (P.baseChange sq).τ) :
    IsAffineBaseChangePair hZ (sq₂.paste_horiz sq) hfp hY'' P.ω P.τ := by
  obtain ⟨e₃, h3⟩ := h₃
  let α := (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) (h ≫ g)).symm ≪≫
    ((smallEtaleDerivedModulePullbackCompIso B S hS h g).app
      (derivedStructureSheaf B S hS Y.1 Y.2).obj).symm ≪≫
    (smallEtaleDerivedModulePullback B S hS h).mapIso
      (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g) ≪≫
    smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) h
  refine isAffineBaseChangePair_of_comp_iso hZ (sq₂.paste_horiz sq) hfp hY'' P.ω P.τ
    (((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').app P.ω).symm ≪≫ e₃) α.symm ?_
  exact isAffineBaseChangePair_paste_aux (derivedModulePushforward B S hS f'')
    ((smallEtaleDerivedModulePullbackCompIso B S hS g'' g').inv_hom_id_app P.ω) α.hom_inv_id
    (baseChange_baseChangeTrace sq sq₂ P)
    (cancel_iso_aux ((P.baseChange sq).isIso_smallEtaleDerivedBaseChangeMap sq₂)
      (((P.baseChange sq).smallEtaleDerivedBaseChangeMap_comp_baseChangeTrace sq₂).trans h3))
    (P.smallEtaleDerivedBaseChangeMap_comp_baseChangeTrace (sq₂.paste_horiz sq))

/-- **Stacks 0E60, granted the affine case.** Let `(ω, τ)` be a pair of a `Y`-perfect object of
`D(𝒪_X)` and a map `τ : Rf_* ω ⟶ 𝒪_Y`, and let `X_i ⟶ Y_i` be base changes of `f` to the
members of an étale covering `{Y_i ⟶ Y}` by affines, over which `(ω, τ)` restricts to
`(a_i(𝒪_{Y_i}), Tr)`. If `(a'(𝒪_{Y'}), Tr)` is a relative dualizing complex for every base change
`f'` of `f` to an affine `Y'` (the third remark after Stacks 0E5X), then the base change of
`(ω, τ)` to every affine `Y'` is `(a'(𝒪_{Y'}), Tr)`. -/
theorem isAffineBaseChangePair_of_isEtaleCovering (hf : IsProper B S hS f.hom)
    (hCan : ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1),
      ∃ D : RelativeDualizingComplex hZ f'
          ((isProper_isStableUnderBaseChange B S hS).of_isPullback sq hf)
          ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
          ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp),
        ∃ e : D.ω ≅ ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
            (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj,
          (derivedModulePushforward B S hS f').map e.hom ≫ affineBaseChangeTrace hZ sq hfp hY' =
            D.τ)
    {ι : Type v} {Yi Xi : ι → AlgebraicSpaces B S hS} {fi : ∀ i, Xi i ⟶ Yi i}
    {gi : ∀ i, Yi i ⟶ Y} {g'i : ∀ i, Xi i ⟶ X} (sqi : ∀ i, IsPullback (g'i i) (fi i) f (gi i))
    (hYi : ∀ i, IsAffineSpace B S hS (Yi i).1)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (gi i).hom))
    (hi : ∀ i, IsAffineBaseChangePair hZ (sqi i) hfp (hYi i) P.ω P.τ)
    ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1) :
    IsAffineBaseChangePair hZ sq hfp hY' P.ω P.τ := by
  obtain ⟨D', eD, heD⟩ := hCan f' g g' sq hY'
  obtain ⟨φ₀, hφ₀⟩ := exists_affineBaseChangeTrace_comp hZ sq hfp hY'
    ⟨(P.baseChange sq).ω, (P.baseChange sq).qcohDerived_ω⟩ (P.baseChange sq).τ
  have hφ : (derivedModulePushforward B S hS f').map (φ₀ ≫ eD.inv) ≫ D'.τ =
      (P.baseChange sq).τ :=
    map_comp_inv_comp_eq _ φ₀ eD heD hφ₀
  have hiso : IsIso (φ₀ ≫ eD.inv) := by
    refine isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace B S hS
      (coversTop_hasAffineChartDiagramWith_of_isEtaleCovering f' g hcov) _ fun A => ?_
    obtain ⟨-, V, q, hq, hV, i, k, hk⟩ := A.2
    have hVa : IsAffineSpace B S hS (chartSpace B S hS Y' V).1 :=
      isAffineSpace_chartSpace B S hS Y' V hV
    have sqV := IsPullback.of_hasPullback f' (chartToSpace B S hS Y' V)
    have hm : (pullback.fst f' (chartToSpace B S hS Y' V) ≫ g') ≫ f =
        (pullback.snd f' (chartToSpace B S hS Y' V) ≫ k) ≫ gi i :=
      calc (pullback.fst f' (chartToSpace B S hS Y' V) ≫ g') ≫ f
          = (pullback.fst f' (chartToSpace B S hS Y' V) ≫ f') ≫ g := by
            rw [Category.assoc, sq.w, Category.assoc]
        _ = pullback.snd f' (chartToSpace B S hS Y' V) ≫ chartToSpace B S hS Y' V ≫ g := by
            rw [pullback.condition, Category.assoc]
        _ = (pullback.snd f' (chartToSpace B S hS Y' V) ≫ k) ≫ gi i :=
            (whisker_eq _ hk.symm).trans (Category.assoc _ _ _).symm
    have sqp : IsPullback ((sqi i).lift _ _ hm ≫ g'i i) (pullback.snd f' _) f (k ≫ gi i) := by
      rw [(sqi i).lift_fst, hk]
      exact sqV.paste_horiz sq
    have sq₃ : IsPullback ((sqi i).lift _ _ hm) (pullback.snd f' (chartToSpace B S hS Y' V))
        (fi i) k :=
      IsPullback.of_right sqp ((sqi i).lift_snd _ _ _) (sqi i)
    obtain ⟨Di, eDi, heDi⟩ := hCan (fi i) (gi i) (g'i i) (sqi i) (hYi i)
    obtain ⟨ei, hei⟩ := P.exists_baseChangeTrace_eq (sqi i) (hYi i) (hi i)
    have hpi : (derivedModulePushforward B S hS (fi i)).map (ei ≪≫ eDi.symm).hom ≫ Di.τ =
        (P.baseChange (sqi i)).τ :=
      map_comp_inv_comp_eq _ ei.hom eDi heDi hei.symm
    have h₃ := isAffineBaseChangePair_of_iso hZ
      ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback (sqi i) hfp) sq₃ hVa
      (ei ≪≫ eDi.symm) hpi (Di.isAffineBaseChangePair _ _ _ sq₃ hVa)
    have h₀ := isAffineBaseChangePair_of_eq hZ hfp (sq₃.paste_horiz (sqi i))
      (sqV.paste_horiz sq) hk ((sqi i).lift_fst _ _ hm) hVa
      (P.isAffineBaseChangePair_paste (sqi i) sq₃ hVa h₃)
    have hP'V := P.isAffineBaseChangePair_baseChange sq hZ _ _ _ sqV hVa h₀
    have hisoV := RelativeDualizingPair.isIso_of_baseChange_hom (P.baseChange sq)
      D'.toRelativeDualizingPair sqV hVa hP'V (D'.isAffineBaseChangePair _ _ _ sqV hVa) _
      (RelativeDualizingPair.baseChange_hom (P.baseChange sq) D'.toRelativeDualizingPair sqV
        (φ₀ ≫ eD.inv) hφ)
    have hψ : pullback.lift _ _ (chartSpaceMapOver_comp_chartToSpace B S hS f' q hq).symm ≫
        pullback.fst f' (chartToSpace B S hS Y' V) = chartToSpace B S hS X' A.1 :=
      pullback.lift_fst _ _ _
    exact isIso_map_of_comp_eq _ _ hψ _ hisoV
  exact ⟨@asIso _ _ _ _ φ₀ (isIso_of_isIso_comp_inv_aux eD hiso),
    (P.smallEtaleDerivedBaseChangeMap_comp_baseChangeTrace sq).symm.trans
      (whisker_eq _ hφ₀.symm)⟩

end RelativeDualizingPair

namespace RelativeDualizingComplex

variable {hZ} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {hfl : IsFlat B S hS f.hom} {hfp : IsFinitePresentation B S hS f.hom}

/-- **Stacks 0E60, granted the affine case**, as a relative dualizing complex: a pair `(ω, τ)`
whose base changes to the members of an affine étale covering of `Y` are the pairs
`(a_i(𝒪_{Y_i}), Tr)` is a relative dualizing complex, granted that `(a'(𝒪_{Y'}), Tr)` is one over
every affine `Y'`. -/
def ofIsEtaleCovering (P : RelativeDualizingPair f hfl hfp) (hf : IsProper B S hS f.hom)
    (hCan : ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1),
      ∃ D : RelativeDualizingComplex hZ f'
          ((isProper_isStableUnderBaseChange B S hS).of_isPullback sq hf)
          ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
          ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp),
        ∃ e : D.ω ≅ ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
            (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj,
          (derivedModulePushforward B S hS f').map e.hom ≫ affineBaseChangeTrace hZ sq hfp hY' =
            D.τ)
    {ι : Type v} {Yi Xi : ι → AlgebraicSpaces B S hS} {fi : ∀ i, Xi i ⟶ Yi i}
    {gi : ∀ i, Yi i ⟶ Y} {g'i : ∀ i, Xi i ⟶ X} (sqi : ∀ i, IsPullback (g'i i) (fi i) f (gi i))
    (hYi : ∀ i, IsAffineSpace B S hS (Yi i).1)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (gi i).hom))
    (hi : ∀ i, IsAffineBaseChangePair hZ (sqi i) hfp (hYi i) P.ω P.τ) :
    RelativeDualizingComplex hZ f hf hfl hfp where
  toRelativeDualizingPair := P
  isAffineBaseChangePair := P.isAffineBaseChangePair_of_isEtaleCovering hf hCan sqi hYi hcov hi

end RelativeDualizingComplex

end AlgebraicGeometry.Space

end
