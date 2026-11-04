module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseBaseChangeTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceUnitNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompFlat

/-!
# The base change isomorphism of Stacks 0A1K, and Stacks 0A1P

For a cartesian square of algebraic spaces with `f` quasi-compact and quasi-separated,
`E ∈ D_QCoh(𝒪_X)` and a bounded above complex `𝒢^•` of quasi-coherent `𝒪_X`-modules flat over
`Y`, `Lg^*Rf_*(E ⊗^L 𝒢^•) ≅ Rf'_*(L(g')^*E ⊗^L (g')^*𝒢^•)`. Condition (2) of Stacks 0DKG holds
for `𝒢^•` and its degreewise pullback, and passes to `E ⊗^L 𝒢^•`.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_derivedTensor`: Stacks 0A1K.
* `AlgebraicGeometry.Space.baseChangeIsoStatement`: the isomorphism of Stacks 0A1K for perfect
  `E`, on every site of `B`.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isFlat`: the base change map
  `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` is invertible for flat `f`, the case `𝒢^• = 𝒪_X`.
* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedTensor_and_isIso_baseChange`:
  Stacks 0A1P.
* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedTensor_single`: the
  perfectness of Stacks 0A1P for `𝒢^• = ℳ[0]`.
* `AlgebraicGeometry.Space.exists_finiteProjective_model_derivedSections`: Stacks 0A1Q.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

/-- Stacks 0A1K for `E ⊗^L 𝒢^•`, with the comparison built from
`smallEtaleDerivedPullbackQComparison`. -/
private theorem isIso_baseChangeComp_derivedTensor_pullbackQComparison
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w
      (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))
      (((smallEtaleDerivedTensor B S hS X').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj
        (DerivedCategory.Q.obj
          (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)))
      ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, DerivedCategory.Q.obj G) ≫
        ((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).map
          (smallEtaleDerivedPullbackQComparison g' G))) := by
  obtain ⟨b, hb⟩ := hGb
  have : G.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff G b).2 hb
  have := pullbackModules_smallEtale_additive (B := B) (S := S) (hS := hS) g'
  have hK := qcohDerived_Q_obj_of_isQuasicoherentOnSite G hq
  have hK' := qcohDerived_Q_obj_of_isQuasicoherentOnSite
    (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)
    fun n => isQuasicoherentOnSite_pullbackModules B S hS g' (G.X n) (hq n)
  have h2 := affineChartwiseBaseChange_tensor B S hS f g f' g' sq.w E _ hE hK _ hK' _
    (affineChartwiseBaseChange_pullbackQComparison B S hS sq G b hq hfl)
  exact isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange B S hS sq hfqc
    hfqs _ (qcohDerived_smallEtaleDerivedTensor X _ _ hE hK) _
    (qcohDerived_smallEtaleDerivedTensor X' _ _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ g' _ hE) hK') _ h2

/-- **The base change isomorphism of Stacks 0A1K for perfect `E`, on every site of `B`.**
`Rf'_*(L(g')^*E ⊗^L (g')^*𝒢^•) ≅ Lg^*Rf_*(E ⊗^L 𝒢^•)` for `f` quasi-compact and quasi-separated,
perfect `E` and bounded above `𝒢^•` with quasi-coherent terms flat over `Y`. -/
theorem baseChangeIsoStatement (B : BigFppfSite.{u}) :
    BaseChangeIsoStatement B := by
  constructor
  intro S' hS' X₀ X₁ Y₀ Y₁ f₀ y f₁ a sq hqc hqs P₀ hP₀ G₀ hGb hq hfl
  have hiso := isIso_baseChangeComp_derivedTensor_pullbackQComparison sq hqc hqs P₀
    (qcohDerived_of_isPerfect_derivedCategoryB X₀ P₀ hP₀) G₀ hGb hq hfl
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S' hS' X₁)
    (Y := smallEtaleRingedTopos B S' hS' X₀) (smallEtaleRingedToposHom B S' hS' a).toModulesHom
  let G' : type_of% F := modulePullback B S' hS' a
  have : G'.Additive := modulePullback_additive a
  exact ⟨(derivedModulePushforward B S' hS' f₁).mapIso
      (((smallEtaleDerivedTensor B S' hS' X₁).obj
        ((smallEtaleDerivedModulePullback B S' hS' a).obj P₀)).mapIso
        (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (F := F) (G := G')
          (pullbackModulesIsoModulePullback B S' hS' a) (ComplexShape.up ℤ)).app G₀).symm)) ≪≫
    (@asIso _ _ _ _ _ hiso).symm⟩

section Single

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Stacks 0A1K.** For a cartesian square of algebraic spaces with `f` quasi-compact and
quasi-separated, `E ∈ D_QCoh(𝒪_X)` and a bounded above complex `𝒢^•` of quasi-coherent
`𝒪_X`-modules flat over `Y`, the base change map
`Lg^*Rf_*(E ⊗^L 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L (g')^*𝒢^•)` is an isomorphism. -/
@[stacks 0A1K]
theorem isIso_smallEtaleDerivedBaseChangeComp_derivedTensor
    (sq : IsPullback g' f' f g) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w
      (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))
      (((smallEtaleDerivedTensor B S hS X').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj
        (DerivedCategory.Q.obj (((modulePullback B S hS g').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G)))
      ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, DerivedCategory.Q.obj G) ≫
        ((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).map
          (smallEtaleDerivedModulePullbackQComparison g' G))) := by
  have hiso :=
    isIso_baseChangeComp_derivedTensor_pullbackQComparison sq hfqc hfqs E hE G hGb hq hfl
  unfold smallEtaleDerivedModulePullbackQComparison
  rw [Functor.map_comp, ← Category.assoc]
  exact isIso_smallEtaleDerivedBaseChangeComp_of_comp_inv B S hS f g f' g' sq.w _ _ _ hiso
    (@Functor.map_isIso _ _ _ _ _ _ _ _
      (@Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Q _ (NatIso.hom_app_isIso _ _)))

/-- **The base change map for a flat morphism.** For a cartesian square with `f` flat,
quasi-compact and quasi-separated and `E ∈ D_QCoh(𝒪_X)`, the base change map
`Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of Stacks 07A7 is an isomorphism: this is Stacks 0A1K at `𝒢^• = 𝒪_X`,
read through the unit law `E ⊗^L 𝒪_X ≅ E`. -/
theorem isIso_smallEtaleDerivedBaseChangeMap_of_isFlat
    (sq : IsPullback g' f' f g) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E) := by
  let O := structureSheafModule B S hS X
  let G := (HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (ComplexShape.up ℤ) 0).obj O
  have hGz : ∀ i : ℤ, i ≠ 0 → IsZero (G.X i) := fun i hi =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
  let e₀ : G.X 0 ≅ O := HomologicalComplex.singleObjXSelf _ _ _
  have hq : ∀ n, (G.X n).IsQuasicoherentOnSite := fun n => by
    by_cases hn : n = 0
    · subst hn
      exact SheafOfModules.IsQuasicoherentOnSite.of_iso e₀.symm
        (SheafOfModules.isQuasicoherentOnSite_unit _)
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero (hGz n hn)
  have hfl' : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n) := fun n => by
    by_cases hn : n = 0
    · subst hn
      exact IsFlatOver.of_iso B S hS X.2 e₀.symm (isFlatOver_structureSheafModule B S hS f hfl)
    · exact isFlatOver_of_isZero B S hS f (hGz n hn)
  have h := isIso_smallEtaleDerivedBaseChangeComp_derivedTensor sq hfqc hfqs E hE G
    ⟨0, fun i hi => hGz i (by omega)⟩ hq hfl'
  -- the comparison `L(g')^*𝒪_X ⟶ (g')^*𝒪_X` is invertible
  have hflat : ∀ j : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS X).O) (G.X j) := fun j => by
    by_cases hj : j = 0
    · subst hj
      exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _ e₀.symm
        (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
          (Y := smallEtaleRingedSite B S hS X.1 X.2))
    · exact isFlat_of_isZero B S hS (hGz j hj)
  have : CochainComplex.IsStrictlyLE G 0 :=
    (CochainComplex.isStrictlyLE_iff G 0).2 fun i hi => hGz i (by omega)
  have := isIso_smallEtaleDerivedModulePullbackComparison_app B S hS g'
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj G)
    (smallEtaleModuleKFlat_of_isStrictlyLE B S hS X G 0 hflat)
  have hc : IsIso (smallEtaleDerivedPullbackQComparison g' G) := by
    rw [smallEtaleDerivedPullbackQComparison.eq_1]
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) (IsIso.comp_isIso' inferInstance
      (Iso.isIso_hom ((DerivedCategory.quotientCompQhIso _).app _)))
  have hc' : IsIso (smallEtaleDerivedModulePullbackQComparison g' G) := by
    unfold smallEtaleDerivedModulePullbackQComparison
    exact @IsIso.comp_isIso' _ _ _ _ _ _ _ hc
      (@Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Q _ (NatIso.hom_app_isIso _ _))
  let ψ := (smallEtaleDerivedPullbackTensorIso g').hom.app (E, DerivedCategory.Q.obj G) ≫
    ((smallEtaleDerivedTensor B S hS X').obj
      ((smallEtaleDerivedModulePullback B S hS g').obj E)).map
      (smallEtaleDerivedModulePullbackQComparison g' G)
  have : IsIso ψ := @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
    (@Functor.map_isIso _ _ _ _ _ _ _ _ hc')
  -- the unit law `E ⊗^L 𝒪_X ≅ E`
  let e : ((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G) ≅ E :=
    ((smallEtaleDerivedTensor B S hS X).obj E).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app O).symm ≪≫
      (smallEtaleDerivedTensorProduct B S hS X).unitComplexNatIso.app E
  let e' := (asIso ψ).symm ≪≫ (smallEtaleDerivedModulePullback B S hS g').mapIso e
  rw [← smallEtaleDerivedBaseChangeComp_id]
  exact (isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS f g f' g' sq.w _ _ ψ _ _ (𝟙 _)
    e e' (by simp [e'])).1 h

end Single

section FinitePresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The perfectness of Stacks 0A1P for one module.** For
`f : X ⟶ Y` of finite presentation, a perfect `E` and an `𝒪_X`-module `ℳ` of finite presentation,
flat over `Y`, with support proper over `Y`, `Rf_*(E ⊗^L ℳ[0])` is perfect. -/
theorem isPerfect_derivedModulePushforward_derivedTensor_single (f : X ⟶ Y)
    (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (M : Modules.{u, u} B S hS X.1 X.2) (hMfp : M.IsFinitePresentation)
    (hMflat : IsFlatOver B S hS X.2 f.hom M)
    (hMsupp : HasProperSupport B S hS X.2 Y.2 f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj M)) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let G := (HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (ComplexShape.up ℤ) 0).obj M
  have hGz : ∀ i : ℤ, i ≠ 0 → IsZero (G.X i) := fun i hi =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
  have hX : G.X 0 = M := by
    simp only [G, HomologicalComplex.single]
    rfl
  have hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite :=
    (Set.finite_singleton (0 : ℤ)).subset fun i hi =>
      Classical.byContradiction fun h => hi (hGz i h)
  have h := isPerfect_derivedModulePushforward_derivedTensor_of_baseChangeIso
    (baseChangeIsoStatement B) f hf E hE G hGb
    (fun n => by
      by_cases hn : n = 0
      · subst hn
        exact hX ▸ hMfp
      · exact isFinitePresentation_of_isZero B S hS (hGz n hn))
    (fun n => by
      by_cases hn : n = 0
      · subst hn
        exact IsFlatOver.of_iso B S hS X.2 (HomologicalComplex.singleObjXSelf _ _ _).symm hMflat
      · exact isFlatOver_of_isZero B S hS f (hGz n hn))
    (fun n => by
      by_cases hn : n = 0
      · subst hn
        exact hX ▸ hMsupp
      · exact hasProperSupport_of_isZero B S hS X.2 Y.2 f.hom _ (hGz n hn))
  exact isPerfect_of_iso B S hS h ((derivedModulePushforward B S hS f).mapIso
    (((smallEtaleDerivedTensor B S hS X).obj E).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm))

/-- **Stacks 0A1P.** For `f : X ⟶ Y` of finite presentation, a perfect `E` and a bounded complex
`𝒢^•` of `𝒪_X`-modules of finite presentation, flat over `Y`, with support proper over `Y`,
`Rf_*(E ⊗^L 𝒢^•)` is perfect, and its formation commutes with arbitrary base change: for every
cartesian square, `Lg^*Rf_*(E ⊗^L 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L (g')^*𝒢^•)` is an isomorphism. -/
@[stacks 0A1P]
theorem isPerfect_derivedModulePushforward_derivedTensor_and_isIso_baseChange
    (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (hGfp : ∀ n, (G.X n).IsFinitePresentation)
    (hGflat : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hGsupp : ∀ n, HasProperSupport B S hS X.2 Y.2 f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj (G.X n))) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
        ((derivedModulePushforward B S hS f).obj
          (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w
          (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))
          (((smallEtaleDerivedTensor B S hS X').obj
            ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj
            (DerivedCategory.Q.obj (((modulePullback B S hS g').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)))
          ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, DerivedCategory.Q.obj G) ≫
            ((smallEtaleDerivedTensor B S hS X').obj
              ((smallEtaleDerivedModulePullback B S hS g').obj E)).map
              (smallEtaleDerivedModulePullbackQComparison g' G))) := by
  refine ⟨isPerfect_derivedModulePushforward_derivedTensor_of_baseChangeIso
    (baseChangeIsoStatement B) f hf E hE G hGb hGfp hGflat hGsupp, fun g f' g' sq => ?_⟩
  obtain ⟨b, hb⟩ := hGb.bddAbove
  exact isIso_smallEtaleDerivedBaseChangeComp_derivedTensor sq hf.2.1 hf.2.2 E
    (qcohDerived_of_isPerfect_derivedCategoryB X E hE) G
    ⟨b, fun i hi => Classical.byContradiction fun h => not_le.2 hi (hb h)⟩
    (fun n => @SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ (G.X n)
      (isFinitePresentationOnSite_of_isFinitePresentation' (G.X n) (hGfp n))) hGflat

end FinitePresentation

section FiniteProjectiveModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0A1Q.** Let `U` have affine underlying scheme `Spec R`, `f : X ⟶ U` of finite
presentation and `𝒢` an `𝒪_X`-module of finite presentation, flat over `U`, with support proper
over `U`. There is a bounded complex `M^•` of finite projective `R`-modules (so that
`M^• ⊗ᴸ_R R' = M^• ⊗_R R'`) and isomorphisms `RΓ(X_{R'}, 𝒢_{R'}) ≅ M^• ⊗ᴸ_R R'`, functorial in the
`R`-algebra `R' = Γ(U', 𝒪)`: compatible with the pullback maps and the composition law of
derived extensions of scalars. -/
@[stacks 0A1Q]
theorem exists_finiteProjective_model_derivedSections
    {U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (hf : IsFinitePresentation B S hS f.hom)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hGfp : G.IsFinitePresentation) (hGflat : IsFlatOver B S hS X.2 f.hom G)
    (hGsupp : HasProperSupport B S hS X.2 (isAlgebraicSpace_yoneda B S hS U) f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj G)) :
    ∃ (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
      (∀ i, Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (M.X i)) ∧
      (∀ i, Module.Projective Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (M.X i)) ∧
      (∀ {U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
        (g : U' ⟶ U), IsIso ((representedAffineDerivedExtension B S hS g).comparison.app M)) ∧
      ∃ φ : ∀ {U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
          (g : U' ⟶ U) {X' : AlgebraicSpaces B S hS}
          (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X),
          IsPullback g' f' f (representedSpaceMap B S hS g) →
          ((representedAffineDerivedSections B S hS U').obj
            ((derivedModulePushforward B S hS f').obj (DerivedCategory.Q.obj
              (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS X)
                (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj
                ((HomologicalComplex.single
                  (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
                  (ComplexShape.up ℤ) 0).obj G)))) ≅
            (representedAffineDerivedExtension B S hS g).functor.obj (DerivedCategory.Q.obj M)),
        ∀ {U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
          [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')
          {X' X'' : AlgebraicSpaces B S hS}
          (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
          (f'' : X'' ⟶ ⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩) (g' : X' ⟶ X)
          (g₂' : X'' ⟶ X') (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
          (sq₂ : IsPullback g₂' f'' f' (representedSpaceMap B S hS g₂))
          (sq₃ : IsPullback (g₂' ≫ g') f'' f (representedSpaceMap B S hS (g₂ ≫ g))),
          affineBaseDerivedSectionsPullbackMap B S hS g₂ f' f'' g₂' sq₂.w
              (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS X)
                (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj
                ((HomologicalComplex.single
                  (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
                  (ComplexShape.up ℤ) 0).obj G)) ≫
            (representedAffineDerivedSections B S hS U'').map
              ((derivedModulePushforward B S hS f'').map (DerivedCategory.Q.map
                ((NatIso.mapHomologicalComplex (smallEtaleModulePullbackCompIso B S hS g₂' g')
                  (ComplexShape.up ℤ)).hom.app
                  ((HomologicalComplex.single
                    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
                    (ComplexShape.up ℤ) 0).obj G)))) ≫
            (φ (g₂ ≫ g) f'' (g₂' ≫ g') sq₃).hom =
          (representedAffineDerivedExtension B S hS g₂).functor.map (φ g f' g' sq).hom ≫
            (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS g).hom
              (representedAffineCommRingCatHom B S hS g₂).hom
              (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
              (representedAffineRingHom_comp B S hS g₂ g).symm).hom.app
                (DerivedCategory.Q.obj M) := by
  have hG0 : ∀ n, n ≠ 0 → IsZero (((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ) 0).obj G).X n) :=
    fun n hn => HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
  refine exists_finiteProjective_model_derivedSections_of_perfectness B S hS
    (fun f' hf' E' hE' G' h₁ h₂ h₃ h₄ =>
      (isPerfect_derivedModulePushforward_derivedTensor_and_isIso_baseChange f' hf' E' hE' G' h₁ h₂
        h₃ h₄).1)
    f hf G hGfp hGflat hGsupp fun g _ f' g' sq => ?_
  refine isIso_smallEtaleDerivedBaseChangeComp_modulePullbackQComparison_of_isFlatOver B S hS sq
    hf.2.1 hf.2.2 _ ⟨0, fun i hi => hG0 i (by omega)⟩ (fun n => ?_) (fun n => ?_)
  · by_cases hn : n = 0
    · subst hn
      exact SheafOfModules.IsQuasicoherentOnSite.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm
        (@SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ G
          (isFinitePresentationOnSite_of_isFinitePresentation' G hGfp))
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero (hG0 n hn)
  · by_cases hn : n = 0
    · subst hn
      exact IsFlatOver.of_iso B S hS _
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm hGflat
    · exact isFlatOver_of_isZero B S hS _ (hG0 n hn)

end FiniteProjectiveModel

end AlgebraicGeometry.Space
