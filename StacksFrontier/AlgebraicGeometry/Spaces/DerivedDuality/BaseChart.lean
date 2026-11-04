module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ChartTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSheafHomPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHigherDirectImageRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationOfPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ZariskiPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionUpperShriekDualizing
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.SchemeDualBound
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic

/-!
# The duality chart of an affine Noetherian scheme on its small étale site

Let `T` be an affine Noetherian scheme and `ω` a dualizing complex on `T`. On the equi-universe
model `AlgebraicGeometry.SmallEtale.modelSite` of the small étale ringed site of `T`, the pullback
`ε^*` along the comparison morphism `ε` with the Zariski site is a duality chart for `ε^*ω`
(`AlgebraicGeometry.RingedSite.DualityChart`).

## Main definitions

* `AlgebraicGeometry.SmallEtale.modelSite`: the equi-universe model of `(T_étale, 𝒪)`.
* `AlgebraicGeometry.SmallEtale.chartFunctor`: `ε^*`, as a chart functor.

## References

* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 08JP](https://stacks.math.columbia.edu/tag/08JP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.SmallEtale

/-- In a distinguished triangle whose first vertex has vanishing cohomology in degrees `n` and
`n + 1`, the second morphism is an isomorphism on cohomology in degree `n`. -/
theorem _root_.DerivedCategory.isIso_homologyMap_mor₂_of_isZero {C : Type*} [Category C]
    [Abelian C] [HasDerivedCategory C] (Tr : Pretriangulated.Triangle (DerivedCategory C))
    (hT : Tr ∈ distTriang _) (n : ℤ)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor C n).obj Tr.obj₁))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor C (n + 1)).obj Tr.obj₁)) :
    IsIso ((DerivedCategory.homologyFunctor C n).map Tr.mor₂) := by
  have : Epi ((DerivedCategory.homologyFunctor C n).map Tr.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff Tr hT n (n + 1) rfl]
    exact h₁.eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor C n).map Tr.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff Tr hT n]
    exact h₀.eq_of_src _ _
  exact isIso_of_mono_of_epi _

variable (E : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : E.Contains T)

/-- The small étale ringed site of `T`, at its equi-universe model. -/
abbrev modelSite : RingedSite.{u, u, u} := (smallModelRingedTopos E T hT).toRingedSite

/-- The small model of the small étale site has fibre products. -/
instance smallModel_hasPullbacks : HasPullbacks (SmallModel.{u} (SmallEtale E T hT)) :=
  haveI := (smallModelEquiv E T hT).isEquivalence_inverse
  Adjunction.hasLimitsOfShape_of_equivalence (smallModelEquiv E T hT).inverse

/-- The model of the small étale site has fibre products. -/
instance modelSite_hasPullbacks : HasPullbacks (modelSite E T hT).C :=
  inferInstanceAs (HasPullbacks (SmallModel.{u} (SmallEtale E T hT)))

/-- The comparison of the small étale site with its model is a dense subsite inclusion. -/
instance smallModelEquiv_functor_isDenseSubsite :
    (smallModelEquiv E T hT).functor.IsDenseSubsite (ringedTopos E T hT).J
      (smallModelRingedTopos E T hT).J :=
  inferInstanceAs ((equivSmallModel.{u} (SmallEtale E T hT)).functor.IsDenseSubsite
    (topology E T hT) ((equivSmallModel.{u} (SmallEtale E T hT)).inverse.inducedTopology
      (topology E T hT)))

/-- The comparison of the model with the small étale site is a dense subsite inclusion. -/
instance smallModelEquiv_symm_functor_isDenseSubsite :
    (smallModelEquiv E T hT).symm.functor.IsDenseSubsite (smallModelRingedTopos E T hT).J
      (ringedTopos E T hT).J :=
  inferInstanceAs ((equivSmallModel.{u} (SmallEtale E T hT)).inverse.IsDenseSubsite
    ((equivSmallModel.{u} (SmallEtale E T hT)).inverse.inducedTopology (topology E T hT))
    (topology E T hT))

/-- The comparison of the model with the small étale site, at the spelling of the small étale
topology. -/
instance smallModelEquiv_symm_functor_isDenseSubsite' :
    (smallModelEquiv E T hT).symm.functor.IsDenseSubsite (smallModelRingedTopos E T hT).J
      (topology E T hT) :=
  smallModelEquiv_symm_functor_isDenseSubsite E T hT

/-- The structure map of the comparison of the model with the small étale site is invertible. -/
instance isIso_toEtaleHom_fSharpRing : IsIso (toEtaleHom E T hT).fSharpRing := by
  have h1 : IsIso (toEtaleHom E T hT).fSharp.hom :=
    haveI := isIso_toEtaleHom_fSharp E T hT
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map (toEtaleHom E T hT).fSharp))
  have h2 : IsIso (toEtaleHom E T hT).fSharpPresheaf :=
    inferInstanceAs (IsIso (Functor.whiskerRight (toEtaleHom E T hT).fSharp.hom
      (forget₂ CommRingCat.{u} RingCat.{u})))
  have : IsIso ((sheafToPresheaf _ _).map (toEtaleHom E T hT).fSharpRing) := h2
  exact isIso_of_fully_faithful (sheafToPresheaf _ _) _

/-- **Finite presentation is invariant under transport to the model.** -/
theorem isFinitePresentation_modelModulesEquiv_functor_obj_iff
    (M : SheafOfModules.{u} (structureSheaf E T hT)) :
    ((modelModulesEquiv E T hT).functor.obj M).IsFinitePresentation ↔ M.IsFinitePresentation := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((modelModulesEquiv E T hT).unitIso.app M).symm
      (Stacks.SheafOfModules.ModelFinitePresentation.isFinitePresentation_pushforward_of_isIso
        (C := SmallModel.{u} (SmallEtale E T hT)) (C' := SmallEtale E T hT)
        (J := smallModelTopology E T hT) (J' := topology E T hT)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallModelRingedTopos E T hT).O)
        (S := structureSheaf E T hT)
        (smallModelEquiv E T hT) (toEtaleHom E T hT).fSharpRing
        (isIso_toEtaleHom_fSharpRing E T hT) ((modelModulesEquiv E T hT).functor.obj M) h)
  · exact Stacks.SheafOfModules.ModelFinitePresentation.isFinitePresentation_pushforward
      (C := SmallEtale E T hT) (C' := SmallModel.{u} (SmallEtale E T hT))
      (J := topology E T hT) (J' := smallModelTopology E T hT)
      (R := structureSheaf E T hT)
      (hdense := smallModelEquiv_symm_functor_isDenseSubsite E T hT)
      (smallModelEquiv E T hT).symm (𝟙 _) (Iso.refl _) M

variable [_root_.AlgebraicGeometry.IsAffine T] [_root_.AlgebraicGeometry.IsNoetherian T]

/-- `ε^*` on the model, as the functor of a duality chart. -/
abbrev chartFunctor : RingedSite.ChartFunctor (modelSite E T hT) where
  T := T
  isAffine := ‹_›
  isNoetherian := ‹_›
  Φ := (toZariskiSmallModelHom E T hT).pullbackTopos
  additive := inferInstanceAs (toZariskiSmallModelHom E T hT).pullbackTopos.Additive
  preservesFiniteLimits :=
    inferInstanceAs (PreservesFiniteLimits (toZariskiSmallModelHom E T hT).pullbackTopos)
  preservesFiniteColimits :=
    inferInstanceAs (PreservesFiniteColimits (toZariskiSmallModelHom E T hT).pullbackTopos)

/-- On a quasi-coherent module, coherence is finite presentation of its pullback to the model. -/
theorem isCoherent_iff_chartFunctor (M : T.Modules) (hM : M.IsQuasicoherent) :
    M.IsCoherent ↔ ((chartFunctor E T hT).Φ.obj M).IsFinitePresentation := by
  refine (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isFinitePresentation
    M).trans ?_
  refine (isFinitePresentation_associatedModule_iff E T hT M hM).trans ?_
  refine (isFinitePresentation_modelModulesEquiv_functor_obj_iff E T hT _).symm.trans ?_
  exact ⟨Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((pullbackToposIsoAssociatedModel E T hT).app M).symm,
    Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((pullbackToposIsoAssociatedModel E T hT).app M)⟩

/-- `ε^*` on the model reflects vanishing. -/
theorem isZero_of_isZero_chartFunctor (M : T.Modules)
    (h : IsZero ((chartFunctor E T hT).Φ.obj M)) : IsZero M :=
  isZero_of_isZero_pullbackTopos_toZariskiSmallModelHom E T hT M h

/-! ### The derived functor of the chart -/

/-- `ε^*` on derived categories, at the standard models. -/
abbrev assocDerived :
    RingedSite.SchemeStdDerived T ⥤
      @DerivedCategory (SheafOfModules.{u} (structureSheaf E T hT)) _ _
        (HasDerivedCategory.standard _) :=
  letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheaf E T hT))
  letI := preservesFiniteLimits_associatedModule E T hT
  (associatedModule E T hT).mapDerivedCategory

/-- Transport to the model on derived categories, at the standard models. -/
abbrev modelDerived :
    @DerivedCategory (SheafOfModules.{u} (structureSheaf E T hT)) _ _
        (HasDerivedCategory.standard _) ≌ RingedSite.StdDerived (modelSite E T hT) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheaf E T hT))
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite E T hT).O))
  letI : (modelModulesEquiv E T hT).functor.Additive :=
    inferInstanceAs (fromEtaleHom E T hT).pushforwardTopos.Additive
  Stacks.DerivedQCoh.Equivalence.mapDerivedCategory (modelModulesEquiv E T hT)

/-- **The derived functor of the chart is `ε^*` followed by transport to the model.** -/
def chartDerivedIso :
    (chartFunctor E T hT).derived ≅ assocDerived E T hT ⋙ (modelDerived E T hT).functor :=
  letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheaf E T hT))
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite E T hT).O))
  letI : (modelModulesEquiv E T hT).functor.Additive :=
    inferInstanceAs (fromEtaleHom E T hT).pushforwardTopos.Additive
  letI := (chartFunctor E T hT).additive
  letI := (chartFunctor E T hT).preservesFiniteLimits
  letI := (chartFunctor E T hT).preservesFiniteColimits
  letI := preservesFiniteLimits_associatedModule E T hT
  let e : (chartFunctor E T hT).Φ ≅ associatedModule E T hT ⋙ (modelModulesEquiv E T hT).functor :=
    pullbackToposIsoAssociatedModel E T hT
  letI := Functor.additive_of_iso e
  letI := preservesFiniteLimits_of_natIso e
  letI := preservesFiniteColimits_of_natIso e
  Stacks.DerivedGlueing.mapDerivedCategoryCongr e ≪≫
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIso (associatedModule E T hT)
      (modelModulesEquiv E T hT).functor).symm

omit [_root_.AlgebraicGeometry.IsAffine T] [_root_.AlgebraicGeometry.IsNoetherian T] in
/-- **Stacks 071Q, on morphisms**: `ε^*` is bijective on morphisms between objects with
quasi-coherent cohomology. -/
theorem assocDerived_map_bijective (A B : RingedSite.SchemeStdDerived T)
    (hA : ∀ n : ℤ, ((RingedSite.schemeStdHomology T n).obj A).IsQuasicoherent)
    (hB : ∀ n : ℤ, ((RingedSite.schemeStdHomology T n).obj B).IsQuasicoherent) :
    Function.Bijective (fun f : A ⟶ B => (assocDerived E T hT).map f) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{u} T.ringCatSheaf) := HasDerivedCategory.standard _
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheaf E T hT))
  have := derivedAssociatedModule_isEquivalence E T hT
  let P := DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent T.ringCatSheaf)
  let Q := DerivedCategoryB.derivedCategoryB (qcohOnSite E T hT)
  let A' : P.FullSubcategory := ⟨A, hA⟩
  let B' : P.FullSubcategory := ⟨B, hB⟩
  have h1 : Function.Bijective (fun g : A' ⟶ B' => (derivedAssociatedModule E T hT).map g) :=
    (Functor.FullyFaithful.ofFullyFaithful (derivedAssociatedModule E T hT)).map_bijective _ _
  have h2 : Function.Bijective (fun g : (derivedAssociatedModule E T hT).obj A' ⟶
      (derivedAssociatedModule E T hT).obj B' => Q.ι.map g) :=
    (ObjectProperty.fullyFaithfulι Q).map_bijective _ _
  have h3 : Function.Bijective (fun f : A ⟶ B => (ObjectProperty.homMk f : A' ⟶ B')) :=
    ((ObjectProperty.fullyFaithfulι P).homEquiv (X := A') (Y := B')).symm.bijective
  exact (h2.comp h1).comp h3

/-- **`ε^*` on the model is bijective on morphisms** between objects with quasi-coherent
cohomology. -/
theorem chartFunctor_map_bijective (A B : RingedSite.SchemeStdDerived T)
    (hA : ∀ n : ℤ, ((RingedSite.schemeStdHomology T n).obj A).IsQuasicoherent)
    (hB : ∀ n : ℤ, ((RingedSite.schemeStdHomology T n).obj B).IsQuasicoherent) :
    Function.Bijective (fun f : A ⟶ B => (chartFunctor E T hT).derived.map f) := by
  let e := chartDerivedIso E T hT
  have h2 : Function.Bijective (fun g : (assocDerived E T hT).obj A ⟶ (assocDerived E T hT).obj B =>
      (modelDerived E T hT).functor.map g) :=
    (modelDerived E T hT).fullyFaithfulFunctor.map_bijective _ _
  have hfun : (fun f : A ⟶ B => (chartFunctor E T hT).derived.map f) =
      ((Iso.homCongr (e.app A).symm (e.app B).symm) ∘
        fun g => (modelDerived E T hT).functor.map g) ∘ fun f => (assocDerived E T hT).map f := by
    funext f
    exact (NatIso.naturality_1 e.symm f).symm
  rw [hfun]
  exact ((Iso.homCongr (e.app A).symm (e.app B).symm).bijective.comp h2).comp
    (assocDerived_map_bijective E T hT A B hA hB)

/-- **Stacks 071Q, on objects**: every object of the model with cohomology sheaves of finite
presentation is `ε^*` of an object with quasi-coherent cohomology. -/
theorem chartFunctor_exists_iso (L : RingedSite.StdDerived (modelSite E T hT))
    (hL : ∀ n : ℤ, ((RingedSite.stdHomology (modelSite E T hT) n).obj L).IsFinitePresentation) :
    ∃ L' : RingedSite.SchemeStdDerived T,
      (∀ n : ℤ, ((RingedSite.schemeStdHomology T n).obj L').IsQuasicoherent) ∧
        Nonempty ((chartFunctor E T hT).derived.obj L' ≅ L) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{u} T.ringCatSheaf) := HasDerivedCategory.standard _
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheaf E T hT))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite E T hT).O))
  let : (modelModulesEquiv E T hT).functor.Additive :=
    inferInstanceAs (fromEtaleHom E T hT).pushforwardTopos.Additive
  have := derivedAssociatedModule_isEquivalence E T hT
  let L₀ := (modelDerived E T hT).inverse.obj L
  have hL₀ : DerivedCategoryB.derivedCategoryB (qcohOnSite E T hT) L₀ := fun n => by
    let N := (DerivedCategory.homologyFunctor _ n).obj L₀
    have e : (modelModulesEquiv E T hT).functor.obj N ≅
        (RingedSite.stdHomology (modelSite E T hT) n).obj L :=
      (((modelModulesEquiv E T hT).functor.mapDerivedCategoryHomologyIso n).app L₀).symm ≪≫
        (DerivedCategory.homologyFunctor _ n).mapIso ((modelDerived E T hT).counitIso.app L)
    have hN : N.IsFinitePresentation :=
      (isFinitePresentation_modelModulesEquiv_functor_obj_iff E T hT N).1
        (Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso e.symm (hL n))
    exact SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent N
  obtain ⟨X, ⟨i⟩⟩ : ∃ X, Nonempty ((derivedAssociatedModule E T hT).obj X ≅ ⟨L₀, hL₀⟩) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  refine ⟨X.obj, X.property, ⟨(chartDerivedIso E T hT).app X.obj ≪≫
    (modelDerived E T hT).functor.mapIso
      ((DerivedCategoryB.derivedCategoryB (qcohOnSite E T hT)).ι.mapIso i) ≪≫
    (modelDerived E T hT).counitIso.app L⟩⟩

/-- **Stacks 08JP (1) for the chart**: for `X` bounded above with coherent cohomology sheaves,
`R𝓗om(ε^* X, ε^* ω) ≅ ε^* R𝓗om(X, ω)`. -/
theorem chartFunctor_dualIso_of_isBoundedAbove (ω : RingedSite.SchemeStdDerived T)
    (hω : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω)
    (X : RingedSite.SchemeStdDerived T) (hX : RingedSite.SchemeCoherent T X) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((RingedSite.schemeStdHomology T i).obj X)) :
    Nonempty (((RingedSite.stdSheafHom (modelSite E T hT)).obj
        (op ((chartFunctor E T hT).derived.obj X))).obj ((chartFunctor E T hT).derived.obj ω) ≅
      (chartFunctor E T hT).derived.obj (RingedSite.schemeDual T ω X)) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  obtain ⟨n₀, hn₀⟩ := Stacks.Duality.isBoundedBelow_of_isDualizingComplex ω hω
  have hge : ω.IsGE n₀ := (DerivedCategory.isGE_iff ω n₀).2 hn₀
  have h := isIso_homComparisonMonoidal_derivedPullbackSmallModel_of_isPseudoCoherent E T hT X ω
    (Scheme.zariskiRingedSite_isPseudoCoherent T X hX b hb) n₀ hge
  exact ⟨(@asIso _ _ _ _ _ h).symm⟩

omit [_root_.AlgebraicGeometry.IsAffine T] [_root_.AlgebraicGeometry.IsNoetherian T] in
/-- If `X` has coherent cohomology sheaves, then so does its truncation `τ_{≥ m} X`. -/
theorem schemeCoherent_truncGE {X : RingedSite.SchemeStdDerived T}
    (hX : RingedSite.SchemeCoherent T X) (m : ℤ) :
    letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
    RingedSite.SchemeCoherent T ((DerivedCategory.TStructure.t.truncGE m).obj X) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  intro j
  by_cases hj : m ≤ j
  · have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ m j hj X
    exact AlgebraicGeometry.isCoherent_of_modulesIso
      (asIso ((DerivedCategory.homologyFunctor _ j).map
        ((DerivedCategory.TStructure.t.truncGEπ m).app X))) (hX j)
  · exact AlgebraicGeometry.ProperCoherentFiniteType.isCoherent_of_isZero
      (DerivedCategory.isZero_of_isGE _ m j (by omega))

omit [_root_.AlgebraicGeometry.IsAffine T] [_root_.AlgebraicGeometry.IsNoetherian T] in
/-- If `X` has coherent cohomology sheaves, then so does its truncation `τ_{< m} X`. -/
theorem schemeCoherent_truncLT {X : RingedSite.SchemeStdDerived T}
    (hX : RingedSite.SchemeCoherent T X) (m : ℤ) :
    letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
    RingedSite.SchemeCoherent T ((DerivedCategory.TStructure.t.truncLT m).obj X) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  intro j
  by_cases hj : j < m
  · have := DerivedCategory.isIso_homologyFunctor_map_truncLTι m j hj X
    exact AlgebraicGeometry.isCoherent_of_modulesIso
      (asIso ((DerivedCategory.homologyFunctor _ j).map
        ((DerivedCategory.TStructure.t.truncLTι m).app X))).symm (hX j)
  · exact AlgebraicGeometry.ProperCoherentFiniteType.isCoherent_of_isZero
      (DerivedCategory.isZero_of_isLE _ (m - 1) j (by omega))

section WayOut

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.Scheme.zariskiRingedTopos

/-- **The way-out argument for the chart** (Stacks 0E50 from Stacks 08JP (1)): if `R𝓗om(ε^* Y,
ε^* ω)` has cohomology vanishing above `b - m` for every `Y` with coherent cohomology vanishing
below `m`, then the comparison `ε^* R𝓗om(X, ω) ⟶ R𝓗om(ε^* X, ε^* ω)` is an isomorphism for every
`X` with coherent cohomology sheaves. In each degree `n` both sides agree with those of the
truncation `τ_{< m} X` for `m ≫ 0`, which is pseudo-coherent. -/
theorem isIso_homComparisonMonoidal_of_bound (ω : RingedSite.SchemeStdDerived T)
    (hω : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) (bEt : ℤ)
    (hEt : ∀ (m : ℤ) (Y : RingedSite.SchemeStdDerived T), RingedSite.SchemeCoherent T Y →
      (∀ i : ℤ, i < m → IsZero ((RingedSite.schemeStdHomology T i).obj Y)) →
        ∀ j : ℤ, bEt - m < j → IsZero ((RingedSite.stdHomology (modelSite E T hT) j).obj
          (((RingedSite.stdSheafHom (modelSite E T hT)).obj
            (op ((chartFunctor E T hT).derived.obj Y))).obj ((chartFunctor E T hT).derived.obj ω))))
    (X : RingedSite.SchemeStdDerived T) (hX : RingedSite.SchemeCoherent T X) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf T.zariskiRingedTopos.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelRingedTopos E T hT).O))
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal T.zariskiRingedTopos.O
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (smallModelRingedTopos E T hT).O
    letI : (Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived
      (toZariskiSmallModelHom E T hT)).Monoidal := derivedPullbackSmallModelMonoidal E T hT
    IsIso (RingedSite.homComparisonMonoidal (X := T.zariskiRingedSite)
      (Y := (smallModelRingedTopos E T hT).toRingedSite)
      (Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived (toZariskiSmallModelHom E T hT))
      X ω) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf T.zariskiRingedTopos.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelRingedTopos E T hT).O))
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal T.zariskiRingedTopos.O
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (smallModelRingedTopos E T hT).O
  let : (Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived
    (toZariskiSmallModelHom E T hT)).Monoidal := derivedPullbackSmallModelMonoidal E T hT
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf T.zariskiRingedSite.O))
  obtain ⟨bT, hbT⟩ := RingedSite.exists_bound_schemeDual T ω hω
  obtain ⟨n₀, hn₀⟩ := Stacks.Duality.isBoundedBelow_of_isDualizingComplex ω hω
  have hge : ω.IsGE n₀ := (DerivedCategory.isGE_iff ω n₀).2 hn₀
  let P := Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived (toZariskiSmallModelHom E T hT)
  refine (DerivedCategory.isIso_iff _ _).2 fun n => ?_
  let m := max bEt bT - n + 2
  let Tr := (DerivedCategory.TStructure.t.triangleLTGE m).obj X
  have hTr : Tr ∈ distTriang _ := DerivedCategory.TStructure.t.triangleLTGE_distinguished m X
  let Y := (DerivedCategory.TStructure.t.truncGE m).obj X
  let X' := (DerivedCategory.TStructure.t.truncLT m).obj X
  let i : X' ⟶ X := (DerivedCategory.TStructure.t.truncLTι m).app X
  have hYc : RingedSite.SchemeCoherent T Y := schemeCoherent_truncGE T hX m
  have hYge : ∀ j : ℤ, j < m → IsZero ((RingedSite.schemeStdHomology T j).obj Y) :=
    fun j hj => DerivedCategory.isZero_of_isGE Y m j hj
  have hX'c : RingedSite.SchemeCoherent T X' := schemeCoherent_truncLT T hX m
  have hX'b : ∀ j : ℤ, m - 1 < j → IsZero ((RingedSite.schemeStdHomology T j).obj X') :=
    fun j hj => DerivedCategory.isZero_of_isLE X' (m - 1) j hj
  have hc' : IsIso (RingedSite.homComparisonMonoidal (X := T.zariskiRingedSite)
      (Y := (smallModelRingedTopos E T hT).toRingedSite) P X' ω) :=
    isIso_homComparisonMonoidal_derivedPullbackSmallModel_of_isPseudoCoherent E T hT X' ω
      (Scheme.zariskiRingedSite_isPseudoCoherent T X' hX'c (m - 1) hX'b) n₀ hge
  have nat := RingedSite.homComparisonMonoidal_naturality_source
    (X := T.zariskiRingedSite) (Y := (smallModelRingedTopos E T hT).toRingedSite) P i ω
  obtain ⟨δ, hδ⟩ := RingedSite.exists_distinguished_derivedSheafHom (modelSite E T hT) (P.obj ω)
    (P.mapTriangle.obj Tr) (P.map_distinguished _ hTr)
  have hB := DerivedCategory.isIso_homologyMap_mor₂_of_isZero _ hδ n
    (hEt m Y hYc hYge n (by omega)) (hEt m Y hYc hYge (n + 1) (by omega))
  obtain ⟨δ', hδ'⟩ := RingedSite.exists_distinguished_derivedSheafHom T.zariskiRingedSite ω Tr hTr
  have hA₀ := DerivedCategory.isIso_homologyMap_mor₂_of_isZero _ hδ' n
    (hbT m Y hYc hYge n (by omega)) (hbT m Y hYc hYge (n + 1) (by omega))
  have hA : IsIso ((DerivedCategory.homologyFunctor _ n).map
      (P.map (((RingedSite.derivedSheafHomBifunctor T.zariskiRingedSite).map i.op).app ω))) :=
    (toZariskiSmallModelHom E T hT).pullbackTopos.isIso_homologyMap_mapDerivedCategory_map _ n hA₀
  have hfac := congrArg (DerivedCategory.homologyFunctor _ n).map nat
  simp only [Functor.map_comp] at hfac
  have : IsIso ((DerivedCategory.homologyFunctor _ n).map
      (((RingedSite.derivedSheafHomBifunctor (modelSite E T hT)).map (P.map i).op).app _)) := hB
  exact IsIso.of_isIso_fac_right
    (hh := IsIso.comp_isIso' hA ((DerivedCategory.isIso_iff _ _).1 hc' n)) hfac.symm

end WayOut

/-- **The duality chart of an affine Noetherian scheme on the model of its small étale site**,
from the vanishing bound `hEt` for `R𝓗om(ε^* Y, ε^* ω)` out of objects bounded below. -/
def baseDualityChart (ω : RingedSite.SchemeStdDerived T)
    (hω : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) (bEt : ℤ)
    (hEt : ∀ (m : ℤ) (Y : RingedSite.SchemeStdDerived T), RingedSite.SchemeCoherent T Y →
      (∀ i : ℤ, i < m → IsZero ((RingedSite.schemeStdHomology T i).obj Y)) →
        ∀ j : ℤ, bEt - m < j → IsZero ((RingedSite.stdHomology (modelSite E T hT) j).obj
          (((RingedSite.stdSheafHom (modelSite E T hT)).obj
            (op ((chartFunctor E T hT).derived.obj Y))).obj
              ((chartFunctor E T hT).derived.obj ω)))) :
    RingedSite.DualityChart (modelSite E T hT) ((chartFunctor E T hT).derived.obj ω)
      RingedSite.ChartClass.all where
  toChartFunctor := chartFunctor E T hT
  ω := ω
  isDualizing := hω
  isCoherent_iff := isCoherent_iff_chartFunctor E T hT
  isZero_of_isZero M _ h := isZero_of_isZero_chartFunctor E T hT M h
  exists_iso := chartFunctor_exists_iso E T hT
  map_bijective := chartFunctor_map_bijective E T hT
  isoDualizing := ⟨Iso.refl _⟩
  dualIso X hX _ :=
    ⟨(@asIso _ _ _ _ _ (isIso_homComparisonMonoidal_of_bound E T hT ω hω bEt hEt X hX)).symm⟩

/-- **The duality chart of an affine Noetherian scheme on the model of its small étale site, at
the class of bounded objects** (Stacks 08JP (1)). -/
def boundedBaseDualityChart (ω : RingedSite.SchemeStdDerived T)
    (hω : letI : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) :
    RingedSite.DualityChart (modelSite E T hT) ((chartFunctor E T hT).derived.obj ω)
      RingedSite.ChartClass.bounded where
  toChartFunctor := chartFunctor E T hT
  ω := ω
  isDualizing := hω
  isCoherent_iff := isCoherent_iff_chartFunctor E T hT
  isZero_of_isZero M _ h := isZero_of_isZero_chartFunctor E T hT M h
  exists_iso := chartFunctor_exists_iso E T hT
  map_bijective := chartFunctor_map_bijective E T hT
  isoDualizing := ⟨Iso.refl _⟩
  dualIso X hX hP := by
    obtain ⟨a, b, hab⟩ := hP
    exact chartFunctor_dualIso_of_isBoundedAbove E T hT ω hω X hX b fun i hi => hab i (Or.inr hi)

end AlgebraicGeometry.SmallEtale
