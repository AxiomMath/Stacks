module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleMapOfSplitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSectionHomReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SubfunctorPreimageLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeRepresentedPoints

/-!
# The closed immersion of a split quotient is the zero scheme of the hyperplane section

Let `X` be an algebraic space over `S` and `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℰ' ⟶ 0` a split short exact sequence
of finite locally free modules: `σ₀ : 𝒪_X ⟶ ℰ`, `u : ℰ ⟶ ℰ'` with `σ₀ ≫ u = 0`, and
`τ : ℰ ⟶ 𝒪_X`, `σ : ℰ' ⟶ ℰ` with `σ ≫ u = 𝟙` and `τ ≫ σ₀ + u ≫ σ = 𝟙`. Let `π : P = 𝐏(ℰ) ⟶ X`
be the projective bundle, `s ∈ Γ(P, 𝒪_P(1))` the hyperplane section of `σ₀` (the image of `π^*σ₀`
under the tautological quotient) and `i : 𝐏(ℰ') ⟶ P` the closed immersion of
`AlgebraicGeometry.Space.projectiveBundleMapOfSplitEpi`. Then **the image of `i` is the zero
scheme `Z(s)` of Stacks 0845**, as subfunctors of `P`.

Both are sheaf subfunctors of `P`, so they are compared on the presenting chart `P_U ⟶ P`
(`CategoryTheory.Subfunctor.eq_of_preimage_eq_of_isLocallySurjective`). A point `y : b ⟶ P_U` of
the chart lands in the image of `i` exactly when the morphism of schemes `y` factors through the
closed immersion `𝐏(ℰ'|_U) ⟶ 𝐏(ℰ|_U)` of the chart bundles
(`AlgebraicGeometry.Space.projectiveBundleChart_app_mem_range_iff`), and in `Z(s)` exactly when
`y^*` of the reading of `s` on `P_U` vanishes
(`AlgebraicGeometry.Space.mem_zeroScheme_iff_modulePullback_map_eq_zero`,
`AlgebraicGeometry.Space.exists_representedZariski_map_projectiveBundleAtlas_sectionHom`). On
the scheme `P_U` the two conditions agree
(`Stacks.RelativeProj.exists_comp_projectiveBundleMapOfEpi_iff`).

## Main results

* `AlgebraicGeometry.Space.projectiveBundleChart_app_mem_zeroScheme_iff`: the points of `Z(s)` on
  the presenting chart.
* `AlgebraicGeometry.Space.range_projectiveBundleMapOfSplitEpi_eq_zeroScheme`: **the image of
  `𝐏(ℰ') ⟶ 𝐏(ℰ)` is `Z(s)`.**

## References

* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

section Reading

variable {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X)
  {E E' E'' : Modules.{u, u} B S hS X.1 X.2}

/-- The inverse of the equivalence of modules on a represented space is additive. -/
theorem additive_representedSmallEtaleModuleEquivalence_inverse (T : BigFppfOver B S hS) :
    (representedSmallEtaleModuleEquivalence B S hS T).inverse.Additive := by
  have : (representedSmallEtaleModuleEquivalence B S hS T).inverse.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (representedSmallEtaleModuleEquivalence B S hS T).inverse
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The reading on a scheme is additive. -/
theorem schemeReadingMap_add (f g : E ⟶ E') :
    schemeReadingMap ψ (f + g) = schemeReadingMap ψ f + schemeReadingMap ψ g := by
  have : (modulePullback B S hS ψ).Additive := additive_modulePullback B S hS ψ
  have := additive_representedSmallEtaleModuleEquivalence_inverse T
  exact (congrArg (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
    ((congrArg (representedSmallEtaleModuleEquivalence B S hS T).inverse.map
      ((modulePullback B S hS ψ).map_add (f := f) (g := g))).trans
      (representedSmallEtaleModuleEquivalence B S hS T).inverse.map_add)).trans
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map_add

/-- The reading on a scheme carries zero to zero. -/
theorem schemeReadingMap_zero : schemeReadingMap ψ (0 : E ⟶ E') = 0 := by
  have : (modulePullback B S hS ψ).Additive := additive_modulePullback B S hS ψ
  have := additive_representedSmallEtaleModuleEquivalence_inverse T
  exact (congrArg (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
    ((congrArg (representedSmallEtaleModuleEquivalence B S hS T).inverse.map
      ((modulePullback B S hS ψ).map_zero E E')).trans
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map_zero _ _))).trans
    ((SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map_zero _ _)

/-- The reading on a scheme is functorial. -/
theorem schemeReadingMap_comp (f : E ⟶ E') (g : E' ⟶ E'') :
    schemeReadingMap ψ (f ≫ g) = schemeReadingMap ψ f ≫ schemeReadingMap ψ g :=
  (congrArg _ ((congrArg _ (Functor.map_comp _ _ _)).trans (Functor.map_comp _ _ _))).trans
    (Functor.map_comp _ _ _)

/-- The reading on a scheme carries identities to identities. -/
theorem schemeReadingMap_id : schemeReadingMap ψ (𝟙 E) = 𝟙 _ :=
  (congrArg _ ((congrArg _ (CategoryTheory.Functor.map_id _ _)).trans
    (CategoryTheory.Functor.map_id _ _))).trans (CategoryTheory.Functor.map_id _ _)

end Reading

/-- A morphism conjugated by two isomorphisms is carried to zero by a functor preserving zero
morphisms exactly when the morphism itself is. -/
theorem _root_.CategoryTheory.Functor.map_iso_comp_comp_iso_eq_zero_iff {C₀ D₀ : Type*}
    [Category C₀] [Category D₀] [Limits.HasZeroMorphisms C₀] [Limits.HasZeroMorphisms D₀]
    (F : C₀ ⥤ D₀) [F.PreservesZeroMorphisms] {a b c d : C₀} (A : a ≅ b) (g : b ⟶ c)
    (C : c ≅ d) : F.map (A.hom ≫ g ≫ C.hom) = 0 ↔ F.map g = 0 := by
  rw [F.map_comp, F.map_comp]
  refine ⟨fun h => ?_, fun h => by rw [h, zero_comp, comp_zero]⟩
  have h' := congrArg (fun k => F.map A.inv ≫ k ≫ F.map C.inv) h
  simp only [← F.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] at h'
  simpa using h'

/-- `CategoryTheory.Functor.map_iso_comp_comp_iso_eq_zero_iff` for the inverse image of modules
along a morphism of schemes. -/
theorem pullback_map_iso_comp_comp_iso_eq_zero_iff {T Y : Scheme.{u}} (g : T ⟶ Y)
    {a b c c' d : Y.Modules} (A : a ≅ b) (φ₁ : b ⟶ c') (φ₂ : c' ⟶ c) (C : c ≅ d) :
    (Scheme.Modules.pullback g).map (A.hom ≫ φ₁ ≫ φ₂ ≫ C.hom) = 0 ↔
      (Scheme.Modules.pullback g).map (φ₁ ≫ φ₂) = 0 := by
  rw [← Category.assoc φ₁ φ₂ C.hom]
  exact Functor.map_iso_comp_comp_iso_eq_zero_iff _ A (φ₁ ≫ φ₂) C

section Main

variable (E E' : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  [hE' : E'.IsQuasicoherentOnSite] (u : E ⟶ E') (σ : E' ⟶ E) (hσ : σ ≫ u = 𝟙 E')
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfree' : SheafOfModules.IsFiniteLocallyFreeOnSite E')
  (σ₀ : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)) ⟶ E)
  (τ : E ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)))
  (hsplit : τ ≫ σ₀ + u ≫ σ = 𝟙 E) (hσ₀u : σ₀ ≫ u = 0)

/-- **The hyperplane section of `σ₀ : 𝒪_X ⟶ ℰ`** on the projective bundle `P = 𝐏(ℰ)`, as a
morphism `𝒪_P ≅ π^*𝒪_X ⟶ π^*ℰ ⟶ 𝒪_P(1)`. -/
def projectiveBundleSectionHom :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (projectiveBundle E hfree).1 (projectiveBundle E hfree).2).O)) ⟶
      (projectiveBundleTwist E hfree).obj :=
  (modulePullbackUnitIso B S hS (projectiveBundleProj E hfree)).inv ≫
    (modulePullback B S hS (projectiveBundleProj E hfree)).map σ₀ ≫
      (projectiveBundleTautological E hfree).hom

/-- The hyperplane section of `σ₀`, as a global section of `𝒪_P(1)`. -/
def projectiveBundleSection : (projectiveBundleTwist E hfree).obj.sections :=
  (projectiveBundleTwist E hfree).obj.unitHomEquiv (projectiveBundleSectionHom E hfree σ₀)

/-- The hyperplane section corresponds to the morphism it is defined by. -/
theorem unitHomEquiv_symm_projectiveBundleSection :
    (projectiveBundleTwist E hfree).obj.unitHomEquiv.symm (projectiveBundleSection E hfree σ₀) =
      projectiveBundleSectionHom E hfree σ₀ :=
  Equiv.symm_apply_apply _ _

/-- **The hyperplane section of the chart bundle `𝐏(ℰ|_V)` pulls back to zero along `g`**: the
inverse image along `g` of `ρ^*σ₀` followed by the tautological quotient vanishes. -/
def ChartSectionPullbackVanishes (V : SmallEtale B S hS X.1) {T : Scheme.{u}}
    (g : T ⟶ chartBundle E V) : Prop :=
  (Scheme.Modules.pullback g).map
    ((Scheme.Modules.pullback (chartBundleToChart E V)).map
      (schemeReadingMap (chartToSpace B S hS X V) σ₀) ≫ chartBundleTautological E V) = 0

include hsplit hσ₀u in
/-- **The points of the image of `𝐏(ℰ') ⟶ 𝐏(ℰ)` on the presenting chart**, read as vanishing of
the hyperplane section of the chart bundle: a point `y : b ⟶ P_U` lands in the image exactly when
`y^*` of `ρ^*σ₀ ≫ τ_U` vanishes, `τ_U` the tautological quotient of `𝐏(ℰ|_U)`. -/
theorem projectiveBundleChart_app_mem_range_iff_eq_zero {b : BigFppfOver B S hS}
    (y : b ⟶ (projectiveBundleChartFamily E hfree).site
      (presentationChart (projectiveBundlePresentation X))) :
    (projectiveBundleChart E hfree).app (op b) y ∈
        (Subfunctor.range (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom).obj
          (op b) ↔
      ChartSectionPullbackVanishes E σ₀ (presentationChart (projectiveBundlePresentation X))
        ((BigFppfOver.toScheme B S hS).map y) := by
  have hsplitU :
      schemeReadingMap (chartToSpace B S hS X (presentationChart (projectiveBundlePresentation X)))
          τ ≫
        schemeReadingMap
          (chartToSpace B S hS X (presentationChart (projectiveBundlePresentation X))) σ₀ +
      chartModuleMap u (presentationChart (projectiveBundlePresentation X)) ≫
        chartModuleMap σ (presentationChart (projectiveBundlePresentation X)) = 𝟙 _ := by
    refine ((congrArg₂ (· + ·) (schemeReadingMap_comp _ τ σ₀).symm
      (schemeReadingMap_comp _ u σ).symm).trans (schemeReadingMap_add _ _ _).symm).trans
      ((congrArg _ hsplit).trans (schemeReadingMap_id _))
  have hσ₀uU :
      schemeReadingMap (chartToSpace B S hS X (presentationChart (projectiveBundlePresentation X)))
          σ₀ ≫
        chartModuleMap u (presentationChart (projectiveBundlePresentation X)) = 0 := by
    exact (schemeReadingMap_comp _ σ₀ u).symm.trans
      ((congrArg _ hσ₀u).trans (schemeReadingMap_zero _))
  exact (projectiveBundleChart_app_mem_range_iff E E' u σ hσ hfree hfree' y).trans
    (@Stacks.RelativeProj.exists_comp_projectiveBundleMapOfEpi_iff
      (chartScheme (presentationChart (projectiveBundlePresentation X)))
      (chartBundleModule E (presentationChart (projectiveBundlePresentation X)))
      (chartBundleModule E' (presentationChart (projectiveBundlePresentation X))) _ _
      (chartModuleMap u (presentationChart (projectiveBundlePresentation X)))
      (epi_chartModuleMap u σ hσ (presentationChart (projectiveBundlePresentation X))) _
      (schemeReadingMap
        (chartToSpace B S hS X (presentationChart (projectiveBundlePresentation X))) σ₀)
      (schemeReadingMap
        (chartToSpace B S hS X (presentationChart (projectiveBundlePresentation X))) τ)
      (chartModuleMap σ (presentationChart (projectiveBundlePresentation X))) hsplitU hσ₀uU
      ((BigFppfOver.toScheme B S hS).obj b)
      ((BigFppfOver.toScheme B S hS).map y : (BigFppfOver.toScheme B S hS).obj b ⟶
        chartBundle E (presentationChart (projectiveBundlePresentation X))))

/-- **The points of the zero scheme of the hyperplane section on the presenting chart**: a point
`y : b ⟶ P_U` lands in `Z(s)` exactly when `y^*` of `ρ^*σ₀ ≫ τ_U` vanishes. -/
theorem projectiveBundleChart_app_mem_zeroScheme_iff {b : BigFppfOver B S hS}
    (y : b ⟶ (projectiveBundleChartFamily E hfree).site
      (presentationChart (projectiveBundlePresentation X))) :
    (projectiveBundleChart E hfree).app (op b) y ∈
        (zeroScheme B S hS (projectiveBundle E hfree) (projectiveBundleTwist E hfree).obj
          (projectiveBundleSection E hfree σ₀)).1.obj (op b) ↔
      ChartSectionPullbackVanishes E σ₀ (presentationChart (projectiveBundlePresentation X))
        ((BigFppfOver.toScheme B S hS).map y) := by
  have hinv := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (isInvertibleModule_projectiveBundleTwist E hfree)
  have hx :
      (ObjectProperty.homMk (yonedaEquiv.symm ((projectiveBundleChart E hfree).app (op b) y)) :
        representedAlgebraicSpace B S hS b ⟶ projectiveBundle E hfree) =
        representedSpaceMap B S hS y ≫ projectiveBundleAtlas E hfree := by
    refine ObjectProperty.hom_ext _ ?_
    show yonedaEquiv.symm ((projectiveBundleChart E hfree).app (op b) y) =
      yoneda.map y ≫ projectiveBundleChart E hfree
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [mem_zeroScheme_iff_modulePullback_map_eq_zero B S hS _ _ hinv,
    unitHomEquiv_symm_projectiveBundleSection, hx, modulePullback_comp_map_eq_zero_iff,
    modulePullback_representedSpaceMap_map_eq_zero_iff B S hS y
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
      (SheafOfModules.isQuasicoherentOnSite_unit _))
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
      (projectiveBundleTwist E hfree).property)]
  obtain ⟨A, C, hAC⟩ := exists_representedZariski_map_projectiveBundleAtlas_sectionHom E hfree σ₀
  rw [projectiveBundleSectionHom, hAC]
  refine (pullback_map_iso_comp_comp_iso_eq_zero_iff
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) y.left) A
    ((Scheme.Modules.pullback (chartBundleToChart E (bundleBaseChart X))).map
      (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ₀))
    (chartBundleTautological E (bundleBaseChart X)) C).trans ?_
  show ChartSectionPullbackVanishes E σ₀ (bundleBaseChart X)
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) y.left) ↔ _
  exact Iff.rfl

include hsplit hσ₀u in
/-- **The image of the closed immersion `𝐏(ℰ') ⟶ 𝐏(ℰ)` of a split quotient is the zero scheme of
the hyperplane section** `s` of `σ₀`, as subfunctors of `𝐏(ℰ)`. -/
theorem range_projectiveBundleMapOfSplitEpi_eq_zeroScheme :
    Subfunctor.range (projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree').hom =
      (zeroScheme B S hS (projectiveBundle E hfree) (projectiveBundleTwist E hfree).obj
        (projectiveBundleSection E hfree σ₀)).1 := by
  have := mono_of_isClosedImmersion B S hS _
    (isClosedImmersion_projectiveBundleMapOfSplitEpi E E' u σ hσ hfree hfree')
  refine Subfunctor.eq_of_preimage_eq_of_isLocallySurjective (BigFppfOver.topology B S hS)
    ((isSheaf_iff_isSheaf_of_type _ _).1 (projectiveBundle E hfree).property.isSheaf)
    (Subfunctor.isSheaf_range_of_mono _
      ((isSheaf_iff_isSheaf_of_type _ _).1 (projectiveBundle E' hfree').property.isSheaf))
    ((isSheaf_iff_isSheaf_of_type _ _).1
      (zeroScheme B S hS (projectiveBundle E hfree) (projectiveBundleTwist E hfree).obj
        (projectiveBundleSection E hfree σ₀)).2.1.isSheaf)
    (projectiveBundleChart E hfree)
    (isLocallySurjective_of_surjective_etale B S hS _
      (projectiveBundleChartPresentation E hfree).surjective
      (projectiveBundleChartPresentation E hfree).etale) ?_
  refine Subfunctor.ext (funext fun U => Set.ext fun y => ?_)
  obtain ⟨b⟩ := U
  exact (projectiveBundleChart_app_mem_range_iff_eq_zero E E' u σ hσ hfree hfree' σ₀ τ hsplit
    hσ₀u y).trans (projectiveBundleChart_app_mem_zeroScheme_iff E hfree σ₀ y).symm

end Main

end AlgebraicGeometry.Space

end
