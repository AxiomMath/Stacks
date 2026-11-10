module

public import StacksFrontier.AlgebraicGeometry.Quot.AffineAlgebraicSpaceOverEqualizer
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitsInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverSchemeRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import
  StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionAlgebraicLimit

/-!
# Cofiltered limits of algebraic spaces affine over an affine scheme

Let `T` be an affine scheme of the site and let `R` be a cofiltered system of functors on the
test schemes over `T`, each an algebraic space affine over `T`.  The limit of `R` is again an
algebraic space affine over `T` as soon as the system of representing algebraic spaces satisfies
the chapter's convention of Section 70.2 (Stacks 07SD) that the limits of its affine charts lie
in the site.  This holds in two cases used in the proof of Stacks 08K6:

* the transition morphisms of `R` are injective, so that the representing system has
  monomorphic transitions (`AlgebraicGeometry.Space.IsSiteSmall`); and
* every member is an algebraic space affine and of finite presentation over `T` and the index
  category is smaller than the cutoff of the site, so that the base changes of the representing
  system are bounded (Stacks 04T7).

Neither needs a bound against the cofinality of the cutoff.

## Main results

* `AlgebraicGeometry.Space.isAffineAlgebraicSpaceOver_of_isLimit_of_siteContainsBaseChangeLimits`
* `AlgebraicGeometry.Space.isAffineAlgebraicSpaceOver_of_isLimit_of_injective`
* `AlgebraicGeometry.Space.isAffineAlgebraicSpaceOver_of_isLimit_of_isAffineFinitePresentation`

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07SE](https://stacks.math.columbia.edu/tag/07SE)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space affine over an affine scheme of the site is an affine algebraic
space.** -/
theorem isAffineSpace_of_isAffineHom_yoneda {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hH : IsAlgebraicSpace B S hS H) {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (π : H ⟶ yoneda.obj T)
    (hπ : IsAffineHom B S hS π) : IsAffineSpace B S hS H := by
  obtain ⟨W, e, P, -, hP⟩ := exists_representing_over_of_isAffineHom B S hS hH π hπ
  exact ⟨W, isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map P), ⟨e⟩⟩

/-- An affine algebraic space is quasi-compact. -/
theorem isQuasiCompactSpace_of_isAffineSpace {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hH : IsAffineSpace B S hS H) : IsQuasiCompactSpace B S hS H := by
  obtain ⟨W, hW, ⟨e⟩⟩ := hH
  exact isQuasiCompactSpace_of_iso B S hS e.symm
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS W hW)

section Limits

variable {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  {I : Type u} [Category.{u} I] [IsCofiltered I]
  (R : I ⥤ ((SchemesOver ((schemeSpaceFunctor B S hS).obj T))ᵒᵖ ⥤ Type (u + 1)))
  (h : ∀ i, IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T) (R.obj i))

omit [IsCofiltered I] in
include hT in
/-- The members of the representing system are affine algebraic spaces. -/
theorem isAffineSpace_predicateSystem (i : I) :
    IsAffineSpace B S hS ((predicateSystem B S hS R h).obj i) :=
  isAffineSpace_of_isAffineHom_yoneda B S hS (isAlgebraicSpace_predicateSystem B S hS R h i) hT
    _ (isAffineHom_predicateSystemProjection B S hS R h i)

omit [IsCofiltered I] in
/-- The transition morphisms of the representing system are affine. -/
theorem isAffineHom_predicateSystem_map {i j : I} (φ : i ⟶ j) :
    IsAffineHom B S hS ((predicateSystem B S hS R h).map φ) :=
  isAffineHom_map_of_isAffineHom_app B S hS _ (predicateSystemProjection B S hS R h)
    (isAlgebraicSpace_predicateSystem B S hS R h) (isAlgebraicSpace_yoneda B S hS T)
    (isAffineHom_predicateSystemProjection B S hS R h) φ

include hT in
/-- **A cofiltered limit of functors on the test schemes over an affine scheme `T`, each an
algebraic space affine over `T`, is an algebraic space affine over `T`, provided the
representing system satisfies the chapter's convention (Stacks 07SD).** -/
theorem isAffineAlgebraicSpaceOver_of_isLimit_of_siteContainsBaseChangeLimits
    (_hZ : B.Contains (⊤_ Scheme.{u}))
    (hconv : SiteContainsBaseChangeLimits B S hS (predicateSystem B S hS R h))
    (c : Cone R) (hc : IsLimit c) :
    IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T) c.pt := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : IsConnected I := IsCofiltered.isConnected I
  have hAff := fun {i j : I} (φ : i ⟶ j) => isAffineHom_predicateSystem_map B S hS R h φ
  have hlim := isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS
    (predicateSystem B S hS R h) hconv (isAlgebraicSpace_predicateSystem B S hS R h) hAff
    (fun i => isQuasiCompactSpace_of_isAffineSpace B S hS
      (isAffineSpace_predicateSystem B S hS hT R h i))
  exact isAffineAlgebraicSpaceOver_of_isLimit_predicateSystem B S hS R h hlim i₀
    (isAffineHom_comp B S hS _ _
      (isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS _ hconv hAff i₀)
      (isAffineHom_predicateSystemProjection B S hS R h i₀)) c hc

end Limits

/-! ### Two cases of the convention -/

section Cases

variable {Y : AlgebraicSpaces B S hS} {I : Type u} [Category.{u} I]
  (R : I ⥤ ((SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)))
  (h : ∀ i, IsAffineAlgebraicSpaceOver Y (R.obj i))

/-- The map on points over `Y` induced by a transition morphism of the representing system is
injective at every test scheme as soon as the transition morphism of `R` is. -/
theorem injective_spacePointsOverMap_dataTransition {Hs : I → AlgebraicSpaces B S hS}
    {ps : ∀ i, Hs i ⟶ Y} (ψs : ∀ i, spacePointsOver (ps i) ⋙ uliftFunctor.{u + 1, u} ≅ R.obj i)
    {i j : I} (φ : i ⟶ j) (T : (SchemesOver Y)ᵒᵖ)
    (hinj : Function.Injective ((R.map φ).app T)) :
    Function.Injective ((spacePointsOverMap (dataTransition R Hs ps ψs φ)
      (dataTransition_comp R Hs ps ψs φ)).app T) := by
  have hm : Mono ((ψs i).hom.app T ≫ (R.map φ).app T) := by
    have := (mono_iff_injective _).2 hinj
    infer_instance
  rw [← NatTrans.comp_app, ← whiskerRight_spacePointsOverMap_dataTransition R Hs ps ψs φ,
    NatTrans.comp_app] at hm
  have hm2 : Mono ((Functor.whiskerRight
      (spacePointsOverMap (dataTransition R Hs ps ψs φ) (dataTransition_comp R Hs ps ψs φ))
        uliftFunctor.{u + 1, u}).app T) := mono_of_mono _ ((ψs j).hom.app T)
  intro a b hab
  have := (mono_iff_injective _).1 hm2 (a₁ := ULift.up a) (a₂ := ULift.up b)
    (congrArg ULift.up hab)
  exact congrArg ULift.down this

/-- **Injective transitions of `R` give monomorphic transitions of the representing system.** -/
theorem mono_predicateSystem_map_of_injective
    (hinj : ∀ {i j : I} (φ : i ⟶ j) (T : (SchemesOver Y)ᵒᵖ), Function.Injective ((R.map φ).app T))
    {i j : I} (φ : i ⟶ j) : Mono ((predicateSystem B S hS R h).map φ) := by
  rw [NatTrans.mono_iff_mono_app]
  intro V
  rw [mono_iff_injective]
  intro x y hxy
  let p := chosenProjection B S hS R h i
  let k := dataTransition R (chosenSpace B S hS R h) (chosenProjection B S hS R h)
    (chosenIso B S hS R h) φ
  have hk : k ≫ chosenProjection B S hS R h j = p := dataTransition_comp R _ _ _ φ
  have hp : p.hom.app V x = p.hom.app V y := by
    rw [← hk]
    exact congrArg ((chosenProjection B S hS R h j).hom.app V) hxy
  let T := pointTest p V.unop x
  let x' : spacePointsOverObj p T := pointTestSection p V.unop x
  let y' : spacePointsOverObj p T := ⟨y, hp.symm.trans (testPoint_pointTest p V.unop x).symm⟩
  have := injective_spacePointsOverMap_dataTransition B S hS R (chosenIso B S hS R h) φ
    (Opposite.op T) (hinj φ (Opposite.op T)) (a₁ := x') (a₂ := y') (Subtype.ext hxy)
  exact congrArg Subtype.val this

/-- **Injective transitions give the chapter's convention for the representing system.** -/
theorem siteContainsBaseChangeLimits_predicateSystem_of_injective [IsCofiltered I]
    (hinj : ∀ {i j : I} (φ : i ⟶ j) (T : (SchemesOver Y)ᵒᵖ), Function.Injective ((R.map φ).app T)) :
    SiteContainsBaseChangeLimits B S hS (predicateSystem B S hS R h) :=
  IsSiteSmall.siteContainsBaseChangeLimits B S hS _
    (Or.inr fun {_ _} φ => mono_predicateSystem_map_of_injective B S hS R h hinj φ)

/-- A morphism of universe lifts composed with another, stripped, is the composite of the
stripped morphisms. -/
theorem stripUlift_comp {C : Type*} [Category* C] {F G J : C ⥤ Type u}
    (β : F ⋙ uliftFunctor.{u + 1, u} ⟶ G ⋙ uliftFunctor.{u + 1, u})
    (γ : G ⋙ uliftFunctor.{u + 1, u} ⟶ J ⋙ uliftFunctor.{u + 1, u}) :
    stripUlift (β ≫ γ) = stripUlift β ≫ stripUlift γ := by
  refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
  change ((γ.app T) ((β.app T) ⟨x⟩)).down = ((γ.app T) ⟨((β.app T) ⟨x⟩).down⟩).down
  rfl

/-- The identity of a universe lift, stripped, is the identity. -/
theorem stripUlift_id {C : Type*} [Category* C] (F : C ⥤ Type u) :
    stripUlift (𝟙 (F ⋙ uliftFunctor.{u + 1, u})) = 𝟙 F := by
  refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
  rfl

/-- **Two algebraic spaces over `Y` with isomorphic universe lifts of their functors of points
over `Y` are isomorphic over `Y`.** -/
def isoOfSpacePointsOverUliftIso {H H' : AlgebraicSpaces B S hS} {p : H ⟶ Y} {p' : H' ⟶ Y}
    (e : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅
      spacePointsOver p' ⋙ uliftFunctor.{u + 1, u}) :
    H ≅ H' where
  hom := spacePointsOverInv (stripUlift e.hom)
  inv := spacePointsOverInv (stripUlift e.inv)
  hom_inv_id := by
    rw [← spacePointsOverInv_comp_eq, ← stripUlift_comp, e.hom_inv_id, stripUlift_id,
      spacePointsOverInv_id]
  inv_hom_id := by
    rw [← spacePointsOverInv_comp_eq, ← stripUlift_comp, e.inv_hom_id, stripUlift_id,
      spacePointsOverInv_id]

/-- The isomorphism `isoOfSpacePointsOverUliftIso B S hS e` is an isomorphism over `Y`: its
forward map followed by `p'` is `p`. -/
theorem isoOfSpacePointsOverUliftIso_hom_comp {H H' : AlgebraicSpaces B S hS} {p : H ⟶ Y}
    {p' : H' ⟶ Y}
    (e : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅
      spacePointsOver p' ⋙ uliftFunctor.{u + 1, u}) :
    (isoOfSpacePointsOverUliftIso B S hS e).hom ≫ p' = p :=
  spacePointsOverInv_comp _

/-- **The chosen representing algebraic spaces of a system of algebraic spaces affine and of
finite presentation over `Y` are locally of finite type over `Y`.** -/
theorem isLocallyOfFiniteType_chosenProjection
    (hfp : ∀ i, IsAffineFinitePresentationAlgebraicSpaceOver Y (R.obj i)) (i : I) :
    IsLocallyOfFiniteType B S hS
      (chosenProjection B S hS R (fun i => (hfp i).isAffineAlgebraicSpaceOver) i).hom := by
  obtain ⟨H, p, -, hpfp, ⟨ψ⟩⟩ := hfp i
  let e := isoOfSpacePointsOverUliftIso B S hS
    (chosenIso B S hS R (fun i => (hfp i).isAffineAlgebraicSpaceOver) i ≪≫ ψ.symm)
  have sq : IsPullback e.hom (chosenProjection B S hS R _ i) p (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨(isoOfSpacePointsOverUliftIso_hom_comp B S hS _).trans
      (Category.comp_id _).symm⟩
  exact (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hpfp.1)

end Cases

section Bounded

variable {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  {I : Type u} [Category.{u} I] [IsCofiltered I]
  (R : I ⥤ ((SchemesOver ((schemeSpaceFunctor B S hS).obj T))ᵒᵖ ⥤ Type (u + 1)))

include hT in
/-- **A cofiltered limit of functors on the test schemes over an affine scheme `T`, each an
algebraic space affine and of finite presentation over `T`, indexed by a category whose slices
are smaller than the cutoff of the site, is an algebraic space affine over `T`.**  The base
changes of the representing system along affine points are of finite type over affine schemes,
hence bounded (Stacks 04T7), so the representing system satisfies the convention. -/
theorem isAffineAlgebraicSpaceOver_of_isLimit_of_isAffineFinitePresentation
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hfp : ∀ i, IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T)
      (R.obj i))
    (hOver : ∀ i : I, #(Over i) < B.cutoff) (c : Cone R) (hc : IsLimit c) :
    IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T) c.pt := by
  let h := fun i => (hfp i).isAffineAlgebraicSpaceOver
  let D := predicateSystem B S hS R h
  have hD := isAlgebraicSpace_predicateSystem B S hS R h
  have hft : ∀ {i j : I} (φ : i ⟶ j), (MorphismProperty.inverseImage
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (D.map φ) := by
    intro i j φ
    obtain ⟨hrep, -⟩ := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS (D.map φ) (hD i)
      (hD j)).out 2 1).mp (isAffineHom_predicateSystem_map B S hS R h φ)
    refine (isLocallyOfFiniteType_iff_presheaf B S hS (hD i) (hD j) hrep).1 ?_
    refine isLocallyOfFiniteType_of_comp B S hS (hD i) (hD j) ((schemeSpaceFunctor B S hS).obj T).2
      (D.map φ) ((predicateSystemProjection B S hS R h).app j) ?_
    have hn : D.map φ ≫ (predicateSystemProjection B S hS R h).app j =
        (predicateSystemProjection B S hS R h).app i :=
      ((predicateSystemProjection B S hS R h).naturality φ).trans (Category.comp_id _)
    rw [hn]
    exact isLocallyOfFiniteType_chosenProjection B S hS R hfp i
  have hconv : SiteContainsBaseChangeLimits B S hS D :=
    siteContainsBaseChangeLimits_of_hasBoundedBaseChanges D fun i₀ =>
      hasBoundedBaseChanges_of_hasBaseChangesOfSizeLE B S hS i₀ D (hOver i₀) B.aleph0_lt_cutoff
        fun φ => hasBaseChangesOfSizeLE_of_locallyOfFiniteType B S hS ℵ₀
          (isAffineHom_predicateSystem_map B S hS R h φ) (hft φ)
  exact isAffineAlgebraicSpaceOver_of_isLimit_of_siteContainsBaseChangeLimits B S hS hT R h hZ
    hconv c hc

end Bounded

end AlgebraicGeometry.Space

end
