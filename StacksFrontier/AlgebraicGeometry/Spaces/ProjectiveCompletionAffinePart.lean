module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSplitEpiComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecLiftOfAlgebraHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafUngradedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.SymmetricAlgebraBounded

/-!
# The morphism from the affine part of the projective completion to the vector bundle

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module of rank `r`, and
`π : P = 𝐏(ℰ ⊕ 𝒪_X) ⟶ X` its projective completion, with the section `s` of `𝒪_P(1)` given by
`(0, 1)`. The projection `ℰ ⊕ 𝒪_X ⟶ ℰ` gives the closed immersion `i : 𝐏(ℰ) ⟶ P` of the
hyperplane at infinity, and its open complement `U = P ∖ i(𝐏(ℰ))` is the affine part of the
completion (Stacks 0ERW, proof). This file constructs the morphism

`ψ : U ⟶ E = \underline{Spec}_X(Sym(ℰ))`

over `X`, granted that `s` is invertible on `U`: the composite
`u^*ℰ ⟶ ι^*π^*(ℰ ⊕ 𝒪_X) ⟶ ι^*𝒪_P(1) ≅ 𝒪_U`, where the last arrow is the inverse of `ι^*s`
(that is, `m ↦ (m, 0) / s`), is adjoint to a morphism `ℰ ⟶ u_*𝒪_U`, whose extension to `Sym(ℰ)`
classifies `ψ` (`AlgebraicGeometry.Space.boundedRelativeSpecLift`).

## Main definitions

* `AlgebraicGeometry.Space.projectiveCompletionInfinityImmersion`: `i : 𝐏(ℰ) ⟶ P`.
* `AlgebraicGeometry.Space.projectiveCompletionAffinePart`: `U = P ∖ i(𝐏(ℰ))`, with
  `AlgebraicGeometry.Space.projectiveCompletionAffinePartHom` its inclusion and
  `AlgebraicGeometry.Space.projectiveCompletionAffinePartProj` its morphism to `X`.
* `AlgebraicGeometry.Space.projectiveCompletionAffinePartQuotient`: the morphism
  `u^*ℰ ⟶ 𝒪_U`, `m ↦ (m, 0) / s`.
* `AlgebraicGeometry.Space.projectiveCompletionAffinePartToVectorBundle`: **the morphism
  `ψ : U ⟶ E` over `X`.**

## Main results

* `AlgebraicGeometry.Space.projectiveCompletionAffinePartToVectorBundle_comp_projection`: `ψ`
  lies over `X`.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)

/-- **The hyperplane at infinity `i : 𝐏(ℰ) ⟶ P = 𝐏(ℰ ⊕ 𝒪_X)`**, the closed immersion of the
projection `ℰ ⊕ 𝒪_X ⟶ ℰ`, split by the inclusion of `ℰ`. -/
abbrev projectiveCompletionInfinityImmersion :
    @projectiveBundle B S hS X E (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite ⟶ projectiveCompletion E hr :=
  @projectiveBundleMapOfSplitEpi B S hS X (addUnit X.2 E) E (isQuasicoherentOnSite_addUnit hr)
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) biprod.fst biprod.inl
    biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr) hr.isFiniteLocallyFreeOnSite

/-- **The affine part `U = P ∖ i(𝐏(ℰ))` of the projective completion.** -/
abbrev projectiveCompletionAffinePart : AlgebraicSpaces B S hS :=
  @projectiveBundleSplitEpiComplement B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite

/-- The inclusion `ι : U ⟶ P`. -/
abbrev projectiveCompletionAffinePartHom :
    projectiveCompletionAffinePart E hr ⟶ projectiveCompletion E hr :=
  @projectiveBundleSplitEpiComplementHom B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite

/-- The morphism `u = π ∘ ι : U ⟶ X`. -/
abbrev projectiveCompletionAffinePartProj : projectiveCompletionAffinePart E hr ⟶ X :=
  projectiveCompletionAffinePartHom E hr ≫ projectiveCompletionProj E hr

/-- The map `π^*ℰ ⟶ 𝒪_P(1)`, `m ↦ (m, 0)`: the tautological surjection on the summand `ℰ`. -/
abbrev projectiveCompletionTautologicalInl :
    (modulePullback B S hS (projectiveCompletionProj E hr)).obj E ⟶
      (projectiveCompletionTwist E hr).obj :=
  (modulePullback B S hS (projectiveCompletionProj E hr)).map biprod.inl ≫
    projectiveCompletionTautological E hr

/-! ### The section `s` is invertible on `U` as soon as it is on the chart -/

/-- The inclusion `ι : U ⟶ P` is representable. -/
theorem relativelyRepresentable_projectiveCompletionAffinePartHom :
    yoneda.relativelyRepresentable (projectiveCompletionAffinePartHom E hr).hom :=
  @relativelyRepresentable_projectiveBundleSplitEpiComplementHom B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite

/-- **The étale chart `U_U = U ×_P P_U` of the affine part**, over the presenting chart bundle
`P_U` of the projective completion. -/
abbrev projectiveCompletionAffinePartChart : BigFppfOver B S hS :=
  @splitEpiComplementAtlasChart B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite

/-- The open immersion `U_U ⟶ P_U`. -/
abbrev projectiveCompletionAffinePartChartHom :
    projectiveCompletionAffinePartChart E hr ⟶
      (@projectiveBundleChartPresentation B S hS X (addUnit X.2 E)
        (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr)).U :=
  @splitEpiComplementAtlasChartHom B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite

/-- The chart `U_U ⟶ U`. -/
abbrev projectiveCompletionAffinePartChartToAffinePart :
    representedAlgebraicSpace B S hS (projectiveCompletionAffinePartChart E hr) ⟶
      projectiveCompletionAffinePart E hr :=
  ObjectProperty.homMk (@splitEpiComplementAtlasChartToComplement B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite)

/-- `U_U = U ×_P P_U`. -/
theorem isPullback_projectiveCompletionAffinePartChart :
    IsPullback (projectiveCompletionAffinePartChartToAffinePart E hr).hom
      (yoneda.map (projectiveCompletionAffinePartChartHom E hr))
      (projectiveCompletionAffinePartHom E hr).hom
      (@projectiveBundleChart B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)) :=
  @isPullback_splitEpiComplementAtlasChart B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite

/-- **The image of `U_U ⟶ P_U` is the complement of the image of the closed immersion of the chart
bundles** `𝐏(ℰ|_U) ⟶ 𝐏((ℰ ⊕ 𝒪)|_U)` over the presenting chart. -/
theorem range_projectiveCompletionAffinePartChartHom :
    Set.range ((BigFppfOver.toScheme B S hS).map
        (projectiveCompletionAffinePartChartHom E hr)).base =
      (Set.range ((BigFppfOver.toScheme B S hS).map
        ((@projectiveBundleChartFamilyHomOfSplitEpi B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite).siteApp
          (presentationChart (projectiveBundlePresentation X)))).base)ᶜ :=
  @range_splitEpiComplementAtlasChartHom B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite

/-- The chart `U_U ⟶ U` followed by `ι` is `U_U ⟶ P_U ⟶ P`. -/
theorem projectiveCompletionAffinePartChartToAffinePart_comp :
    projectiveCompletionAffinePartChartToAffinePart E hr ≫
        projectiveCompletionAffinePartHom E hr =
      representedSpaceMap B S hS (projectiveCompletionAffinePartChartHom E hr) ≫
        @projectiveBundleAtlas B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
          (isFiniteLocallyFreeOnSite_addUnit hr) :=
  ObjectProperty.hom_ext _ (isPullback_projectiveCompletionAffinePartChart E hr).w

/-- The chart `U_U ⟶ U` is étale. -/
theorem isEtale_projectiveCompletionAffinePartChartToAffinePart :
    IsEtale B S hS (projectiveCompletionAffinePartChartToAffinePart E hr).hom := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact (isEtale_iff_presheaf_of_yoneda B S hS _).2
    (MorphismProperty.of_isPullback (isPullback_projectiveCompletionAffinePartChart E hr).flip
      (@projectiveBundleChartPresentation B S hS X (addUnit X.2 E)
        (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr)).etale)

/-- The chart `U_U ⟶ U` is surjective on points. -/
theorem surjective_pointsMap_projectiveCompletionAffinePartChartToAffinePart :
    Function.Surjective (pointsMap B S hS _
      (projectiveCompletionAffinePartChartToAffinePart E hr).hom) :=
  surjective_pointsMap_of_isPullback B S hS
    (isPullback_projectiveCompletionAffinePartChart E hr).flip
    (@surjective_pointsMap_projectiveBundleAtlas B S hS X (addUnit X.2 E)
      (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr))

/-- Inverse images along equal morphisms of algebraic spaces preserve being an isomorphism. -/
theorem isIso_modulePullback_map_of_eq {Y Z : AlgebraicSpaces B S hS} {f g : Y ⟶ Z}
    (hfg : f = g) {M N : Modules.{u, u} B S hS Z.1 Z.2} (v : M ⟶ N)
    (hv : IsIso ((modulePullback B S hS g).map v)) : IsIso ((modulePullback B S hS f).map v) := by
  subst hfg
  exact hv

/-- **The section `s` is invertible on the affine part `U` as soon as its inverse image to the
chart `U_U ⟶ U ⟶ P` (which is `U_U ⟶ P_U ⟶ P`) is invertible**: being an isomorphism descends
along the surjective étale chart `U_U ⟶ U`. -/
theorem isIso_modulePullback_projectiveCompletionAffinePartHom_sectionHom
    (hc : IsIso ((modulePullback B S hS
      (projectiveCompletionAffinePartChartToAffinePart E hr ≫
        projectiveCompletionAffinePartHom E hr)).map (projectiveCompletionSectionHom E hr))) :
    IsIso ((modulePullback B S hS (projectiveCompletionAffinePartHom E hr)).map
      (projectiveCompletionSectionHom E hr)) := by
  refine isIso_of_forall_isIso_modulePullback_map_of_isFlat B S hS
    (fun _ : PUnit.{u + 1} => projectiveCompletionAffinePartChartToAffinePart E hr)
    (fun _ => isFlat_of_isEtale B S hS
      (isEtale_projectiveCompletionAffinePartChartToAffinePart E hr))
    ((isJointlySurjective_iff B S hS _ _).2 fun y =>
      ⟨PUnit.unit, surjective_pointsMap_projectiveCompletionAffinePartChartToAffinePart E hr y⟩)
    _ fun _ => ?_
  have nat := (modulePullbackCompIso B S hS (projectiveCompletionAffinePartChartToAffinePart E hr)
    (projectiveCompletionAffinePartHom E hr)).hom.naturality (projectiveCompletionSectionHom E hr)
  have e : (modulePullback B S hS (projectiveCompletionAffinePartChartToAffinePart E hr)).map
      ((modulePullback B S hS (projectiveCompletionAffinePartHom E hr)).map
        (projectiveCompletionSectionHom E hr)) =
      ((modulePullbackCompIso B S hS (projectiveCompletionAffinePartChartToAffinePart E hr)
          (projectiveCompletionAffinePartHom E hr)).app _).hom ≫
        (modulePullback B S hS (projectiveCompletionAffinePartChartToAffinePart E hr ≫
          projectiveCompletionAffinePartHom E hr)).map (projectiveCompletionSectionHom E hr) ≫
        ((modulePullbackCompIso B S hS (projectiveCompletionAffinePartChartToAffinePart E hr)
          (projectiveCompletionAffinePartHom E hr)).app _).inv := by
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).2 nat
  have := hc
  rw [e]
  infer_instance

variable (hs : IsIso ((modulePullback B S hS (projectiveCompletionAffinePartHom E hr)).map
  (projectiveCompletionSectionHom E hr)))

/-- **The map `u^*ℰ ⟶ 𝒪_U`, `m ↦ (m, 0) / s`**, granted that `s` is invertible on `U`: the
inverse image along `ι` of `(m, 0)`, followed by the inverse of `ι^*s`. -/
def projectiveCompletionAffinePartQuotient :
    (modulePullback B S hS (projectiveCompletionAffinePartProj E hr)).obj E ⟶
      SheafOfModules.unit (structureRingSheaf B S hS (projectiveCompletionAffinePart E hr)) :=
  (modulePullbackCompIso B S hS (projectiveCompletionAffinePartHom E hr)
      (projectiveCompletionProj E hr)).inv.app E ≫
    (modulePullback B S hS (projectiveCompletionAffinePartHom E hr)).map
      (projectiveCompletionTautologicalInl E hr) ≫
    @inv _ _ _ _ ((modulePullback B S hS (projectiveCompletionAffinePartHom E hr)).map
      (projectiveCompletionSectionHom E hr)) hs ≫
    (modulePullbackUnitIso B S hS (projectiveCompletionAffinePartHom E hr)).hom

/-- **The morphism `ℰ ⟶ u_*𝒪_U`** adjoint to `m ↦ (m, 0) / s`, with values in the module
underlying the direct-image algebra. -/
def projectiveCompletionAffinePartModuleMap :
    E ⟶ AlgebraSheaf.underlyingModule
      (pushforwardAlgebra B S hS (Over.mk (projectiveCompletionAffinePartProj E hr))) :=
  (modulePullbackAdjunction B S hS (projectiveCompletionAffinePartProj E hr)).homEquiv _ _
      (projectiveCompletionAffinePartQuotient E hr hs) ≫
    eqToHom (underlyingModule_pushforwardAlgebra B S hS
      (projectiveCompletionAffinePartProj E hr)).symm

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
    (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)]

/-- **The morphism `Sym(ℰ) ⟶ u_*𝒪_U` of `𝒪_X`-algebras** extending `m ↦ (m, 0) / s`. -/
def projectiveCompletionAffinePartAlgebraMap :
    symmetricAlgebraSheaf B S hS X E ⟶
      pushforwardAlgebra B S hS (Over.mk (projectiveCompletionAffinePartProj E hr)) :=
  SymAlgSheaf.algebraLift B S hS X _ E (projectiveCompletionAffinePartModuleMap E hr hs)

/-- **The morphism `ψ : U ⟶ E = \underline{Spec}_X(Sym(ℰ))`** from the affine part of the
projective completion to the vector bundle, classified by `Sym(ℰ) ⟶ u_*𝒪_U`. -/
def projectiveCompletionAffinePartToVectorBundle :
    projectiveCompletionAffinePart E hr ⟶ (vectorBundle B S hS X E).obj.left :=
  boundedRelativeSpecLift B S hS (projectiveCompletionAffinePartProj E hr)
    (symmetricQuasicoherentAlgebra B S hS X
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)) _
    (projectiveCompletionAffinePartAlgebraMap E hr hs)

/-- **`ψ` lies over `X`.** -/
@[reassoc (attr := simp)]
theorem projectiveCompletionAffinePartToVectorBundle_comp_projection :
    projectiveCompletionAffinePartToVectorBundle E hr hs ≫ vectorBundleProjection B S hS X E =
      projectiveCompletionAffinePartProj E hr :=
  boundedRelativeSpecLift_comp_hom B S hS _ _ _ _

end AlgebraicGeometry.Space

end
