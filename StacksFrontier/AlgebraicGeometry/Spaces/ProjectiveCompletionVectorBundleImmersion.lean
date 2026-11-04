module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionAffinePart
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafIsoOfCartesianFamily

/-!
# The vector bundle as the affine part of its projective completion

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module of rank `r`, `E` its vector
bundle and `P = 𝐏(ℰ ⊕ 𝒪_X)` its projective completion with the hyperplane at infinity
`i : 𝐏(ℰ) ⟶ P`. The morphism `ψ : U ⟶ E` from the affine part `U = P ∖ i(𝐏(ℰ))`
(`AlgebraicGeometry.Space.projectiveCompletionAffinePartToVectorBundle`) is an isomorphism as soon
as it is one over a covering family of étale charts of `X`. Its inverse followed by the inclusion
of `U` is then an open immersion `j : E ⟶ P` over `X` whose image is `|P| ∖ |i(𝐏(ℰ))|`.

## Main definitions

* `AlgebraicGeometry.Space.projectiveCompletionVectorBundleImmersionOfIsIso`: the morphism
  `j : E ⟶ P`.

## Main results

* `AlgebraicGeometry.Space.isIso_projectiveCompletionAffinePartToVectorBundle_of_isPullback`:
  `ψ` is an isomorphism as soon as it is one over a covering family of charts.
* `isOpenImmersion_projectiveCompletionVectorBundleImmersionOfIsIso`: `j` is an open immersion.
* `range_pointsMap_projectiveCompletionVectorBundleImmersionOfIsIso`: the image of `j` is the
  complement of the hyperplane at infinity.

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
    (hs : IsIso ((modulePullback B S hS (projectiveCompletionAffinePartHom E hr)).map
      (projectiveCompletionSectionHom E hr)))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] in
/-- For a chart `V` with a morphism `m` to the presenting chart, the square exhibiting
`U ×_X V` as the complement over `V` is cartesian. -/
theorem isPullback_projectiveCompletionAffinePart_toChart {V : SmallEtale B S hS X.1}
    (m : V ⟶ bundleBaseChart X) :
    IsPullback
      (@splitEpiComplementChartToComplement B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m)
      (yoneda.map (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m ≫
        (@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
          (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart V))
      (projectiveCompletionAffinePartProj E hr).hom V.obj.hom :=
  @isPullback_splitEpiComplementChart_toChart B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite V m

/-- `ψ : U ⟶ E` is an isomorphism as soon as it is one over a covering family of charts: for a
family of charts `V_k` with morphisms `m_k` to the presenting chart, which covers `X` locally,
such that each square `U ×_X V_k ⟶ U ⟶ E` over `V_k ⟶ X` is cartesian. -/
theorem isIso_projectiveCompletionAffinePartToVectorBundle_of_isPullback {ι : Type*}
    (V : ι → SmallEtale B S hS X.1) (m : ∀ k, V k ⟶ bundleBaseChart X)
    (hcover : ∀ (T : BigFppfOver B S hS) (x : X.1.obj (Opposite.op T)),
      Presheaf.familyImageSieve (fun k => (V k).obj.hom) x ∈ BigFppfOver.topology B S hS T)
    (hpb : ∀ k, IsPullback
      (@splitEpiComplementChartToComplement B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite (V k) (m k) ≫
        (projectiveCompletionAffinePartToVectorBundle E hr hs).hom)
      (yoneda.map (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite (V k) (m k) ≫
        (@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
          (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart (V k)))
      (vectorBundleProjection B S hS X E).hom (V k).obj.hom) :
    IsIso (projectiveCompletionAffinePartToVectorBundle E hr hs) := by
  have hiso : IsIso (projectiveCompletionAffinePartToVectorBundle E hr hs).hom :=
    Presheaf.isIso_of_isPullback_family (BigFppfOver.topology B S hS)
      (projectiveCompletionAffinePart E hr).2.isSheaf
      (vectorBundle B S hS X E).obj.left.2.isSheaf (projectiveCompletionAffinePartProj E hr).hom
      (vectorBundleProjection B S hS X E).hom
      (projectiveCompletionAffinePartToVectorBundle E hr hs).hom
      (congrArg (fun f => f.hom)
        (projectiveCompletionAffinePartToVectorBundle_comp_projection E hr hs))
      (fun k => (V k).obj.hom) hcover _ _
      (fun k => isPullback_projectiveCompletionAffinePart_toChart E hr (m k)) hpb
  exact ⟨⟨ObjectProperty.homMk (inv (projectiveCompletionAffinePartToVectorBundle E hr hs).hom),
    ObjectProperty.hom_ext _ (IsIso.hom_inv_id _), ObjectProperty.hom_ext _ (IsIso.inv_hom_id _)⟩⟩

variable [IsIso (projectiveCompletionAffinePartToVectorBundle E hr hs)]

/-- The open immersion `j : E ⟶ P = 𝐏(ℰ ⊕ 𝒪_X)` of the vector bundle into its projective
completion, granted that `ψ` is an isomorphism: the inverse of `ψ : U ⟶ E` followed by the
inclusion of the affine part. -/
def projectiveCompletionVectorBundleImmersionOfIsIso :
    (vectorBundle B S hS X E).obj.left ⟶ projectiveCompletion E hr :=
  inv (projectiveCompletionAffinePartToVectorBundle E hr hs) ≫
    projectiveCompletionAffinePartHom E hr

/-- `j` lies over `X`: `π ∘ j = p`. -/
@[reassoc]
theorem projectiveCompletionVectorBundleImmersionOfIsIso_comp_projectiveCompletionProj :
    projectiveCompletionVectorBundleImmersionOfIsIso E hr hs ≫ projectiveCompletionProj E hr =
      vectorBundleProjection B S hS X E := by
  rw [projectiveCompletionVectorBundleImmersionOfIsIso, Category.assoc, IsIso.inv_comp_eq,
    projectiveCompletionAffinePartToVectorBundle_comp_projection]

/-- `j` is an open immersion. -/
theorem isOpenImmersion_projectiveCompletionVectorBundleImmersionOfIsIso :
    IsOpenImmersion B S hS (projectiveCompletionVectorBundleImmersionOfIsIso E hr hs).hom := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : MorphismProperty.RespectsIso (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsIso (inv (projectiveCompletionAffinePartToVectorBundle E hr hs)).hom :=
    (ObjectProperty.ι _).map_isIso _
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2
    (isOpenSubspace_openComplement B S hS (projectiveCompletion E hr).2 _
      (@projectiveBundleSplitEpiImage B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite).2).2

/-- The image of `j` is the complement of the hyperplane at infinity:
`|j(E)| = |P| ∖ |i(𝐏(ℰ))|`. -/
theorem range_pointsMap_projectiveCompletionVectorBundleImmersionOfIsIso :
    Set.range (pointsMap B S hS _ (projectiveCompletionVectorBundleImmersionOfIsIso E hr hs).hom) =
      (Set.range (pointsMap B S hS _ (projectiveCompletionInfinityImmersion E hr).hom))ᶜ := by
  refine Eq.trans ?_ (@range_pointsMap_projectiveBundleSplitEpiComplementHom B S hS X
    (addUnit X.2 E) E (isQuasicoherentOnSite_addUnit hr)
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) biprod.fst biprod.inl
    biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr) hr.isFiniteLocallyFreeOnSite)
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨pointsMap B S hS _ (inv (projectiveCompletionAffinePartToVectorBundle E hr hs)).hom q,
      (pointsMap_comp_apply B S hS _ _ q).symm⟩
  · rintro ⟨q, rfl⟩
    refine ⟨pointsMap B S hS _ (projectiveCompletionAffinePartToVectorBundle E hr hs).hom q, ?_⟩
    refine (pointsMap_comp_apply B S hS _ _ q).symm.trans ?_
    congr 1
    exact congrArg (fun f => f.hom) (show projectiveCompletionAffinePartToVectorBundle E hr hs ≫
        projectiveCompletionVectorBundleImmersionOfIsIso E hr hs =
          projectiveCompletionAffinePartHom E hr by
      rw [projectiveCompletionVectorBundleImmersionOfIsIso, IsIso.hom_inv_id_assoc])

end AlgebraicGeometry.Space

end
