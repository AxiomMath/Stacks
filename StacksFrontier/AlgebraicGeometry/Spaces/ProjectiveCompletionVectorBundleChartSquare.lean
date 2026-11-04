module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartFamilyCoveringSieve
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSplitEpiHyperplaneIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionVectorBundleImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.LocalModel

/-!
# The affine part of the projective completion over an affine chart

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module of rank `r`, `U` the affine
part of the projective completion `P = 𝐏(ℰ ⊕ 𝒪_X)` and `ψ : U ⟶ E` the morphism to the vector
bundle (`AlgebraicGeometry.Space.projectiveCompletionAffinePartToVectorBundle`), defined since
the section `s` is invertible on `U` (in namespace `AlgebraicGeometry.Space`:
`isIso_modulePullback_projectiveCompletionAffinePartHom_projectiveCompletionSectionHom`).

Over an affine étale chart `V` of `X` with a morphism `m` to the presenting chart, `U ×_X V` is the
object `A = U ×_P P_V` of the site and `E ×_X V` is `Q = Spec Γ(V, Sym(ℰ))`
(`AlgebraicGeometry.Space.isPullback_vectorBundleChart`). This file builds the morphism
`φ : A ⟶ Q` over `V` induced by `ψ`, and shows that the square of `ψ` over `V` is cartesian as
soon as `φ` is an isomorphism of schemes. This is the hypothesis of
`AlgebraicGeometry.Space.isIso_projectiveCompletionAffinePartToVectorBundle_of_isPullback`.

## Main definitions

* `AlgebraicGeometry.Space.projectiveCompletionAffinePartChartToVectorBundleChart`: `φ : A ⟶ Q`.

## Main results

* `AlgebraicGeometry.Space.isPullback_projectiveCompletionAffinePartToVectorBundle_chart_of_isIso`:
  the square of `ψ` over the chart is cartesian when `φ` is an isomorphism of schemes.
* `AlgebraicGeometry.Space.isIso_projectiveCompletionAffinePartToVectorBundle_of_forall_chart`:
  `ψ` is an isomorphism when `φ` is one over every affine chart on which `ℰ` is free.

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
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)]

/-- **The morphism `ψ : U ⟶ E` from the affine part of the projective completion to the vector
bundle**, with the invertibility of `s` on `U` supplied. -/
abbrev projectiveCompletionAffinePartToVectorBundle' :
    projectiveCompletionAffinePart E hr ⟶ (vectorBundle B S hS X E).obj.left :=
  projectiveCompletionAffinePartToVectorBundle E hr
    (isIso_modulePullback_projectiveCompletionAffinePartHom_projectiveCompletionSectionHom E hr)

variable {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X) [IsAffine (chartScheme V)]

/-- The object `A = U ×_P P_V = U ×_X V` of the site, over a chart `V` with a morphism `m` to the
presenting chart. -/
abbrev projectiveCompletionAffinePartOverChart : BigFppfOver B S hS :=
  @splitEpiComplementChart B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite V m

/-- The morphism `A ⟶ U`. -/
abbrev projectiveCompletionAffinePartOverChartToAffinePart :
    yoneda.obj (projectiveCompletionAffinePartOverChart E hr m) ⟶
      (projectiveCompletionAffinePart E hr).1 :=
  @splitEpiComplementChartToComplement B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite V m

/-- The morphism `A ⟶ P_V ⟶ V`. -/
abbrev projectiveCompletionAffinePartOverChartToChart :
    projectiveCompletionAffinePartOverChart E hr m ⟶ V.obj.left :=
  @splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
    (isQuasicoherentOnSite_addUnit hr) (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
    hr.isFiniteLocallyFreeOnSite V m ≫
    (@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart V

omit [IsAffine (chartScheme V)] in
/-- The composite `A ⟶ U ⟶ E ⟶ X` equals the composite `A ⟶ V ⟶ X`. -/
theorem projectiveCompletionAffinePartOverChart_w :
    (projectiveCompletionAffinePartOverChartToAffinePart E hr m ≫
        (projectiveCompletionAffinePartToVectorBundle' E hr).hom) ≫
      (vectorBundleProjection B S hS X E).hom =
    yoneda.map (projectiveCompletionAffinePartOverChartToChart E hr m) ≫ V.obj.hom := by
  rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    projectiveCompletionAffinePartToVectorBundle_comp_projection]
  exact (isPullback_projectiveCompletionAffinePart_toChart E hr m).w

/-- **The morphism `φ : A = U ×_X V ⟶ Q = E ×_X V` induced by `ψ`**, a morphism of the site over
`V`. -/
def projectiveCompletionAffinePartChartToVectorBundleChart :
    projectiveCompletionAffinePartOverChart E hr m ⟶
      vectorBundleChart B S hS X (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V :=
  yoneda.preimage ((isPullback_vectorBundleChart B S hS X
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V).lift
    (projectiveCompletionAffinePartOverChartToAffinePart E hr m ≫
      (projectiveCompletionAffinePartToVectorBundle' E hr).hom)
    (yoneda.map (projectiveCompletionAffinePartOverChartToChart E hr m))
    (projectiveCompletionAffinePartOverChart_w E hr m))

/-- The composite of `φ : A ⟶ Q` with `Q ⟶ E` is the composite `A ⟶ U ⟶ E` of `ψ`. -/
theorem yoneda_map_projectiveCompletionAffinePartChartToVectorBundleChart_toTotal :
    yoneda.map (projectiveCompletionAffinePartChartToVectorBundleChart E hr m) ≫
        vectorBundleChartToTotal B S hS X
          (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V =
      projectiveCompletionAffinePartOverChartToAffinePart E hr m ≫
        (projectiveCompletionAffinePartToVectorBundle' E hr).hom := by
  rw [projectiveCompletionAffinePartChartToVectorBundleChart, Functor.map_preimage]
  exact IsPullback.lift_fst _ _ _ _

/-- **`φ` lies over `V`.** -/
theorem projectiveCompletionAffinePartChartToVectorBundleChart_comp_hom :
    projectiveCompletionAffinePartChartToVectorBundleChart E hr m ≫
        vectorBundleChartHom B S hS X
          (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V =
      projectiveCompletionAffinePartOverChartToChart E hr m := by
  apply yoneda.map_injective
  rw [Functor.map_comp, projectiveCompletionAffinePartChartToVectorBundleChart,
    Functor.map_preimage]
  exact IsPullback.lift_snd _ _ _ _

/-- **The square of `ψ` over the chart is cartesian as soon as `φ` is an isomorphism of
schemes**: then `A` is `E ×_X V` through `φ`. -/
theorem isPullback_projectiveCompletionAffinePartToVectorBundle_chart_of_isIso
    (h : IsIso ((BigFppfOver.toScheme B S hS).map
      (projectiveCompletionAffinePartChartToVectorBundleChart E hr m))) :
    IsPullback
      (projectiveCompletionAffinePartOverChartToAffinePart E hr m ≫
        (projectiveCompletionAffinePartToVectorBundle' E hr).hom)
      (yoneda.map (projectiveCompletionAffinePartOverChartToChart E hr m))
      (vectorBundleProjection B S hS X E).hom V.obj.hom := by
  have : IsIso (projectiveCompletionAffinePartChartToVectorBundleChart E hr m) :=
    isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  refine IsPullback.of_iso (isPullback_vectorBundleChart B S hS X
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V)
    (asIso (yoneda.map (projectiveCompletionAffinePartChartToVectorBundleChart E hr m))).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp) <;>
    rw [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id, IsIso.eq_inv_comp]
  · rw [yoneda_map_projectiveCompletionAffinePartChartToVectorBundleChart_toTotal]
  · rw [← Functor.map_comp, projectiveCompletionAffinePartChartToVectorBundleChart_comp_hom]

omit [IsAffine (chartScheme V)] in
/-- **`ψ` is an isomorphism as soon as `φ` is one over every affine chart on which `ℰ` is
free**: the family of such charts over the presenting chart covers `X`
(`AlgebraicGeometry.Space.exists_affine_free_chart_family`). -/
theorem isIso_projectiveCompletionAffinePartToVectorBundle_of_forall_chart
    (H : ∀ (V : SmallEtale B S hS X.1) (m : V ⟶ bundleBaseChart X) [IsAffine (chartScheme V)]
      (n : Type u) [Finite n]
      (_ : (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E).over V ≅
        SheafOfModules.free (R := (structureRingSheaf B S hS X).over V) n),
      IsIso ((BigFppfOver.toScheme B S hS).map
        (projectiveCompletionAffinePartChartToVectorBundleChart E hr m))) :
    IsIso (projectiveCompletionAffinePartToVectorBundle' E hr) := by
  obtain ⟨ι, V, m, n, hn, e, hV, hcover⟩ :=
    exists_affine_free_chart_family (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)
  have hpb := fun k => isPullback_projectiveCompletionAffinePartToVectorBundle_chart_of_isIso E hr
    (m k) (H (V k) (m k) (n k) (e k))
  have key := isIso_projectiveCompletionAffinePartToVectorBundle_of_isPullback E hr
    (isIso_modulePullback_projectiveCompletionAffinePartHom_projectiveCompletionSectionHom E hr)
    V m hcover
  with_reducible exact key hpb

end AlgebraicGeometry.Space

end
