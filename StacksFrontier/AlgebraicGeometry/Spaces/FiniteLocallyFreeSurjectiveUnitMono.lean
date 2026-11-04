module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.FlatBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# The structure map of a surjective finite locally free morphism is injective

Let `f : X ⟶ Y` be a surjective finite locally free morphism of algebraic spaces over a scheme
`S`.  The structure map `𝒪_Y ⟶ f_*𝒪_X` is a monomorphism of `𝒪_Y`-modules.  This is the form in
which the proof of Stacks 0GUV uses that `f_*𝒪_X` has positive rank: on a piece of a covering
where `f_*𝒪_X` is free of rank zero, the structure sheaf itself vanishes.

## Main results

* `AlgebraicGeometry.Space.surjective_toScheme_map_of_isIso_chartLift`: a chart diagram over a
  surjective morphism whose cartesian form is an isomorphism has surjective underlying morphism of
  schemes.
* `AlgebraicGeometry.Space.exists_mono_unit_pushforwardStructureModule`: the structure map of a
  surjective finite locally free morphism is a monomorphism `𝒪_Y ⟶ f_*𝒪_X`.

## Implementation notes

The map is the transpose, along the chartwise universal property of the direct image, of
pullback of regular functions (`AlgebraicGeometry.Space.structureModuleFMap`).  Injectivity is
checked over the affine étale charts `V` of `Y`, where it is injectivity of the faithfully flat
ring map `𝒪_Y(V) ⟶ 𝒪_X(V ×_Y X)`.

## References

* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 0GUV](https://stacks.math.columbia.edu/tag/0GUV)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The underlying morphism of schemes of a chart diagram `W ⟶ V` over a surjective `f` whose
cartesian form `W ⟶ V ×_Y X` is an isomorphism is surjective: it is a base change of `f`. -/
theorem surjective_toScheme_map_of_isIso_chartLift (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (V : SmallEtale B S hS Y.1)
    (W : SmallEtale B S hS X.1)
    (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom)
    (hiso : IsIso (chartLift B S hS f ⟨W, V, b, hb⟩)) :
    Surjective ((BigFppfOver.toScheme B S hS).map b) := by
  refine surjective_of_surjective_pointsMap_yoneda_map B S hS b ?_
  have h1 : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map
      (chartLift B S hS f ⟨W, V, b, hb⟩)).hom :=
    isSurjective_of_isIso B S hS ((SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _).map
      (chartLift B S hS f ⟨W, V, b, hb⟩))
  have h2 : IsSurjective B S hS (chartBaseChangeProjection B S hS f V).hom :=
    isSurjective_of_isPullback B S hS (isPullback_chartBaseChangeInclusion B S hS f V) hsurj
  have h3 := isSurjective_comp B S hS h1 h2
  have he : ((SpacesEtale.toSpaces B S hS X).map (chartLift B S hS f ⟨W, V, b, hb⟩)).hom ≫
      (chartBaseChangeProjection B S hS f V).hom = yoneda.map b :=
    congrArg (fun k => k.hom) (chartLift_projection B S hS f ⟨W, V, b, hb⟩)
  rw [he] at h3
  exact h3

/-- **The structure map of a surjective finite locally free morphism of algebraic spaces is a
monomorphism `𝒪_Y ⟶ f_*𝒪_X`.**

The map is the transpose along the chartwise universal property of the direct image of pullback of
regular functions (`AlgebraicGeometry.Space.structureModuleFMap`).  It is checked on the affine
étale charts `V` of `Y`: over the affine chart `W = V ×_Y X` above `V` it is the ring map
`𝒪_Y(V) ⟶ 𝒪_X(W)`, which is flat because `𝒪_X(W) = (f_*𝒪_X)(V)` is a projective `𝒪_Y(V)`-module,
and surjective on spectra because `W ⟶ V` is a base change of the surjective `f`; so it is
faithfully flat, hence injective. -/
theorem exists_mono_unit_pushforwardStructureModule (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (hf : IsFiniteLocallyFree B S hS f) :
    ∃ m : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶ pushforwardStructureModule B S hS f, Mono m := by
  let m := (modulePushforwardHomEquiv B S hS f _ _).symm (structureModuleFMap B S hS f)
  have hinj : ∀ V : SmallEtale B S hS Y.1, IsAffine (chartScheme V) →
      Function.Injective (m.val.app (op V)) := by
    intro V hV
    obtain ⟨W, b, hb, hWa, hiso, hbij⟩ :=
      exists_affine_chartDiagram_isIso_chartLift_bijective B S hS f hf.1 V hV
    have hc : ∀ r, modulePushforwardCounitApp B S hS f _ ⟨W, V, b, hb⟩ (m.val.app (op V) r) =
        chartDiagramPullback B S hS f ⟨W, V, b, hb⟩ r := fun r =>
      congrArg (fun ξ => ξ.app ⟨W, V, b, hb⟩ r)
        (Equiv.apply_symm_apply (modulePushforwardHomEquiv B S hS f _ _)
          (structureModuleFMap B S hS f))
    let := (chartDiagramPullback B S hS f ⟨W, V, b, hb⟩).hom.toAlgebra
    obtain ⟨-, hproj⟩ := module_finite_projective_chartRing_of_isFiniteLocallyFree B S hS f hf
      ⟨W, V, b, hb⟩ hV (hbij _)
    have : Module.Flat (chartRing B S hS Y.1 Y.2 V) (chartRing B S hS X.1 X.2 W) :=
      Module.Flat.of_projective
    have := surjective_toScheme_map_of_isIso_chartLift B S hS f hsurj V W b hb hiso
    have : IsAffine (chartScheme W) := hWa
    have hspec : Surjective (Spec.map ((BigFppfOver.toScheme B S hS).map b).appTop) :=
      (MorphismProperty.arrow_mk_iso_iff @Surjective
        (arrowIsoSpecΓOfIsAffine ((BigFppfOver.toScheme B S hS).map b))).mp inferInstance
    have : Module.FaithfullyFlat (chartRing B S hS Y.1 Y.2 V) (chartRing B S hS X.1 X.2 W) :=
      Module.FaithfullyFlat.of_comap_surjective hspec.surj
    have hρ : Function.Injective (chartDiagramPullback B S hS f ⟨W, V, b, hb⟩).hom :=
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance).injective
    intro r t hrt
    exact hρ ((hc r).symm.trans ((congrArg _ hrt).trans (hc t)))
  refine ⟨m, Preadditive.mono_of_cancel_zero _ fun {L} ψ hψ => ?_⟩
  refine eq_zero_of_affineChartDiagram (𝟙 Y) ψ fun d hU _ => ?_
  ext y
  refine hinj d.U hU ?_
  have h := congrArg (fun k => k.val.app (op d.U) y) hψ
  exact h.trans (map_zero _).symm

end AlgebraicGeometry.Space

end
