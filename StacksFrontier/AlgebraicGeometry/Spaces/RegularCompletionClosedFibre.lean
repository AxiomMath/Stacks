module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CompletionBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularCompletionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Regularity over the closed fibre after base change to the completion

Let `(A, 𝔪)` be a Noetherian local ring, let `X` be a decent algebraic space locally of finite
type over `Spec A` and let `Y = X ×_{Spec A} Spec A^` be its base change to the `𝔪`-adic
completion. At a point of `Y` lying over the closed point of `Spec A^` the henselian local
rings of `Y` and of `X` are regular together.

## Main results

* `AlgebraicGeometry.Space.isRegularAt_completionSpace_iff_of_mem_closedFibre`: regularity at a
  point of the closed fibre is unchanged by the base change.
* `AlgebraicGeometry.Space.isRegularLocalRing_henselianLocalRing_completion_iff`: the same
  statement for the henselian local rings.

## References

* [Stacks Project, Tag 0BHQ](https://stacks.math.columbia.edu/tag/0BHQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
variable (hAc : B.Contains (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))))
variable {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
variable (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))

attribute [local instance high] hasPullbacks_presheaf_CompletionBaseChange
  hasPullback_presheaf_CompletionBaseChange


omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The identity of the represented presheaf of the terminal object is an étale chart. -/
private theorem presheaf_etale_id_terminal :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf
      (𝟙 (yoneda.obj (Over.mk (𝟙 (B.obj hA))))) := by
  refine presheaf_id_of_iso B (Spec (.of A)) hA _ (fun {_ _} g hg ↦ ?_) _
  have : IsIso ((BigFppfOver.toScheme B (Spec (.of A)) hA).map g) := by
    let _ := hg; infer_instance
  change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B (Spec (.of A)) hA).map g)
  infer_instance

/-- Regularity at a point of the closed fibre is unchanged by base change of the base ring to
its `𝔪`-adic completion, read on a prescribed étale scheme chart of the source. -/
private theorem isRegularAt_completionSpace_iff_of_chart
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f)
    (U : BigFppfOver B (Spec (.of A)) hA) (a : yoneda.obj U ⟶ X)
    (haE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf a)
    (y : points B (Spec (.of A)) hA (completionSpace A B hA hAc f))
    (z : points B (Spec (.of A)) hA (yoneda.obj (completionChart A B hA hAc U)))
    (hz : pointsMap B (Spec (.of A)) hA (yoneda.obj (completionChart A B hA hAc U))
      (completionChartMap A B hA hAc f a) z = y)
    (hy : pointsToScheme B (Spec (.of A)) hA (completionBase A B hA hAc)
        (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
          (pullback.snd f (completionBaseMap A B hA hAc)) y) =
      (⟨IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A),
        inferInstance⟩ :
        PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A))) :
    IsRegularAt B (Spec (.of A)) hA (completionSpace A B hA hAc f) y ↔
      IsRegularAt B (Spec (.of A)) hA X
        (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
          (completionProjection A B hA hAc f) y) := by
  set gU : U ⟶ Over.mk (𝟙 (B.obj hA)) := Over.homMk U.hom
  set h0 := yoneda.preimage (completionBaseMap A B hA hAc)
  have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B (Spec (.of A)) hA).map gU) :=
    hf U (Over.mk (𝟙 (B.obj hA))) a (𝟙 _) gU haE
      (presheaf_etale_id_terminal A B hA)
      (by rw [Category.comp_id, comp_eq_yoneda_structureHom A B hA f a])
  have hsndeq : completionChartMap A B hA hAc f a ≫
      pullback.snd f (completionBaseMap A B hA hAc) =
      yoneda.map (pullback.snd gU h0) := pullback.lift_snd _ _ _
  have h1 : pointsMap B (Spec (.of A)) hA (yoneda.obj (completionChart A B hA hAc U))
      (yoneda.map (pullback.snd gU h0)) z =
      pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
        (pullback.snd f (completionBaseMap A B hA hAc)) y :=
    (congrArg (fun m ↦ pointsMap B (Spec (.of A)) hA
        (yoneda.obj (completionChart A B hA hAc U)) m z) hsndeq).symm.trans
      ((pointsMap_comp_apply B (Spec (.of A)) hA (completionChartMap A B hA hAc f a)
          (pullback.snd f (completionBaseMap A B hA hAc)) z).trans
        (congrArg (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
          (pullback.snd f (completionBaseMap A B hA hAc))) hz))
  have hclosed :
      (BigFppfOver.toScheme B (Spec (.of A)) hA).map (pullback.snd gU h0)
        (pointsToScheme B (Spec (.of A)) hA (completionChart A B hA hAc U) z) =
      (⟨IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A),
        inferInstance⟩ :
        PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :=
    (pointsToScheme_pointsMap_yoneda B (Spec (.of A)) hA (pullback.snd gU h0) z).symm.trans
      ((congrArg (pointsToScheme B (Spec (.of A)) hA (completionBase A B hA hAc)) h1).trans hy)
  have haE' := (isEtale_iff_presheaf_of_yoneda B (Spec (.of A)) hA a).2 haE
  exact isRegularAt_iff_of_chartData A B hA hX
    (isAlgebraicSpace_completionSpace A B hA hAc f hX)
    (completionProjection A B hA hAc f) U (completionChart A B hA hAc U) a haE'
    (completionChartMap A B hA hAc f a) (isEtale_completionChartMap A B hA hAc f a haE')
    (pullback.fst gU h0) ((BigFppfOver.toScheme B (Spec (.of A)) hA).map gU)
    ((BigFppfOver.toScheme B (Spec (.of A)) hA).map (pullback.snd gU h0))
    (isPullback_completionChart A B hA hAc f a)
    (isPullback_toScheme_completionChart A B hA hAc U) y z hz hclosed

/-- Regularity at a point of the closed fibre is unchanged by base change of the base ring to
its `𝔪`-adic completion. -/
theorem isRegularAt_completionSpace_iff_of_mem_closedFibre
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f)
    (y : points B (Spec (.of A)) hA (completionSpace A B hA hAc f))
    (hy : pointsToScheme B (Spec (.of A)) hA (completionBase A B hA hAc)
        (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
          (pullback.snd f (completionBaseMap A B hA hAc)) y) =
      (⟨IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A),
        inferInstance⟩ :
        PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A))) :
    IsRegularAt B (Spec (.of A)) hA (completionSpace A B hA hAc f) y ↔
      IsRegularAt B (Spec (.of A)) hA X
        (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
          (completionProjection A B hA hAc f) y) := by
  obtain ⟨U, a, hsurj, haE⟩ := hX.exists_atlas
  obtain ⟨p, hp⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B (Spec (.of A)) hA X hX U a).mp hsurj
      (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
        (completionProjection A B hA hAc f) y)
  obtain ⟨z, -, hz⟩ := exists_points_of_isPullback B (Spec (.of A)) hA
    (isPullback_completionChart A B hA hAc f a) p y hp
  exact isRegularAt_completionSpace_iff_of_chart A B hA hAc f hX hf U a haE y z hz hy

/-- Let `(A, 𝔪)` be a Noetherian local ring, let `X` be a decent algebraic space locally of finite
type over `Spec A` and let `Y = X ×_{Spec A} Spec A^` be its base change to the `𝔪`-adic
completion. At a point `y` of `Y` lying over the closed point of `Spec A^`, the henselian local
ring of `Y` at `y` is regular if and only if the henselian local ring of `X` at the image of `y`
is regular. -/
@[stacks 0BHQ "part (2)"]
theorem isRegularLocalRing_henselianLocalRing_completion_iff
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hXdec : IsDecentSpace B (Spec (.of A)) hA X)
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f)
    (y : points B (Spec (.of A)) hA (completionSpace A B hA hAc f))
    (hy : pointsToScheme B (Spec (.of A)) hA (completionBase A B hA hAc)
        (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
          (pullback.snd f (completionBaseMap A B hA hAc)) y) =
      (⟨IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A),
        inferInstance⟩ :
        PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A))) :
    IsRegularLocalRing
        (henselianLocalRing B (Spec (.of A)) hA (completionSpace A B hA hAc f)
          (isAlgebraicSpace_completionSpace A B hA hAc f hX) y
          (isDecentSpace_completionSpace A B hA hAc f hX hXdec) : Type (u + 1)) ↔
      IsRegularLocalRing
        (henselianLocalRing B (Spec (.of A)) hA X hX
          (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
            (completionProjection A B hA hAc f) y) hXdec : Type (u + 1)) := by
  have hNX := hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_base
    A B hA f hX hf
  have hNY := hasEtaleLocalProperty_isLocallyNoetherian_completionSpace A B hA hAc f hX hf
  rw [← isRegularAt_iff_isRegularLocalRing_henselianLocalRing B (Spec (.of A)) hA
      (completionSpace A B hA hAc f) (isAlgebraicSpace_completionSpace A B hA hAc f hX)
      (isDecentSpace_completionSpace A B hA hAc f hX hXdec) hNY y,
    ← isRegularAt_iff_isRegularLocalRing_henselianLocalRing B (Spec (.of A)) hA X hX hXdec
      hNX _]
  exact isRegularAt_completionSpace_iff_of_mem_closedFibre A B hA hAc f hX hf y hy

end AlgebraicGeometry.Space

end
