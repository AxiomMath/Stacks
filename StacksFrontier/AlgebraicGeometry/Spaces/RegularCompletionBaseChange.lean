module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.RegularGerm
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.RegularBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CompletionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CompletionBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RegularHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularFlatDescent

/-!
# Regularity and base change to the completion of the base ring

Let `(A, 𝔪)` be a Noetherian local ring, let `X` be a decent algebraic space locally of finite
type over `Spec A`, and let `Y = X ×_{Spec A} Spec A^` be its base change to the `𝔪`-adic
completion. The projection `Y ⟶ X` is flat, so regularity of a local ring of `Y` descends to the
local ring of `X` at the image point; read through the identification of the henselian local
ring with a henselization of the local ring of an étale chart, this says that regularity of
`𝒪^h_{Y,y}` implies regularity of `𝒪^h_{X,x}`.

## Main results

* `AlgebraicGeometry.Space.isRegularAt_completionSpace_descent`: regularity at a point descends
  from the completed base change.
* `AlgebraicGeometry.Space.isRegularLocalRing_henselianLocalRing_of_completion`: the same
  statement for the henselian local rings.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_base`
  — an algebraic space locally of finite type over the spectrum of a Noetherian local ring is
  locally Noetherian.

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

omit [IsLocalRing A] in
/-- The spectrum of a Noetherian local ring, as the terminal object of the big fppf site over
itself, is locally Noetherian. -/
private theorem hasEtaleLocalProperty_isLocallyNoetherian_base :
    HasEtaleLocalProperty B (Spec (.of A)) hA (yoneda.obj (Over.mk (𝟙 (B.obj hA))))
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) := by
  refine hasEtaleLocalProperty_of_representable B (Spec (.of A)) hA _ _
    (Over.mk (𝟙 (B.obj hA))) (Iso.refl _) ?_
  show IsLocallyNoetherian (Spec (CommRingCat.of A))
  infer_instance

omit [IsLocalRing A] hAc in
/-- An algebraic space locally of finite type over the spectrum of a Noetherian local ring is
locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_base
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f) :
    HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B (Spec (.of A)) hA hX
    (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))) f hf
    (hasEtaleLocalProperty_isLocallyNoetherian_base A B hA)

/-- Regularity at a point descends from the base change to the completion of the base ring: the
projection of the completed base change is flat, and regularity at a point descends along a flat
morphism of locally Noetherian algebraic spaces. -/
theorem isRegularAt_completionSpace_descent
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f)
    (y : points B (Spec (.of A)) hA (completionSpace A B hA hAc f))
    (hy : IsRegularAt B (Spec (.of A)) hA (completionSpace A B hA hAc f) y) :
    IsRegularAt B (Spec (.of A)) hA X
      (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
        (completionProjection A B hA hAc f) y) :=
  isRegularAt_of_isFlat B (Spec (.of A)) hA
    (isAlgebraicSpace_completionSpace A B hA hAc f hX) hX
    (completionProjection A B hA hAc f) (isFlat_completionProjection A B hA hAc f hX)
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_base A B hA f hX hf)
    y hy

/-- **Stacks 0BHQ, part (1).** Let `(A, 𝔪)` be a Noetherian local ring, let `X` be a decent
algebraic space locally of finite type over `Spec A` and let `Y = X ×_{Spec A} Spec A^` be its
base change to the `𝔪`-adic completion. If the henselian local ring of `Y` at a point `y` is
regular, then so is the henselian local ring of `X` at the image of `y`. -/
@[stacks 0BHQ "part (1)"]
theorem isRegularLocalRing_henselianLocalRing_of_completion
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hXdec : IsDecentSpace B (Spec (.of A)) hA X)
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f)
    (y : points B (Spec (.of A)) hA (completionSpace A B hA hAc f))
    (hy : IsRegularLocalRing
      (henselianLocalRing B (Spec (.of A)) hA (completionSpace A B hA hAc f)
        (isAlgebraicSpace_completionSpace A B hA hAc f hX) y
        (isDecentSpace_completionSpace A B hA hAc f hX hXdec) : Type (u + 1))) :
    IsRegularLocalRing
      (henselianLocalRing B (Spec (.of A)) hA X hX
        (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
          (completionProjection A B hA hAc f) y) hXdec : Type (u + 1)) := by
  have hNX := hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_base
    A B hA f hX hf
  have hNY := hasEtaleLocalProperty_isLocallyNoetherian_completionSpace A B hA hAc f hX hf
  have hreg := (isRegularAt_iff_isRegularLocalRing_henselianLocalRing B (Spec (.of A)) hA
    (completionSpace A B hA hAc f) (isAlgebraicSpace_completionSpace A B hA hAc f hX)
    (isDecentSpace_completionSpace A B hA hAc f hX hXdec) hNY y).mpr hy
  exact (isRegularAt_iff_isRegularLocalRing_henselianLocalRing B (Spec (.of A)) hA X hX hXdec
    hNX _).mp (isRegularAt_completionSpace_descent A B hA hAc f hX hf y hreg)

/-! ### Regularity over the closed fibre -/

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- Regularity at a point of an algebraic space is regularity of the local ring of an étale
scheme chart at any point of the chart above it. -/
theorem isRegularAt_iff_isRegularLocalRing_chart
    {F : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (Spec (.of A)) hA F) (x : points B (Spec (.of A)) hA F)
    (V : BigFppfOver B (Spec (.of A)) hA) (b : yoneda.obj V ⟶ F)
    (hb : IsEtale B (Spec (.of A)) hA b) (w : points B (Spec (.of A)) hA (yoneda.obj V))
    (hw : pointsMap B (Spec (.of A)) hA (yoneda.obj V) b w = x) :
    IsRegularAt B (Spec (.of A)) hA F x ↔
      IsRegularLocalRing (((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V).presheaf.stalk
        (pointsToScheme B (Spec (.of A)) hA V w)) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep w
  have hpre := (isEtale_iff_presheaf_of_yoneda B (Spec (.of A)) hA b).1 hb
  exact ⟨fun h ↦ h V b hpre p hw,
    fun h ↦ (isRegularAt_iff_exists_etale_chart B (Spec (.of A)) hA F hF x).mpr
      ⟨V, b, hpre, p, hw, h⟩⟩

/-- Regularity at a point of the closed fibre is the same before and after base change to the
completion, read on a pair of corresponding étale scheme charts. -/
theorem isRegularAt_iff_of_chartData
    {Y : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hY : IsAlgebraicSpace B (Spec (.of A)) hA Y)
    (π : Y ⟶ X) (U P : BigFppfOver B (Spec (.of A)) hA)
    (a : yoneda.obj U ⟶ X) (ha : IsEtale B (Spec (.of A)) hA a)
    (c : yoneda.obj P ⟶ Y) (hc : IsEtale B (Spec (.of A)) hA c)
    (j : P ⟶ U)
    (gU : (BigFppfOver.toScheme B (Spec (.of A)) hA).obj U ⟶ Spec (.of A))
    (kP : (BigFppfOver.toScheme B (Spec (.of A)) hA).obj P ⟶
      Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
    [LocallyOfFiniteType gU]
    (hsq : IsPullback (yoneda.map j) c a π)
    (hsch : IsPullback ((BigFppfOver.toScheme B (Spec (.of A)) hA).map j) kP gU
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))))
    (y : points B (Spec (.of A)) hA Y)
    (z : points B (Spec (.of A)) hA (yoneda.obj P))
    (hzy : pointsMap B (Spec (.of A)) hA (yoneda.obj P) c z = y)
    (hclosed : kP.base (pointsToScheme B (Spec (.of A)) hA P z) =
      (⟨IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A),
        inferInstance⟩ :
        PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A))) :
    IsRegularAt B (Spec (.of A)) hA Y y ↔
      IsRegularAt B (Spec (.of A)) hA X (pointsMap B (Spec (.of A)) hA Y π y) := by
  have hY' := isRegularAt_iff_isRegularLocalRing_chart A B hA hY y P c hc z hzy
  have hxU : pointsMap B (Spec (.of A)) hA (yoneda.obj U) a
      (pointsMap B (Spec (.of A)) hA (yoneda.obj P) (yoneda.map j) z) =
      pointsMap B (Spec (.of A)) hA Y π y := by
    rw [← hzy, ← pointsMap_comp_apply, ← pointsMap_comp_apply, hsq.w]
  have hX' := isRegularAt_iff_isRegularLocalRing_chart A B hA hX _ U a ha
    (pointsMap B (Spec (.of A)) hA (yoneda.obj P) (yoneda.map j) z) hxU
  rw [pointsToScheme_pointsMap_yoneda] at hX'
  have key : IsRegularLocalRing
        (((BigFppfOver.toScheme B (Spec (.of A)) hA).obj P).presheaf.stalk
          (pointsToScheme B (Spec (.of A)) hA P z)) ↔
      IsRegularLocalRing
        (((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).presheaf.stalk
          (((BigFppfOver.toScheme B (Spec (.of A)) hA).map j).base
            (pointsToScheme B (Spec (.of A)) hA P z))) := by
    set kk := Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))) with hkk
    let e := hsch.isoPullback
    let w : (pullback gU kk : Scheme.{u}) :=
      e.hom.base (pointsToScheme B (Spec (.of A)) hA P z)
    have h1 : (pullback.fst gU kk).base w =
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).map j).base
          (pointsToScheme B (Spec (.of A)) hA P z) := by
      have h : e.hom ≫ pullback.fst gU kk =
          (BigFppfOver.toScheme B (Spec (.of A)) hA).map j := hsch.isoPullback_hom_fst
      rw [← h]; rfl
    have h2 : (pullback.snd gU kk).base w =
        (⟨IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A),
          inferInstance⟩ :
          PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
      have h : e.hom ≫ pullback.snd gU kk = kP := hsch.isoPullback_hom_snd
      rw [← hclosed, ← h]; rfl
    have hmain := isRegularLocalRing_stalk_pullback_completion_iff A
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) gU _ w h1 h2
    exact (isRegularLocalRing_stalk_iff_of_etale e.hom
      (pointsToScheme B (Spec (.of A)) hA P z)).trans hmain
  exact hY'.trans (key.trans hX'.symm)

end AlgebraicGeometry.Space

end
