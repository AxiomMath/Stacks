module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationTransitions
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFppfDescent

/-!
# Condition (2) of Stacks 0E8A for a glued stabilization

Let `X ⟶ S` be a family of curves, `{φᵢ : Wᵢ ⟶ S}` an fppf covering by schemes of the site, and
`cᵢ : X ×_S Wᵢ ⟶ Yᵢ` morphisms over `Wᵢ` to families of curves, glued to `c : X ⟶ Q` over `S` with
`Yᵢ = Q ×_S Wᵢ`. Suppose every field-valued point of `S` lifts, over the same field, to some `Wᵢ`;
this holds for the covering by elementary étale neighbourhoods `(Uₛ, uₛ)` of the points `s` of `S`
used in the proof of Stacks 0E8A, a point `Spec k ⟶ S` with image `s` factoring through
`Spec κ(s) = Spec κ(uₛ) ⟶ Uₛ`. Then condition (2) of Stacks 0E8A for the `cᵢ` gives it for `c`:
presentations of the fibres of `X` and `Q` over a field-valued point of `S` are presentations of
the fibres of `X ×_S Wᵢ` and `Yᵢ` over its lift.

## Main results

* `AlgebraicGeometry.CurveFamily.hasStableContractionFibres_ofIsFppfCovering`: condition (2) of
  Stacks 0E8A for the glued contraction.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A pullback square over `e ≫ h` refines to one over `e` along a second pullback square. -/
private theorem exists_isPullback_of_isPullback_comp {C : Type*} [Category C] {P A D E T V : C}
    {p : P ⟶ A} {f : P ⟶ D} {g : A ⟶ E} {h : D ⟶ E} {e : V ⟶ D} {q : T ⟶ A} {v : T ⟶ V}
    (hp : IsPullback p f g h) (hq : IsPullback q v g (e ≫ h)) :
    ∃ q' : T ⟶ P, q' ≫ p = q ∧ q' ≫ f = v ≫ e ∧ IsPullback q' v f e := by
  have w : q ≫ g = (v ≫ e) ≫ h := by rw [Category.assoc]; exact hq.w
  have h₁ : hp.lift q (v ≫ e) w ≫ p = q := hp.lift_fst _ _ _
  have h₂ : hp.lift q (v ≫ e) w ≫ f = v ≫ e := hp.lift_snd _ _ _
  exact ⟨_, h₁, h₂, IsPullback.of_right (by rw [h₁]; exact hq) h₂ hp⟩

/-- **Condition (2) of Stacks 0E8A for a glued contraction.** If every field-valued point of the
base lifts, over the same field, to a member of the covering, condition (2) for the local
contractions `cᵢ` gives condition (2) for the glued contraction `c : X ⟶ Q`. -/
theorem hasStableContractionFibres_ofIsFppfCovering {X : CurveFamily B hZ}
    {Q : AlgebraicSpaces B integerBase hZ} (q : Q ⟶ schemeSpace X.base) {ι : Type v}
    {W : ι → BigFppfOver B integerBase hZ} (φ : ∀ i, W i ⟶ X.base)
    (hcov : Space.IsFppfCovering B integerBase hZ (fun i => (schemeSpace (W i)).obj)
      (fun i => (schemeSpaceMap (φ i)).hom))
    (hlift : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
      ∃ i, ∃ p' : Space.FieldValuedPoint B integerBase hZ (schemeSpace (W i)).obj,
        Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap (φ i)).hom p' = p)
    {Y : ι → CurveFamily B hZ} (hY : ∀ i, (Y i).base = W i) (r : ∀ i, (Y i).total ⟶ Q)
    (hsq : ∀ i, IsPullback (r i) ((Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i))) q
      (schemeSpaceMap (φ i)))
    (c : ∀ i, AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ i)) ⟶
      (Y i).total)
    (hc : ∀ i, c i ≫ (Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i)) =
      ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap (φ i)).hom))
    (h2 : ∀ i, (X.baseChangeAlong (φ i)).HasStableContractionFibres B hZ (Y i) (hY i) (c i))
    (cQ : X.total ⟶ Q)
    (hcQ : ∀ i, (ObjectProperty.homMk (pullback.fst X.toBase.hom (schemeSpaceMap (φ i)).hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ i)) ⟶
        X.total) ≫ cQ = c i ≫ r i) :
    X.HasStableContractionFibres B hZ (ofIsFppfCovering q φ hcov hY r hsq) rfl cQ := by
  intro p VX VY vX vY qX qY a hqX hqY ha hqa
  obtain ⟨i, p', rfl⟩ := hlift p
  have hval : yonedaEquiv.symm (Space.FieldValuedPoint.map B integerBase hZ _
      (schemeSpaceMap (φ i)).hom p').value =
        yonedaEquiv.symm p'.value ≫ (schemeSpaceMap (φ i)).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  rw [hval] at hqX
  have hqY' : IsPullback qY (yoneda.map vY) q.hom
      (yonedaEquiv.symm p'.value ≫ (schemeSpaceMap (φ i)).hom) := by
    rw [hval] at hqY
    have e : ((ofIsFppfCovering q φ hcov hY r hsq).toBase ≫
        eqToHom (congrArg schemeSpace (rfl : (ofIsFppfCovering q φ hcov hY r hsq).base =
          X.base))).hom = q.hom :=
      congrArg (fun m => m.hom) (Category.comp_id q)
    rw [e] at hqY
    exact hqY
  -- the presentations of the fibres over the lift
  let pXi : AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ i)) ⟶
    X.total := ObjectProperty.homMk (pullback.fst X.toBase.hom (schemeSpaceMap (φ i)).hom)
  let fXi : AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ i)) ⟶
    schemeSpace (W i) := ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap (φ i)).hom)
  have hpX : IsPullback pXi.hom fXi.hom X.toBase.hom (schemeSpaceMap (φ i)).hom :=
    AlgebraicSpaces.isPullback_hom B integerBase hZ
      (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ i)))
  have hpY := AlgebraicSpaces.isPullback_hom B integerBase hZ (hsq i)
  obtain ⟨qX', hqX₁, hqX₂, sqX⟩ := exists_isPullback_of_isPullback_comp hpX hqX
  obtain ⟨qY', hqY₁, hqY₂, sqY⟩ := exists_isPullback_of_isPullback_comp hpY hqY'
  have hcQ' : pXi.hom ≫ cQ.hom = (c i).hom ≫ (r i).hom := congrArg (fun m => m.hom) (hcQ i)
  have hc' : (c i).hom ≫ ((Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i))).hom =
      fXi.hom := congrArg (fun m => m.hom) (hc i)
  refine h2 i p' VX VY vX vY qX' qY' a sqX sqY ha ?_
  change qX' ≫ (c i).hom = yoneda.map a ≫ qY'
  apply hpY.hom_ext
  · rw [Category.assoc, Category.assoc, ← hcQ', ← Category.assoc, hqX₁, hqY₁, hqa]
  · rw [Category.assoc, Category.assoc, hc', hqX₂, hqY₂, ← Category.assoc, ← yoneda.map_comp,
      ha]
    rfl

end CurveFamily

end AlgebraicGeometry

end
