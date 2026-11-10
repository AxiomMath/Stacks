module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilization
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01

/-!
# Base change of the conditions of Stacks 0E8A

Let `X ⟶ S` be a family of curves and `t : T ⟶ S` a morphism of schemes of the site. Any cartesian
square exhibiting an algebraic space `X'` as `X ×_S T` makes `X' ⟶ T` a family of curves: flatness,
properness and finite presentation are stable under base change (Stacks 03MO, 04WP, 03XR) and so is
the bound on the relative dimension (Stacks 0D4N); this is
`AlgebraicGeometry.CurveFamily.ofIsPullback`. This file shows that the conditions entering
Stacks 0E8A (prestability, stability, the genus of the fibres, and conditions (1) and (2) for a
morphism `c : X ⟶ Y` of families over `S`) pass to base changes.

This is the base change used to compare two stabilizations over the overlaps of an étale covering
of the base in the proof of Stacks 0E8A.

For the second family `Y`,
whose base is identified with that of `X` through `hb : Y.base = X.base`, it is taken along the
composite `T ⟶ X.base = Y.base`.

## Main results

* `AlgebraicGeometry.CurveFamily.isUniversalStructureContraction_ofIsPullback`: condition (1) of
  Stacks 0E8A passes to base changes.
* `AlgebraicGeometry.CurveFamily.hasStableContractionFibres_ofIsPullback`: condition (2) of
  Stacks 0E8A passes to base changes.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0D51](https://stacks.math.columbia.edu/tag/0D51)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A cartesian square over a morphism into a transported base is a cartesian square over the
composite morphism into the base itself. -/
theorem isPullback_toBase_of_isPullback_toBase_comp_eqToHom (Y : CurveFamily B hZ)
    {Q T : BigFppfOver B integerBase hZ} (hb : Y.base = Q) (t : T ⟶ Q)
    {Y' : AlgebraicSpaces B integerBase hZ} {p : Y' ⟶ Y.total} {f : Y' ⟶ schemeSpace T}
    (h : IsPullback p f (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) (schemeSpaceMap t)) :
    IsPullback p f Y.toBase (schemeSpaceMap (t ≫ eqToHom hb.symm)) := by
  subst hb
  simpa only [eqToHom_refl, Category.comp_id] using h

section BaseChange

variable {X Y : CurveFamily B hZ} {hb : Y.base = X.base} {c : X.total ⟶ Y.total}
  {T : BigFppfOver B integerBase hZ} (t : T ⟶ X.base) {X' Y' : AlgebraicSpaces B integerBase hZ}
  {pX : X' ⟶ X.total} {fX : X' ⟶ schemeSpace T} {pY : Y' ⟶ Y.total} {fY : Y' ⟶ schemeSpace T}
  (sqX : IsPullback pX fX X.toBase (schemeSpaceMap t))
  (sqY : IsPullback pY fY (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) (schemeSpaceMap t))
  {c' : X' ⟶ Y'} (hc₁ : c' ≫ pY = pX ≫ c)

include sqX sqY hc₁ in
/-- **Condition (1) of Stacks 0E8A passes to base changes.** If `c : X ⟶ Y` over `S` satisfies
`𝒪 = c_*𝒪` and `R¹c_*𝒪 = 0` after every base change, so does its base change `c' : X_T ⟶ Y_T`
along any `T ⟶ S`, every base change of `c'` being a base change of `c`. -/
theorem isUniversalStructureContraction_ofIsPullback
    (h : X.IsUniversalStructureContraction B hZ Y hb c) :
    (X.ofIsPullback B hZ t pX fX sqX).IsUniversalStructureContraction B hZ
      (Y.ofIsPullback B hZ (t ≫ eqToHom hb.symm) pY fY
        (Y.isPullback_toBase_of_isPullback_toBase_comp_eqToHom hb t sqY)) rfl c' := by
  dsimp only [IsUniversalStructureContraction, ofIsPullback]
  intro T' h' X'' Y'' pX'' fX'' pY'' fY'' c'' sq₁ sq₂ e₁ e₂
  have sqX' : IsPullback pX fX X.toBase (schemeSpaceMap t) := sqX
  have sq₂' : IsPullback pY'' fY'' fY (schemeSpaceMap h') := by
    simpa using sq₂
  have hX := sq₁.paste_horiz sqX'
  have hY := sq₂'.paste_horiz sqY
  rw [← schemeSpaceMap_comp] at hX hY
  refine h T' (h' ≫ t) X'' Y'' (pX'' ≫ pX) fX'' (pY'' ≫ pY) fY'' c'' hX hY ?_ e₂
  rw [← Category.assoc, e₁, Category.assoc, hc₁, Category.assoc]

include sqX sqY hc₁ in
/-- **Condition (2) of Stacks 0E8A passes to base changes.** A field-valued point of `T` is,
through `t`, a field-valued point of `S`, and presentations of the fibres of `X_T` and `Y_T` there
are presentations of the fibres of `X` and `Y`. -/
theorem hasStableContractionFibres_ofIsPullback
    (h : X.HasStableContractionFibres B hZ Y hb c) :
    (X.ofIsPullback B hZ t pX fX sqX).HasStableContractionFibres B hZ
      (Y.ofIsPullback B hZ (t ≫ eqToHom hb.symm) pY fY
        (Y.isPullback_toBase_of_isPullback_toBase_comp_eqToHom hb t sqY)) rfl c' := by
  dsimp only [HasStableContractionFibres, ofIsPullback]
  intro p VX VY vX vY qX qY a hqX hqY ha hqa
  have hval : yonedaEquiv.symm (Space.FieldValuedPoint.map B integerBase hZ _
      (schemeSpaceMap t).hom p).value =
        yonedaEquiv.symm p.value ≫ (schemeSpaceMap t).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  have sqX' : IsPullback pX fX X.toBase (schemeSpaceMap t) := sqX
  have hsX := AlgebraicSpaces.isPullback_hom B integerBase hZ sqX'
  have hsY := AlgebraicSpaces.isPullback_hom B integerBase hZ sqY
  have hqY' : IsPullback qY (yoneda.map vY) fY.hom (yonedaEquiv.symm p.value) := by
    simpa using hqY
  refine h (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap t).hom p) VX VY vX vY
    (qX ≫ pX.hom) (qY ≫ pY.hom) a ?_ ?_ ha ?_
  · rw [hval]
    exact hqX.paste_horiz hsX
  · rw [hval]
    exact hqY'.paste_horiz hsY
  · have h₁ : c'.hom ≫ pY.hom = pX.hom ≫ c.hom := congrArg (fun m => m.hom) hc₁
    rw [Category.assoc, ← h₁, reassoc_of% hqa]

end BaseChange

end CurveFamily

end AlgebraicGeometry

end
