module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliCurves

/-!
# The moduli stack of stable curves of genus `g` (Stacks 0E77)

Stacks 0E77 names `𝓜̄_g`, for `g ≥ 2`, the *moduli stack of stable curves of genus `g`*: the
substack of the stack of curves of Stacks 0E78, the summand of genus `g` of the decomposition
`𝓜̄ = ∐_{g ≥ 2} 𝓜̄_g` of the moduli stack `𝓜̄ = Curves^{stable}` of stable curves
(`AlgebraicGeometry.moduliStableCurves`). Its points are, by part (2) of Stacks 0E78, the stable
curves of genus `g` over fields.

## Main definitions

* `AlgebraicGeometry.CurveFamily.HasFieldPointFibreGenus`: the fibre of a family of curves over
  every field-valued point of the base has genus `g`.
* `AlgebraicGeometry.IsStableCurveFamilyOfFibreGenus`: stable, with every fibre of genus `g`.
* `AlgebraicGeometry.moduliStableCurvesOfGenus`: the stack `𝓜̄_g` of Stacks 0E77, with inclusion
  `AlgebraicGeometry.moduliStableCurvesOfGenusInclusion` into `Curves`.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isPullback_of_hom`: a presentation of a fibre of a family
  of curves is a presentation of the corresponding fibre of every family mapping to it.
* `AlgebraicGeometry.CurveFamily.hasFieldPointFibreGenus_of_hom`: the genus of the fibres passes to
  base changes, so `𝓜̄_g` is a category fibred in groupoids.

## Implementation notes

`𝓜̄_g` is the open substack of `Curves` whose points are the stable curves of genus `g`. An open
substack of `Curves` is determined by its points: the classifying morphism of a family factors
through it exactly when every point of the base does (condition (o) of Stacks 0E0E). So `𝓜̄_g` is
the strictly full subcategory of the families of curves which are stable (Stacks 0E75) and whose
fibre over every point of the base has genus `g`, the genus of a curve over a field `k` being
`dim_k H¹(X, 𝒪_X)` (`AlgebraicGeometry.genus`, Stacks 0BY7). The fibres are presented by schemes
of the site exactly as in `AlgebraicGeometry.IsStableCurveFamily`.

Stacks 0E78 also characterizes `𝓜̄_g` by its families: a stable family `f : X → S` lies in `𝓜̄_g`
exactly when `R¹f_*𝒪_X` is a locally free `𝒪_S`-module of rank `g`
(`AlgebraicGeometry.IsStableCurveFamilyOfGenus`). That characterization is part (1) of
Stacks 0E78, a consequence of cohomology and base change for families of curves (Stacks 0E6V,
0E6F), and is not used to define the stack: the definition by fibres is visibly stable under
base change, which the subcategory needs in order to be fibred in groupoids.

The source names `𝓜̄_g` only for `g ≥ 2`. The definition is made for every `g`; for `g < 2` it is
the empty substack, a stable curve having genus at least two.

## References

* [Stacks Project, Tag 0E77](https://stacks.math.columbia.edu/tag/0E77)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

namespace CurveFamily

/-- A family of curves `f : X ⟶ S` *has fibres of genus `g`* when, for every point of the base,
its fibre there has genus `g`: the fibre over a field-valued point `p` is presented by a scheme
`V` of the site, the `CategoryTheory.IsPullback` clause exhibiting `V` as the fibre product of the
family with `p`, and `AlgebraicGeometry.genus` of `V` over the field of `p` is `g`. -/
abbrev HasFieldPointFibreGenus (X : CurveFamily B hZ) (g : ℕ) : Prop :=
  ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
    ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
      (q : yoneda.obj V ⟶ X.total.obj),
      IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value) ∧
        genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g

variable {B hZ}

/-- A presentation of a fibre of a family of curves is a presentation of the corresponding fibre of
every family of curves mapping to it: the square of a morphism of families is cartesian. -/
theorem exists_isPullback_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ Y.total.obj)
    (hq : IsPullback q (yoneda.map v) Y.toBase.hom
      (yonedaEquiv.symm (Space.FieldValuedPoint.map B integerBase hZ _
        (schemeSpaceMap φ.baseMap).hom p).value)) :
    ∃ q' : yoneda.obj V ⟶ X.total.obj,
      IsPullback q' (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value) := by
  have hsq := AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian
  have hval : yonedaEquiv.symm (Space.FieldValuedPoint.map B integerBase hZ _
      (schemeSpaceMap φ.baseMap).hom p).value =
        yonedaEquiv.symm p.value ≫ (schemeSpaceMap φ.baseMap).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  replace hq : IsPullback q (yoneda.map v) Y.toBase.hom
      (yonedaEquiv.symm p.value ≫ (schemeSpaceMap φ.baseMap).hom) := by
    convert hq using 1
    exact hval.symm
  have hw : q ≫ Y.toBase.hom = (yoneda.map v ≫ yonedaEquiv.symm p.value) ≫
      (schemeSpaceMap φ.baseMap).hom := by
    rw [Category.assoc]
    exact hq.w
  refine ⟨hsq.lift q (yoneda.map v ≫ yonedaEquiv.symm p.value) hw,
    IsPullback.of_right ?_ (hsq.lift_snd _ _ _) hsq⟩
  rw [hsq.lift_fst]
  exact hq

/-- **The genus of the fibres passes to base changes**: a family of curves mapping to a family
whose fibres have genus `g` has fibres of genus `g`, each of its fibres being a fibre of the
target. -/
theorem hasFieldPointFibreGenus_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y) {g : ℕ}
    (hY : HasFieldPointFibreGenus B hZ Y g) : HasFieldPointFibreGenus B hZ X g := by
  intro p
  obtain ⟨V, v, q, hq, hgen⟩ := hY (Space.FieldValuedPoint.map B integerBase hZ _
    (schemeSpaceMap φ.baseMap).hom p)
  obtain ⟨q', hq'⟩ := exists_isPullback_of_hom φ p v q hq
  exact ⟨V, v, q', hq', hgen⟩

end CurveFamily

/-- A family of curves is *stable with fibres of genus `g`* when it is stable (Stacks 0E75) and
its fibre over every point of the base has genus `g`. -/
abbrev IsStableCurveFamilyOfFibreGenus (g : ℕ) (X : CurveFamily B hZ) : Prop :=
  IsStableCurveFamily B hZ X ∧ CurveFamily.HasFieldPointFibreGenus B hZ X g

/-- A family of curves mapping to a stable family with fibres of genus `g` is stable with fibres of
genus `g`. -/
theorem CurveFamily.isStableCurveFamilyOfFibreGenus_of_hom {g : ℕ} {X Y : CurveFamily B hZ}
    (φ : X ⟶ Y) (hY : IsStableCurveFamilyOfFibreGenus B hZ g Y) :
    IsStableCurveFamilyOfFibreGenus B hZ g X :=
  ⟨isStableCurveFamily_of_hom φ hY.1, hasFieldPointFibreGenus_of_hom φ hY.2⟩

/-- **Stacks 0E77, `𝓜̄_g`.** The moduli stack `𝓜̄_g` of stable curves of genus `g`: the substack of
the stack of curves of the families `f : X → S` which are stable (Stacks 0E75) and whose fibre
over every point of `S` has genus `g`, as a category fibred in groupoids over the big fppf site of
`Spec(ℤ)`. It lies in `𝓜̄ = AlgebraicGeometry.moduliStableCurves`, and its points are the stable
curves of genus `g` over fields, as in part (2) of Stacks 0E78. -/
@[stacks 0E77 "the moduli stack of stable curves of genus g, 𝓜̄_g"]
def moduliStableCurvesOfGenus (g : ℕ) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesSubstack B hZ (IsStableCurveFamilyOfFibreGenus B hZ g)
    (CurveFamily.isStableCurveFamilyOfFibreGenus_of_hom B hZ)

/-- The inclusion `𝓜̄_g ⟶ Curves`. -/
def moduliStableCurvesOfGenusInclusion (g : ℕ) :
    moduliStableCurvesOfGenus B hZ g ⟶ curvesFiberedCategory B hZ :=
  curvesSubstackInclusion B hZ (IsStableCurveFamilyOfFibreGenus B hZ g)
    (CurveFamily.isStableCurveFamilyOfFibreGenus_of_hom B hZ)

end AlgebraicGeometry

end
