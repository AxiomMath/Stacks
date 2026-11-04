module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenus

/-!
# The moduli stack of smooth proper curves of genus `g` (Stacks 0E82)

Stacks 0E82 names `𝓜_g`, for `g ≥ 0`, the *moduli stack of smooth proper curves of genus `g`*:
the substack of the stack of curves of Stacks 0E83, the summand of genus `g` of the decomposition
`𝓜 = ∐_{g ≥ 0} 𝓜_g` of the moduli stack `𝓜 = Curves^{smooth, h0}` of smooth proper curves
(`AlgebraicGeometry.moduliSmoothCurves`). Its points are, by part (2) of Stacks 0E83, the smooth
proper curves `X` over fields `k` with `k = H⁰(X, 𝒪_X)` and of genus `g`.

## Main definitions

* `AlgebraicGeometry.IsSmoothH0FamilyOfFibreGenus`: a family of curves in `𝓜` all of whose
  fibres have genus `g`.
* `AlgebraicGeometry.moduliSmoothCurvesOfGenus`: the stack `𝓜_g` of Stacks 0E82, with inclusion
  `AlgebraicGeometry.moduliSmoothCurvesOfGenusInclusion` into `Curves`.

## Main results

* `AlgebraicGeometry.CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom`: the defining condition of
  `𝓜_g` passes to base changes.

## Implementation notes

`𝓜_g` is the open substack of `Curves` whose points are the smooth proper curves of genus `g` with
`H⁰(X, 𝒪_X) = k`. An open substack of `Curves` is determined by its points: the classifying
morphism of a family factors through it exactly when every point of the base does (condition (o)
of Stacks 0E0E). So `𝓜_g` is the strictly full subcategory of the families of curves which lie in
`𝓜` (smooth of relative dimension one with `f_*𝒪_X = 𝒪_S` universally) and whose fibre over every
point of the base has genus `g`, the genus of a curve over a field `k` with `H⁰(X, 𝒪_X) = k` being
`dim_k H¹(X, 𝒪_X)` (`AlgebraicGeometry.genus`, Stacks 0BY7); the fibres are presented as in
`AlgebraicGeometry.CurveFamily.HasFieldPointFibreGenus`.

Stacks 0E83 also characterizes `𝓜_g` by its families: a family in `𝓜` lies in `𝓜_g` exactly when
`R¹f_*𝒪_X` is a locally free `𝒪_S`-module of rank `g` (`AlgebraicGeometry.CurveFamily.HasGenus`).
That characterization is part (1) of Stacks 0E83, a consequence of cohomology and base change
(Stacks 0E1J).

## References

* [Stacks Project, Tag 0E82](https://stacks.math.columbia.edu/tag/0E82)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- A family of curves `f : X → S` is *smooth proper with fibres of genus `g`* when it lies in
`𝓜 = Curves^{smooth, h0}` (it is smooth of relative dimension one with `f_*𝒪_X = 𝒪_S`,
universally) and its fibre over every point of `S` has genus `g`. -/
abbrev IsSmoothH0FamilyOfFibreGenus (g : ℕ) (X : CurveFamily B hZ) : Prop :=
  IsSmoothH0Family B hZ X ∧ CurveFamily.HasFieldPointFibreGenus B hZ X g

variable {B hZ}

/-- A family of curves mapping to a family in `𝓜` with fibres of genus `g` is in `𝓜` with fibres
of genus `g`. -/
theorem CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom {g : ℕ} {X Y : CurveFamily B hZ}
    (φ : X ⟶ Y) (hY : IsSmoothH0FamilyOfFibreGenus B hZ g Y) :
    IsSmoothH0FamilyOfFibreGenus B hZ g X :=
  ⟨isSmoothH0Family_of_hom B hZ φ hY.1, hasFieldPointFibreGenus_of_hom φ hY.2⟩

variable (B hZ)

/-- The moduli stack `𝓜_g` of smooth proper curves of genus `g`: the substack of the stack of
curves of the families `f : X → S` which are smooth of relative dimension one with
`f_*𝒪_X = 𝒪_S`, universally, and whose fibre over every point of `S` has genus `g`, as a category
fibred in groupoids over the big fppf site of `Spec(ℤ)`. It lies in
`𝓜 = AlgebraicGeometry.moduliSmoothCurves`, and its points are the smooth proper curves of genus
`g` over fields, as in part (2) of Stacks 0E83. -/
@[stacks 0E82 "the moduli stack of smooth proper curves of genus g, 𝓜_g"]
def moduliSmoothCurvesOfGenus (g : ℕ) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesSubstack B hZ (IsSmoothH0FamilyOfFibreGenus B hZ g)
    (CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom)

/-- The inclusion `𝓜_g ⟶ Curves`. -/
def moduliSmoothCurvesOfGenusInclusion (g : ℕ) :
    moduliSmoothCurvesOfGenus B hZ g ⟶ curvesFiberedCategory B hZ :=
  curvesSubstackInclusion B hZ (IsSmoothH0FamilyOfFibreGenus B hZ g)
    (CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom)

end AlgebraicGeometry

end
