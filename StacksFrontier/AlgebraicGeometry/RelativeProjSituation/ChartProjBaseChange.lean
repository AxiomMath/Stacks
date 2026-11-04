module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ChartHypothesisBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chart square of a relative-`Proj` base change along a morphism of base schemes

For a morphism `g : S' ⟶ S` of base schemes, an identification `Φ` of the graded algebra of `s'`
with the pullback of that of `s`, and a pair of affine opens `W' ⊆ g⁻¹W`, the square

```
Proj 𝒜'(W')  ⟶  W'
    |             |
    v             v
Proj 𝒜(W)   ⟶   W
```

is cartesian: the chart of `relativeProj s'` over `W'` is the base change of the chart of
`relativeProj s` over `W` along the restriction `W' ⟶ W` of `g`.

It is pasted from three cartesian squares: the `Proj` square over the degree-zero spectra, the
degree-zero square, and the square of affine identifications.

## Main results

* `Stacks.RelativeProj.isoSpec_inv_resLE`: for affine opens `W' ⊆ g⁻¹W`, the restriction
  `W' ⟶ W` of `g` is `Spec` of `AlgebraicGeometry.Scheme.Hom.appLE` read through the affine
  identifications.
* `Stacks.RelativeProj.Situation.isPullback_toSpecZero_gradedBaseChange`: `Proj 𝒜'(W')` is the
  base change of `Proj 𝒜(W)` along `Spec 𝒜'₀(W') ⟶ Spec 𝒜₀(W)`, [Stacks, Tag 01N2] for the base
  change of graded section rings along a morphism of base schemes.
* `Stacks.RelativeProj.Situation.isPullback_projInclusionToOpen_gradedBaseChange`: the chart
  square: `Proj 𝒜'(W')` is the base change of `Proj 𝒜(W)` along `W' ⟶ W`.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal

universe u

namespace Stacks.RelativeProj

/-- **The restriction of a morphism to affine opens is `Spec` of `appLE`.** For affine opens
`W' ⊆ g⁻¹W`, the morphism `g.resLE W W' : W' ⟶ W` agrees with
`Spec (g.appLE W W') : Spec Γ(S', W') ⟶ Spec Γ(S, W)` under the affine identifications. -/
public theorem isoSpec_inv_resLE {X Y : Scheme.{u}} (g : Y ⟶ X) {W : X.Opens} {W' : Y.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W) :
    hW'.isoSpec.inv ≫ g.resLE W W' h = Spec.map (g.appLE W W' h) ≫ hW.isoSpec.inv := by
  rw [← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι,
    ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.isoSpec_inv_ι,
    IsAffineOpen.SpecMap_appLE_fromSpec g hW hW' h]

namespace Situation

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)

/-- **`Proj 𝒜'(W')` is the base change of `Proj 𝒜(W)` along `Spec 𝒜'₀(W') ⟶ Spec 𝒜₀(W)`.** This
is [Stacks, Tag 01N2] for the graded base change
`Stacks.RelativeProj.Situation.gradedBaseChange`. -/
public theorem isPullback_toSpecZero_gradedBaseChange (W : s.base.affineOpens)
    (W' : s'.base.affineOpens) (h : W'.1 ≤ g ⁻¹ᵁ W.1)
    (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ))) :
    IsPullback (AlgebraicGeometry.Proj.toSpecZero (s'.chartGrading W'))
      (AlgebraicGeometry.Proj.map (gradedBaseChange g Φ W.1 W'.1 h)
        (irrelevant_le_gradedBaseChange g Φ W W' h hΦ))
      (Spec.map (CommRingCat.ofHom (gradedBaseChange g Φ W.1 W'.1 h).gradedZeroRingHom))
      (AlgebraicGeometry.Proj.toSpecZero (s.chartGrading W)) :=
  AlgebraicGeometry.Proj.isPullback_toSpecZero_map
    (irrelevant_le_gradedBaseChange g Φ W W' h hΦ)
    (isBaseChangeOnCharts_gradedBaseChange g Φ (isAffineOpen W) (isAffineOpen W') h hΦ)

/-- **The chart square of a relative-`Proj` base change.** For affine opens `W ⊆ S` and
`W' ⊆ g⁻¹W ⊆ S'`, the chart `Proj 𝒜'(W') ⟶ W'` is the base change of the chart
`Proj 𝒜(W) ⟶ W` along the restriction `W' ⟶ W` of `g`. -/
@[ega "II 3.1.1" "more general"]
public theorem isPullback_projInclusionToOpen_gradedBaseChange (W : s.base.affineOpens)
    (W' : s'.base.affineOpens) (h : W'.1 ≤ g ⁻¹ᵁ W.1)
    (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ))) :
    IsPullback
      (AlgebraicGeometry.Proj.map (gradedBaseChange g Φ W.1 W'.1 h)
        (irrelevant_le_gradedBaseChange g Φ W W' h hΦ))
      (projInclusionToOpen s' W'.1 W'.2) (projInclusionToOpen s W.1 W.2)
      (g.resLE W.1 W'.1 h) := by
  have sq1 := (isPullback_toSpecZero_gradedBaseChange g Φ W W' h hΦ).flip
  have sq2 := (isPullback_specMap_baseHom_baseChange g Φ W.1 W'.1 (isAffineOpen W)
    (isAffineOpen W') h (hΦ 0)).flip
  have sq3 : IsPullback (Spec.map (g.appLE W.1 W'.1 h)) (isAffineOpen W').isoSpec.inv
      (isAffineOpen W).isoSpec.inv (g.resLE W.1 W'.1 h) :=
    IsPullback.of_vert_isIso
      ⟨(isoSpec_inv_resLE g (isAffineOpen W) (isAffineOpen W') h).symm⟩
  have key := (sq1.paste_vert sq2).paste_vert sq3
  rwa [Category.assoc, Category.assoc] at key

end Situation

end Stacks.RelativeProj

end
