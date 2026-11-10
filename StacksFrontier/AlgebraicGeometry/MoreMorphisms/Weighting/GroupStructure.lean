module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.FibreIntegral
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import StacksCore.Tactic.StacksAttribute

/-!
# Weightings of a morphism form a subgroup of the integer-valued functions on its source

The weightings of a fixed morphism of schemes `f : X ⟶ Y` are closed under addition, negation
and subtraction, contain the zero function, and are closed under multiplication by a fixed
integer. In other words they form a subgroup, indeed a sub-`ℤ`-module, of `X → ℤ`.

## Main results

* `AlgebraicGeometry.isWeighting_zero` — the zero function is a weighting of every morphism.
* `AlgebraicGeometry.IsWeighting.add` — the sum of two weightings is a weighting.
* `AlgebraicGeometry.IsWeighting.neg` — the negative of a weighting is a weighting.
* `AlgebraicGeometry.IsWeighting.sub` — the difference of two weightings is a weighting.
* `AlgebraicGeometry.IsWeighting.const_mul` — an integer multiple of a weighting is a weighting.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_zero` — the weighted fibre sum of the zero
  weight vanishes identically.
* `AlgebraicGeometry.etale_of_openImmersion_pullback_lift` and
  `AlgebraicGeometry.locallyQuasiFinite_of_isWeighting_data` — the two morphisms occurring in the
  chart data that defines a weighting inherit étaleness, resp. local quasi-finiteness, from the
  data.

## Implementation notes

The defining condition of `AlgebraicGeometry.IsWeighting` is a statement about the weighted fibre
sum `AlgebraicGeometry.separableDegreeWeightedFiberSum π (w ∘ h)` of a chart
`h : U ⟶ X`, `π : U ⟶ V`, `g : V ⟶ Y` with `g` étale, `π` finite and the induced morphism
`U ⟶ X ×_Y V` an open immersion. All five closure statements are proved by rewriting that fibre
sum and applying the corresponding closure property of `IsLocallyConstant`.

Scaling and negation need no finiteness input, because
`AlgebraicGeometry.separableDegreeWeightedFiberSum_const_mul` holds for an arbitrary morphism:
scaling commutes with an unconditional `finsum`. Additivity does need the terms to have finite
support, but that comes for free from the chart data: `IsFinite π` gives both
`LocallyQuasiFinite π` and `QuasiCompact π`, hence finite fibres by
`AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`. Consequently none of the five results
below assumes anything about `f` itself — in particular `IsWeighting.add` needs no
`LocallyQuasiFinite f`, which would otherwise be the natural hypothesis to impose.

The two helper lemmas record the étaleness of the chart morphism `h` and the local
quasi-finiteness of `π` directly from the shape of the chart data: the open immersion
`U ⟶ X ×_Y V` composed with `pullback.fst f g` is `h`, and composed with `pullback.snd f g` is
`π`, and the two projections are base changes of `g` resp. `f`. The second helper deduces
`LocallyQuasiFinite π` from `LocallyQuasiFinite f` without using `IsFinite π`, so it also applies
to chart data in which the finiteness of `π` is not yet known.

## References

* [Stacks Project, Tag 0F3A](https://stacks.math.columbia.edu/tag/0F3A)
* [Stacks Project, Tag 0GK8](https://stacks.math.columbia.edu/tag/0GK8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- In the chart data defining a weighting, the morphism `h : U ⟶ X` is étale: it factors as the
open immersion `U ⟶ X ×_Y V` followed by the first projection, which is a base change of the
étale morphism `g`. -/
theorem etale_of_openImmersion_pullback_lift {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    (h : U ⟶ X) (π : U ⟶ V) (g : V ⟶ Y) (comm : h ≫ f = π ≫ g)
    (hg : Etale g) (hU : IsOpenImmersion (pullback.lift h π comm)) :
    Etale h := by
  have := hg
  have := hU
  have hfac : h = pullback.lift h π comm ≫ pullback.fst f g :=
    (pullback.lift_fst h π comm).symm
  rw [hfac]
  infer_instance

/-- In the chart data defining a weighting of a locally quasi-finite morphism, the morphism
`π : U ⟶ V` is locally quasi-finite: it factors as the open immersion `U ⟶ X ×_Y V` followed by
the second projection, which is a base change of `f`. -/
theorem locallyQuasiFinite_of_isWeighting_data {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    [LocallyQuasiFinite f] (h : U ⟶ X) (π : U ⟶ V) (g : V ⟶ Y) (comm : h ≫ f = π ≫ g)
    (hU : IsOpenImmersion (pullback.lift h π comm)) :
    LocallyQuasiFinite π := by
  have := hU
  have hfac : π = pullback.lift h π comm ≫ pullback.snd f g :=
    (pullback.lift_snd h π comm).symm
  rw [hfac]
  infer_instance

/-- The separable-degree weighted fibre sum of the zero weight is identically zero. -/
theorem separableDegreeWeightedFiberSum_zero {U V : Scheme.{u}} (π : U ⟶ V) :
    separableDegreeWeightedFiberSum π 0 = 0 := by
  funext v
  simp [separableDegreeWeightedFiberSum]

/-- The zero function is a weighting of every morphism of schemes: all of its weighted fibre
sums vanish, hence are locally constant. -/
theorem isWeighting_zero {X Y : Scheme.{u}} (f : X ⟶ Y) : IsWeighting f 0 := by
  intro U V h π g comm _ _ _
  have hzero : separableDegreeWeightedFiberSum π ((0 : X → ℤ) ∘ h) = 0 :=
    separableDegreeWeightedFiberSum_zero π
  rw [hzero]
  exact IsLocallyConstant.zero

/-- The sum of two weightings of a morphism is a weighting: on every chart the weighted fibre sum
of the sum is the sum of the weighted fibre sums, the chart's finiteness making the two fibre
sums genuinely finite. -/
theorem IsWeighting.add {X Y : Scheme.{u}} {f : X ⟶ Y} {w₁ w₂ : X → ℤ}
    (h₁ : IsWeighting f w₁) (h₂ : IsWeighting f w₂) : IsWeighting f (w₁ + w₂) := by
  intro U V h π g comm hg hU hπ
  have := hπ
  have hfin : ∀ v : V, (π ⁻¹' {v}).Finite := fun v ↦ π.finite_preimage_singleton v
  have key : separableDegreeWeightedFiberSum π ((w₁ + w₂) ∘ h) =
      separableDegreeWeightedFiberSum π (w₁ ∘ h) +
        separableDegreeWeightedFiberSum π (w₂ ∘ h) := by
    funext v
    change separableDegreeWeightedFiberSum π ((w₁ + w₂) ∘ h) v =
      separableDegreeWeightedFiberSum π (w₁ ∘ h) v +
        separableDegreeWeightedFiberSum π (w₂ ∘ h) v
    exact separableDegreeWeightedFiberSum_add π (w₁ ∘ h) (w₂ ∘ h) v
      (separableDegreeWeightedFiberTerm_hasFiniteSupport π (w₁ ∘ h) v (hfin v))
      (separableDegreeWeightedFiberTerm_hasFiniteSupport π (w₂ ∘ h) v (hfin v))
  rw [key]
  exact (h₁ h π g comm hg hU hπ).add (h₂ h π g comm hg hU hπ)

/-- An integer multiple of a weighting of a morphism is a weighting: scaling the weight scales
every weighted fibre sum, and this needs no finiteness hypothesis. -/
theorem IsWeighting.const_mul {X Y : Scheme.{u}} {f : X ⟶ Y} {w : X → ℤ} (c : ℤ)
    (hw : IsWeighting f w) : IsWeighting f (fun x ↦ c * w x) := by
  intro U V h π g comm hg hU hπ
  have key : separableDegreeWeightedFiberSum π ((fun x ↦ c * w x) ∘ h) =
      fun v ↦ c * separableDegreeWeightedFiberSum π (w ∘ h) v := by
    funext v
    exact separableDegreeWeightedFiberSum_const_mul π c (w ∘ h) v
  rw [key]
  exact (hw h π g comm hg hU hπ).comp fun n ↦ c * n

/-- The negative of a weighting of a morphism is a weighting. -/
theorem IsWeighting.neg {X Y : Scheme.{u}} {f : X ⟶ Y} {w : X → ℤ}
    (hw : IsWeighting f w) : IsWeighting f (-w) := by
  intro U V h π g comm hg hU hπ
  have key : separableDegreeWeightedFiberSum π ((-w) ∘ h) =
      fun v ↦ -separableDegreeWeightedFiberSum π (w ∘ h) v := by
    have hmul : ((-w) ∘ h) = fun y ↦ (-1 : ℤ) * (w ∘ h) y := by
      funext y
      simp
    rw [hmul]
    funext v
    rw [separableDegreeWeightedFiberSum_const_mul π (-1) (w ∘ h) v, neg_one_mul]
  rw [key]
  exact (hw h π g comm hg hU hπ).comp fun n ↦ -n

/-- The difference of two weightings of a morphism is a weighting. -/
theorem IsWeighting.sub {X Y : Scheme.{u}} {f : X ⟶ Y} {w₁ w₂ : X → ℤ}
    (h₁ : IsWeighting f w₁) (h₂ : IsWeighting f w₂) : IsWeighting f (w₁ - w₂) := by
  rw [sub_eq_add_neg]
  exact h₁.add h₂.neg

end AlgebraicGeometry
