module

public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RegularImmersion

/-!
# Perfect morphisms into a smooth scheme over a base

A morphism `f : X ⟶ Y` of schemes over a base `S` with `Y ⟶ S` smooth is perfect as soon as the
structure morphism `X ⟶ S` is perfect.

## Main results

* `AlgebraicGeometry.perfect_of_smooth_section`: a section of a smooth morphism of schemes is
  perfect.
* `AlgebraicGeometry.perfect_of_comp_of_smooth` and
  `AlgebraicGeometry.perfect_of_comp_eq_of_smooth`: Stacks 068D, in the composite and in the
  commutative-triangle form.

## Implementation notes

The factorisation of the source is `f = (1, f) ≫ pullback.snd`, through the fibre product
`X ×_S Y`. The projection `X ×_S Y ⟶ Y` is a base change of `X ⟶ S` along the flat morphism
`Y ⟶ S`, hence perfect by Stacks 0688; the projection `X ×_S Y ⟶ X` is a base change of `Y ⟶ S`,
hence smooth, so `(1, f)` is a section of a smooth morphism and therefore a regular immersion by
Stacks 067R and perfect by Stacks 068C. Perfectness composes by Stacks 0689.

## References

* [The Stacks Project, Lemma 37.61.7 (068D)](https://stacks.math.columbia.edu/tag/068D)
* [The Stacks Project, Lemma 37.61.3 (0688)](https://stacks.math.columbia.edu/tag/0688)
* [The Stacks Project, Lemma 37.61.6 (068C)](https://stacks.math.columbia.edu/tag/068C)
* [The Stacks Project, Lemma 37.61.2 (0689)](https://stacks.math.columbia.edu/tag/0689)
* [The Stacks Project, Lemma 31.22.5 (067R)](https://stacks.math.columbia.edu/tag/067R)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A section of a smooth morphism of schemes is perfect: it is a regular immersion by Stacks
067R, and a regular immersion is perfect by Stacks 068C. -/
public theorem perfect_of_smooth_section {W X : Scheme.{u}} (g : W ⟶ X) [Smooth g] (σ : X ⟶ W)
    (hσ : σ ≫ g = 𝟙 X) : Perfect σ := by
  have : IsImmersion σ := _root_.Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id σ g hσ
  exact perfect_of_isRegularImmersion σ
    (_root_.Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section g σ hσ)

/-- **Stacks 068D.** Let `f : X ⟶ Y` and `q : Y ⟶ S` be morphisms of schemes with `q` smooth. If
the composite `f ≫ q` is perfect, then `f` is perfect. -/
public theorem perfect_of_comp_of_smooth {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) [Smooth q]
    [Perfect (f ≫ q)] : Perfect f := by
  have hw : 𝟙 X ≫ f ≫ q = f ≫ q := Category.id_comp _
  have : Perfect (pullback.lift (𝟙 X) f hw) :=
    perfect_of_smooth_section (pullback.fst (f ≫ q) q) _ (pullback.lift_fst _ _ _)
  have : Perfect (pullback.snd (f ≫ q) q) := perfect_pullback_snd (f ≫ q) q
  rw [← pullback.lift_snd (𝟙 X) f hw]
  infer_instance

/-- **Stacks 068D.** In a commutative triangle of morphisms of schemes with `f ≫ q = p`, `q`
smooth and `p` perfect, the morphism `f` is perfect. -/
@[stacks 068D]
public theorem perfect_of_comp_eq_of_smooth {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    {p : X ⟶ S} (hfq : f ≫ q = p) [Smooth q] [Perfect p] : Perfect f := by
  subst hfq
  exact perfect_of_comp_of_smooth f q

end AlgebraicGeometry

end
