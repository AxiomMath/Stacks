module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentBounded

/-!
# Bounded base changes from uniformly bounded étale charts

Let `D` be an inverse system of presheaves on the big fppf site of `S` and `i₀` a stage. If the
stages beyond `i₀` are fewer than the site's cutoff and each of them admits a surjective étale
chart by an object of the site of size at most one fixed `ν` below the cutoff, then the base
changes `D j ×_{D i₀} U₀` of the later stages along any affine point `U₀ ⟶ D i₀` are bounded
below the cutoff (`AlgebraicGeometry.Space.HasBoundedBaseChanges`). No condition on the
cofinality of the cutoff is needed.

## Main results

* `AlgebraicGeometry.Space.hasBoundedBaseChanges_of_etaleCharts`: the statement just described.

## Implementation notes

Let `W` represent `D j ×_{D i₀} U₀` and let `v : V ⟶ D j` be the chart of the stage. The base
change `P = W ×_{D j} V` is represented, `v` being representable, and `P ⟶ W` is étale and
surjective, so `size W ≤ 2 ^ 2 ^ size P` by
`AlgebraicGeometry.Scheme.size_le_two_pow_two_pow_size_of_flat_of_surjective`. On the other hand
`P = U₀ ×_{D i₀} V` maps by a monomorphism to the product `U₀ ×_S V` of the site, whose size is
at most `max (size U₀) ν` (`AlgebraicGeometry.Space.size_toScheme_obj_prod_le`), so
`AlgebraicGeometry.Scheme.size_le_of_mono` bounds `size P` in terms of `size U₀` and `ν` alone.
The cutoff being a strong limit, the resulting bound is below it, uniformly in `j`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Monotonicity of `2 ^ ·` on cardinals. -/
private theorem two_pow_le_two_pow {a b : Cardinal.{u}} (h : a ≤ b) :
    (2 : Cardinal.{u}) ^ a ≤ 2 ^ b :=
  power_le_power_left two_ne_zero h

/-- **The size of a base change along a point with a bounded étale chart of the stage.** Let
`W` represent the fibre product of `g : X ⟶ Y` with `f₀ : U₀ ⟶ Y`, and let `v : V ⟶ X` be a
surjective étale chart of `X`. Then `size W` is bounded in terms of `size U₀` and `size V`
alone: `size W ≤ 2 ^ 2 ^ n` with `n = max (2 ^ 2 ^ m) m` and `m = max (size U₀) (size V)`. -/
theorem size_le_of_isPullback_of_etaleChart {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g : X ⟶ Y} {U₀ W V : BigFppfOver B S hS} {f₀ : yoneda.obj U₀ ⟶ Y}
    {p : yoneda.obj W ⟶ X} {q : yoneda.obj W ⟶ yoneda.obj U₀} (hpq : IsPullback p q g f₀)
    {v : yoneda.obj V ⟶ X}
    (hvE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf v)
    (hvS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf v) :
    ((BigFppfOver.toScheme B S hS).obj W).size ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
        max ((BigFppfOver.toScheme B S hS).obj U₀).size ((BigFppfOver.toScheme B S hS).obj V).size)
        (max ((BigFppfOver.toScheme B S hS).obj U₀).size
          ((BigFppfOver.toScheme B S hS).obj V).size) := by
  set H := BigFppfOver.toScheme B S hS
  set m := max (H.obj U₀).size (H.obj V).size
  have hr := hvE.rep
  set P := hr.pullback p
  set snd := hr.snd p
  set fst' := hr.fst' p
  have hP : IsPullback (yoneda.map fst') (yoneda.map snd) v p := hr.isPullback' p
  have : Etale (H.map snd) := hvE.property p _ snd hP
  have : Surjective (H.map snd) := hvS.property p _ snd hP
  set q' := yoneda.preimage q
  have hq' : yoneda.map q' = q := Functor.map_preimage _ _
  set e : P ⟶ U₀ ⨯ V := prod.lift (snd ≫ q') fst'
  have he : Mono e := by
    constructor
    intro T a b hab
    have h1 : a ≫ snd ≫ q' = b ≫ snd ≫ q' := by
      simpa [e] using congrArg (· ≫ (prod.fst : U₀ ⨯ V ⟶ U₀)) hab
    have h2 : a ≫ fst' = b ≫ fst' := by
      simpa [e] using congrArg (· ≫ (prod.snd : U₀ ⨯ V ⟶ V)) hab
    have hw : ∀ x : T ⟶ P, yoneda.map (x ≫ snd) ≫ p = yoneda.map (x ≫ fst') ≫ v := fun x => by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hP.w]
    have h3 : a ≫ snd = b ≫ snd := by
      refine yoneda.map_injective (hpq.hom_ext ?_ ?_)
      · exact (hw a).trans ((congrArg (fun x => yoneda.map x ≫ v) h2).trans (hw b).symm)
      · rw [← hq', ← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc, h1]
    exact yoneda.map_injective (hP.hom_ext (by rw [← Functor.map_comp, ← Functor.map_comp, h2])
      (by rw [← Functor.map_comp, ← Functor.map_comp, h3]))
  have : Mono (H.map e) := Functor.map_mono H e
  have hprod : (H.obj (U₀ ⨯ V)).size ≤ m := size_toScheme_obj_prod_le B S hS U₀ V
  have hPsize : (H.obj P).size ≤ max ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ m) m :=
    (Scheme.size_le_of_mono (H.map e)).trans (max_le_max
      (two_pow_le_two_pow ((Scheme.mk_le_two_pow_size _).trans (two_pow_le_two_pow hprod))) hprod)
  exact (Scheme.size_le_two_pow_two_pow_size_of_flat_of_surjective (H.map snd)).trans
    (two_pow_le_two_pow (two_pow_le_two_pow hPsize))

/-- **Bounded base changes from uniformly bounded étale charts.** If the stages of `D` beyond
`i₀` are fewer than the site's cutoff, and each of them admits a surjective étale chart by an
object of the site of size at most a fixed `ν` below the cutoff, then the base changes of the
later stages along any affine point of `i₀` are bounded below the cutoff. No condition on the
cofinality of the cutoff is needed; that the cutoff is a strong limit cardinal absorbs the
exponentials of `AlgebraicGeometry.Space.size_le_of_isPullback_of_etaleChart`. -/
theorem hasBoundedBaseChanges_of_etaleCharts {I : Type u} [Category.{u} I] (i₀ : I)
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hOver : #(Over i₀) < B.cutoff)
    {ν : Cardinal.{u}} (hν : ν < B.cutoff)
    (hcharts : ∀ j : Over i₀, ∃ (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ D.obj j.left),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf v ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf v ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ ν) :
    HasBoundedBaseChanges B S hS i₀ D := by
  intro U₀ f₀
  set H := BigFppfOver.toScheme B S hS
  set m := max (H.obj ((BigAffineFppf.inclusion B S hS).obj U₀)).size ν
  have hsl := B.cutoff_isStrongPrelimit
  have hm' : m < B.cutoff := max_lt ((BigAffineFppf.inclusion B S hS).obj U₀).left.property hν
  have hn : max ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ m) m < B.cutoff :=
    max_lt (hsl (hsl hm')) hm'
  refine ⟨max #(Over i₀) ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
      max ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ m) m),
    max_lt hOver (hsl (hsl hn)), le_max_left _ _, fun j W p q hpq => ?_⟩
  obtain ⟨V, v, hvE, hvS, hV⟩ := hcharts j
  have hle : max (H.obj ((BigAffineFppf.inclusion B S hS).obj U₀)).size (H.obj V).size ≤ m :=
    max_le_max le_rfl hV
  exact (size_le_of_isPullback_of_etaleChart B S hS hpq hvE hvS).trans
    (le_max_of_le_right (two_pow_le_two_pow (two_pow_le_two_pow
      (max_le_max (two_pow_le_two_pow (two_pow_le_two_pow hle)) hle))))

end AlgebraicGeometry.Space

end
