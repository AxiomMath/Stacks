module

public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.RationalPointsAffineOpen

/-!
# A group scheme covered by translates of one smooth chart is smooth

Let `G` be a group scheme over a field `k` and let `c : W ⟶ G` be an open immersion such that `W`
is smooth of relative dimension `n` over `k`. If the right translates of the image of `c` by the
`k`-points of `G` cover `G`, then `G` is smooth of relative dimension `n` over `k`: every point
has an open neighbourhood, a translate of the chart, isomorphic over `k` to `W`, and smoothness
of relative dimension `n` is local on the source.

This is how [Stacks, Tag 0BA0] obtains the smoothness of the Picard scheme of a curve: by the
proof of [Stacks, Tag 0B9Z], the Abel map `γ_g` restricts to an open immersion on the open `W` of
the Hilbert scheme `Hilb^g_{X/k}` of [Stacks, Tag 0B9X], its translates by `k`-points of the Picard
scheme cover it ([Stacks, Tag 0B9Y]), and `Hilb^g_{X/k}` is smooth of relative dimension `g`
([Stacks, Tag 0B9H]).

## Main results

* `AlgebraicGeometry.smoothOfRelativeDimension_of_rightTranslates`: the smoothness statement.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **A group scheme covered by right translates of one smooth chart is smooth.** Let `G` be a
group scheme over `k` and `c : W ⟶ G` an open immersion with `W` smooth of relative dimension `n`
over `k`. If every point of `G` is carried into the image of `c` by right translation by some
`k`-point of `G`, then `G` is smooth of relative dimension `n` over `k`. -/
theorem smoothOfRelativeDimension_of_rightTranslates (G : Grp (Over (Spec (.of k)))) (n : ℕ)
    {W : Scheme.{u}} (c : W ⟶ G.X.left) [IsOpenImmersion c]
    [SmoothOfRelativeDimension n (c ≫ G.X.hom)]
    (hcov : ∀ p : G.X.left, ∃ r : 𝟙_ (Over (Spec (.of k))) ⟶ G.X,
      (rightTranslationIso G r).hom.left p ∈ Set.range c) :
    SmoothOfRelativeDimension n G.X.hom := by
  choose r hr using hcov
  let map : ∀ p : G.X.left, W ⟶ G.X.left := fun p => c ≫ (rightTranslationIso G (r p)).inv.left
  have (p : G.X.left) : IsOpenImmersion (map p) := by
    have : IsIso (rightTranslationIso G (r p)).inv.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (rightTranslationIso G (r p)).inv))
    dsimp only [map]
    infer_instance
  let 𝒰 : G.X.left.OpenCover := Scheme.Cover.mkOfCovers G.X.left (fun _ => W) map (fun p => by
    obtain ⟨w, hw⟩ := hr p
    refine ⟨p, w, ?_⟩
    show (rightTranslationIso G (r p)).inv.left (c w) = p
    rw [hw, ← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    rfl)
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{u} n) 𝒰
    fun p => ?_
  show SmoothOfRelativeDimension n ((c ≫ (rightTranslationIso G (r p)).inv.left) ≫ G.X.hom)
  rw [Category.assoc, Over.w]
  infer_instance

end AlgebraicGeometry

end
