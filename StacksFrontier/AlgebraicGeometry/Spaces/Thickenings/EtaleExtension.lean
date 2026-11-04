module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Morphisms into a scheme étale over the base of a thickening

Let `t : T₀ ⟶ T` be a morphism of the big fppf site of `S` whose underlying morphism of schemes
is a thickening of arbitrary order, and let `V` be étale over `T`. A morphism into `V` over `T`
from the base change `T'₀ ⟶ T'` of `t` along any `T' ⟶ T` extends uniquely to `T'`. This is the
scheme-level input that identifies, over every object of the site, the pushforward
`CategoryTheory.monoPushforward i u₀` of an étale morphism `u₀` out of a scheme along a
representable thickening `i` with the étale lift of Stacks 039R, which is how an étale morphism
is extended across a thickening of algebraic spaces in the proof of Stacks 0AIU (Stacks 05ZH).

## Main results

* `AlgebraicGeometry.Space.existsUnique_extend_of_isPullback_of_isThickening`: Stacks 0BTY in the
  big fppf site: a morphism from the base change of a thickening into a scheme étale over the
  target extends uniquely.

## Implementation notes

The order of the thickening plays no role: a surjective closed immersion is a universal
homeomorphism, so is its base change, and Stacks 0BTY in the form
`Stacks.Etale.existsUnique_section_of_universalHomeomorphism` applies to the étale base change
of `V` to `T'`. The resulting morphism of schemes lies over `S`, so
`AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq` places it in the site.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0BTY in the big fppf site.** Let `t : T₀ ⟶ T` be a morphism of the site whose
underlying morphism of schemes is a thickening, let `q : V ⟶ T` be étale, and let `a : T'₀ ⟶ T'`
be the base change of `t` along `k : T' ⟶ T`. A morphism `n : T'₀ ⟶ V` over `T` extends uniquely
to a morphism `T' ⟶ V` over `T`. -/
theorem existsUnique_extend_of_isPullback_of_isThickening
    {T₀ T V T' T'₀ : BigFppfOver B S hS} {t : T₀ ⟶ T}
    (ht : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map t))
    {q : V ⟶ T} (hq : Etale ((BigFppfOver.toScheme B S hS).map q))
    {k : T' ⟶ T} {a : T'₀ ⟶ T'} {b : T'₀ ⟶ T₀} (hT' : IsPullback a b k t)
    (n : T'₀ ⟶ V) (hn : n ≫ q = a ≫ k) :
    ∃! v : T' ⟶ V, v ≫ q = k ∧ a ≫ v = n := by
  let H := BigFppfOver.toScheme B S hS
  have hpres : PreservesLimitsOfShape WalkingCospan H := by
    dsimp [H, BigFppfOver.toScheme]
    infer_instance
  have hsq : IsPullback (H.map a) (H.map b) (H.map k) (H.map t) := hT'.map H
  have _ : AlgebraicGeometry.IsClosedImmersion (H.map t) := ht.1
  have hut : UniversalHomeomorphism (H.map t) :=
    Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective _ ht.2
  have _ : UniversalHomeomorphism (H.map a) := by
    rw [universalHomeomorphism_iff]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip
      ((universalHomeomorphism_iff _).mp hut)
  have _ : Etale (H.map q) := hq
  have hnk : H.map n ≫ H.map q = H.map a ≫ H.map k := by
    rw [← H.map_comp, ← H.map_comp, hn]
  obtain ⟨σ, ⟨hσ1, hσ2⟩, hσu⟩ := Stacks.Etale.existsUnique_section_of_universalHomeomorphism
    (H.map a) (pullback.snd (H.map q) (H.map k)) (pullback.lift (H.map n) (H.map a) hnk)
    (pullback.lift_snd _ _ _)
  let vs : H.obj T' ⟶ H.obj V := σ ≫ pullback.fst (H.map q) (H.map k)
  have hvs : vs ≫ H.map q = H.map k := by
    simp only [vs, Category.assoc, pullback.condition, reassoc_of% hσ1]
  have hw : vs ≫ B.inclusion.map V.hom = B.inclusion.map T'.hom := by
    have hcomp {X Y : BigFppfOver B S hS} (f : X ⟶ Y) :
        H.map f ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom :=
      (B.inclusion.map_comp f.left Y.hom).symm.trans (congrArg B.inclusion.map (Over.w f))
    rw [← hcomp q, ← Category.assoc, hvs, hcomp k]
  obtain ⟨v, hv⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS vs hw
  have hv' : H.map v = vs := hv
  refine ⟨v, ⟨?_, ?_⟩, ?_⟩
  · apply H.map_injective
    rw [H.map_comp, hv', hvs]
  · apply H.map_injective
    rw [H.map_comp, hv', ← Category.assoc, hσ2, pullback.lift_fst]
  · rintro v' ⟨hv'1, hv'2⟩
    apply H.map_injective
    rw [hv']
    have hcomm : H.map v' ≫ H.map q = 𝟙 _ ≫ H.map k := by
      rw [← H.map_comp, hv'1, Category.id_comp]
    have h := hσu (pullback.lift (H.map v') (𝟙 _) hcomm) ⟨pullback.lift_snd _ _ _, by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← H.map_comp, hv'2]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]⟩
    simp only [vs, ← h, pullback.lift_fst]

end AlgebraicGeometry.Space

end
