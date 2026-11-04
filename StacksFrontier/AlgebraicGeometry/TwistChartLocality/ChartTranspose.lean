module

public import StacksFrontier.AlgebraicGeometry.Modules.TransposeFactorization
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Comparison
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.AdjointSections
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.TransposePullback

/-!
# The chart inverse image of the twist comparison is an inverse adjoint transpose over a spectrum

Tag 01MY's comparison map `θ n = Stacks.ProjTwistComparison.twistMap ψ hψ n` is the inverse
adjoint transpose, along `r = AlgebraicGeometry.Proj.map ψ hψ`, of the explicit pointwise
comparison `Stacks.ProjTwistComparison.pushforwardTwistMap`. Invertibility of `θ n` is detected
by its inverse images along the chart spectra `i = AlgebraicGeometry.Proj.awayι ℬ (ψ f)`, by
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_of_isIso_pullback_awayι`. This file identifies
`i^* (θ n)` as an inverse adjoint transpose along `Spec.map` of the chart ring homomorphism
`HomogeneousLocalization.Away.map ψ f`, which is the form the affine criterion
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension` consumes.

The identification is the composite of two changes of adjunction and nothing else.

* `Stacks.AlgebraicGeometry.TwistChartLocality.map_homEquiv_symm` turns `i^*` applied to a
  transpose along `r` into a transpose along the composite adjunction of `r` and `i`.
* `Stacks.TransposeFactorization.homEquiv_symm_comp_eq` moves that to the composite adjunction of
  the other factorization of the same morphism, `i ≫ r = Spec.map (Away.map ψ f) ≫ awayι 𝒜 f` by
  `AlgebraicGeometry.Proj.awayι_comp_map` — the chart square of `AlgebraicGeometry.Proj.map`.
* `CategoryTheory.Adjunction.comp_homEquiv_symm_apply` splits the resulting transpose along
  `adj_{awayι 𝒜 f}.comp adj_{Spec.map (Away.map ψ f)}` into a transpose along the chart of the
  target followed by a transpose along the morphism of spectra.

What comes out is a transpose along `Spec.map` of a ring homomorphism, of the morphism named
below, between two inverse images along chart morphisms. Both of those are quasi-coherent by
`Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_pullback_awayι_twistingSheaf`, so
the affine criterion applies to it.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistChartLocality.chartPushforwardTwistMap`: the morphism out of
  `𝒪_{Proj 𝒜}(n)` that the second factorization's composite adjunction transposes — the explicit
  pointwise comparison, followed by the unit of the chart adjunction of the source and by the
  three comparisons of direct images.
* `Stacks.AlgebraicGeometry.TwistChartLocality.chartAdjointTwistMap`: its transpose along the
  chart of the target, a morphism
  `(awayι 𝒜 f)^* 𝒪_{Proj 𝒜}(n) ⟶ (Spec.map (Away.map ψ f))_* (awayι ℬ (ψ f))^* 𝒪_{Proj ℬ}(n)`.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartLocality.pullback_awayι_map_twistMap_eq`: **the
  identification.** The inverse image of `θ n` along the chart spectrum of `ψ f` is the inverse
  adjoint transpose of
  `Stacks.AlgebraicGeometry.TwistChartLocality.chartAdjointTwistMap`, preceded by the three
  comparisons of inverse images.
* `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_pullback_awayι_map_twistMap_iff`: **the
  criterion.** Those three comparisons being isomorphisms, invertibility of the chart inverse
  image of `θ n` is invertibility of that transpose.

## Implementation notes

Every step is taken by `Eq.trans` against a fully applied lemma rather than by `rw`. The
rewriting form of
`Stacks.AlgebraicGeometry.TwistChartLocality.map_homEquiv_symm` does not fire here: its left-hand
side mentions the second adjunction only through that adjunction's left adjoint, so the pattern
leaves the adjunction itself undetermined, and supplying it explicitly still leaves `rw` unable
to match the twisting sheaves. Unification against an applied term has no such difficulty.

`CategoryTheory.NatIso.isIso_app_of_isIso` is supplied by hand for each of the three comparisons
of inverse images. It is not found by instance search at the components occurring here, so the
three instances are introduced as local hypotheses before `CategoryTheory.isIso_comp_left_iff`
is used.

No local reducibility attribute is in force. The statements below mention `θ n` but never unfold
it: with `AlgebraicGeometry.Proj` made reducible the definitional check that unfolding
`Stacks.ProjTwistComparison.twistMap` demands exhausts the heartbeat budget, and
`Stacks.ProjTwistComparison.homEquiv_twistMap` — the characterisation of `θ n` by its transpose —
removes the need for it.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open AlgebraicGeometry.Scheme.Modules

namespace Stacks.AlgebraicGeometry.TwistChartLocality

universe u

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ) {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) (n : ℤ)

/-- The morphism out of `𝒪_{Proj 𝒜}(n)` whose inverse adjoint transpose along the composite
adjunction of the chart square's bottom row is the chart inverse image of Tag 01MY's comparison
map: the explicit pointwise comparison
`Stacks.ProjTwistComparison.pushforwardTwistMap`, followed by the unit of the chart adjunction of
`Proj ℬ` and by the three comparisons of direct images that the chart square supplies. -/
public def chartPushforwardTwistMap :
    twistingSheaf 𝒜 n ⟶
      (pushforward (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).obj
        ((pushforward (Spec.map (CommRingCat.ofHom (Away.map ψ f)))).obj
          ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).obj
            (twistingSheaf ℬ n))) :=
  (Stacks.ProjTwistComparison.pushforwardTwistMap ψ hψ n ≫
      (pushforward (AlgebraicGeometry.Proj.map ψ hψ)).map
        ((pullbackPushforwardAdjunction
          (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).unit.app
            (twistingSheaf ℬ n))) ≫
    (pushforwardComp (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)
        (AlgebraicGeometry.Proj.map ψ hψ)).hom.app _ ≫
      (pushforwardCongr (AlgebraicGeometry.Proj.awayι_comp_map ψ hψ hd f hf)).hom.app _ ≫
        (pushforwardComp (Spec.map (CommRingCat.ofHom (Away.map ψ f)))
            (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).inv.app _

/-- The inverse adjoint transpose, along the chart `AlgebraicGeometry.Proj.awayι 𝒜 f` of the
target, of `Stacks.AlgebraicGeometry.TwistChartLocality.chartPushforwardTwistMap`. It is a
morphism of modules on the chart spectrum `Spec (𝒜₍f₎)`, out of the chart inverse image of
`𝒪_{Proj 𝒜}(n)` and into the direct image along `Spec.map` of the chart ring homomorphism of the
chart inverse image of `𝒪_{Proj ℬ}(n)`. -/
public def chartAdjointTwistMap :
    (pullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).obj (twistingSheaf 𝒜 n) ⟶
      (pushforward (Spec.map (CommRingCat.ofHom (Away.map ψ f)))).obj
        ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).obj
          (twistingSheaf ℬ n)) :=
  ((pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).homEquiv _ _).symm
    (chartPushforwardTwistMap 𝒜 ℬ ψ hψ hd hf n)

/-- **The chart inverse image of Tag 01MY's comparison map is an inverse adjoint transpose along
`Spec.map` of the chart ring homomorphism.** It is the transpose of
`Stacks.AlgebraicGeometry.TwistChartLocality.chartAdjointTwistMap`, preceded by the comparison of
the inverse images along the two factorizations of the chart square's diagonal.

The three leading morphisms are the pseudofunctoriality isomorphism of
`awayι ℬ (ψ f) ≫ Proj.map ψ hψ`, the comparison of the inverse images along the two equal
composites of `AlgebraicGeometry.Proj.awayι_comp_map`, and the inverse of the
pseudofunctoriality isomorphism of `Spec.map (Away.map ψ f) ≫ awayι 𝒜 f`. -/
public theorem pullback_awayι_map_twistMap_eq :
    (pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).map
        (Stacks.ProjTwistComparison.twistMap ψ hψ n) =
      (pullbackComp (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)
            (AlgebraicGeometry.Proj.map ψ hψ)).hom.app (twistingSheaf 𝒜 n) ≫
        (pullbackCongr
              (AlgebraicGeometry.Proj.awayι_comp_map ψ hψ hd f hf)).hom.app
            (twistingSheaf 𝒜 n) ≫
          (pullbackComp (Spec.map (CommRingCat.ofHom (Away.map ψ f)))
                (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).inv.app (twistingSheaf 𝒜 n) ≫
            transpose (CommRingCat.ofHom (Away.map ψ f))
              ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).obj (twistingSheaf 𝒜 n))
              ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).obj
                (twistingSheaf ℬ n))
              (chartAdjointTwistMap 𝒜 ℬ ψ hψ hd hf n) := by
  have h1 : Stacks.ProjTwistComparison.twistMap ψ hψ n =
      ((pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.map ψ hψ)).homEquiv
        (twistingSheaf 𝒜 n) (twistingSheaf ℬ n)).symm
          (Stacks.ProjTwistComparison.pushforwardTwistMap ψ hψ n) :=
    (Equiv.eq_symm_apply _).mpr (Stacks.ProjTwistComparison.homEquiv_twistMap ψ hψ n)
  refine Eq.trans (congrArg (pullback
    (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).map h1) ?_
  refine Eq.trans (map_homEquiv_symm
    (pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.map ψ hψ))
    (pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd))
    (Stacks.ProjTwistComparison.pushforwardTwistMap ψ hψ n)) ?_
  refine Eq.trans (Stacks.TransposeFactorization.homEquiv_symm_comp_eq
    (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd) (AlgebraicGeometry.Proj.map ψ hψ)
    (Spec.map (CommRingCat.ofHom (Away.map ψ f))) (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)
    (AlgebraicGeometry.Proj.awayι_comp_map ψ hψ hd f hf) (twistingSheaf 𝒜 n) _ _) ?_
  refine congrArg _ ?_
  refine congrArg _ ?_
  refine congrArg _ ?_
  exact CategoryTheory.Adjunction.comp_homEquiv_symm_apply
    (pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd))
    (pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom (Away.map ψ f)))) _ _ _

/-- **The chart form of the invertibility question for Tag 01MY's comparison map.** The inverse
image of `θ n` along the chart spectrum of `ψ f` is invertible exactly when the inverse adjoint
transpose of `Stacks.AlgebraicGeometry.TwistChartLocality.chartAdjointTwistMap` is, the two
differing by the three comparisons of inverse images of
`Stacks.AlgebraicGeometry.TwistChartLocality.pullback_awayι_map_twistMap_eq`, which are
isomorphisms.

The right-hand side is a transpose along `Spec.map` of a ring homomorphism between two
quasi-coherent modules, so
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension` applies to
it. -/
public theorem isIso_pullback_awayι_map_twistMap_iff :
    IsIso ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).map
        (Stacks.ProjTwistComparison.twistMap ψ hψ n)) ↔
      IsIso (transpose (CommRingCat.ofHom (Away.map ψ f))
        ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).obj (twistingSheaf 𝒜 n))
        ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).obj
          (twistingSheaf ℬ n))
        (chartAdjointTwistMap 𝒜 ℬ ψ hψ hd hf n)) := by
  have := NatIso.isIso_app_of_isIso (pullbackComp
    (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)
    (AlgebraicGeometry.Proj.map ψ hψ)).hom (twistingSheaf 𝒜 n)
  have := NatIso.isIso_app_of_isIso (pullbackCongr
    (AlgebraicGeometry.Proj.awayι_comp_map ψ hψ hd f hf)).hom (twistingSheaf 𝒜 n)
  have := NatIso.isIso_app_of_isIso (pullbackComp
    (Spec.map (CommRingCat.ofHom (Away.map ψ f)))
    (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).inv (twistingSheaf 𝒜 n)
  rw [pullback_awayι_map_twistMap_eq 𝒜 ℬ ψ hψ hd hf n]
  simp only [isIso_comp_left_iff]

end Stacks.AlgebraicGeometry.TwistChartLocality

end
