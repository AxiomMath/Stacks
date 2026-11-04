module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# An affine morphism of schemes over `S` is quasi-compact as a morphism of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism `g : U ⟶ V` of the big fppf
category over `S` whose underlying morphism of schemes is affine induces a quasi-compact morphism
`yoneda.map g` of algebraic spaces over `S`, in the sense of **Stacks 03HE**: every base change of
it along a morphism from a quasi-compact algebraic space again has quasi-compact source.

The proof is the affine criterion for quasi-compactness
(`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine`), which reduces
the condition to the base changes along the scheme-valued points `yoneda.obj T ⟶ yoneda.obj V`
with `T` affine. Such a
point is `yoneda.map` of a morphism of the site, because Yoneda is fully faithful; the big fppf
category over `S` has fibre products, and both Yoneda and the functor to schemes preserve them, so
the base change in question is the representable presheaf of the fibre product `T ×_V U` taken in
the site. Its underlying scheme is affine: the projection to `T` is the base change of the affine
morphism `g`, hence affine, and `T` is affine. A representable presheaf whose scheme is affine is a
quasi-compact algebraic space.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_yoneda_map_of_isAffineHom`: a morphism of the big fppf
  category over `S` with affine underlying morphism of schemes is quasi-compact as a morphism of
  algebraic spaces over `S`.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of the big fppf category over `S` whose underlying morphism of schemes is affine
is quasi-compact as a morphism of algebraic spaces over `S`** (**Stacks 03HE** for an affine
morphism).

By the affine criterion it is enough to check the base change along an affine scheme-valued point
`h` of the target. Yoneda being fully faithful, `h` comes from a morphism `h₀` of the site; the
base change is then the representable presheaf of `T ×_V U`, because the site has fibre products
and Yoneda preserves them, and the underlying scheme of that fibre product is affine since the
projection to `T` is a base change of `g`. -/
theorem isQuasiCompact_yoneda_map_of_isAffineHom {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (haff : IsAffineHom ((BigFppfOver.toScheme B S hS).map g)) :
    IsQuasiCompact B S hS (yoneda.map g) := by
  have hps : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  refine isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS
    (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V) (yoneda.map g) ?_
  intro T hTaff h
  obtain ⟨h₀, hh⟩ : ∃ h₀ : T ⟶ V, yoneda.map h₀ = h :=
    ⟨Yoneda.fullyFaithful.preimage h, Yoneda.fullyFaithful.map_preimage _⟩
  subst hh
  have hsq : IsPullback (pullback.fst h₀ g) (pullback.snd h₀ g) h₀ g :=
    IsPullback.of_hasPullback _ _
  have hafffst : IsAffineHom ((BigFppfOver.toScheme B S hS).map (pullback.fst h₀ g)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (hsq.map (BigFppfOver.toScheme B S hS)).flip haff
  have hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hTaff
  have haffP : IsAffine ((BigFppfOver.toScheme B S hS).obj (Limits.pullback h₀ g)) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (pullback.fst h₀ g))
  exact isQuasiCompactSpace_of_iso B S hS
    ((hsq.map yoneda).isoIsPullback _ _
      (IsPullback.of_hasPullback (yoneda.map h₀) (yoneda.map g)))
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ haffP)

end AlgebraicGeometry.Space

end
