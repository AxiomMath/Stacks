module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageRingSectionsChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDirectImageChartEqualizer
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective

/-!
# The chart sections of a direct-image algebra are bounded by the site's cutoff

Let `X` be an algebraic space. The sections over an étale chart of `X` of the direct-image algebra
`f_* 𝒪_Y` of a morphism `f : Y ⟶ X` of algebraic spaces are fewer than the cutoff cardinal of the
ambient big fppf site. In particular this holds for every value of the direct-image functor
`AlgebraicGeometry.Space.affinePushforwardQuasicoherentAlgebraFunctor` of Stacks 081V, and, if
that functor is essentially surjective, for every quasi-coherent `𝒪_X`-algebra.

## Main results

* `AlgebraicGeometry.Space.mk_sections_structureRingSheaf_le_two_pow_size`: the global regular
  functions on an étale chart of an algebraic space are at most `2 ^ size` of the chart's scheme.
* `AlgebraicGeometry.Space.mk_sections_structureRingSheaf_lt_cutoff`: hence they are fewer than
  the cutoff.
* `AlgebraicGeometry.Space.mk_sections_pushforwardAlgebra_lt_cutoff`: the sections of the
  direct-image algebra `f_* 𝒪_Y` over an étale chart of `X` are fewer than the cutoff, for every
  morphism `f` of algebraic spaces.
* `AlgebraicGeometry.Space.mk_sections_affinePushforwardQuasicoherentAlgebraFunctor_lt_cutoff`:
  the same for every value of the direct-image functor of Stacks 081V.
* `AlgebraicGeometry.Space.mk_sections_lt_cutoff_of_essSurj`: if that functor is essentially
  surjective over `X`, then every quasi-coherent `𝒪_X`-algebra is subject to the same bound.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Section 000H](https://stacks.math.columbia.edu/tag/000H)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The global functions on an étale chart of an algebraic space are at most `2 ^ size` of the
chart's scheme. -/
theorem mk_sections_structureRingSheaf_le_two_pow_size (X : AlgebraicSpaces B S hS)
    (W : SmallEtale B S hS X.1) :
    Cardinal.mk (ToType ((structureRingSheaf B S hS X).obj.obj (op W))) ≤
      2 ^ (chartScheme W).size :=
  Scheme.mk_sections_le_two_pow_size
    ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) ⊤

/-- The global functions on an étale chart of an algebraic space are fewer than the site's
cutoff. -/
theorem mk_sections_structureRingSheaf_lt_cutoff (X : AlgebraicSpaces B S hS)
    (W : SmallEtale B S hS X.1) :
    Cardinal.mk (ToType ((structureRingSheaf B S hS X).obj.obj (op W))) < B.cutoff :=
  (mk_sections_structureRingSheaf_le_two_pow_size B S hS X W).trans_lt
    (B.cutoff_isStrongPrelimit ((SmallEtale.toOver B S hS X.1).obj W).left.2)

/-- For every morphism `f : Y ⟶ X` of algebraic spaces, the sections of the direct-image algebra
`f_* 𝒪_Y` over an étale chart of `X` are fewer than the site's cutoff. -/
theorem mk_sections_pushforwardAlgebra_lt_cutoff {X : AlgebraicSpaces B S hS} (Y : Over X)
    (V : SmallEtale B S hS X.1) :
    Cardinal.mk (ToType ((pushforwardAlgebra B S hS Y).right.obj.obj (op V))) < B.cutoff := by
  obtain ⟨W, W', a, b, ⟨e⟩⟩ := exists_smallEtaleDirectImageChartEqualizerEquiv B S hS Y.hom
    ((sheafCompose (SmallEtale.topology B S hS Y.left.1)
      (CategoryTheory.forget RingCat.{u})).obj (structureRingSheaf B S hS Y.left)) V
  exact ((Cardinal.mk_congr e).trans_le
    (Cardinal.mk_le_of_injective Subtype.val_injective)).trans_lt
    (mk_sections_structureRingSheaf_lt_cutoff B S hS Y.left W)

/-- Every value of the direct-image functor of Stacks 081V has fewer sections over every étale
chart than the site's cutoff. -/
theorem mk_sections_affinePushforwardQuasicoherentAlgebraFunctor_lt_cutoff
    (X : AlgebraicSpaces B S hS) (Y : AffineOver B S hS X) (V : SmallEtale B S hS X.1) :
    Cardinal.mk (ToType
        (((affinePushforwardQuasicoherentAlgebraFunctor B S hS X).obj (op Y)).obj.right.obj.obj
          (op V))) < B.cutoff :=
  mk_sections_pushforwardAlgebra_lt_cutoff B S hS Y.obj V

/-- If the direct-image functor of Stacks 081V is essentially surjective over `X`, then every
quasi-coherent `𝒪_X`-algebra has fewer sections over every étale chart than the site's cutoff. -/
theorem mk_sections_lt_cutoff_of_essSurj (X : AlgebraicSpaces B S hS)
    (h : (affinePushforwardQuasicoherentAlgebraFunctor B S hS X).EssSurj)
    (A : QuasicoherentAlgebra B S hS X) (V : SmallEtale B S hS X.1) :
    Cardinal.mk (ToType (A.obj.right.obj.obj (op V))) < B.cutoff :=
  have := h
  (Cardinal.mk_congr
    (((CategoryTheory.forget CommRingCat.{u}).mapIso
      (((sheafToPresheaf _ _).mapIso (AlgebraSheaf.forget.mapIso
        ((quasicoherentAlgebraInclusion B S hS X).mapIso
          ((affinePushforwardQuasicoherentAlgebraFunctor B S hS X).objObjPreimageIso
            A).symm))).app (op V))).toEquiv)).trans_lt
    (mk_sections_affinePushforwardQuasicoherentAlgebraFunctor_lt_cutoff B S hS X
      (((affinePushforwardQuasicoherentAlgebraFunctor B S hS X).objPreimage A).unop) V)

end AlgebraicGeometry.Space

end
