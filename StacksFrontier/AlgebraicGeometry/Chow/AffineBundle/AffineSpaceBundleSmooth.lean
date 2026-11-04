module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleChow
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves

/-!
# Affine-space bundles are smooth, and the zero section of a line bundle is a divisor

An affine-space bundle of rank `r` is smooth of relative dimension `r`: smoothness of relative
dimension `r` is Zariski-local on the target, so by `Stacks.Chow.IsAffineSpaceBundle` it is
enough to check the projection `𝔸(r; T) ⟶ T` of affine `r`-space over an arbitrary base, and
that projection is the base change along `T ⟶ Spec ℤ` of the smooth morphism
`Spec ℤ[x_1, …, x_r] ⟶ Spec ℤ`.

The application is the first clause of [Stacks, Tag 0F96]. For an invertible module `ℒ` on a
scheme `X` with total space `p : L ⟶ X`, the zero section `o : X ⟶ L` is a closed immersion and
its image is a **relative effective Cartier divisor on `L/X`**. Indeed `p` is an affine-space
bundle of rank one, hence smooth of relative dimension one, and the closed subscheme `o(X)` is
finite locally free over `X` because `p` restricted to it is the comparison isomorphism
`o(X) ≅ X` — the zero section splits the projection. [Stacks, Tag 0B9D] then turns a closed
subscheme finite locally free over the base of a smooth relative curve into a relative effective
Cartier divisor.

## Main results

* `Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver`: the projection of affine `r`-space
  over any scheme is smooth of relative dimension `r`.
* `Stacks.Chow.smoothOfRelativeDimension_of_isAffineSpaceBundle`: **an affine-space bundle of
  rank `r` is smooth of relative dimension `r`.**
* `Stacks.LineBundle.Situation.isRelativeEffectiveCartierDivisor_ker_zeroSection`: **the image of
  the zero section of a line bundle is a relative effective Cartier divisor on the total space
  over the base**, part of clause (1) of [Stacks, Tag 0F96].

## References

* [Stacks Project, Tag 02G2](https://stacks.math.columbia.edu/tag/02G2)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The projection of affine `r`-space over a scheme is smooth of relative dimension `r`: the
polynomial ring in `r` variables over `ℤ` is standard smooth of relative dimension `r`, and
smoothness of relative dimension `r` is stable under base change. -/
theorem smoothOfRelativeDimension_affineSpaceOver (T : Scheme.{u}) (r : ℕ) :
    SmoothOfRelativeDimension r (𝔸(ULift.{u} (Fin r); T) ↘ T) := by
  set g := Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} (Fin r))
    (R := ULift.{u} ℤ))) with hg
  have hC : SmoothOfRelativeDimension r g := by
    rw [hg, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension r)]
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    change (algebraMap (ULift.{u} ℤ)
      (MvPolynomial (ULift.{u} (Fin r)) (ULift.{u} ℤ))).IsStandardSmoothOfRelativeDimension r
    rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv r
      (MvPolynomial.renameEquiv (ULift.{u} ℤ) (Equiv.ulift.{u, 0} (α := Fin r)).symm)
  have hterm : SmoothOfRelativeDimension r
      (terminal.from (Spec (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin r)) (ULift.{u} ℤ))))) := by
    have _ := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal
      (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))))
    have _ := hC
    have h : SmoothOfRelativeDimension (r + 0)
        (g ≫ terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) := inferInstance
    rwa [Nat.add_zero, terminal.comp_from] at h
  have _ : MorphismProperty.IsStableUnderBaseChangeAlong
      (@SmoothOfRelativeDimension r : MorphismProperty Scheme.{u}) (terminal.from T) :=
    ⟨fun pb hpb ↦ (smoothOfRelativeDimension_isStableUnderBaseChange r).of_isPullback pb hpb⟩
  exact MorphismProperty.pullback_fst
    (P := (@SmoothOfRelativeDimension r : MorphismProperty Scheme.{u})) _ _ hterm

/-- **An affine-space bundle of rank `r` is smooth of relative dimension `r`.** Smoothness of
relative dimension `r` is Zariski-local on the target, so local triviality reduces the claim to
the projection of affine `r`-space over a base. -/
theorem smoothOfRelativeDimension_of_isAffineSpaceBundle {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    (h : IsAffineSpaceBundle f r) : AlgebraicGeometry.SmoothOfRelativeDimension r f := by
  have _ : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension r : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @SmoothOfRelativeDimension r)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension r))
  exact morphismProperty_of_isAffineSpaceBundle (@SmoothOfRelativeDimension r) f r
    (fun T ↦ smoothOfRelativeDimension_affineSpaceOver T r) h

end Stacks.Chow

namespace Stacks.LineBundle

/-- **The total space of a line bundle is smooth of relative dimension one over the base**: it is
an affine-space bundle of rank one. -/
theorem Situation.smoothOfRelativeDimension_totalSpaceToBase (D : Situation.{u}) :
    AlgebraicGeometry.SmoothOfRelativeDimension 1 D.totalSpaceToBase :=
  Stacks.Chow.smoothOfRelativeDimension_of_isAffineSpaceBundle _ 1
    D.isAffineSpaceBundle_totalSpaceToBase

/-- **The image of the zero section of a line bundle is a relative effective Cartier divisor**,
part of clause (1) of [Stacks, Tag 0F96]. The projection of the total space is smooth of relative
dimension one, and the closed subscheme cut out by the zero section is finite locally free over
the base because the projection restricts on it to the comparison isomorphism with the base; so
[Stacks, Tag 0B9D] applies. -/
@[stacks 0F96 "(1), the zero section is a relative effective Cartier divisor"]
theorem Situation.isRelativeEffectiveCartierDivisor_ker_zeroSection (D : Situation.{u}) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor D.totalSpaceToBase
      D.zeroSection.ker := by
  have _ : AlgebraicGeometry.SmoothOfRelativeDimension 1 D.totalSpaceToBase :=
    D.smoothOfRelativeDimension_totalSpaceToBase
  have _ := Stacks.Chow.isIso_lift_zeroSection D
  set g := IsClosedImmersion.lift D.zeroSection D.zeroSection.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι D.zeroSection.ker).ge
  have hrw : D.zeroSection.ker.subschemeι ≫ D.totalSpaceToBase = g := by
    rw [← IsClosedImmersion.lift_fac D.zeroSection D.zeroSection.ker.subschemeι
      (Scheme.IdealSheafData.ker_subschemeι D.zeroSection.ker).ge, Category.assoc,
      D.zeroSection_comp_totalSpaceToBase, Category.comp_id]
  have _ : Stacks.Morphisms.IsFiniteLocallyFree
      (D.zeroSection.ker.subschemeι ≫ D.totalSpaceToBase) := by
    rw [hrw]
    have _ := Stacks.Morphisms.isFiniteLocallyFreeOfRank_one_of_isIso g
    exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  exact isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree D.totalSpaceToBase
    D.zeroSection.ker

end Stacks.LineBundle

end
