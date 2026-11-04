module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# Smooth morphisms of algebraic spaces of a given relative dimension

A morphism of algebraic spaces over `S` is *smooth of relative dimension `d`* if it is smooth
(Stacks 03ZC) and has relative dimension `d` at every point of its source in the sense of
Stacks 04NM and Stacks 06LR. This file packages that condition as a property of morphisms of the
category of algebraic spaces over `S` and proves that it is stable under base change and local
on the base for the fppf topology, which are the two conditions under which a property of
morphisms of algebraic spaces has a relative counterpart for 1-morphisms of categories fibred in
groupoids representable by algebraic spaces (Stacks 03YK).

## Main definitions

* `AlgebraicGeometry.Space.IsSmoothOfRelativeDimension`: smooth, of relative dimension `d` at
  every point.
* `AlgebraicGeometry.Space.smoothOfRelativeDimensionProperty`: the same as a
  `CategoryTheory.MorphismProperty` of `AlgebraicGeometry.AlgebraicSpaces`.

## Main results

* `AlgebraicGeometry.Space.isSmoothOfRelativeDimension_of_isPullback`: the condition is stable
  under base change, by Stacks 03ZE for smoothness and part (1) of Stacks 04NS for the relative
  dimension.
* `AlgebraicGeometry.Space.smoothOfRelativeDimension_isLocalAtTarget_fppf`: it is local on the
  base for the fppf topology.

## Implementation notes

Locality on the base is reduced to the two ingredients that already exist: smoothness is fpqc
local on the base (Stacks 0429), and an fpqc covering is jointly surjective on points, so every
point of the source of `f` lifts to a point of one of the base changes, where part (1) of
Stacks 04NS computes the relative dimension. Smoothness is used there to make `f` locally of
finite type, which is what Stacks 04NS asks of the morphism being base changed.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of algebraic spaces over `S` is *smooth of relative dimension `d`* when it is
smooth and has relative dimension `d` at every point of its source. -/
abbrev IsSmoothOfRelativeDimension (d : ℕ) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) : Prop :=
  IsSmooth B S hS f ∧ HasRelativeDimension d B S hS f

/-- Smoothness of relative dimension `d`, as a property of morphisms of the category of
algebraic spaces over `S`. -/
abbrev smoothOfRelativeDimensionProperty (d : ℕ) : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsSmoothOfRelativeDimension B S hS d f.hom

/-- **Smoothness of relative dimension `d` is stable under base change.** If `f` is smooth of
relative dimension `d` and `p` is a base change of `f`, then `p` is smooth of relative dimension
`d`. -/
theorem isSmoothOfRelativeDimension_of_isPullback (d : ℕ) {W X Z Y : AlgebraicSpaces B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsSmoothOfRelativeDimension B S hS d f.hom) :
    IsSmoothOfRelativeDimension B S hS d p.hom :=
  ⟨(smoothMorphismProperty B S hS).of_isPullback sq.flip hf.1, fun w =>
    (hasRelativeDimensionAt_iff_of_isPullback' B S hS (d : ℕ∞)
      (AlgebraicSpaces.isPullback_hom B S hS sq) X.property Y.property Z.property
      (isLocallyOfFiniteType_of_isSmooth B S hS hf.1) w).2 (hf.2 _)⟩

/-- Smoothness of relative dimension `d` is stable under base change. -/
instance smoothOfRelativeDimensionProperty_isStableUnderBaseChange (d : ℕ) :
    (smoothOfRelativeDimensionProperty B S hS d).IsStableUnderBaseChange where
  of_isPullback sq hg := isSmoothOfRelativeDimension_of_isPullback B S hS d sq.flip hg

/-- **Smoothness of relative dimension `d` is local on the base for the fppf topology.** -/
instance smoothOfRelativeDimension_isLocalAtTarget_fppf (d : ℕ) :
    (smoothOfRelativeDimensionProperty B S hS d).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, v} B S hS) := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff
    (P := smoothOfRelativeDimensionProperty B S hS d)
    (K := Topology.fppf.precoverage.{u, v} B S hS) ?_
  intro X Y f R hR
  constructor
  · intro hf U g _ _
    exact isSmoothOfRelativeDimension_of_isPullback B S hS d
      (IsPullback.of_hasPullback f g).flip hf
  · intro h
    have hsm : IsSmooth B S hS f.hom :=
      (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
        (P := smoothMorphismProperty B S hS) hR).2 (fun g _ hg => (h g hg).1)
    refine ⟨hsm, fun x => ?_⟩
    obtain ⟨I, Yi, g, hRg, -, -, hcover⟩ := fppfPrecoverage_le_fpqcPrecoverage B S hS Y hR
    obtain ⟨i, yi, hyi⟩ := (isJointlySurjective_iff B S hS _ _).1
      (isJointlySurjective_of_isFpqcCovering B S hS (fun i => (g i).hom) hcover)
      (pointsMap B S hS X.1 f.hom x)
    have hmem : R (g i) := by
      rw [hRg]
      exact ⟨i⟩
    obtain ⟨w, hwx, hwy⟩ := exists_point_of_isPullback B S hS
      (IsPullback.of_hasPullback f (g i)) x yi hyi.symm
    have key := (hasRelativeDimensionAt_iff_of_isPullback' B S hS (d : ℕ∞)
      (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f (g i)).flip)
      X.property Y.property (Yi i).property
      (isLocallyOfFiniteType_of_isSmooth B S hS hsm) w).1 ((h (g i) hmem).2 w)
    rwa [hwx] at key

end AlgebraicGeometry.Space

end
