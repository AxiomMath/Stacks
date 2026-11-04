module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion

/-!
# Affine morphisms of algebraic spaces are fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`. A property of morphisms of algebraic
spaces over `S` is *local on the base* for one of the fpqc, fppf, syntomic, smooth or étale
topologies when it holds for a morphism exactly when it holds for the base change of that
morphism to every member of every covering family, that is, when it is Mathlib's
`CategoryTheory.MorphismProperty.IsLocalAtTarget` for the precoverage
`AlgebraicGeometry.Space.Topology.precoverage` of that topology. This file proves that affineness
of morphisms of algebraic spaces is fpqc local on the base, modulo one named hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc` is effective descent for affine
  morphisms along a finite fpqc covering of an affine object of the site.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_isPullback`: affineness of a morphism of presheaves
  on the big fppf site of `S` is stable under base change, and
  `AlgebraicGeometry.Space.isAffineHom_hom_of_isPullback` is the same statement in the
  category of algebraic spaces.
* `AlgebraicGeometry.Space.respectsIso_isAffineHom`: affineness of morphisms of algebraic
  spaces respects isomorphisms.
* `AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc`: given that hypothesis, affineness
  of morphisms of algebraic spaces over `S` is fpqc local on the base.

## Implementation notes

The index type `I` of a covering family lives in its own universe `v`, independent of the
universe `u` of the schemes. In `AlgebraicGeometry.Space.Topology.IsCovering` it is pinned by
the explicit family argument; in `AlgebraicGeometry.Space.Topology.precoverage` it is
existentially quantified, so `v` is a free universe parameter of that definition and has to be
supplied by every user. It is deliberately left free rather than pinned to `u` or to `u + 1`,
because a precoverage carries no size restriction of its own.

## References

* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041J](https://stacks.math.columbia.edu/tag/041J)
* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-! ### Base change of affine morphisms -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Affineness of a morphism of presheaves on the big fppf site of `S` is stable under base
change: in a Cartesian square of presheaves whose right-hand column is affine, the left-hand
column is affine. -/
theorem isAffineHom_of_isPullback {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {g : G' ⟶ G} {p : F' ⟶ F} {q : F' ⟶ G'} (h : IsPullback p q f g)
    (hf : IsAffineHom B S hS f) : IsAffineHom B S hS q := by
  intro Z k
  obtain ⟨W, p₀, q₀, hpb⟩ := hf Z (k ≫ g)
  exact ⟨W, _, q₀, hpb.of_right' h⟩

/-- Affineness of a morphism of presheaves is unchanged by precomposition with an
isomorphism. -/
theorem isAffineHom_iso_comp {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F' ⟶ F)
    [IsIso e] {f : F ⟶ G} (hf : IsAffineHom B S hS f) : IsAffineHom B S hS (e ≫ f) :=
  isAffineHom_of_isPullback (g := 𝟙 G)
    (IsPullback.of_horiz_isIso (fst := e) (snd := e ≫ f) ⟨by simp⟩) hf

/-- Affineness of a morphism of presheaves is unchanged by postcomposition with an
isomorphism. -/
theorem isAffineHom_comp_iso {F G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (e : G ⟶ G') [IsIso e] (hf : IsAffineHom B S hS f) : IsAffineHom B S hS (f ≫ e) :=
  isAffineHom_of_isPullback (g := inv e)
    (IsPullback.of_horiz_isIso (fst := 𝟙 F) (snd := f ≫ e) ⟨by simp⟩) hf

/-- Affineness of a morphism of algebraic spaces over `S` is stable under base change in the
category of algebraic spaces. -/
theorem isAffineHom_hom_of_isPullback {F G H K : AlgebraicSpaces B S hS}
    {f : F ⟶ H} {g : G ⟶ H} {p : K ⟶ F} {q : K ⟶ G} (h : IsPullback p q f g)
    (hf : IsAffineHom B S hS f.hom) : IsAffineHom B S hS q.hom :=
  isAffineHom_of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ h) hf

/-- Affineness of morphisms of algebraic spaces over `S` respects isomorphisms. -/
instance respectsIso_isAffineHom :
    MorphismProperty.RespectsIso
      (fun {X Y} (f : X ⟶ Y) => IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS)) :=
  MorphismProperty.RespectsIso.mk _
    (fun e _ hf => isAffineHom_iso_comp e.hom.hom hf)
    (fun e _ hf => isAffineHom_comp_iso e.hom.hom hf)

/-! ### Effective descent for affine morphisms along an fpqc covering -/

variable (B S hS) in
/-- *Effective descent for affine morphisms along an fpqc covering of an affine object of the
site.* Let `Z` be an affine object of the big fppf site of `S` and let `{Zⱼ → Z}` be a finite
fpqc covering of `Z` by affine objects of the site. Let `f : F ⟶ G` be a morphism of algebraic
spaces over `S` and let `k : h_Z ⟶ G`. If the base change of `f` along each composite
`h_{Zⱼ} → h_Z → G` is represented by an affine object of the site, then so is the base change
of `f` along `k`. -/
def IsEffectiveAffineDescentAlongFpqc : Prop :=
  ∀ (Z : BigAffineFppf B S hS) (𝒰 : PreZeroHypercover.{u + 1} Z), Finite 𝒰.I₀ →
    Presieve.map (BigAffineFppf.toScheme B S hS) 𝒰.presieve₀ ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj Z) →
    ∀ ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄, IsAlgebraicSpace B S hS F →
      IsAlgebraicSpace B S hS G → ∀ (f : F ⟶ G)
        (k : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ G),
        (∀ j : 𝒰.I₀, ∃ (W : BigAffineFppf B S hS)
            (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ F)
            (q : (BigAffineFppf.inclusion B S hS).obj W ⟶
              (BigAffineFppf.inclusion B S hS).obj (𝒰.X j)),
            IsPullback p (yoneda.map q) f
              (yoneda.map ((BigAffineFppf.inclusion B S hS).map (𝒰.f j)) ≫ k)) →
        ∃ (W : BigAffineFppf B S hS)
          (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ F)
          (q : (BigAffineFppf.inclusion B S hS).obj W ⟶
            (BigAffineFppf.inclusion B S hS).obj Z),
          IsPullback p (yoneda.map q) f k

/-! ### Affineness is fpqc local on the base -/

/-- Given effective descent for affine morphisms along the finite fpqc coverings of the affine
objects of the site, affineness of morphisms of algebraic spaces over `S` is fpqc local on the
base: a morphism of algebraic spaces is affine exactly when its base change to every member of
some fpqc covering of its target is affine. -/
theorem isAffineHom_isLocalAtTarget_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hdesc : IsEffectiveAffineDescentAlongFpqc B S hS) :
    MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fpqc.precoverage.{u, v} B S hS) where
  pullbackSnd _ _ hf := isAffineHom_hom_of_isPullback (IsPullback.of_hasPullback _ _) hf
  of_forall_pullbackSnd := by
    rintro T A f R ⟨I, Yi, gi, rfl, -, -, -, hfpqc⟩ hbc Z k
    obtain ⟨𝒰, hfin, hmem, href⟩ := hfpqc Z k
    refine hdesc Z 𝒰 hfin hmem A.property T.property f.hom k fun j => ?_
    obtain ⟨i, a, ha⟩ := href j
    obtain ⟨W, p₀, q₀, hpb⟩ :=
      hbc (g := gi i) (Presieve.ofArrows.mk i) (𝒰.X j) a
    refine ⟨W, p₀ ≫ (pullback.fst f (gi i)).hom, q₀, ?_⟩
    rw [← ha]
    exact hpb.paste_horiz
      (AlgebraicSpaces.isPullback_hom _ _ _ (IsPullback.of_hasPullback f (gi i)))

end AlgebraicGeometry.Space

end
