module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.AffineExistence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposCompTwoIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleRingedToposCompConjugate
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleRingedToposTransport

/-!
# Recovering a morphism of representable algebraic spaces over a base

Let `U` and `W` be objects of a big fppf site over `S`, read as representable algebraic spaces,
let `g_U : U ⟶ V₀` and `g_W : W ⟶ V₀` be morphisms to a third object, and let `ρ` be a locally
ringed morphism of the small étale ringed topoi of `U` and `W` which is 2-compatible with the
two structure morphisms.  If the underlying scheme of `W` is affine, then `ρ` is induced by a
morphism `U ⟶ W` **of the big fppf site**, that is, by a morphism over `S`.

This is the affine-chart case of [Stacks Project, Tag 04KL], and it is where the passage from an
absolute morphism of schemes to a morphism over the base happens.
[Stacks Project, Tag 04I6] produces only an *absolute* morphism of schemes
`a : U.left ⟶ W.left`; the 2-compatibility, carried to the scheme level by
`AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHomComp` and turned into an equality by
[Stacks Project, Tag 04LW], gives `a ≫ g_W = g_U`, and hence `a ≫ W.hom = U.hom`.  That
equation is exactly the datum a morphism of the slice category carries beyond its underlying
morphism of schemes, so `a` lifts.

## Main results

* `AlgebraicGeometry.Space.eq_comp_of_twoIso_schemeOfRepresentedRingedToposHom` — the
  2-compatibility, read as an equality of morphisms of schemes.
* `AlgebraicGeometry.Space.exists_hom_twoIso_of_isLocallyRinged_of_twoIso` — the affine-chart
  case of [Stacks Project, Tag 04KL]: the morphism over `S` and the 2-isomorphism.

## Implementation notes

The 2-compatibility is stated with the two structure morphisms presented as
`AlgebraicGeometry.Space.representedSpaceMap`s, which is the presentation
`AlgebraicGeometry.Space.twoIsoSchemeOfSmallEtaleRingedToposHom` converts to the scheme level.
The target of the structure morphisms is an arbitrary object `V₀` rather than the terminal one,
which costs nothing and makes the statement usable before the base is identified.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04LW](https://stacks.math.columbia.edu/tag/04LW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U W V₀ : BigFppfOver B S hS} (gU : U ⟶ V₀) (gW : W ⟶ V₀)
    (ρ : RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩))

/-- **The 2-compatibility of `ρ` with the structure morphisms, read as an equality of morphisms
of schemes.**  If `ρ` is 2-isomorphic over `V₀` to the structure morphisms, and `a` is a
morphism of schemes whose conjugated morphism of small étale ringed topoi is 2-isomorphic to the
conjugate of `ρ`, then `a ≫ g_W = g_U` on underlying schemes.

The chain is: the scheme-level composition 2-isomorphism
`AlgebraicGeometry.smallEtaleRingedToposHomCompTwoIso` splits `a ≫ g_W`; the conjugation
compatibility `AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHomComp` turns the
composite of conjugates into the conjugate of the composite; the hypothesis is transported by
`AlgebraicGeometry.Space.twoIsoSchemeOfRepresentedRingedToposHom`; and
[Stacks Project, Tag 04LW] concludes. -/
theorem eq_comp_of_twoIso_schemeOfRepresentedRingedToposHom
    (hcompat : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS gW)) ρ)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS gU)))
    (a : U.left ⟶ W.left)
    (ta : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (schemeOfRepresentedRingedToposHom B S hS U W ρ)
      (AlgebraicGeometry.smallEtaleRingedToposHom (associatedBigEtaleSite B) a)) :
    a ≫ gW.left = gU.left := by
  refine AlgebraicGeometry.eq_of_smallEtaleRingedToposHom_twoIso (associatedBigEtaleSite B)
    (a ≫ gW.left) gU.left ?_
  have c1 := AlgebraicGeometry.smallEtaleRingedToposHomCompTwoIso (associatedBigEtaleSite B)
    U.left W.left V₀.left a gW.left
  have c2 := RingedToposHom.TwoIso.whiskerRight ta.symm
    (AlgebraicGeometry.smallEtaleRingedToposHom (associatedBigEtaleSite B) gW.left)
  have c3 := RingedToposHom.TwoIso.whiskerLeft
    (C := _root_.AlgebraicGeometry.RingedSite.toRingedTopos
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V₀) V₀.left.property))
    (schemeOfRepresentedRingedToposHom B S hS U W ρ)
    (twoIsoSchemeOfSmallEtaleRingedToposHom B S hS W V₀ gW).symm
  have c4 := schemeOfRepresentedRingedToposHomComp B S hS U W V₀ ρ
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS gW))
  have c5 := twoIsoSchemeOfRepresentedRingedToposHom B S hS U V₀ hcompat
  have c6 := twoIsoSchemeOfSmallEtaleRingedToposHom B S hS U V₀ gU
  exact c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6))))

/-- **The affine-chart case of [Stacks Project, Tag 04KL].**  A locally ringed morphism `ρ` of
the small étale ringed topoi of two representable algebraic spaces over a big fppf site, which
is 2-compatible with a pair of structure morphisms to a third object, is induced by a morphism
`U ⟶ W` *of the big fppf site* — a morphism over `S` — provided the underlying scheme of `W` is
affine.

Affineness of `W` is what [Stacks Project, Tag 04I6] needs; `U` is arbitrary.  The morphism over
`S` is the absolute morphism of schemes of [Stacks Project, Tag 04I6] together with the equality
`AlgebraicGeometry.Space.eq_comp_of_twoIso_schemeOfRepresentedRingedToposHom`, which is the
datum a morphism of the slice carries beyond its underlying morphism of schemes. -/
theorem exists_hom_twoIso_of_isLocallyRinged_of_twoIso
    (hW : IsAffineOver B S hS W)
    (hρ : ρ.IsLocallyRinged)
    (hcompat : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS gW)) ρ)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS gU))) :
    ∃ g : U ⟶ W, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} ρ
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))) := by
  have : IsAffine ((BigFppfOver.forget B S hS).obj W).obj := hW
  obtain ⟨a, ⟨ta⟩, -⟩ :=
    AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_isLocallyRinged (associatedBigEtaleSite B)
      (schemeOfRepresentedRingedToposHom B S hS U W ρ)
      (isLocallyRinged_schemeOfRepresentedRingedToposHom B S hS U W ρ hρ)
  have hgW : a ≫ gW.left = gU.left :=
    eq_comp_of_twoIso_schemeOfRepresentedRingedToposHom B S hS gU gW ρ hcompat a ta
  have hover : a ≫ W.hom = U.hom := by
    rw [← Over.w gW, ← Category.assoc, hgW]
    exact Over.w gU
  exact ⟨Over.homMk a hover,
    ⟨reflectTwoIsoSmallEtaleRingedToposHom B S hS U W (Over.homMk a hover) ta⟩⟩

end AlgebraicGeometry.Space

end
