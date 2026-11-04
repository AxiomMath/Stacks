module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# Reducing the faithfulness of Stacks 04M6 to a scheme source

Stacks 04M6 says that two morphisms `a, b : X ⟶ Y` of algebraic spaces over a scheme `S` whose
morphisms of small étale ringed topoi are 2-isomorphic are equal.  This file reduces that
statement to the case in which the *source* is the algebraic space of a scheme.

Two things make the reduction work.  First, the construction of the morphism of small étale
ringed topoi is functorial: `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compTwoIso` is the
2-isomorphism between the composite of the two morphisms of ringed topoi and the morphism of the
composite, and whiskering a 2-isomorphism `t : a_{small} ≅ b_{small}` by it gives a
2-isomorphism `(p ≫ a)_{small} ≅ (p ≫ b)_{small}` for any `p : W ⟶ X`.  Second, an étale scheme
atlas of `X` is an epimorphism of fppf sheaves, so two morphisms out of `X` that agree after
composing with it are equal.

## Main results

* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compTwoIso`: the composition law of
  Stacks 03G8 read as a 2-isomorphism of morphisms of ringed topoi.
* `AlgebraicGeometry.Space.twoIso_comp_left`: a 2-isomorphism of the morphisms of ringed topoi
  of `a` and `b` whiskered by a morphism `p` into their source.
* `AlgebraicGeometry.Space.hom_ext_of_surjectiveEtale_atlas`: two morphisms of algebraic spaces
  that agree after composition with a surjective étale morphism from a scheme are equal.
* `AlgebraicGeometry.Space.eq_of_twoIso_of_schemeSource`: **the reduction** — if Stacks 04M6
  holds whenever the source is the algebraic space of a scheme, then it holds for every pair of
  morphisms of algebraic spaces.

## Implementation notes

The composition 2-isomorphism is assembled from the two halves that are already proved: its
underlying isomorphism of direct images is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` (Stacks 03G2 part (3) at the universe of
the structure rings), and its compatibility with the structure maps is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp` with the ring operations
forgotten, which is where
`AlgebraicGeometry.Space.underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom`
identifies the forgetful image of the comparison of direct images of sheaves of commutative
rings with the isomorphism of direct images of sheaves of sets it was built from.

The atlas cancellation is `AlgebraicGeometry.Space.hom_ext_of_etale_atlas`, which rests on the
descent of morphisms along an étale scheme atlas: the atlas is an epimorphism of fppf sheaves,
and morphisms of algebraic spaces are morphisms of fppf sheaves.

What the reduction does *not* do is prove the case it reduces to.  A morphism out of the
algebraic space of a scheme is automatically representable — the diagonal of an algebraic space
is representable — so the remaining case is covered by the chart comparison of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleTwoIsoChartComparison.lean` together with the
compatibility of the chart isomorphism with the two chart projections, which is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleTwoIsoAffineCover.lean`.  Stacks 04M6 itself is
`AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso` there.

## References

* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The composition law as a 2-isomorphism -/

/-- **Stacks 03G8, the composition law as a 2-isomorphism.** The composite of the morphisms of
small étale ringed topoi of `f : X ⟶ Y` and `g : Y ⟶ Z` is 2-isomorphic to the morphism of
small étale ringed topoi of `f ≫ g`. -/
noncomputable def smallEtaleRingedToposHom_compTwoIso {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f))
      (smallEtaleRingedToposHom B S hS (f ≫ g)) where
  e := smallToposMorphismTypeU_comp B S hS f g
  commutes := by
    have h := congrArg (fun m ↦ (smallEtaleRingedTopos B S hS Z).forgetRing.map m)
      (smallEtaleRingedToposHom_comp_fSharp B S hS f g)
    have h2 : (smallEtaleRingedTopos B S hS Z).forgetRing.map
        ((smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app
          (smallEtaleRingedTopos B S hS X).O) =
        (smallToposMorphismTypeU_comp B S hS f g).hom.app (structureSetSheaf B S hS X) :=
      underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
        (SmallEtale.topology B S hS Z.1) _ (smallToposMorphismTypeU_comp B S hS f g)
    simp only [CategoryTheory.Functor.map_comp, h2] at h
    exact h

/-- A 2-isomorphism of the morphisms of small étale ringed topoi of `a, b : X ⟶ Y`, whiskered
by a morphism `p : W ⟶ X`: the morphisms of small étale ringed topoi of `p ≫ a` and `p ≫ b` are
2-isomorphic. -/
noncomputable def twoIso_comp_left {W X Y : AlgebraicSpaces B S hS} (p : W ⟶ X) {a b : X ⟶ Y}
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS a)
      (smallEtaleRingedToposHom B S hS b)) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS (p ≫ a))
      (smallEtaleRingedToposHom B S hS (p ≫ b)) :=
  ((smallEtaleRingedToposHom_compTwoIso B S hS p a).symm.trans
      (t.whiskerLeft (smallEtaleRingedToposHom B S hS p))).trans
    (smallEtaleRingedToposHom_compTwoIso B S hS p b)

/-! ### Cancelling an étale scheme atlas -/

/-- Two morphisms of algebraic spaces which agree after composition with a surjective étale
morphism from the algebraic space of a scheme are equal.

This is `AlgebraicGeometry.Space.hom_ext_of_etale_atlas` for the full subcategory of algebraic
spaces: a morphism of algebraic spaces is a morphism of the underlying fppf sheaves, and two of
them are equal as soon as those are. -/
theorem hom_ext_of_surjectiveEtale_atlas {X Y : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} (p : schemeSpace U ⟶ X)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p.hom)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p.hom)
    (a b : X ⟶ Y) (h : p ≫ a = p ≫ b) : a = b :=
  ObjectProperty.hom_ext _ <| hom_ext_of_etale_atlas B S hS X.property.isSheaf Y.property.isSheaf
    p.hom hsurj hetale (congrArg (fun k : schemeSpace U ⟶ Y => k.hom) h)

/-! ### The reduction -/

/-- **The reduction of Stacks 04M6 to a scheme source.** If two morphisms *out of the algebraic
space of a scheme* whose morphisms of small étale ringed topoi are 2-isomorphic are always
equal, then the same holds for two morphisms of arbitrary algebraic spaces.

An algebraic space has a surjective étale morphism from the algebraic space of a scheme by
definition (Stacks 025Y); composing a 2-isomorphism with it reduces the general statement to
the hypothesis, and the atlas cancels. -/
theorem eq_of_twoIso_of_schemeSource
    (H : ∀ (U : BigFppfOver B S hS) (Z : AlgebraicSpaces B S hS)
      (a b : schemeSpace U ⟶ Z),
      RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS a)
        (smallEtaleRingedToposHom B S hS b) → a = b)
    {X Y : AlgebraicSpaces B S hS} (a b : X ⟶ Y)
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS a)
      (smallEtaleRingedToposHom B S hS b)) : a = b := by
  obtain ⟨U, p, hsurj, hetale⟩ := X.property.exists_atlas
  let P : schemeSpace U ⟶ X := ObjectProperty.homMk p
  refine hom_ext_of_surjectiveEtale_atlas B S hS P hsurj hetale a b ?_
  exact H U Y (P ≫ a) (P ≫ b) (twoIso_comp_left B S hS P t)

end AlgebraicGeometry.Space

end
