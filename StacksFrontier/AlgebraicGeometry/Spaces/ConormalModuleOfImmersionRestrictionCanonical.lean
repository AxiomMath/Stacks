module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalEtaleRestrictionSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersionFunctorial

/-!
# The change of ambient of the conormal module of an immersion is the canonical map of 04CP

Let `i : Z ⟶ X` be an immersion of algebraic spaces over `S`, let `φ : U ⟶ X` be étale and let
`Z_U = U ×_X Z` with projections `p : Z_U ⟶ Z` and `i_U : Z_U ⟶ U`.  [Stacks Project, Tag 04CO]
identifies `p^*𝒞_{Z/X}` with `𝒞_{Z_U/U}`, as
`AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso`.  This file proves that
that identification **is** the canonical map of [Stacks Project, Tag 04CP] of the cartesian
square, `AlgebraicGeometry.Space.conormalMapOfImmersions`.

The corresponding statement for the conormal **algebra** is proved, as
`AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso_hom_eq`, in every degree; its
own docstring says it is "what makes a change of ambient space an instance of the canonical map,
so that the composition law `AlgebraicGeometry.Space.conormalMapOfImmersions_comp` applies to it".
The conormal module of an immersion is the degree-one piece taken through the closed factorisation
of [Stacks Project, Tag 04CE], and both the 04CO isomorphism and the canonical map of 04CP are the
degree-one algebra data conjugated by the **same** bridge
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` at `i` and at `i_U`.  So the module
statement is the algebra statement conjugated, and the conjugation is a single `congrArg`; before
this file nothing in the tree computed the forward map of
`AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso` at all.

This is what the composition law of part (3) of [Stacks Project, Tag 04G2]
(`AlgebraicGeometry.Space.conormalMapOfImmersions_comp_of_comm`) needs in order to apply to a
change of ambient, which is the step the source's proof of part (2) of
[Stacks Project, Tag 04G2] takes.

## Main results

* `AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso_hom`: the forward map of
  [Stacks Project, Tag 04CO]'s isomorphism is
  `AlgebraicGeometry.Space.conormalMapOfImmersions` of the cartesian square.

No `@[stacks]` attribute is claimed: 04CO is registered where the isomorphism is built, and this
is the identification of that isomorphism with the canonical map rather than a clause of a tag.

## References

* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X ZU U : AlgebraicSpaces B S hS}

/-- **The change of ambient of the conormal module of an immersion is the canonical map of
[Stacks Project, Tag 04CP].**  The forward map of [Stacks Project, Tag 04CO]'s isomorphism
`AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso` is
`AlgebraicGeometry.Space.conormalMapOfImmersions` of the cartesian square.

Both sides are the degree-one conormal-algebra data of the square conjugated by the same bridge
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` at `i` and at `i_U`, so this is the
algebra-level identification
`AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso_hom_eq` carried through that
conjugation. -/
theorem conormalModuleOfImmersionEtaleRestrictionIso_hom (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hi : IsImmersion B S hS i.hom)
    (hφ : IsEtale B S hS φ.hom) :
    (conormalModuleOfImmersionEtaleRestrictionIso B S hS p iU i φ sq hi hφ).hom =
      conormalMapOfImmersions B S hS iU i p φ
        (isImmersion_of_isPullback B S hS sq hi) hi sq.w.symm :=
  (congrArg
      (fun t => (modulePullback B S hS p).map
            (conormalAlgebraOfImmersionPieceIso B S hS i hi 1).inv ≫ t ≫
          (conormalAlgebraOfImmersionPieceIso B S hS iU
            (isImmersion_of_isPullback B S hS sq hi) 1).hom)
      (conormalAlgebraEtaleRestrictionPieceIso_hom_eq B S hS p iU i φ sq hφ 1)).trans
    (conormalMapOfImmersions_eq B S hS iU i p φ
      (isImmersion_of_isPullback B S hS sq hi) hi sq.w.symm).symm

end AlgebraicGeometry.Space

end
