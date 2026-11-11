module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.DominantRationalMaps
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericStalkCriterion

/-!
# The generic-stalk criterion for `S`-birationality

Let `X` and `Y` be irreducible schemes locally of finite presentation over a scheme `S`, with
generic points `x` and `y`. The following are equivalent:

1. `X` and `Y` are `S`-birational, that is, isomorphic in the category of irreducible schemes over
   `S` and dominant `S`-rational maps (`AlgebraicGeometry.Scheme.DominantBirationalOver`);
2. there are nonempty opens of `X` and `Y` which are isomorphic over `S`;
3. `x` and `y` map to the same point `s` of `S` and `𝒪_{X, x}` and `𝒪_{Y, y}` are isomorphic
   as `𝒪_{S, s}`-algebras.

## Main results

* `AlgebraicGeometry.Scheme.dominantBirationalOver_tfae_generic_stalk_iso`: the three conditions
  above are equivalent.

## Implementation notes

The equivalence of (1) and (2) is
`AlgebraicGeometry.Scheme.dominantBirationalOver_iff_exists_nonempty_open_iso`; that of (1) and
(3) passes through `AlgebraicGeometry.Scheme.dominantBirationalOver_iff_birationalOver` and
`AlgebraicGeometry.birationalOver_iff_generic_stalk_iso`.

## References

* [Stacks Project, Tag 0BAD](https://stacks.math.columbia.edu/tag/0BAD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- For irreducible schemes `X` and `Y` locally of finite presentation over `S`, with generic
points `x` and `y`, the following are equivalent: `X` and `Y` are `S`-birational (isomorphic in
the category of irreducible schemes over `S` and dominant `S`-rational maps); there are nonempty
opens of `X` and `Y` which are isomorphic over `S`; `x` and `y` map to the same point `s` of `S`
and the local rings `𝒪_{X, x}` and `𝒪_{Y, y}` are isomorphic as `𝒪_{S, s}`-algebras. -/
@[stacks 0BAD "Conditions (1), (2) and (3) of the lemma, with (1) the `S`-birationality of Tag
0A20."]
theorem dominantBirationalOver_tfae_generic_stalk_iso {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y]
    [LocallyOfFinitePresentation (X ↘ S)] [LocallyOfFinitePresentation (Y ↘ S)] :
    List.TFAE
      [DominantBirationalOver S X Y,
        ∃ (U : X.Opens) (V : Y.Opens),
          (U : Set X).Nonempty ∧ (V : Set Y).Nonempty ∧
            ∃ e : U.toScheme ≅ V.toScheme, e.hom ≫ V.ι ≫ Y ↘ S = U.ι ≫ X ↘ S,
        ∃ (h : (X ↘ S) (genericPoint X) = (Y ↘ S) (genericPoint Y))
          (e : X.presheaf.stalk (genericPoint X) ≅ Y.presheaf.stalk (genericPoint Y)),
            h ▸ ((X ↘ S).stalkMap (genericPoint X) ≫ e.hom) =
              (Y ↘ S).stalkMap (genericPoint Y)] := by
  tfae_have 1 ↔ 2 := dominantBirationalOver_iff_exists_nonempty_open_iso
  tfae_have 1 ↔ 3 :=
    dominantBirationalOver_iff_birationalOver.trans
      (birationalOver_iff_generic_stalk_iso (X ↘ S) (Y ↘ S))
  tfae_finish

end Scheme

end AlgebraicGeometry

end
