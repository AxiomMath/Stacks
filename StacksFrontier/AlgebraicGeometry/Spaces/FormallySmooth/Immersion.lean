module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An immersion of algebraic spaces is formally unramified

Let `S` be a scheme and let `i : Z ⟶ X` be an immersion of algebraic spaces over `S`, that is a
representable morphism every represented base change of which is an immersion of schemes.  Then
`i` is formally unramified: a square-zero closed immersion of affine objects of the site admits
at most one lift against `i`.

This is the first clause of [Stacks Project, Tag 0608].  The argument of the source is the one
carried out below: an immersion of schemes is unramified, so `i` is an unramified representable
morphism, and an unramified representable morphism is formally unramified by
[Stacks Project, Tag 04AL].

## Main results

* `AlgebraicGeometry.unramified_of_isImmersion`: an immersion of schemes is unramified.
* `AlgebraicGeometry.Space.formallyUnramified_of_isImmersion`: **the first clause of
  [Stacks Project, Tag 0608]**, an immersion of algebraic spaces is formally unramified.

## Implementation notes

No hypothesis is placed on the source or the target beyond the morphism being an immersion:
`AlgebraicGeometry.Space.FormallyUnramified` and `AlgebraicGeometry.Space.IsImmersion` are
conditions on a morphism of presheaves on the big fppf site, and
`AlgebraicGeometry.Space.formallyUnramified_of_unramified` needs neither presheaf to be an
algebraic space.  The statement below is therefore stronger than the clause of the source, which
assumes both are algebraic spaces.

The passage from the scheme-level implication to the implication between the two conditions on
represented base changes is `CategoryTheory.MorphismProperty.relative_monotone` composed with
`CategoryTheory.MorphismProperty.monotone_inverseImage`, which is how
`AlgebraicGeometry.Space.formallyUnramified_comp_of_etale` passes from étaleness to
unramifiedness one line at a time.

## Where the other clauses are proved

The second clause of [Stacks Project, Tag 0608] is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningImmersion.lean`, as
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_infinitesimalNeighbourhood`, and the
third in `StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningImmersionConormal.lean`, as
`AlgebraicGeometry.Space.conormalSheafIsoConormalModule`; each carries the tag with a clause
string naming it.

## References

* [Stacks Project, Tag 0608](https://stacks.math.columbia.edu/tag/0608)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 05ZX](https://stacks.math.columbia.edu/tag/05ZX)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An immersion of schemes is unramified.

An immersion is a monomorphism, so its relative diagonal is an isomorphism and it is formally
unramified, and it is locally of finite type; now apply [Stacks Project, Tag 02HE]. -/
@[ega "IV 17.1.3" "(i), special case", sga "1 I 3.5" "more general"]
theorem unramified_of_isImmersion {X Y : Scheme.{u}} (g : X ⟶ Y) [IsImmersion g] :
    Unramified g :=
  (unramified_iff_locallyOfFiniteType_and_formallyUnramified g).mpr
    ⟨inferInstance, inferInstance⟩

namespace Space

/-- **The first clause of [Stacks Project, Tag 0608].**  An immersion of algebraic spaces over
`S` is formally unramified.

An immersion is a representable morphism whose every represented base change is an immersion of
schemes, hence unramified by `AlgebraicGeometry.unramified_of_isImmersion`; a representable
unramified morphism is formally unramified by [Stacks Project, Tag 04AL]. -/
@[stacks 0608 "formally unramified"]
theorem formallyUnramified_of_isImmersion (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : Z ⟶ X)
    (hi : IsImmersion B S hS i) :
    FormallyUnramified i :=
  formallyUnramified_of_unramified B S hS i
    (MorphismProperty.relative_monotone (F := CategoryTheory.yoneda)
      (MorphismProperty.monotone_inverseImage _
        (fun _ _ f hf => @unramified_of_isImmersion _ _ f hf)) i hi)

end Space

end AlgebraicGeometry

end
