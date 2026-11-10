module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.SyntomicDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.PerfectComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.PerfectFlatBaseChange

/-!
# Composition and flat base change of perfect morphisms of algebraic spaces

Perfectness of a morphism of algebraic spaces over `S` is preserved by composition, and by base
change along a flat morphism of algebraic spaces. It is *not* preserved by arbitrary base change,
so flatness of the base of the base change is used in an essential way.

## Main results

* `AlgebraicGeometry.Space.IsPerfect.of_isPullback_of_isFlat`: **Stacks 06C0**, a flat base
  change of a perfect morphism of algebraic spaces is perfect, for an arbitrary cartesian square.
* `AlgebraicGeometry.Space.IsPerfect.pullback_snd`: the same in the `pullback` spelling.
* `AlgebraicGeometry.Space.IsPerfect.comp`: **Stacks 06C1**, a composition of perfect morphisms
  of algebraic spaces is perfect.

## Implementation notes

Both statements reduce to the corresponding statements for morphisms of schemes, Stacks 0688 and
0689, exactly as the source's proofs indicate; what the reduction needs beyond them is that
perfectness of morphisms of *schemes* is local on the source for the étale topology, which is
`AlgebraicGeometry.Perfect.isLocalAtSource_etalePrecoverage`. Perfectness of a morphism of
algebraic spaces is the every-étale-chart condition of Stacks 03MJ, so a chart square built from
charts of the data at hand is in general only one whose chart of the source is surjective, and
upgrading that to every square is what étale locality provides.

For the composite the reduction is Stacks 0AML,
`AlgebraicGeometry.Space.isPerfect_comp`, whose hypothesis is the full étale-locality structure
of Stacks 04QZ; that structure is obtained from locality on the source alone by
`AlgebraicGeometry.perfect_isEtaleLocalOnSourceAndTarget`. For the flat base change it is
`AlgebraicGeometry.Space.isPerfect_of_isPullback_of_isFlat`.

## References

* [Stacks Project, Tag 06C0](https://stacks.math.columbia.edu/tag/06C0)
* [Stacks Project, Tag 06C1](https://stacks.math.columbia.edu/tag/06C1)
* [Stacks Project, Tag 0688](https://stacks.math.columbia.edu/tag/0688)
* [Stacks Project, Tag 0689](https://stacks.math.columbia.edu/tag/0689)
* [Stacks Project, Tag 06BZ](https://stacks.math.columbia.edu/tag/06BZ)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_PerfectStability :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- The pullback of a cospan of presheaves on the big fppf site over `S`, found directly. -/
local instance (priority := high) hasPullback_presheaf_PerfectStability
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 06C0.** A flat base change of a perfect morphism of algebraic spaces over `S` is
perfect: in a cartesian square with `g : Y ⟶ Z` perfect and `f : X ⟶ Z` flat, the base change
`g' : Y' ⟶ X` of `g` along `f` is perfect. -/
@[stacks 06C0]
theorem IsPerfect.of_isPullback_of_isFlat
    {X Y Y' Z : AlgebraicSpaces B S hS} {f : X ⟶ Z} {g : Y ⟶ Z} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hflat : IsFlat B S hS f.hom) (hf : IsPerfect B S hS g.hom) :
    IsPerfect B S hS g'.hom :=
  isPerfect_of_isPullback_of_isFlat B S hS
    _root_.AlgebraicGeometry.Perfect.isLocalAtSource_etalePrecoverage sq hflat hf

/-- **Stacks 06C0** in the `pullback` spelling: if `f : X ⟶ Y` is a perfect morphism of algebraic
spaces over `S` and `g : Y' ⟶ Y` is flat, then the projection `X ×_Y Y' ⟶ Y'` is perfect. -/
@[stacks 06C0 "pullback spelling"]
theorem IsPerfect.pullback_snd {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hg : IsFlat B S hS g.hom) (hf : IsPerfect B S hS f.hom) :
    IsPerfect B S hS (Limits.pullback.snd f.hom g.hom) :=
  isPerfect_pullback_snd B S hS
    _root_.AlgebraicGeometry.Perfect.isLocalAtSource_etalePrecoverage f g hg hf

/-- **Stacks 06C1.** A composition of perfect morphisms of algebraic spaces over `S` is
perfect. -/
@[stacks 06C1]
theorem IsPerfect.comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsPerfect B S hS f) (hg : IsPerfect B S hS g) :
    IsPerfect B S hS (f ≫ g) :=
  isPerfect_comp B S hS
    (_root_.AlgebraicGeometry.perfect_isEtaleLocalOnSourceAndTarget
      _root_.AlgebraicGeometry.Perfect.isLocalAtSource_etalePrecoverage)
    hX hY hZ f g hf hg

end AlgebraicGeometry.Space

end
