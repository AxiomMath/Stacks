module

public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# Separation of a representable morphism of algebraic spaces matches separation of schemes

Let `S` be a scheme and let `f : X ⟶ Y` be a representable morphism of algebraic spaces over
`S`.  There are two readings of "`f` is (quasi-)separated": the relative-diagonal one of
Stacks 03HL, which is `AlgebraicGeometry.Space.IsSeparated` and
`AlgebraicGeometry.Space.IsQuasiSeparated`, and the one of Stacks 03HA for a representable
morphism, which asks the property of every represented base change of `f` and is
`CategoryTheory.MorphismProperty.presheaf` applied to the inverse image of the scheme-level
property along `AlgebraicGeometry.BigFppfOver.toScheme`.  This file states the whole of
Stacks 03KY as a single result: such an `f` is locally separated, the two readings of
separatedness agree for it, the two readings of quasi-separatedness agree for it, and — the
source's concluding "in particular" — for a morphism of schemes over `S` the
relative-diagonal reading is (quasi-)separatedness of that morphism of schemes.

The "in particular" clause carries a hypothesis the rest of the statement does not, namely
that the morphism is one of schemes; a morphism of schemes over `S` is a morphism `m` of the
site, read as a morphism of algebraic spaces through `CategoryTheory.yoneda`, so inside the
single statement that clause appears as the assertion quantified over all such `m`, which is
the form the source's sentence has.

## Main results

* `AlgebraicGeometry.Space.separationProperties_of_relativelyRepresentable`: the whole of
  Stacks 03KY, both parts together with the concluding statement about morphisms of schemes,
  for a representable morphism of algebraic spaces over a scheme.

## References

* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03KY.** Let `S` be a scheme and let `f : X ⟶ Y` be a representable morphism of
algebraic spaces over `S`.  Then:

1. `f` is locally separated; and
2. `f` is separated in the sense of Stacks 03HL if and only if it is separated in the sense
   of Stacks 03HA, that is, if and only if every represented base change of `f` is a
   separated morphism of schemes, and likewise for quasi-separatedness.

In particular, a morphism `m` of schemes over `S` is (quasi-)separated in the sense of
Stacks 03HL, as the morphism of algebraic spaces `yoneda.map m`, if and only if it is
(quasi-)separated as a morphism of schemes.

Part (1) holds because the relative diagonal of a morphism of schemes is an immersion, by
Stacks 01KJ, and local separatedness of a morphism with algebraic source is tested on its
represented base changes, by Stacks 03KM, each of which is the Yoneda image of a morphism of
the site.  Part (2) is the equivalence of conditions (1) and (2) of Stacks 03KM for
separatedness and for quasi-separatedness, taken together with the fact that separatedness
and quasi-separatedness of the Yoneda image of a morphism of the site are those properties of
the underlying morphism of schemes; that last fact, stated for every morphism of the site, is
also the concluding assertion. -/
@[stacks 03KY]
theorem separationProperties_of_relativelyRepresentable
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : yoneda.relativelyRepresentable f) :
    IsLocallySeparated B S hS f ∧
      (IsSeparated B S hS f ↔
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@_root_.AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS))) f) ∧
      (IsQuasiSeparated B S hS f ↔
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@_root_.AlgebraicGeometry.QuasiSeparated.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS))) f) ∧
      ∀ (a b : BigFppfOver B S hS) (m : a ⟶ b),
        (IsSeparated B S hS (yoneda.map m) ↔
            _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map m)) ∧
          (IsQuasiSeparated B S hS (yoneda.map m) ↔
            _root_.AlgebraicGeometry.QuasiSeparated ((BigFppfOver.toScheme B S hS).map m)) :=
  ⟨isLocallySeparated_of_relativelyRepresentable B S hS f hX hY hf,
    isSeparated_iff_presheaf B S hS f hX hY hf,
    isQuasiSeparated_iff_presheaf B S hS f hX hY hf,
    fun _ _ m ↦ ⟨isSeparated_yoneda_map_iff B S hS m, isQuasiSeparated_yoneda_map_iff B S hS m⟩⟩

end AlgebraicGeometry.Space

end
