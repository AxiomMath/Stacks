module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableProperty

/-!
# Weakening the property of a representable morphism of presheaves

Let `a : F ⟶ G` be a representable morphism of presheaves on the big fppf site of a scheme `S`,
and let `P`, `P'` be properties of morphisms of schemes such that `P f` implies `P' f` for every
morphism of schemes `f`. If `a` has `P` in the sense of Stacks 025V, then `a` has `P'`.

## Main results

* `AlgebraicGeometry.Space.HasSchemeProperty.of_le`: **Stacks 02YO**.

## Implementation notes

Stacks 025V applies the definition only to properties which are stable under base change and
fppf local on the base; neither condition is needed here, so neither is imposed. The
representability of `a` is part of `AlgebraicGeometry.Space.HasSchemeProperty`, so it is not a
separate hypothesis. The statement is the instance of
`CategoryTheory.MorphismProperty.relative_monotone` for the Yoneda embedding of the big fppf
site of `S`, the implication being transported along the functor to schemes.

## References

* [Stacks Project, Tag 02YO](https://stacks.math.columbia.edu/tag/02YO)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 02YO.** Let `a : F ⟶ G` be a representable morphism of presheaves on the big fppf
site of `S`, and let `P`, `P'` be properties of morphisms of schemes such that `P f` implies
`P' f` for every morphism of schemes `f : X ⟶ Y`. If `a` has property `P` then `a` has
property `P'`. -/
theorem HasSchemeProperty.of_le {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {P P' : MorphismProperty Scheme.{u}} (h : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), P f → P' f)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G} (ha : HasSchemeProperty B S hS P a) :
    HasSchemeProperty B S hS P' a :=
  MorphismProperty.relative_monotone (fun _ _ _f hf ↦ h _ hf) a ha

end AlgebraicGeometry.Space

end
