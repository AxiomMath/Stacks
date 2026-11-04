module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange

/-!
# Quasi-separatedness and finite presentation are stable under base change

A morphism of algebraic spaces over `S` is of finite presentation when it is locally of finite
presentation, quasi-compact and quasi-separated. Quasi-separatedness is quasi-compactness of the
relative diagonal, so it is the `CategoryTheory.MorphismProperty.diagonal` of quasi-compactness,
read as a property of morphisms of presheaves on the big fppf site of `S`. This file shows that
quasi-separatedness, and hence being of finite presentation, is stable under base change.

## Main definitions

* `AlgebraicGeometry.Space.quasiCompactPresheafProperty`: quasi-compactness of morphisms of
  algebraic spaces over `S`, as a morphism property of presheaves on the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Space.isQuasiSeparated_pullback`: a base change of a quasi-separated morphism
  of algebraic spaces over `S` is quasi-separated.
* `AlgebraicGeometry.Space.isFinitePresentation_isStableUnderBaseChange`: being of finite
  presentation is stable under base change of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.IsFinitePresentation.of_isPullback`: the base change of a morphism of
  finite presentation along a cartesian square of presheaves whose corners are algebraic spaces is
  of finite presentation.

## References

* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Quasi-compactness of a morphism of algebraic spaces over `S`, as a morphism property of the
presheaves on the big fppf site of `S` which carry them. -/
abbrev quasiCompactPresheafProperty :
    MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  fun _ _ f => IsQuasiCompact B S hS f

/-- Quasi-compactness of morphisms of presheaves on the big fppf site of `S` is stable under base
change along an arbitrary cartesian square. -/
instance quasiCompactPresheafProperty_isStableUnderBaseChange :
    (quasiCompactPresheafProperty B S hS).IsStableUnderBaseChange where
  of_isPullback sq hg := isQuasiCompact_of_isPullback B S hS sq hg

/-- A base change of a quasi-separated morphism of algebraic spaces over `S` is quasi-separated. -/
@[stacks 03KL "quasi_separated_base_change", sga "4 VI 1.9.1" "(ii), special case"]
theorem isQuasiSeparated_pullback {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hf : IsQuasiSeparated B S hS f) :
    IsQuasiSeparated B S hS (pullback.snd f g) :=
  (MorphismProperty.IsStableUnderBaseChange.diagonal
    (P := quasiCompactPresheafProperty B S hS)).of_isPullback
      (IsPullback.of_hasPullback f g) hf

/-- Quasi-separatedness of a morphism of algebraic spaces over `S` is stable under base change,
stated for an arbitrary cartesian square in the category of algebraic spaces over `S`. -/
instance isQuasiSeparated_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsQuasiSeparated B S hS f.hom) where
  of_isPullback sq hg :=
    (MorphismProperty.IsStableUnderBaseChange.diagonal
      (P := quasiCompactPresheafProperty B S hS)).of_isPullback
        (AlgebraicSpaces.isPullback_hom B S hS sq) hg

/-- Being of finite presentation is a property of morphisms of algebraic spaces over `S` that is
stable under base change. -/
@[stacks 03XR "finite presentation", sga "1 VIII 3.6" "more general"]
instance isFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsFinitePresentation B S hS f.hom) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsQuasiCompact B S hS f.hom) :=
    ⟨fun sq hg => isQuasiCompact_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_hom B S hS sq) hg⟩
  have := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsQuasiCompact B S hS f.hom ∧ IsQuasiSeparated B S hS f.hom) :=
    MorphismProperty.IsStableUnderBaseChange.inf
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsQuasiCompact B S hS f.hom)
      (Q := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsQuasiSeparated B S hS f.hom)
  exact MorphismProperty.IsStableUnderBaseChange.inf
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
      IsLocallyOfFinitePresentation B S hS f.hom)
    (Q := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
      IsQuasiCompact B S hS f.hom ∧ IsQuasiSeparated B S hS f.hom)

/-- If `b` is the base change of a morphism `f` of finite presentation along a cartesian square of
presheaves on the big fppf site of `S` whose four corners are algebraic spaces, then `b` is of
finite presentation. -/
theorem IsFinitePresentation.of_isPullback
    {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (hf : IsFinitePresentation B S hS f) :
    IsFinitePresentation B S hS b := by
  let P : ObjectProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := IsAlgebraicSpace B S hS
  let W' : P.FullSubcategory := ⟨W, hW⟩
  let X' : P.FullSubcategory := ⟨X, hX⟩
  let Y' : P.FullSubcategory := ⟨Y, hY⟩
  let Z' : P.FullSubcategory := ⟨Z, hZ⟩
  have h' : IsPullback (ObjectProperty.homMk a : W' ⟶ X')
      (ObjectProperty.homMk b : W' ⟶ Y')
      (ObjectProperty.homMk f : X' ⟶ Z') (ObjectProperty.homMk g : Y' ⟶ Z') :=
    IsPullback.of_map P.ι (ObjectProperty.hom_ext _ h.w) h
  exact MorphismProperty.of_isPullback
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) =>
      IsFinitePresentation B S hS k.hom) h' hf

end AlgebraicGeometry.Space

end
