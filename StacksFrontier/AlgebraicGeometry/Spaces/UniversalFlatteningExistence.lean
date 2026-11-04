module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionFunctorRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionPurityContainment
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFlattening
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian

/-!
# Existence of universal flattenings of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `F` be a
quasi-coherent `𝒪_X`-module. Stacks 0CX2 says that a universal flattening `Y' ⟶ Y` of `F`
exists, and that it is a monomorphism of finite presentation, in each of these cases:

1. `f` is of finite presentation, `F` is of finite presentation and `F` is pure relative to `Y`;
2. `f` is of finite presentation and `X` is pure relative to `Y`, for the universal flattening
   of `X`;
3. `f` is proper and of finite presentation and `F` is of finite presentation;
4. `f` is proper and of finite presentation, for the universal flattening of `X`. Here the
   source asserts existence only.

The source deduces all four from Theorem 0CX1 applied to `F_0 = F_flat`. In cases (3) and (4)
it also uses Stacks 0CVI: over a proper morphism every finite type quasi-coherent module is
pure relative to the target.

## Main definitions

* `AlgebraicGeometry.Space.FlatnessSituation.toFlatDimensionSituation`: the flatness situation
  of Stacks 0CWX with `f` and `F` of finite presentation, viewed as an instance of
  Situation 0CWU. Finite presentation gives local finite type of `f` and finite type of `F`.

## Main results

* `AlgebraicGeometry.Space.FlatnessSituation.hasUniversalFlattening_of_isPureAbove`: part (1).
* `AlgebraicGeometry.Space.hasUniversalFlattening_of_isPureAbove_structure`: part (2).
* `AlgebraicGeometry.Space.FlatnessSituation.hasUniversalFlattening_of_isProper`: part (3).
* `AlgebraicGeometry.Space.hasUniversalFlattening_of_isProper`: part (4).
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_structureSheaf`: the structure sheaf
  `𝒪_X` is of finite presentation, which reduces parts (2) and (4) to parts (1) and (3).

## Implementation notes

A universal flattening of `F` is `AlgebraicGeometry.Space.FlatnessSituation.HasUniversalFlattening`
of Stacks 0CWR. It says that the functor `F_flat` of Stacks 0CWX, taken as the subfunctor
`AlgebraicGeometry.Space.FlatnessSituation.flatSubfunctor` of `Y`, is an algebraic space. The
morphism `Y' ⟶ Y` of the source is the inclusion `Subfunctor.ι` of that subfunctor. Parts (1) to
(3) assert that this inclusion is a monomorphism of finite presentation in the sense of
Stacks 03XP. The subfunctor depends on a proof that flatness is stable under base change, and is
evaluated at the unconditional proof
`AlgebraicGeometry.Space.FlatnessSituation.isFlatStableUnderBaseChange`.

Theorem 0CX1 is
`AlgebraicGeometry.Space.FlatDimensionSituation.isAlgebraicSpace_flatDimensionSubfunctor`, for the
subfunctor `F_n` of `Y`. At `n = 0` that subfunctor is `F_flat`, by
`AlgebraicGeometry.Space.FlatDimensionSituation.flatDimensionSubfunctor_zero`. It is applied to the
situation `AlgebraicGeometry.Space.FlatnessSituation.toFlatDimensionSituation`.

"Pure relative to `Y`" is Definition 0CVD (5): purity above every point `y ∈ |Y|`. It is stated
in the situation of Stacks 0CV6, which asks `f` to be of finite type and decent and `F` to be of
finite type and quasi-coherent. All of these follow from the hypotheses of the lemma: finite
presentation of `f` gives finite type and decency (the footnote of Situation 0CV6,
`AlgebraicGeometry.Space.isDecent_of_isFinitePresentation`), and finite presentation of `F` gives
finite type. So the purity hypothesis is read on a situation built from those hypotheses alone,
`AlgebraicGeometry.Space.FlatDimensionSituation.fpPrePureSituation`,
and nothing beyond them is assumed. "`X` is pure relative to `Y`" is the same condition for the
structure sheaf `𝒪_X`, Definition 0CVD (6), read on
`AlgebraicGeometry.Space.structurePrePureSituation`. `𝒪_X` is of finite presentation
unconditionally (`SheafOfModules.isFinitePresentationOnSite_unit`), so part (2) is part (1) at
`F = 𝒪_X`, and part (4) is part (3) at `F = 𝒪_X`.

## References

* [Stacks Project, Tag 0CX2](https://stacks.math.columbia.edu/tag/0CX2)
* [Stacks Project, Tag 0CX1](https://stacks.math.columbia.edu/tag/0CX1)
* [Stacks Project, Tag 0CVI](https://stacks.math.columbia.edu/tag/0CVI)
* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 0CWR](https://stacks.math.columbia.edu/tag/0CWR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace FlatnessSituation

/-- The flatness situation of Stacks 0CWX with `f` and `F` of finite presentation, viewed as
an instance of Situation 0CWU. A morphism of finite presentation is locally of finite type, and a
module of finite presentation is of finite type. -/
def toFlatDimensionSituation (D : FlatnessSituation.{u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F) :
    FlatDimensionSituation.{u} B S hS where
  toFlatnessSituation := D
  locallyOfFiniteType := (isFiniteType_of_isFinitePresentation B S hS hf).1
  finiteType := SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite D.F

/-- **Stacks 0CX2, part (1).** Let `f : X ⟶ Y` be a morphism of algebraic spaces of finite
presentation and let `F` be a quasi-coherent `𝒪_X`-module of finite presentation which is pure
relative to `Y`, that is, pure above every point `y ∈ |Y|`. Then the universal flattening
`Y' ⟶ Y` of `F` exists, and `Y' ⟶ Y` is a monomorphism of finite presentation.

Here `Y'` is the subfunctor `F_flat` of `Y` and `Y' ⟶ Y` is its inclusion. This is Theorem 0CX1
at `n = 0`, where `F_0 = F_flat`. -/
@[stacks 0CX2 "part (1)"]
theorem hasUniversalFlattening_of_isPureAbove (D : FlatnessSituation.{u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F)
    (hpure : ∀ y : points B S hS D.Y.1,
      IsPureAbove ((D.toFlatDimensionSituation hf hF).fpPrePureSituation hf y)) :
    D.HasUniversalFlattening ∧ Mono (D.flatSubfunctor D.isFlatStableUnderBaseChange).ι ∧
      IsFinitePresentation B S hS (D.flatSubfunctor D.isFlatStableUnderBaseChange).ι := by
  have h := (D.toFlatDimensionSituation hf hF).isAlgebraicSpace_flatDimensionSubfunctor 0 hf hF
    hpure
  rw [FlatDimensionSituation.flatDimensionSubfunctor_zero] at h
  exact ⟨⟨D.isFlatStableUnderBaseChange, h.1⟩, h.2⟩

/-- **Stacks 0CX2, part (3).** Let `f : X ⟶ Y` be a proper morphism of algebraic spaces of finite
presentation and let `F` be a quasi-coherent `𝒪_X`-module of finite presentation. Then the
universal flattening `Y' ⟶ Y` of `F` exists, and `Y' ⟶ Y` is a monomorphism of finite
presentation.

Over a proper morphism `F` is universally pure above every point of `Y`, by Stacks 0CVI, part (2).
So it is pure relative to `Y`, and part (1) applies. -/
@[stacks 0CX2 "part (3)"]
theorem hasUniversalFlattening_of_isProper (D : FlatnessSituation.{u} B S hS)
    (hproper : IsProper B S hS D.f.hom) (hf : IsFinitePresentation B S hS D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F) :
    D.HasUniversalFlattening ∧ Mono (D.flatSubfunctor D.isFlatStableUnderBaseChange).ι ∧
      IsFinitePresentation B S hS (D.flatSubfunctor D.isFlatStableUnderBaseChange).ι :=
  D.hasUniversalFlattening_of_isPureAbove hf hF
    (fun _ => IsPureAbove.of_isUniversallyPureAbove
      (isUniversallyPureAbove_of_isProper _ hproper))

end FlatnessSituation

/-- The structure sheaf of an algebraic space is of finite presentation. -/
theorem isFinitePresentationOnSite_structureSheaf {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    SheafOfModules.IsFinitePresentationOnSite (structureSheafFlatnessSituation f).F :=
  SheafOfModules.isFinitePresentationOnSite_unit

/-- **Stacks 0CX2, part (2).** Let `f : X ⟶ Y` be a morphism of algebraic spaces of finite
presentation such that `X` is pure relative to `Y`, that is, `𝒪_X` is pure above every point
`y ∈ |Y|`. Then the universal flattening `Y' ⟶ Y` of `X` exists, and `Y' ⟶ Y` is a monomorphism
of finite presentation.

This is part (1) for the module `𝒪_X`, which is of finite presentation. -/
@[stacks 0CX2 "part (2)"]
theorem hasUniversalFlattening_of_isPureAbove_structure {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (hpure : ∀ y : points B S hS Y.1, IsPureAbove (structurePrePureSituation X.2 Y.2 f.hom
      (isFiniteType_of_isFinitePresentation B S hS hf)
      (isDecent_of_isFinitePresentation B S hS f hf) y)) :
    HasUniversalFlattening f ∧
      Mono ((structureSheafFlatnessSituation f).flatSubfunctor
        (structureSheafFlatnessSituation f).isFlatStableUnderBaseChange).ι ∧
      IsFinitePresentation B S hS ((structureSheafFlatnessSituation f).flatSubfunctor
        (structureSheafFlatnessSituation f).isFlatStableUnderBaseChange).ι :=
  (structureSheafFlatnessSituation f).hasUniversalFlattening_of_isPureAbove hf
    (isFinitePresentationOnSite_structureSheaf f) hpure

/-- **Stacks 0CX2, part (4).** Let `f : X ⟶ Y` be a proper morphism of algebraic spaces of finite
presentation. Then the universal flattening of `X` exists.

This is part (3) for the module `𝒪_X`, which is of finite presentation. -/
@[stacks 0CX2 "part (4)"]
theorem hasUniversalFlattening_of_isProper {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hproper : IsProper B S hS f.hom) (hf : IsFinitePresentation B S hS f.hom) :
    HasUniversalFlattening f :=
  ((structureSheafFlatnessSituation f).hasUniversalFlattening_of_isProper hproper hf
    (isFinitePresentationOnSite_structureSheaf f)).1

end AlgebraicGeometry.Space

end
