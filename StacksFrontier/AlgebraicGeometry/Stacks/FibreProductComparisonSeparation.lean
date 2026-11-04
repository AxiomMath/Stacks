module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange

/-!
# The separation properties of the comparison of two fibre products

Let `f : 𝒳 ⟶ 𝒵`, `g : 𝒴 ⟶ 𝒵` and `h : 𝒵 ⟶ 𝒯` be 1-morphisms of algebraic stacks over `S` and
let

    i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴

be the induced 1-morphism. The square

```text
                   i
  𝒳 ×_𝒵 𝒴  ------------>  𝒳 ×_𝒯 𝒴
    |                         |
    |                         |
    v                         v
    𝒵  --Δ_{𝒵/𝒯}-->       𝒵 ×_𝒯 𝒵
```

is 2-cartesian (`AlgebraicGeometry.Stack.isTwoFibreProduct_comparisonSquare`), so `i` is a base
change of the relative diagonal `Δ_{𝒵/𝒯}`. The properties of `i` below are properties of a
1-morphism in the sense of Properties of Stacks, Section 04XB, each inherited from the
corresponding property of `Δ_{𝒵/𝒯}`.

## Main results

* `AlgebraicGeometry.Stack.isQuasiSeparated_comparison_of_diagonal`: if `Δ_{𝒵/𝒯}` is
  quasi-separated, so is `i`.
* `AlgebraicGeometry.Stack.isSeparated_comparison_of_diagonal`: if `Δ_{𝒵/𝒯}` is separated, so
  is `i`.
* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_comparison`: if `h` is quasi-DM, then `i` is
  locally quasi-finite.
* `AlgebraicGeometry.Stack.isProper_comparison`: if `h` is separated, then `i` is proper.
* `AlgebraicGeometry.Stack.isQuasiCompact_comparison` and
  `AlgebraicGeometry.Stack.isQuasiSeparated_comparison`: if `h` is quasi-separated, then `i` is
  quasi-compact and quasi-separated.

## References

* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04Z1](https://stacks.math.columbia.edu/tag/04Z1)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 𝒯 : AlgebraicStacks.{u, w} B S hS}

/-- The condition of Stacks 04XB for a property `P` of morphisms of algebraic spaces, on a
1-morphism of categories fibred in groupoids over the big fppf site of `S`. -/
private abbrev RelativeCondition (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))

/-- The comparison 1-morphism `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` satisfies the condition of Stacks 04XB for
`P` as soon as the relative diagonal `Δ_{𝒵/𝒯}` does (Stacks 045C). -/
private theorem relativeCondition_comparison (P : MorphismProperty (AlgebraicSpaces B S hS))
    (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hΔ : RelativeCondition B S hS P (relativeDiagonalAlgebraicStacks B S hS h).hom) :
    RelativeCondition B S hS P (comparison B S hS f g h).hom :=
  relativeProperty_baseChange.{u, u, u + 1} B S hS P
    𝒵.val (twoFibreProductAlgebraicStack B S hS h h).val
    (twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h)).val
    (relativeDiagonalAlgebraicStacks B S hS h).hom
    (comparisonCospanRight B S hS f g h).hom
    (comparisonSquare B S hS f g h)
    (isTwoFibreProduct_comparisonSquare B S hS f g h) hΔ

/-- If the relative diagonal `Δ_{𝒵/𝒯}` is quasi-separated, then so is the comparison 1-morphism
`i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴`, both in the sense of Properties of Stacks, Section 04XB. -/
@[stacks 050H "quasi_separated_diagonal"]
theorem isQuasiSeparated_comparison_of_diagonal (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hΔ : IsQuasiSeparated B S hS (relativeDiagonalAlgebraicStacks B S hS h).hom) :
    IsQuasiSeparated B S hS (comparison B S hS f g h).hom :=
  relativeCondition_comparison B S hS (fun _ _ k => Space.IsQuasiSeparated B S hS k.hom) f g h hΔ

/-- If the relative diagonal `Δ_{𝒵/𝒯}` is separated, then so is the comparison 1-morphism
`i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴`, both in the sense of Properties of Stacks, Section 04XB. -/
@[stacks 050H "separated_diagonal"]
theorem isSeparated_comparison_of_diagonal (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hΔ : IsSeparated B S hS (relativeDiagonalAlgebraicStacks B S hS h).hom) :
    IsSeparated B S hS (comparison B S hS f g h).hom :=
  relativeCondition_comparison B S hS (fun _ _ k => Space.IsSeparated B S hS k.hom) f g h hΔ

/-- If `h : 𝒵 ⟶ 𝒯` is quasi-DM then the comparison 1-morphism `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is
locally quasi-finite, in the sense of Properties of Stacks, Section 04XB. -/
@[stacks 050H "quasi_dm_lqf"]
theorem isLocallyQuasiFinite_comparison (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hh : AlgebraicStacks.IsQuasiDM B S hS h) :
    IsLocallyQuasiFinite B S hS (comparison B S hS f g h).hom :=
  relativeCondition_comparison B S hS (fun _ _ k => Space.IsLocallyQuasiFinite B S hS k.hom)
    f g h hh

/-- If `h : 𝒵 ⟶ 𝒯` is separated then the comparison 1-morphism `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is
proper, in the sense of Properties of Stacks, Section 04XB. -/
@[stacks 050H "separated_proper"]
theorem isProper_comparison (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hh : AlgebraicStacks.IsSeparated B S hS h) :
    IsProper B S hS (comparison B S hS f g h).hom :=
  relativeCondition_comparison B S hS (fun _ _ k => Space.IsProper B S hS k.hom) f g h hh

/-- If `h : 𝒵 ⟶ 𝒯` is quasi-separated as a 1-morphism of algebraic stacks, then the comparison
1-morphism `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is quasi-compact, in the sense of Properties of Stacks,
Section 04XB. -/
@[stacks 050H "part (7), the quasi-compactness half"]
theorem isQuasiCompact_comparison (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hh : AlgebraicStacks.IsQuasiSeparated B S hS h) :
    IsQuasiCompact B S hS (comparison B S hS f g h).hom :=
  fun U y hy F hF he =>
    (relativeCondition_comparison B S hS
      (fun _ _ k => Space.IsQuasiCompact B S hS k.hom ∧ Space.IsQuasiSeparated B S hS k.hom)
      f g h ((AlgebraicStacks.isQuasiSeparated_iff_forall B S hS h).mp hh) U y hy F hF he).1

/-- If `h : 𝒵 ⟶ 𝒯` is quasi-separated as a 1-morphism of algebraic stacks, then the comparison
1-morphism `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is quasi-separated, in the sense of Properties of Stacks,
Section 04XB. -/
@[stacks 050H "part (7), the quasi-separatedness half"]
theorem isQuasiSeparated_comparison (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hh : AlgebraicStacks.IsQuasiSeparated B S hS h) :
    IsQuasiSeparated B S hS (comparison B S hS f g h).hom :=
  fun U y hy F hF he =>
    (relativeCondition_comparison B S hS
      (fun _ _ k => Space.IsQuasiCompact B S hS k.hom ∧ Space.IsQuasiSeparated B S hS k.hom)
      f g h ((AlgebraicStacks.isQuasiSeparated_iff_forall B S hS h).mp hh) U y hy F hF he).2

end AlgebraicGeometry.Stack

end
