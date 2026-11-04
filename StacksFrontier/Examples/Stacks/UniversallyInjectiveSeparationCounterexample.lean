module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackUniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationUniversallyInjectiveCover
public import StacksFrontier.Examples.Spaces.DoubledOriginGroupSpace

/-!
# A counterexample to the published form of Stacks 0CPQ

Stacks 0CPQ asserts: let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks; if `f` is
surjective, flat, locally of finite presentation and universally injective and `g ∘ f` is
separated, then `g` is separated. This file proves that statement false.

Let `S` be the affine line over a field, `H` the affine line with doubled origin, a group over `S`
whose fibres are `ℤ/2` over the origin and trivial elsewhere, and `q : (ℤ/2)_S ⟶ H` the
homomorphism carrying the two sections onto the two charts. Take `𝒳 = B(ℤ/2)_S`, `𝒴 = BH`,
`𝒵 = S`, `f = Bq` and `g` the structure 1-morphism of `BH`.

* `f` is surjective, flat and locally of finite presentation, being so after composition with the
  fppf atlas of `B(ℤ/2)_S` (`AlgebraicGeometry.Stack.isFlat_classifyingMap` and its companions).
* `f` is universally injective by condition (3) of Stacks 0CPN: over an algebraically closed
  field every object of a classifying stack is trivial, a 2-arrow between images under `f` is a
  point of `H`, and field-valued points of `H` lift through `q`, because such a point factors
  through one of the two charts (`Stacks.Examples.exists_lift_doubledOriginQuotientMap`,
  consumed by
  `AlgebraicGeometry.Stack.universallyInjective_classifyingMap`).
* `g ∘ f` is the structure 1-morphism of `B(ℤ/2)_S`, which is separated because `(ℤ/2)_S ⟶ S` is
  proper, flat and locally of finite presentation (Stacks 0DTY, part (6), at the trivial action).
* `g` is not separated, the diagonal of `BH` pulling back to `H ⟶ S`, which is not separated
  (`AlgebraicGeometry.Stack.not_isSeparatedOver_classifyingAlgebraicStack`).

The source's proof fails at the separatedness of the comparison 1-morphism
`𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳`, a base change of the diagonal of `g`; the corrected statement, assuming
that diagonal separated, is
`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isSeparated_of_isSeparated_comp_of_universallyInjective_of_isSeparated_diagonal`.

## Main results

* `Stacks.Examples.not_forall_isSeparated_of_isSeparated_comp_of_universallyInjective`: the
  negation of the published statement of Stacks 0CPQ.

## References

* [Stacks Project, Tag 0CPN](https://stacks.math.columbia.edu/tag/0CPN)
* [Stacks Project, Tag 0CPQ](https://stacks.math.columbia.edu/tag/0CPQ)
* [Stacks Project, Tag 0DTY](https://stacks.math.columbia.edu/tag/0DTY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Examples

/-- **The published form of Stacks 0CPQ is false.** It is not the case that for all 1-morphisms
`f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` of algebraic stacks over a scheme `S` of a big fppf site, if `f` is
surjective, flat, locally of finite presentation and universally injective and `f ≫ g` is
separated, then `g` is separated.

The counterexample: `S` is the affine line over a field, `H` the affine line with doubled origin
as a group over `S`, `q : (ℤ/2)_S ⟶ H` the homomorphism matching the two charts, `𝒳 = B(ℤ/2)_S`,
`𝒴 = BH`, `𝒵 = S`, `f = Bq` and `g` the structure 1-morphism of `BH`. Then `f` is surjective,
flat and locally of finite presentation (`AlgebraicGeometry.Stack.isFlat_classifyingMap` and its
companions) and universally injective because field-valued points of `H` lift through `q`
(`AlgebraicGeometry.Stack.universallyInjective_classifyingMap`); `f ≫ g` is the structure
1-morphism of `B(ℤ/2)_S`, separated because `(ℤ/2)_S ⟶ S` is proper, flat and locally of finite
presentation; and `g` is not separated because `H ⟶ S` is not. -/
theorem not_forall_isSeparated_of_isSeparated_comp_of_universallyInjective :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵),
        Stack.IsSurjective B S hS f →
        Stack.AlgebraicStacks.IsFlat B S hS f →
        Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f →
        Stack.UniversallyInjective B S hS f →
        Stack.AlgebraicStacks.IsSeparated B S hS (f ≫ g) →
        Stack.AlgebraicStacks.IsSeparated B S hS g := by
  intro H
  let k := ULift.{u} ℚ
  obtain ⟨𝒞, hS, -, -⟩ := exists_bigFppfSite_contains k
  have h₁ := isSmooth_constantZ2GroupSpace k hS
  have h₂ := isSmooth_doubledOriginGroupSpace k hS
  let φ := doubledOriginQuotientMap k hS
  refine Stack.not_isSeparatedOver_classifyingAlgebraicStack.{u, w} _ h₂
    (not_isSeparated_doubledOriginGroupSpace k hS)
    (H 𝒞 _ hS (Stack.classifyingMap.{u, w} h₁ h₂ φ)
      (Stack.structureMorphism 𝒞 _ hS (Stack.classifyingAlgebraicStack.{u, w} _ h₂))
      (Stack.isSurjective_classifyingMap.{u, w} h₁ h₂ φ)
      (Stack.isFlat_classifyingMap.{u, w} h₁ h₂ φ)
      (Stack.isLocallyOfFinitePresentation_classifyingMap.{u, w} h₁ h₂ φ)
      (Stack.universallyInjective_classifyingMap.{u, w} h₁ h₂ φ
        (fun K _ _ V e x => exists_lift_doubledOriginQuotientMap k hS V K e x))
      (Stack.isSeparated_classifyingMap_comp_structureMorphism.{u, w} h₁ h₂ φ
        (isProper_constantZ2GroupSpace k hS) (isFlat_constantZ2GroupSpace k hS)
        (isLocallyOfFinitePresentation_constantZ2GroupSpace k hS)))

end Stacks.Examples

end
