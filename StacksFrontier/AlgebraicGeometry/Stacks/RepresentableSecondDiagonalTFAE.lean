module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalRepresentable

/-!
# Representability by algebraic spaces and the second diagonal (Stacks 04YY)

**Stacks 04YY** says that for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the
following are equivalent: (1) `f` is representable by algebraic spaces; (2) the second diagonal
`Δ_{f, 2}` is an isomorphism; (3) the relative inertia `I_{𝒳/𝒴}` is trivial over `𝒳`; (4) for
every scheme `T` and every `x : T ⟶ 𝒳` the kernel of `Isom_𝒳(x, x) ⟶ Isom_𝒴(f ∘ x, f ∘ x)` is
trivial.

The pieces are in the library:
`StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalRepresentable` proves (2) ⟺ (3) ⟺ (4) and
(1) ⟹ (2), and `StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional` proves
(2) ⟹ (1). This file assembles them into the four-way equivalence the tag states.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_tfae`:
  **Stacks 04YY**.

## References

* [Stacks Project, Tag 04YY](https://stacks.math.columbia.edu/tag/04YY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04YY.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are
equivalent:

1. `f` is representable by algebraic spaces;
2. the second diagonal `Δ_{f, 2}` is an isomorphism;
3. the relative inertia `I_{𝒳/𝒴}` is trivial over `𝒳`, that is, its neutral section
   `e : 𝒳 ⟶ I_{𝒳/𝒴}` is an isomorphism;
4. for every scheme `T` and every `x : T ⟶ 𝒳` the kernel of
   `Isom_𝒳(x, x) ⟶ Isom_𝒴(f ∘ x, f ∘ x)` is trivial — stated as: every endomorphism of an object
   of `𝒳` which `f` sends to an identity is an identity. -/
@[stacks 04YY]
theorem isRepresentableByAlgebraicSpaces_tfae (f : 𝒳 ⟶ 𝒴) :
    List.TFAE
      [IsRepresentableByAlgebraicSpaces B S hS f.hom.hom,
        Functor.IsEquivalence (secondRelativeDiagonal B S hS f.hom).hom.toFunctor,
        Functor.IsEquivalence
          (relativeInertiaStackNeutralSection B S hS f).hom.hom.toFunctor,
        ∀ (x : 𝒳.val.val.obj) (a : x ⟶ x),
          (CatFiberedInGroupoids.homFunctor f.hom).map a = 𝟙 _ → a = 𝟙 x] := by
  tfae_have 1 → 2 :=
    isEquivalence_secondRelativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS f
  tfae_have 2 → 1 :=
    isRepresentableByAlgebraicSpaces_of_isEquivalence_secondRelativeDiagonal B S hS f
  tfae_have 2 ↔ 3 :=
    isEquivalence_secondRelativeDiagonal_iff_relativeInertiaTrivial B S hS f
  tfae_have 3 ↔ 4 := relativeInertiaTrivial_iff_isomKernel_trivial B S hS f
  tfae_finish

end AlgebraicGeometry.Stack.AlgebraicStacks

end
