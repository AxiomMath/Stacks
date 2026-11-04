module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Associativity of 2-fibre products of categories (Stacks 02XC)

Given four functors `H : 𝒜 ⥤ ℬ`, `K : 𝒞 ⥤ ℬ`, `L : 𝒞 ⥤ 𝒟` and `M : ℰ ⥤ 𝒟`, there are two
ways to iterate the 2-fibre product of Example 003R: one may first form `𝒜 ×_ℬ 𝒞` and then
pull back its second projection along `M`, or first form `𝒞 ×_𝒟 ℰ` and then pull `𝒜` back
along the first projection. In Mathlib's model these are
`CategoricalPullback (π₂ H K ⋙ L) M` and `CategoricalPullback H (π₁ L M ⋙ K)`, and this file
constructs the rebracketing equivalence `(𝒜 ×_ℬ 𝒞) ×_𝒟 ℰ ≌ 𝒜 ×_ℬ (𝒞 ×_𝒟 ℰ)` between them.

The comparison functor is `((A, C, φ), E, ψ) ↦ (A, (C, E, ψ), φ)`: the two nestings hold the
same data, only bracketed differently, and both structural isomorphisms are carried over
unchanged. Because Lean 4's η-rule for structures makes the two rebracketings mutually
inverse *definitionally*, the unit and counit of the equivalence are the identity
isomorphisms, so the equivalence is an isomorphism of categories in all but name.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {𝒜 ℬ 𝒞 𝒟 ℰ : Type*}
    [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟] [Category ℰ]

/-- **Stacks 02XC.** The canonical comparison functor
`(𝒜 ×_ℬ 𝒞) ×_𝒟 ℰ ⥤ 𝒜 ×_ℬ (𝒞 ×_𝒟 ℰ)`, rebracketing `((A, C, φ), E, ψ) ↦ (A, (C, E, ψ), φ)`. -/
@[stacks 02XC]
def CategoricalPullback.assocFunctor
    (H : 𝒜 ⥤ ℬ) (K : 𝒞 ⥤ ℬ) (L : 𝒞 ⥤ 𝒟) (M : ℰ ⥤ 𝒟) :
    CategoricalPullback (CategoricalPullback.π₂ H K ⋙ L) M ⥤
      CategoricalPullback H (CategoricalPullback.π₁ L M ⋙ K) where
  obj X := ⟨X.fst.fst, ⟨X.fst.snd, X.snd, X.iso⟩, X.fst.iso⟩
  map f := ⟨f.fst.fst, ⟨f.fst.snd, f.snd, f.w⟩, f.fst.w⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inverse rebracketing `(A, (C, E, ψ), φ) ↦ ((A, C, φ), E, ψ)`, inverse to
`CategoricalPullback.assocFunctor`. -/
def CategoricalPullback.assocInverse
    (H : 𝒜 ⥤ ℬ) (K : 𝒞 ⥤ ℬ) (L : 𝒞 ⥤ 𝒟) (M : ℰ ⥤ 𝒟) :
    CategoricalPullback H (CategoricalPullback.π₁ L M ⋙ K) ⥤
      CategoricalPullback (CategoricalPullback.π₂ H K ⋙ L) M where
  obj Y := ⟨⟨Y.fst, Y.snd.fst, Y.iso⟩, Y.snd.snd, Y.snd.iso⟩
  map g := ⟨⟨g.fst, g.snd.fst, g.w⟩, g.snd.snd, g.snd.w⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Stacks 02XC.** Associativity of 2-fibre products of categories: for
`H : 𝒜 ⥤ ℬ`, `K : 𝒞 ⥤ ℬ`, `L : 𝒞 ⥤ 𝒟` and `M : ℰ ⥤ 𝒟` the two iterated 2-fibre products
are canonically equivalent, `(𝒜 ×_ℬ 𝒞) ×_𝒟 ℰ ≌ 𝒜 ×_ℬ (𝒞 ×_𝒟 ℰ)`, via
`CategoricalPullback.assocFunctor`. -/
@[stacks 02XC]
def CategoricalPullback.assoc
    (H : 𝒜 ⥤ ℬ) (K : 𝒞 ⥤ ℬ) (L : 𝒞 ⥤ 𝒟) (M : ℰ ⥤ 𝒟) :
    CategoricalPullback (CategoricalPullback.π₂ H K ⋙ L) M ≌
      CategoricalPullback H (CategoricalPullback.π₁ L M ⋙ K) :=
  Equivalence.mk
    (CategoricalPullback.assocFunctor H K L M)
    (CategoricalPullback.assocInverse H K L M)
    (Iso.refl _) (Iso.refl _)

end CategoryTheory.Limits
