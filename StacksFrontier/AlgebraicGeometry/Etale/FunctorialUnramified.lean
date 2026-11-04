module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksCore.Tactic.StacksAttribute

/-!
# The functorial characterization of unramified morphisms

Let `f : X ⟶ S` be a morphism of schemes with `S` locally Noetherian and `f` locally of finite
type. Then `f` is unramified exactly when it is *formally unramified* in the functorial sense:
for every affine `S`-scheme `T` and every subscheme `T₀ ⊆ T` defined by a square-zero ideal, the
restriction map `Hom_S(T, X) ⟶ Hom_S(T₀, X)` is injective.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.unramified_iff_injective_hom_restriction`: **Stacks 024R**.

## Implementation notes

`Hom_S(T, X)` is the morphism type `T ⟶ Over.mk f` of the slice category `CategoryTheory.Over S`,
so the restriction map along a subscheme inclusion `i : T₀ ⟶ T` of `S`-schemes is literally
precomposition `fun g => i ≫ g`. A subscheme of `T` defined by a square-zero ideal is a closed
immersion whose kernel ideal sheaf has vanishing square, which is
`Stacks.Thickenings.IsFirstOrderThickening`.

Unramifiedness is traded for the pair "locally of finite type and formally unramified" by
`AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_formallyUnramified` (Tag 02HE), whose
local finite type half is the hypothesis on `f`; only the formal half has to be matched with the
functorial condition, and Mathlib's infinitesimal lifting criterion for
`AlgebraicGeometry.FormallyUnramified` does that in both directions:

* `AlgebraicGeometry.FormallyUnramified.hom_ext` gives uniqueness of a filler against an
  arbitrary closed immersion with nilpotent kernel ideal sheaf, which covers the square-zero case
  of the functorial condition for an arbitrary, not necessarily affine, `T`.
* `AlgebraicGeometry.FormallyUnramified.of_hom_ext` reduces formal unramifiedness to the
  functorial condition for `T = Spec R` and `T₀ = Spec (R/I)` with `I² = 0`; the thickening to
  feed to it is `Spec.map φ` for a square-zero surjection `φ`, recognized as a first-order
  thickening by `Stacks.Smooth.isFirstOrderThickening_specMap`.

Only morphisms in the slice category appear, so the compatibility of each morphism with the
structure morphisms to `S` is carried by `CategoryTheory.Over.w` and no separate bookkeeping of
commuting triangles is needed.

The local Noetherian hypothesis on `S` is the one of the source; the proof does not consume it.

## References

* [Stacks Project, Tag 024R](https://stacks.math.columbia.edu/tag/024R)
* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 024R.** Let `f : X ⟶ S` be a morphism of schemes with `S` locally Noetherian and `f`
locally of finite type. Then `f` is unramified if and only if it is formally unramified in the
functorial sense: for every affine `S`-scheme `T` and every subscheme `T₀` of `T` defined by a
square-zero ideal, the natural map `Hom_S(T, X) → Hom_S(T₀, X)` is injective. -/
@[stacks 024R]
public theorem unramified_iff_injective_hom_restriction {X S : Scheme.{u}}
    [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    Unramified f ↔
      ∀ (T T₀ : Over S) (_ : IsAffine T.left) (i : T₀ ⟶ T),
        Stacks.Thickenings.IsFirstOrderThickening i.left →
          Function.Injective fun g : T ⟶ Over.mk f => i ≫ g := by
  constructor
  · intro hf T T₀ _ i hi g₁ g₂ hg
    have _ : FormallyUnramified f := formallyUnramified_of_unramified f
    have _ : IsClosedImmersion i.left := hi.1
    refine Over.OverMorphism.ext (FormallyUnramified.hom_ext i.left ⟨2, by simpa using hi.2⟩ f
      ?_ ?_)
    · simpa using congrArg Over.Hom.left hg
    · simpa using (Over.w g₁).trans (Over.w g₂).symm
  · intro H
    rw [unramified_iff_locallyOfFiniteType_and_formallyUnramified]
    refine ⟨inferInstance, FormallyUnramified.of_hom_ext f ?_⟩
    intro R A φ hφ hker g₁ g₂ hig hgf
    have h := H (Over.mk (g₁ ≫ f)) (Over.mk (Spec.map φ ≫ g₁ ≫ f))
      (inferInstanceAs (IsAffine (Spec R)))
      (Over.homMk (Spec.map φ) rfl)
      (Stacks.Smooth.isFirstOrderThickening_specMap φ hφ hker)
      (a₁ := Over.homMk g₁ rfl) (a₂ := Over.homMk g₂ hgf.symm)
      (Over.OverMorphism.ext (by simpa using hig))
    simpa using congrArg Over.Hom.left h

end AlgebraicGeometry

end
