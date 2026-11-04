module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliProperness.ProperOfCategoricalModuliSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.KeelMoriTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliFiniteType

/-!
# The moduli space of a proper stack with finite inertia is proper over the base (Stacks 0DUZ)

Let `p : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space such that the
inertia `I_𝒳 ⟶ 𝒳` is finite, `p` is proper and `Y` is locally Noetherian, and let `f : 𝒳 ⟶ M`
be the moduli space of the Keel–Mori theorem (Stacks 0DUT). Then the morphism `M ⟶ Y` through
which `p` factors is proper.

The statement is proved for every categorical moduli space `f : 𝒳 ⟶ M` (Stacks 0DUG). A
categorical moduli space is unique up to a unique isomorphism compatible with the 1-morphisms
(`AlgebraicGeometry.Stack.exists_iso_of_isCategoricalModuliSpace`), so this is the moduli space
constructed in Stacks 0DUT, and the morphism `M ⟶ Y` is the one the universal property of `f`
provides, which the statement also records.

The proof is the source's. By Stacks 0DUX the morphism `M ⟶ Y` is locally of finite type. The
rest of the argument only uses that the moduli map of Stacks 0DUT is a universal homeomorphism and
is `AlgebraicGeometry.Stack.isProper_of_universalHomeomorphism_of_isProper_comp`: `M ⟶ Y` is
universally closed by Stacks 0CQK, read on algebraic spaces through Stacks 0512 and the bridge of
Stacks 04XB (Stacks 045A); separated because `Δ_{M/Y} ∘ f = (f ×_Y f) ∘ Δ_{𝒳/Y}` is universally
closed (Stacks 0515, 0CQK) and Stacks 04Y0 in the form Stacks 04YS; and quasi-compact by
Stacks 04XW. The result is carried from the moduli space of Stacks 0DUT to an arbitrary
categorical moduli space by
`AlgebraicGeometry.Stack.isProper_of_isCategoricalModuliSpace_of_isProper_comp`.

## Main results

* `AlgebraicGeometry.Stack.isProper_of_isCategoricalModuliSpace_of_isFinite_inertia`:
  **Stacks 0DUZ**.

## Implementation notes

Finiteness of the inertia is `AlgebraicGeometry.Stack.AlgebraicStacks.IsFinite` of the inertia
projection (Stacks 04Z2), properness of `p` is Stacks 0CL5, local Noetherianity of `Y` is the
étale-local scheme property `AlgebraicGeometry.IsLocallyNoetherian` (Stacks 03EA), and properness
of `M ⟶ Y` is Stacks 03ZM. The morphism `M ⟶ Y` is a morphism `g` of algebraic spaces with
`f ≫ g ≅ p`, read through the 1-morphism `AlgebraicGeometry.Stack.associatedMap` of Stacks 0458.

## References

* [Stacks Project, Tag 0DUZ](https://stacks.math.columbia.edu/tag/0DUZ)
* [Stacks Project, Tag 0DUT](https://stacks.math.columbia.edu/tag/0DUT)
* [Stacks Project, Tag 0DUX](https://stacks.math.columbia.edu/tag/0DUX)
* [Stacks Project, Tag 0DUG](https://stacks.math.columbia.edu/tag/0DUG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DUZ.** Let `p : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic
space. Assume
1. `I_𝒳 ⟶ 𝒳` is finite,
2. `p` is proper, and
3. `Y` is locally Noetherian.

Let `f : 𝒳 ⟶ M` be a categorical moduli space — for instance the moduli space constructed in
Stacks 0DUT, which every categorical moduli space of `𝒳` is up to unique isomorphism. Then `p`
factors as `f` followed by a unique morphism `M ⟶ Y` of algebraic spaces, up to a 2-isomorphism,
and `M ⟶ Y` is proper. -/
@[stacks 0DUZ]
theorem isProper_of_isCategoricalModuliSpace_of_isFinite_inertia
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hI : AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (Y : AlgebraicSpaces B S hS)
    (hY : Space.HasEtaleLocalProperty B S hS Y.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (p : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hp : AlgebraicStacks.IsProper B S hS p)
    (M : AlgebraicSpaces B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : IsCategoricalModuliSpace B S hS M f.hom) :
    (∃! g : M ⟶ Y, Nonempty (f.hom ≫ (associatedMap B S hS g.hom).1 ≅ p.hom)) ∧
      ∀ g : M ⟶ Y, Nonempty (f.hom ≫ (associatedMap B S hS g.hom).1 ≅ p.hom) →
        Space.IsProper B S hS g.hom := by
  refine ⟨hf Y p.hom, fun g hg => ?_⟩
  obtain ⟨M₀, f₀, hf₀, -, -, hUH⟩ :=
    exists_isUniformCategoricalModuliSpace_of_isFinite_inertia B S hS 𝒳 hI
  have hc₀ := isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS hf₀
  have hlft := (isLocallyOfFiniteType_of_isCategoricalModuliSpace_of_isFinite_inertia B S hS 𝒳
    hI Y hY p hp.2.1.1 M₀ f₀ hc₀).2
  exact isProper_of_isCategoricalModuliSpace_of_isProper_comp B S hS Y.property p hp f₀ hc₀
    (fun 𝒵 k => hUH 𝒵 k (twoFibreProductSquareAlgebraicStacks B S hS k f₀)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k f₀))
    (fun g₀ hg₀ => hlft (ObjectProperty.homMk g₀) hg₀) f hf g.hom hg

end AlgebraicGeometry.Stack

end
