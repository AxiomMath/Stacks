module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.SectionsInfinitesimalDiffZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpFaithful

/-!
# A section of `Γ₀` is determined by its difference from a given one

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S`, let `U₀ ⊆ U` be a
first order thickening, let `R₀ = s^{-1}(U₀) ⊆ R` and let `Γ₀` be the set of
[Stacks Project, Tag 0CKB] of sections of the source agreeing with the unit on `U₀`.
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDiff` is the `𝒪_{U₀}`-linear
map `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` by which two elements of `Γ₀` differ.

This file proves that two elements of `Γ₀` whose difference vanishes are equal, and hence that an
element of `Γ₀` is determined by its difference from a given one. Consequently the uniqueness
clause of the field `existsUnique_diff` of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference` follows from the
existence clause.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.eq_of_infinitesimalSectionDiff_eq_zero`: two
  elements of `Γ₀` whose difference vanishes are equal.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDiff_injective`: an element
  of `Γ₀` is determined by its difference from a given one.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.existsUnique_infinitesimalSectionDiff_of_exists`:
  if every `𝒪_{U₀}`-linear map is the difference from a given section of *some* section, then it
  is the difference of exactly one.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDifferenceOfExists`:
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference` from the bare
  existence clause.

## Implementation notes

By `restrictedSharpThroughThickening_eq_of_infinitesimalSectionDiff_eq_zero`, two sections whose
difference vanishes have equal comorphisms read through the thickening. Two morphisms `U ⟶ R`
agreeing on a first order thickening factor through one affine étale chart diagram of the target,
on which they are compared as ring maps between affine schemes; so they are determined by these
comorphisms (`AlgebraicGeometry.Space.eq_of_restrictedSharpThroughThickening_eq`).

## References

* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bas : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Bas)
  (U₀ : ClosedSubspaces C S hS G.objects.1)
  (hU₀ : Space.IsFirstOrderThickening C S hS G.objects U₀.1)

include hU₀ in
/-- Two elements of `Γ₀` whose difference vanishes are equal. -/
theorem eq_of_infinitesimalSectionDiff_eq_zero (δ₁ δ₂ : InfinitesimalSections G U₀)
    (h : infinitesimalSectionDiff G U₀ hU₀ δ₁ δ₂ = 0) : δ₁ = δ₂ :=
  Subtype.ext (Subtype.ext (Space.eq_of_restrictedSharpThroughThickening_eq C S hS U₀ hU₀
    (preimageSubspace C S hS G.source U₀) δ₁.1.1 δ₂.1.1 (restrictedUnit G U₀)
    (comp_eq_restrictedUnit_comp G U₀ δ₁.2) (comp_eq_restrictedUnit_comp G U₀ δ₂.2)
    (restrictedSharpThroughThickening_eq_of_infinitesimalSectionDiff_eq_zero G U₀ hU₀ δ₁ δ₂ h)))

include hU₀ in
/-- An element of `Γ₀` is determined by its difference from a given one: for fixed `δ`, the map
`ε ↦ infinitesimalSectionDiff G U₀ hU₀ δ ε` is injective. -/
theorem infinitesimalSectionDiff_injective (δ : InfinitesimalSections G U₀) :
    Function.Injective (infinitesimalSectionDiff G U₀ hU₀ δ) := by
  intro ε₁ ε₂ h
  refine eq_of_infinitesimalSectionDiff_eq_zero G U₀ hU₀ ε₁ ε₂ ?_
  calc infinitesimalSectionDiff G U₀ hU₀ ε₁ ε₂
      = infinitesimalSectionDiff G U₀ hU₀ ε₁ δ + infinitesimalSectionDiff G U₀ hU₀ δ ε₂ :=
        (infinitesimalSectionDiff_add_infinitesimalSectionDiff G U₀ hU₀ ε₁ δ ε₂).symm
    _ = infinitesimalSectionDiff G U₀ hU₀ ε₁ δ + infinitesimalSectionDiff G U₀ hU₀ δ ε₁ := by
        rw [h]
    _ = infinitesimalSectionDiff G U₀ hU₀ ε₁ ε₁ :=
        infinitesimalSectionDiff_add_infinitesimalSectionDiff G U₀ hU₀ ε₁ δ ε₁
    _ = 0 := infinitesimalSectionDiff_self G U₀ hU₀ ε₁

include hU₀ in
/-- If every `𝒪_{U₀}`-linear map `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` is the difference from any given
element of `Γ₀` of some element of `Γ₀`, then it is the difference from that element of exactly
one element of `Γ₀`. -/
theorem existsUnique_infinitesimalSectionDiff_of_exists
    (hex : ∀ (δ : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀),
      ∃ ε : InfinitesimalSections G U₀, infinitesimalSectionDiff G U₀ hU₀ δ ε = θ)
    (δ : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀) :
    ∃! ε : InfinitesimalSections G U₀, infinitesimalSectionDiff G U₀ hU₀ δ ε = θ := by
  obtain ⟨ε, hε⟩ := hex δ θ
  exact ⟨ε, hε, fun ε' hε' =>
    infinitesimalSectionDiff_injective G U₀ hU₀ δ (hε'.trans hε.symm)⟩

include hU₀ in
/-- The structure `InfinitesimalSectionDifference G U₀` built from the existence clause alone:
every `𝒪_{U₀}`-linear map is the difference from any given element of `Γ₀` of some element of
`Γ₀`. -/
noncomputable def infinitesimalSectionDifferenceOfExists
    (hex : ∀ (δ : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀),
      ∃ ε : InfinitesimalSections G U₀, infinitesimalSectionDiff G U₀ hU₀ δ ε = θ) :
    InfinitesimalSectionDifference G U₀ :=
  infinitesimalSectionDifferenceOfExistsUnique G U₀ hU₀
    (existsUnique_infinitesimalSectionDiff_of_exists G U₀ hU₀ hex)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
