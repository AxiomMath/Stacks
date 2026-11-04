module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonalSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothQuotientStack

/-!
# A gerbe morphism of algebraic stacks is surjective and smooth (Stacks 0DN8)

**Stacks 0DN8** asserts that a 1-morphism `π : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which
exhibits `𝒳` as a gerbe over `𝒴` (**Stacks 06QC**) is surjective and smooth.

Surjectivity is the surjectivity clause of **Stacks 06QI**
(`AlgebraicGeometry.Stack.isSurjective_of_isGerbeOver`).

For smoothness the source argues fppf-locally on `𝒴`: by **Stacks 0DN7** it suffices to prove it
after a surjective, flat, locally finitely presented base change, and by **Stacks 06QH** and
**Stacks 0DLS** a suitable base change is a classifying stack `[U/G] ⟶ U`, which is smooth. The
proof here makes the base change along `π` itself, where the reduction is immediate:

* `π` is surjective, flat and locally of finite presentation (**Stacks 06QI**), so by
  **Stacks 0DN7** (`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_baseChange`) it suffices
  that the first projection `pr : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳` is smooth;
* `pr` has the relative diagonal `Δ_π : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` as a section, and `Δ_π` is representable
  by algebraic spaces (**Stacks 04XS**), surjective, flat and locally of finite presentation
  (**Stacks 0CPR**, part (2));
* so smoothness of `Δ_π ≫ pr = 𝟙 𝒳` descends to `pr` by **Stacks 0AHE**
  (`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_comp_of_fppf`).

This is the source's argument with the base change `𝒴' ⟶ 𝒴` taken to be `π`: over `𝒳` the gerbe
`𝒳 ×_𝒴 𝒳 ⟶ 𝒳` has the section `Δ_π`, so it is the classifying stack of its automorphism group,
and the smoothness of that classifying stack, which the source reads off from Stacks 0DLS, is the
descent along the section.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_id`: the identity 1-morphism of an algebraic
  stack is smooth.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_isGerbeOver`: a gerbe is smooth.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSurjective_and_isSmooth_of_isGerbeOver`:
  **Stacks 0DN8**.

## References

* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QH](https://stacks.math.columbia.edu/tag/06QH)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
* [Stacks Project, Tag 0AHE](https://stacks.math.columbia.edu/tag/0AHE)
* [Stacks Project, Tag 0CPR](https://stacks.math.columbia.edu/tag/0CPR)
* [Stacks Project, Tag 0DLS](https://stacks.math.columbia.edu/tag/0DLS)
* [Stacks Project, Tag 0DN7](https://stacks.math.columbia.edu/tag/0DN7)
* [Stacks Project, Tag 0DN8](https://stacks.math.columbia.edu/tag/0DN8)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The identity 1-morphism of an algebraic stack over `S` is smooth.** A smooth presentation
of `𝒳` by an algebraic space `V`, surjective on objects, is a diagram of Stacks 06FM over `𝟙 𝒳`
whose two vertical 1-morphisms are that presentation and whose top horizontal morphism is `𝟙 V`,
which is smooth. -/
theorem isSmooth_id (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : IsSmooth B S hS (𝟙 𝒳) := by
  obtain ⟨V, hV, b, hbsm, hbsu⟩ :=
    Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS
      𝒳.property
  obtain ⟨κ⟩ := Stack.nonempty_twoIso_associatedMap_id B S hS V
  refine ⟨V, V, hV, hV, b, b, 𝟙 V, ⟨?_⟩, hbsm, hbsu, hbsm, Space.isSmooth_id B S hS hV⟩
  exact Bicategory.whiskerRightIso κ b ≪≫ Bicategory.leftUnitor b ≪≫
    (Bicategory.rightUnitor b).symm

/-- **A gerbe is smooth.** A 1-morphism `π : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which exhibits
`𝒳` as a gerbe over `𝒴` is smooth.

By Stacks 0DN7 along `π`, which is surjective, flat and locally of finite presentation, it
suffices that the first projection `𝒳 ×_𝒴 𝒳 ⟶ 𝒳` is smooth; the relative diagonal is a section
of it which is representable by algebraic spaces, surjective, flat and locally of finite
presentation, so Stacks 0AHE descends the smoothness of the identity along it. -/
theorem isSmooth_of_isGerbeOver {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsGerbeOver B S hS f) : IsSmooth B S hS f := by
  obtain ⟨hflat, hlfp⟩ := isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS f hf
  obtain ⟨hΔflat, hΔlfp⟩ :=
    isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf
  refine isSmooth_of_baseChange B S hS f f (Stack.isSurjective_of_isGerbeOver B S hS f hf)
    hflat hlfp ?_
  exact isSmooth_of_comp_of_fppf B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) _
    (isSmooth_id B S hS 𝒳)
    (Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
    (isSurjective_relativeDiagonal_of_isGerbeOver B S hS f hf) hΔflat hΔlfp

/-- **Stacks 0DN8.** Let `π : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. If `𝒳` is a
gerbe over `𝒴`, then `π` is surjective and smooth. -/
@[stacks 0DN8]
theorem isSurjective_and_isSmooth_of_isGerbeOver {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    Stack.IsSurjective B S hS f ∧ IsSmooth B S hS f :=
  ⟨Stack.isSurjective_of_isGerbeOver B S hS f hf, isSmooth_of_isGerbeOver B S hS f hf⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
